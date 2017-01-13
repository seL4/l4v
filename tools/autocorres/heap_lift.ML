(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Rewrite L2 specifications to use a higher-level ("lifted") heap representation.
 *
 * The main interface to this module is translate (and inner functions
 * convert and define). See AutoCorresUtil for a conceptual overview.
 *)

structure HeapLift =
struct

(* Convenience shortcuts. *)
val warning = Utils.ac_warning
val apply_tac = Utils.apply_tac
val the' = Utils.the'

(* Print the current goal state then fail hard. *)
exception ProofFailed of string

fun fail_tac ctxt s = (print_tac ctxt s THEN (fn _ => Seq.single (raise (ProofFailed s))))

type heap_info = HeapLiftBase.heap_info

(* Return the function for fetching an object of a particular type. *)
fun get_heap_getter (heap_info : heap_info) T =
  case Typtab.lookup (#heap_getters heap_info) T of
    SOME x => Const x
  | NONE => Utils.invalid_typ "heap type for getter" T

(* Return the function for updating an object of a particular type. *)
fun get_heap_setter (heap_info : heap_info) T =
  case Typtab.lookup (#heap_setters heap_info) T of
    SOME x => Const x
  | NONE => Utils.invalid_typ "heap type for setter" T

(* Return the function for determining if a given pointer is valid for a type. *)
fun get_heap_valid_getter (heap_info : heap_info) T =
  case Typtab.lookup (#heap_valid_getters heap_info) T of
    SOME x => Const x
  | NONE => Utils.invalid_typ "heap type for valid getter" T

(* Return the function for updating if a given pointer is valid for a type. *)
fun get_heap_valid_setter (heap_info : heap_info) T =
  case Typtab.lookup (#heap_valid_setters heap_info) T of
    SOME x => Const x
  | NONE => Utils.invalid_typ "heap type for valid setter" T

(* Return the heap type used by a function. *)
fun get_expected_fn_state_type heap_info is_function_lifted fn_name =
  if is_function_lifted fn_name then
    #globals_type heap_info
  else
    #old_globals_type heap_info

(* Get a state translation function for the given function. *)
fun get_expected_st heap_info is_function_lifted fn_name =
  if is_function_lifted fn_name then
    (#lift_fn_full heap_info)
  else
    @{mk_term "id :: ?'a => ?'a" ('a)} (#old_globals_type heap_info)

(* Get the expected type of a function from its name. *)
fun get_expected_hl_fn_type prog_info l2_infos (heap_info : HeapLiftBase.heap_info)
                            is_function_lifted fn_name =
let
  val fn_def = the (Symtab.lookup l2_infos fn_name)
  val fn_params_typ = map snd (#args fn_def)
  (* Fill in the measure argument and return type *)
  val globals_typ = get_expected_fn_state_type heap_info is_function_lifted fn_name
  val fn_ret_typ = #return_type fn_def
  val measure_typ = @{typ "nat"}
  val fn_typ = (measure_typ :: fn_params_typ)
                 ---> LocalVarExtract.mk_l2monadT globals_typ fn_ret_typ @{typ unit}
in
  fn_typ
end

(* Get the expected theorem that will be generated about a function. *)
fun get_expected_hl_fn_thm prog_info l2_infos (heap_info : HeapLiftBase.heap_info)
    is_function_lifted ctxt fn_name function_free fn_args _ measure_var =
let
  (* Get L2 const *)
  val l2_def = the (Symtab.lookup l2_infos fn_name)
  val l2_term = betapplys (#const l2_def, measure_var :: fn_args)

  (* Get expected HL const. *)
  val hl_term = betapplys (function_free, measure_var :: fn_args)
in
  @{mk_term "Trueprop (L2Tcorres ?st ?A ?C)" (st, A, C)}
    (get_expected_st heap_info is_function_lifted fn_name, hl_term, l2_term)
end

(* Get arguments passed into the function. *)
fun get_expected_hl_fn_args prog_info l2_infos fn_name =
  #args (the (Symtab.lookup l2_infos fn_name))

(*
 * Guess whether a function can be lifted.
 *
 * For example, we probably can't lift functions that introspect the heap-type
 * data "hrs_htd".
 *)
fun can_lift_function lthy prog_info fn_info =
let
  val t = #definition fn_info |> Thm.prop_of |> Utils.rhs_of
  (* Determine if everything in term "t" appears valid for lifting. *)
  val bad_consts = [@{const_name hrs_htd}, @{const_name hrs_htd_update}, @{const_name ptr_retyp}]
  fun term_contains_const_name c t =
    exists_Const (fn (const_name, _) => c = const_name) t
in
  not (exists (fn c => term_contains_const_name c t) bad_consts)
end

(*
 * Convert a cterm from the format "f a (b n) c" into "((f $ a) $ (b $ n)) $ c".
 *
 * Return a "thm" of the form "old = new".
 *)
fun mk_first_order ctxt ct =
let
  fun expand_conv ct =
    Utils.named_cterm_instantiate ctxt
        [("a", Thm.dest_fun ct),("b", Thm.dest_arg ct)] @{lemma "a b == (a $ b)" by simp}
in
  Conv.bottom_conv (K (Conv.try_conv expand_conv)) ctxt ct
end

(* The opposite to "mk_first_order" *)
fun dest_first_order ctxt ct =
  Conv.bottom_conv (K (Conv.try_conv (Conv.rewr_conv
    @{lemma "(op $) == (%a b. a b)" by (rule meta_ext, rule ext, simp)}))) ctxt ct

(*
 * Resolve "base_thm" with "subgoal_thm" in all assumptions it is possible to
 * do so.
 *
 * Return a tuple: (<new thm>, <a change was made>).
 *)
fun greedy_thm_instantiate base_thm subgoal_thm =
let
  val asms = Thm.prop_of base_thm |> Logic.strip_assums_hyp
in
  fold (fn (i, asm) => fn (thm, change_made) =>
    if (Term.could_unify (asm, Thm.concl_of subgoal_thm)) then
      (subgoal_thm RSN (i, thm), true) handle (THM _ ) => (thm, change_made)
    else
      (thm, change_made)) (tag_list 1 asms) (base_thm, false)
end

(* Return a list of thm's where "base_thm" has been successfully resolved with
 * one of "subgoal_thms". *)
fun instantiate_against_thms base_thm subgoal_thms =
  map (greedy_thm_instantiate base_thm) subgoal_thms
  |> filter snd
  |> map fst

(*
 * Modify a list of thms to instantiate assumptions where ever possible.
 *)
fun cross_instantiate base_thms subgoal_thm_lists =
let
  fun iterate_base subgoal_thms base_thms =
    map (fn thm => (instantiate_against_thms thm subgoal_thms) @ [thm]) base_thms
    |> List.concat
in
  fold iterate_base subgoal_thm_lists base_thms
end



(*
 * EXPERIMENTAL: define wrappers and syntax for common heap operations.
 * We use the notations "s[p]->r" for {p->r} and "s[p->r := q]" for {p->r = q}.
 * For non-fields, "s[p]" and "s[p := q]".
 * The wrappers are named like "get_type_field" and "update_type_field".
 *
 * Known issues:
 *  * Every pair of getter/setter and valid/setter lemmas should be generated.
 *    If you find yourself expanding one of the wrapper definitions, then
 *    something wasn't generated correctly.
 *
 *  * On that note, lemmas relating structs and struct fields
 *    (foo vs foo.field) are not being generated.
 *    * TODO: this problem appears in Suzuki.thy
 *
 *  * The syntax looks as terrible as c-parser's. Well, at least you won't need
 *    to subscript greek letters.
 *
 *  * Isabelle doesn't like overloaded syntax. Issue VER-412
 *)

exception NO_GETTER_SETTER (* Not visible externally *)

fun mixfix (sy, ps, p) = Mixfix (Input.string sy, ps, p, Position.no_range)

(* Define getter/setter and syntax for one struct field.
   Returns the getter/setter and their definitions. *)
fun field_syntax (heap_info : HeapLiftBase.heap_info)
                 (struct_info : HeapLiftBase.struct_info)
                 (field_info: HeapLiftBase.field_info)
                 (new_getters, new_setters, lthy) =
let
    fun unsuffix' suffix str = if String.isSuffix suffix str then unsuffix suffix str else str
    val struct_pname = unsuffix' "_C" (#name struct_info)
    val field_pname = unsuffix' "_C" (#name field_info)
    val struct_typ = #struct_type struct_info

    val state_var = ("s", #globals_type heap_info)
    val ptr_var = ("ptr", Type (@{type_name "ptr"}, [struct_typ]))
    val val_var = ("val", #field_type field_info)

    val struct_getter = case Typtab.lookup (#heap_getters heap_info) struct_typ of
                          SOME getter => Const getter
                        | _ => raise NO_GETTER_SETTER
    val struct_setter = case Typtab.lookup (#heap_setters heap_info) struct_typ of
                          SOME setter => Const setter
                        | _ => raise NO_GETTER_SETTER

    (* We will modify lthy soon, so may not exit with NO_GETTER_SETTER after this point *)

    (* Define field accessor function *)
    val field_getter_term = @{mk_term "?field_get (?heap_get s ptr)" (heap_get, field_get)}
                            (struct_getter, #getter field_info)
    val new_heap_get_name = "get_" ^ struct_pname ^ "_" ^ field_pname
    val (new_heap_get, new_heap_get_thm, lthy) =
      Utils.define_const_args new_heap_get_name false field_getter_term
                              [state_var, ptr_var] lthy

    val field_getter = @{mk_term "?get s ptr" (get)} new_heap_get
    val field_getter_typ = type_of (fold lambda (rev [Free state_var, Free ptr_var]) field_getter)

    (* Define field update function *)
    val field_setter_term = @{mk_term "?heap_update (%old. old(ptr := ?field_update (%_. val) (old ptr))) s"
                            (heap_update, field_update)} (struct_setter, #setter field_info)
    val new_heap_update_name = "update_" ^ struct_pname ^ "_" ^ field_pname
    val (new_heap_update, new_heap_update_thm, lthy) =
      Utils.define_const_args new_heap_update_name false field_setter_term
                              [state_var, ptr_var, val_var] lthy

    val field_setter = @{mk_term "?update s ptr new" (update)} new_heap_update
    val field_setter_typ = type_of (fold lambda (rev [Free state_var, Free ptr_var, Free val_var]) field_setter)

    val getter_mixfix = mixfix ("_[_]\<rightarrow>" ^ (Syntax_Ext.escape field_pname), [1000], 1000)
    val setter_mixfix = mixfix ("_[_\<rightarrow>" ^ (Syntax_Ext.escape field_pname) ^ " := _]", [1000], 1000)

    val lthy = Specification.notation true Syntax.mode_default [
                 (new_heap_get, getter_mixfix),
                 (new_heap_update, setter_mixfix)] lthy

    (* The struct_pname returned here must match the type_pname returned in heap_syntax.
     * new_heap_update_thm relies on this to determine what kind of thm to generate. *)
    val new_getters = Symtab.update_new (new_heap_get_name,
          (struct_pname, field_pname, new_heap_get, SOME new_heap_get_thm)) new_getters
    val new_setters = Symtab.update_new (new_heap_update_name,
          (struct_pname, field_pname, new_heap_update, SOME new_heap_update_thm)) new_setters
in
  (new_getters, new_setters, lthy)
end
handle NO_GETTER_SETTER => (new_getters, new_setters, lthy)

(* Define syntax for one C type. This also creates new wrappers for heap updates. *)
fun heap_syntax (heap_info : HeapLiftBase.heap_info)
                (heap_type : typ)
                (new_getters, new_setters, lthy) =
let
    val getter = case Typtab.lookup (#heap_getters heap_info) heap_type of
                   SOME x => x
                 | NONE => raise TYPE ("heap_lift/heap_syntax: no getter", [heap_type], [])
    val setter = case Typtab.lookup (#heap_setters heap_info) heap_type of
                   SOME x => x
                 | NONE => raise TYPE ("heap_lift/heap_syntax: no setter", [heap_type], [])

    fun replace_C (#"_" :: #"C" :: xs) = replace_C xs
      | replace_C (x :: xs) = x :: replace_C xs
      | replace_C [] = []
    val type_pname = HeapLiftBase.name_from_type heap_type
                     |> String.explode |> replace_C |> String.implode

    val state_var = ("s", #globals_type heap_info)
    val heap_ptr_type = Type (@{type_name "ptr"}, [heap_type])
    val ptr_var = ("ptr", heap_ptr_type)
    val val_var = ("val", heap_type)

    val setter_def = @{mk_term "?heap_update (%old. old(ptr := val)) s" heap_update} (Const setter)
    val new_heap_update_name = "update_" ^ type_pname
    val (new_heap_update, new_heap_update_thm, lthy) =
      Utils.define_const_args new_heap_update_name false setter_def
                              [state_var, ptr_var, val_var] lthy

    val getter_mixfix = mixfix ("_[_]", [1000], 1000)
    val setter_mixfix = mixfix ("_[_ := _]", [1000], 1000)

    val lthy = Specification.notation true Syntax.mode_default
               [(Const getter, getter_mixfix), (new_heap_update, setter_mixfix)] lthy

    val new_getters = Symtab.update_new (Long_Name.base_name (fst getter), (type_pname, "", Const getter, NONE)) new_getters
    val new_setters = Symtab.update_new (new_heap_update_name, (type_pname, "", new_heap_update, SOME new_heap_update_thm)) new_setters
in
    (new_getters, new_setters, lthy)
end

(* Make all heap syntax and collect the results. *)
fun make_heap_syntax heap_info lthy =
    (Symtab.empty, Symtab.empty, lthy)
    (* struct fields *)
    |> Symtab.fold (fn (_, struct_info) =>
                       fold (field_syntax heap_info struct_info)
                            (#field_info struct_info)
                   ) (#structs heap_info)
    (* types *)
    |> fold (heap_syntax heap_info) (Typtab.keys (#heap_getters heap_info))

(* Prove lemmas for the new getter/setter definitions. *)
fun new_heap_update_thm (getter_type_name, getter_field_name, getter, getter_def)
                        (setter_type_name, setter_field_name, setter, setter_def)
                        lthy =
  (* TODO: also generate lemmas relating whole-struct updates to field updates *)
  if getter_type_name = setter_type_name
     andalso not ((getter_field_name = "") = (setter_field_name = "")) then NONE else

  let val lhs = @{mk_term "?get (?set s p v)" (get, set)} (getter, setter)
      val rhs = if getter_type_name = setter_type_name andalso
                   getter_field_name = setter_field_name
                (* functional update *)
                then @{mk_term "(?get s) (p := v)" (get)} getter
                (* separation *)
                else @{mk_term "?get s" (get)} getter
      val prop = @{mk_term "Trueprop (?lhs = ?rhs)" (lhs, rhs)} (lhs, rhs)
      val defs = the_list getter_def @ the_list setter_def
      val thm = Goal.prove_future lthy ["s", "p", "v"] [] prop
                  (fn params => (simp_tac ((#context params) addsimps
                                @{thms ext fun_upd_apply} @ defs) 1))
  in SOME thm end

fun new_heap_valid_thm valid_term (_, _, setter, NONE) lthy = NONE
  | new_heap_valid_thm valid_term (_, _, setter, SOME setter_def) lthy =
  let val prop = @{mk_term "Trueprop (?valid (?set s p v) q = ?valid s q)" (valid, set)}
                 (Const valid_term, setter)
      val thm = Goal.prove_future lthy ["s", "p", "v", "q"] [] prop
                  (fn params => (simp_tac ((#context params) addsimps
                                [@{thm fun_upd_apply}, setter_def]) 1))
  in SOME thm end

(* Take a definition and eta contract the RHS:
     lhs = rhs s   ==>   (%s. lhs) = rhs
   This allows us to rewrite a heap update even if the state is eta contracted away. *)
fun eta_rhs lthy thm = let
  val Const (@{const_name "Pure.eq"}, typ) $ lhs $ (rhs $ Var (("s", s_n), s_typ)) = term_of_thm thm
  val abs_term = @{mk_term "?a == ?b" (a, b)} (lambda (Var (("s", s_n), s_typ)) lhs, rhs)
  val thm' = Goal.prove_future lthy [] [] abs_term
               (fn params => simp_tac (put_simpset HOL_basic_ss (#context params) addsimps thm :: @{thms atomize_eq ext}) 1)
in thm' end

(* Extract the abstract term out of a L2Tcorres thm. *)
fun dest_L2Tcorres_term_abs @{term_pat "L2Tcorres _ ?t _"} = t

(* Generate lifted_globals lemmas and instantiate them into the heap lifting rules. *)
fun lifted_globals_lemmas prog_info heap_info lthy = let
  (* Tactic to solve subgoals below. *)
  local
    (* Fetch simp rules generated by the C Parser about structures. *)
    val struct_simpset = UMM_Proof_Theorems.get (Proof_Context.theory_of lthy)
    fun lookup_the t k = case Symtab.lookup t k of SOME x => x | NONE => []
    val struct_simps =
        (lookup_the struct_simpset "typ_name_simps")
        @ (lookup_the struct_simpset "typ_name_itself")
        @ (lookup_the struct_simpset "fl_ti_simps")
        @ (lookup_the struct_simpset "fl_simps")
        @ (lookup_the struct_simpset "fg_cons_simps")
    val base_ss = simpset_of @{theory_context HeapLift}
    val record_ss = RecordUtils.get_record_simpset lthy
    val merged_ss = merge_ss (base_ss, record_ss)

    (* Generate a simpset containing everything we need. *)
    val ss =
      (Context_Position.set_visible false lthy)
      |> put_simpset merged_ss
      |> (fn ctxt => ctxt
                addsimps [#lift_fn_thm heap_info]
                    @ @{thms typ_simple_heap_simps}
                    @ @{thms valid_globals_field_def}
                    @ @{thms the_fun_upd_lemmas}
                    @ struct_simps)
      |> simpset_of
  in
    fun subgoal_solver_tac ctxt =
      (fast_force_tac (put_simpset ss ctxt) 1)
        ORELSE (CHANGED (Method.try_intros_tac ctxt [@{thm conjI}, @{thm ext}] []
            THEN clarsimp_tac (put_simpset ss ctxt) 1))
  end

  (* Generate "valid_typ_heap" predicates for each heap type we have. *)
  fun mk_valid_typ_heap_thm typ =
    @{mk_term "Trueprop (valid_typ_heap ?st ?getter ?setter ?valid_getter ?valid_setter ?t_hrs ?t_hrs_update)"
        (st, getter, setter, valid_getter, valid_setter, t_hrs, t_hrs_update)}
      (#lift_fn_full heap_info,
          get_heap_getter heap_info typ,
          get_heap_setter heap_info typ,
          get_heap_valid_getter heap_info typ,
          get_heap_valid_setter heap_info typ,
          #t_hrs_getter prog_info,
          #t_hrs_setter prog_info)
    |> (fn prop => Goal.prove_future lthy [] [] prop
         (fn params =>
             ((resolve_tac lthy @{thms valid_typ_heapI} 1) THEN (
                 REPEAT (subgoal_solver_tac (#context params))))))

  (* Make thms for all types. *)
  (* FIXME: these are currently auto-parallelised using prove_future, but perhaps
   * we should exercise finer control over the evaluation, as prove_futures
   * persist long after the AutoCorres command actually returns. *)
  val heap_types = (#heap_getters heap_info |> Typtab.dest |> map fst)
  val valid_typ_heap_thms = map mk_valid_typ_heap_thm heap_types

  (* Generate "valid_typ_heap" thms for signed words. *)
  val valid_typ_heap_thms =
      valid_typ_heap_thms
      @ (map_product
            (fn a => fn b => try (fn _ => a OF [b]) ())
            @{thms signed_valid_typ_heaps}
            valid_typ_heap_thms
        |> map_filter I)

  (* Generate "valid_struct_field" for each field of each struct. *)
  fun mk_valid_struct_field_thm struct_name typ (field_info : HeapLiftBase.field_info) =
    @{mk_term "Trueprop (valid_struct_field ?st [?fname] ?fgetter ?fsetter ?t_hrs ?t_hrs_update)"
        (st, fname, fgetter, fsetter, t_hrs, t_hrs_update) }
      (#lift_fn_full heap_info,
          Utils.encode_isa_string (#name field_info),
          #getter field_info,
          #setter field_info,
          #t_hrs_getter prog_info,
          #t_hrs_setter prog_info)
    |> (fn prop =>
         (* HACK: valid_struct_field currently works only for packed types,
          * so typecheck the prop first *)
         case try (Syntax.check_term lthy) prop of
           SOME _ =>
             [Goal.prove_future lthy [] [] prop
                (fn params =>
                   (resolve_tac lthy @{thms valid_struct_fieldI} 1) THEN
                   (* Need some extra thms from the records package for our struct type. *)
                   (EqSubst.eqsubst_tac lthy [0]
                      [hd (Proof_Context.get_thms lthy (struct_name ^ "_idupdates")) RS @{thm sym}] 1
                      THEN asm_full_simp_tac lthy 1) THEN
                   (FIRST (Proof_Context.get_thms lthy (struct_name ^ "_fold_congs")
                           |> map (fn t => resolve_tac lthy [t OF @{thms refl refl}] 1))
                      THEN asm_full_simp_tac lthy 1) THEN
                   (REPEAT (subgoal_solver_tac (#context params))))]
           | NONE => [])

  (* Generate "valid_struct_field_legacy" for each field of each struct. *)
  fun mk_valid_struct_field_legacy_thm typ (field_info : HeapLiftBase.field_info) =
    @{mk_term "Trueprop (valid_struct_field_legacy ?st [?fname] ?fgetter (%v. ?fsetter (%_. v)) ?getter ?setter ?valid_getter ?valid_setter ?t_hrs ?t_hrs_update)"
        (st, fname, fgetter, fsetter, getter, setter, valid_getter, valid_setter, t_hrs, t_hrs_update) }
      (#lift_fn_full heap_info,
          Utils.encode_isa_string (#name field_info),
          #getter field_info,
          #setter field_info,
          get_heap_getter heap_info typ,
          get_heap_setter heap_info typ,
          get_heap_valid_getter heap_info typ,
          get_heap_valid_setter heap_info typ,
          #t_hrs_getter prog_info,
          #t_hrs_setter prog_info)
    |> (fn prop => Goal.prove_future lthy [] [] prop
           (fn params =>
               (resolve_tac lthy @{thms valid_struct_field_legacyI} 1) THEN (
                   REPEAT (subgoal_solver_tac (#context params)))))

  (* Make thms for all fields of structs in our heap. *)
  fun valid_struct_abs_thms T =
    case (Typtab.lookup (#struct_types heap_info) T) of
      NONE => []
    | SOME struct_info =>
        map (fn field =>
                  mk_valid_struct_field_thm (#name struct_info) T field
                  @ [mk_valid_struct_field_legacy_thm T field])
            (#field_info struct_info)
        |> List.concat
  val valid_field_thms =
    map valid_struct_abs_thms heap_types |> List.concat

  (* Generate conversions from globals embedded directly in the "globals" and
   * "lifted_globals" record. *)
  fun mk_valid_globals_field_thm name =
    @{mk_term "Trueprop (valid_globals_field ?st ?old_get ?old_set ?new_get ?new_set)"
      (st, old_get, old_set, new_get, new_set)}
      (#lift_fn_full heap_info,
        Symtab.lookup (#global_field_getters heap_info) name |> the |> fst,
        Symtab.lookup (#global_field_setters heap_info) name |> the |> fst,
        Symtab.lookup (#global_field_getters heap_info) name |> the |> snd,
        Symtab.lookup (#global_field_setters heap_info) name |> the |> snd)
    |> (fn prop => Goal.prove_future lthy [] [] prop (fn params => subgoal_solver_tac (#context params)))
  val valid_global_field_thms = map (#1 #> mk_valid_globals_field_thm) (#global_fields heap_info)

  (* At this point, the lemmas are ready to be instantiated into the generic
   * heap_abs rules (which will be fetched from the most recent lthy). *)
in
  [ valid_typ_heap_thms, valid_field_thms, valid_global_field_thms ]
end;


(*
 * Prepare for the heap lifting phase.
 * We need to:
 *   - define a lifted_globals type
 *   - prove generic heap lifting lemmas for the lifted_globals type
 *   - define heap syntax and rewrite rules (if heap_abs_syntax is set)
 *   - store these new results into the HeapInfo theory data
 * Note that because we are adding definitions that are required by all
 * conversions, we need to wait for all previous L2 conversions to finish,
 * limiting parallelism somewhat. This requires us to modify l2_results by
 * updating its intermediate lthys.
 *
 * These results are cached in the local theory, so we attempt to fetch an
 * existing definition (in the case that we are resuming a previous run).
 * In this scenario, we don't have to modify l2_results.
 *)
fun prepare_heap_lift
    (filename : string)
    (prog_info : ProgramInfo.prog_info)
    (l2_results : (local_theory * FunctionInfo.function_info Symtab.table) FSeq.fseq)
    (* An initial lthy, used to check for an existing heap_lift_setup.
     * Also used as fallback target in the unlikely case where l2_results = [] *)
    (lthy0 : local_theory)
    (* We define the lifted heap for all functions in the program, even if they are
     * not included in this translation. This allows heap lifting to work with
     * incremental translations. *)
    (all_simpl_infos : FunctionInfo.function_info Symtab.table)
    (* Settings *)
    (make_lifted_globals_field_name : string -> string)
    (gen_word_heaps : bool)
    (heap_abs_syntax : bool)
    : ((local_theory * FunctionInfo.function_info Symtab.table) FSeq.fseq
        * HeapLiftBase.heap_lift_setup) =
let
  (* Get target lthy for adding new definitions.
   * This is the most recent l2_results lthy, except if there are no results,
   * in which case the fallback lthy is used. *)
  fun get_target_lthy l2_results fallback_lthy =
        if FSeq.null l2_results then Option.getOpt (fallback_lthy, lthy0)
        else fst (List.last (FSeq.list_of l2_results));

  fun update_results lthy = FSeq.map (apfst (K lthy));

  (* Set up heap_info and associated lemmas *)
  val (l2_results, HL_setup, fallback_lthy) =
      case Symtab.lookup (HeapInfo.get (Proof_Context.theory_of lthy0)) filename of
          SOME HL_setup => (l2_results, HL_setup, NONE)
        | NONE => let
            val lthy = get_target_lthy l2_results NONE;
            val (heap_info, lthy) = HeapLiftBase.setup prog_info all_simpl_infos
                                        make_lifted_globals_field_name gen_word_heaps lthy;
            val lifted_heap_lemmas = lifted_globals_lemmas prog_info heap_info lthy;
            val HL_setup = { heap_info = heap_info,
                             lifted_heap_lemmas = lifted_heap_lemmas,
                             heap_syntax_rewrs = [] };
            val lthy = Local_Theory.background_theory (
                  HeapInfo.map (fn tbl => Symtab.update (filename, HL_setup) tbl)) lthy;
            in (update_results lthy l2_results, HL_setup, SOME lthy) end;

  (* Do some extra lifting and create syntax (see field_syntax comment).
   * We do this separately because heap_abs_syntax could be enabled halfway
   * through an incremental translation. *)
  val (l2_results, HL_setup, fallback_lthy) =
    if not heap_abs_syntax orelse not (null (#heap_syntax_rewrs HL_setup))
    then (l2_results, HL_setup, fallback_lthy)
    else
      let val lthy = get_target_lthy l2_results fallback_lthy;
          val (heap_syntax_rewrs, lthy) =
            Utils.exec_background_result (fn lthy => let
                val optcat = List.mapPartial I
                val heap_info = #heap_info HL_setup

                (* Define the new heap operations and their syntax. *)
                val (new_getters, new_setters, lthy) =
                    make_heap_syntax heap_info lthy

                (* Make simplification thms and add them to the simpset. *)
                val update_thms = map (fn get => map (fn set => new_heap_update_thm get set lthy)
                                                     (Symtab.dest new_setters |> map snd))
                                      (Symtab.dest new_getters |> map snd)
                                  |> List.concat
                val valid_thms = map (fn valid => map (fn set => new_heap_valid_thm valid set lthy)
                                                      (Symtab.dest new_setters |> map snd))
                                     (Typtab.dest (#heap_valid_getters heap_info) |> map snd)
                                 |> List.concat
                val thms = update_thms @ valid_thms |> optcat
                val lthy = Utils.simp_add thms lthy

                (* Name the thms. (FIXME: do this elsewhere?) *)
                val (_, lthy) = Utils.define_lemmas "heap_abs_simps" thms lthy

                (* Rewrite rules for converting the program. *)
                val getter_thms = Symtab.dest new_getters |> map (#4 o snd) |> optcat
                val setter_thms = Symtab.dest new_setters |> map (#4 o snd) |> optcat
                val eta_setter_thms = map (eta_rhs lthy) setter_thms
                val rewrite_thms = map (fn thm => @{thm symmetric} OF [thm])
                                       (getter_thms @ eta_setter_thms)
            in (rewrite_thms, lthy) end) lthy;
      val HL_setup = { heap_info = #heap_info HL_setup,
                       lifted_heap_lemmas = #lifted_heap_lemmas HL_setup,
                       heap_syntax_rewrs = heap_syntax_rewrs };
      val lthy = Local_Theory.background_theory (
            HeapInfo.map (fn tbl => Symtab.update (filename, HL_setup) tbl)) lthy;
      in (update_results lthy l2_results, HL_setup, SOME lthy) end;

  in (l2_results, HL_setup) end;

(* Convert a program to use a lifted heap. *)
fun translate
    (filename : string)
    (prog_info : ProgramInfo.prog_info)
    (l2_results : FunctionInfo.phase_results)
    (existing_l2_infos : FunctionInfo.function_info Symtab.table)
    (existing_hl_infos : FunctionInfo.function_info Symtab.table)
    (HL_setup : HeapLiftBase.heap_lift_setup)
    (no_heap_abs : Symset.key Symset.set)
    (force_heap_abs : Symset.key Symset.set)
    (heap_abs_syntax : bool)
    (keep_going : bool)
    (trace_funcs : string list)
    (do_opt : bool)
    (trace_opt : bool)
    (add_trace: string -> string -> AutoCorresData.Trace -> unit)
    (hl_function_name : string -> string)
    : FunctionInfo.phase_results =
if FSeq.null l2_results then FSeq.empty () else
let
  (* lthy for conversion rules. This needs to be (at latest) the earliest lthy
   * result so that the rules can be used in all conversions *)
  val lthy0 = fst (FSeq.hd l2_results);
  val heap_info = #heap_info HL_setup;

  (*
   * Fetch rules from the theory, instantiating any rule with the
   * lifted_globals lemmas for "valid_globals_field", "valid_typ_heap" etc.
   * that we generated previously.
   *)
  val base_rules = Utils.get_rules lthy0 @{named_theorems heap_abs}
  val rules =
      cross_instantiate base_rules (#lifted_heap_lemmas HL_setup)
      (* Remove rules that haven't been fully instantiated *)
      |> filter_out (Thm.prop_of #> exists_subterm (fn x =>
           case x of Const (@{const_name "valid_globals_field"}, _) => true
                   | Const (@{const_name "valid_struct_field"}, _) => true
                   | Const (@{const_name "valid_struct_field_legacy"}, _) => true
                   | Const (@{const_name "valid_typ_heap"}, _) => true
                   | _ => false));

  (* We only use this blanket rule for non-lifted functions;
   * liftable expressions can be handled by specific struct_rewrite rules *)
  val nolift_rules = @{thms struct_rewrite_expr_id}

  (* This does a linear search. We will only need it in is_function_lifted, though *)
  fun lookup_l2_results f_name =
        FSeq.find (fn (_, l2_infos) => Symtab.defined l2_infos f_name) l2_results
        |> the' ("HL: missing L2 results for " ^ f_name);
  fun is_function_lifted f_name =
        case Symtab.lookup existing_hl_infos f_name of
            SOME info => let
              (* We heap-lifted this function earlier. Check its state type. *)
              val body = #definition info |> Thm.prop_of |> Utils.rhs_of_eq;
              val stT = LocalVarExtract.l2monad_state_type body;
              in stT = #globals_type heap_info end
          | NONE => let
              val (lthy, l2_infos) = lookup_l2_results f_name;
              val can_lift =
                    if can_lift_function lthy prog_info (the (Symtab.lookup l2_infos f_name))
                    then not (Symset.contains no_heap_abs f_name)
                    else if Symset.contains force_heap_abs f_name
                         then true
                         else (* Report functions that we're not lifting,
                               * but not if the user has overridden explicitly *)
                              (if Symset.contains no_heap_abs f_name then () else
                                 writeln ("HL: disabling heap lift for: " ^ f_name ^
                                          " (use force_heap_abs to enable)");
                               false);
              in can_lift end;
  (* Cache answers for which functions we are lifting. *)
  val is_function_lifted = String_Memo.memo is_function_lifted;

  (* Convert to new heap format. *)
  fun convert lthy l2_infos f: AutoCorresUtil.convert_result =
  let
    val f_l2_info = the (Symtab.lookup l2_infos f);

    (* Fix measure variable. *)
    val ([measure_var_name], lthy) = Variable.variant_fixes ["rec_measure'"] lthy;
    val measure_var = Free (measure_var_name, AutoCorresUtil.measureT);

  (* Add callee assumptions. *)
    val (lthy, export_thm, callee_terms) =
      AutoCorresUtil.assume_called_functions_corres lthy
        (#callees f_l2_info) (#rec_callees f_l2_info)
        (get_expected_hl_fn_type prog_info l2_infos heap_info is_function_lifted)
        (get_expected_hl_fn_thm prog_info l2_infos heap_info is_function_lifted)
        (get_expected_hl_fn_args prog_info l2_infos)
        hl_function_name
        measure_var;

    (* Fix argument variables. *)
    val new_fn_args = get_expected_hl_fn_args prog_info l2_infos f;
    val (arg_names, lthy) = Variable.variant_fixes (map fst new_fn_args) lthy;
    val arg_frees = map Free (arg_names ~~ map snd new_fn_args);

    (* Fetch the function definition. *)
    val l2_body_def =
        #definition f_l2_info
        (* Instantiate the arguments. *)
        |> Utils.inst_args lthy (map (Thm.cterm_of lthy) (measure_var :: arg_frees))

    (* Get L2 body definition with function arguments. *)
    val l2_term = betapplys (#const f_l2_info, measure_var :: arg_frees)

    (* Get our state translation function. *)
    val st = get_expected_st heap_info is_function_lifted f

    (* Generate a schematic goal. *)
    val goal = @{mk_term "Trueprop (L2Tcorres ?st ?A ?C)" (st, C)}
        (st, l2_term)
        |> Thm.cterm_of lthy
        |> Goal.init
        |> Utils.apply_tac "unfold RHS" (EqSubst.eqsubst_tac lthy [0] [l2_body_def] 1)

    val callee_mono_thms =
        callee_terms |> map fst
        |> List.mapPartial (fn callee =>
               if FunctionInfo.is_function_recursive (the (Symtab.lookup l2_infos callee))
               then #mono_thm (the (Symtab.lookup l2_infos callee))
               else NONE)
    val rules = rules @ (map (snd #> #3) callee_terms) @ callee_mono_thms
    val rules = if is_function_lifted f then rules else rules @ nolift_rules
    val fo_rules = Utils.get_rules lthy @{named_theorems heap_abs_fo}

    (* Apply a conversion to the concrete side of the given L2T term.
     * By convention, the concrete side is the last argument (index ~1). *)
    fun l2t_conc_body_conv conv =
      Conv.params_conv (~1) (K (Conv.arg_conv (Utils.nth_arg_conv (~1) conv)))

    (* Standard tactics. *)
    val print_debug = f = ""
    fun rtac_all r n = (APPEND_LIST (map (fn thm =>
                          resolve_tac lthy [thm] n THEN (fn x =>
                            (if print_debug then @{trace} thm else ();
                            Seq.succeed x))) r))

    (* Convert the concrete side of the given L2T term to/from first-order form. *)
    val l2t_to_fo_tac = CONVERSION (Drule.beta_eta_conversion then_conv l2t_conc_body_conv (mk_first_order lthy) lthy)
    val l2t_from_fo_tac = CONVERSION (l2t_conc_body_conv (dest_first_order lthy then_conv Drule.beta_eta_conversion) lthy)
    val fo_tac = ((l2t_to_fo_tac THEN' rtac_all fo_rules) THEN_ALL_NEW l2t_from_fo_tac) 1

    (*
     * Recursively solve subgoals.
     *
     * We allow backtracking in order to solve a particular subgoal, but once a
     * subgoal is completed we don't ever try to solve it in a different way.
     *
     * This allows us to try different approaches to solving subgoals without
     * leading to exponential explosion (of many different combinations of
     * "good solutions") once we hit an unsolvable subgoal.
     *)
    val tactics =
        if #is_simpl_wrapper f_l2_info
        then (* Solver for trivial simpl wrappers. *)
             [(@{thm L2Tcorres_id}, resolve_tac lthy [@{thm L2Tcorres_id}] 1)]
        else map (fn rule => (rule, resolve_tac lthy [rule] 1)) rules
             @ [(@{thm fun_app_def}, fo_tac)]

    val replay_failure_start = 1
    val replay_failures = Unsynchronized.ref replay_failure_start
    val (thm, trace) =
         case AutoCorresTrace.maybe_trace_solve_tac lthy (member (op =) trace_funcs f)
                true false (K tactics) goal NONE replay_failures of
            NONE => (* intentionally generate a TRACE_SOLVE_TAC_FAIL *)
                    (AutoCorresTrace.trace_solve_tac lthy false false (K tactics) goal NONE (Unsynchronized.ref 0);
                     (* never reached *) error "heap_lift fail tac: impossible")
          | SOME (thm, [trace]) => (Goal.finish lthy thm, trace)
    val _ = if !replay_failures < replay_failure_start then
              warning ("HL: " ^ f ^ ": reverted to slow replay " ^
                        Int.toString(replay_failure_start - !replay_failures) ^ " time(s)") else ()

    (* DEBUG: make sure that all uses of field_lvalue and c_guard are rewritten.
     *        Also make sure that we cleaned up internal constants. *)
    fun contains_const name = exists_subterm (fn x => case x of Const (n, _) => n = name | _ => false)
    fun const_gone term name =
        if not (contains_const name term) then ()
        else Utils.TERM_non_critical keep_going
               ("Heap lift: could not remove " ^ name ^ " in " ^ f ^ ".") [term]
    fun const_old_heap term name =
        if not (contains_const name term) then ()
        else warning ("Heap lift: could not remove " ^ name ^ " in " ^ f ^
                      ". Output program may be unprovable.")
    val _ = if not (is_function_lifted f) then []
            else (map (const_gone (term_of_thm thm))
                      [@{const_name "heap_lift__h_val"}];
                  map (const_old_heap (term_of_thm thm))
                      [@{const_name "field_lvalue"}, @{const_name "c_guard"}]
                 )

    (* Apply peephole optimisations to the theorem. *)
    val _ = writeln ("Simplifying (HL) " ^ f)
    val (thm, opt_traces) = L2Opt.cleanup_thm_tagged lthy thm (if do_opt then 0 else 2) 2 trace_opt "HL"

    (* If we created extra heap wrappers, apply them now.
     * Our simp rules don't seem to be enough for L2Opt,
     * so we cannot change the program before that. *)
    val thm = if not heap_abs_syntax then thm else
                Raw_Simplifier.rewrite_rule lthy (#heap_syntax_rewrs HL_setup) thm

    val f_body = dest_L2Tcorres_term_abs (HOLogic.dest_Trueprop (Thm.concl_of thm));
    (* Get actual recursive callees *)
    val rec_callees = AutoCorresUtil.get_rec_callees callee_terms f_body;

    (* Return the constants that we fixed. This will be used to process the returned body. *)
    val callee_consts =
          callee_terms |> map (fn (callee, (_, const, _)) => (callee, const)) |> Symtab.make;
  in
    { body = f_body,
      proof = Morphism.thm export_thm thm,
      rec_callees = rec_callees,
      callee_consts = callee_consts,
      arg_frees = map dest_Free (measure_var :: arg_frees),
      traces = (if member (op =) trace_funcs f
                then [("HL", AutoCorresData.RuleTrace trace)] else []) @ opt_traces
    }
  end

  (* Define a previously-converted function (or recursive function group).
   * lthy must include all definitions from hl_callees. *)
  fun define
        (lthy: local_theory)
        (l2_infos: FunctionInfo.function_info Symtab.table)
        (hl_callees: FunctionInfo.function_info Symtab.table)
        (funcs: AutoCorresUtil.convert_result Symtab.table)
        : FunctionInfo.function_info Symtab.table * local_theory = let
    val funcs' = Symtab.dest funcs |>
          map (fn result as (name, {proof, arg_frees, ...}) =>
                     (name, (AutoCorresUtil.abstract_fn_body l2_infos result,
                             proof, arg_frees)));
    val (new_thms, lthy') =
          AutoCorresUtil.define_funcs
              FunctionInfo.HL filename l2_infos hl_function_name
              (get_expected_hl_fn_type prog_info l2_infos heap_info is_function_lifted)
              (get_expected_hl_fn_thm prog_info l2_infos heap_info is_function_lifted)
              (get_expected_hl_fn_args prog_info l2_infos)
              @{thm L2Tcorres_recguard_0}
              lthy (Symtab.map (K #corres_thm) hl_callees)
              funcs';
    val new_infos = Symtab.map (fn f_name => fn (const, def, corres_thm) => let
          val old_info = the (Symtab.lookup l2_infos f_name);
          in old_info
             |> FunctionInfo.function_info_upd_phase FunctionInfo.HL
             |> FunctionInfo.function_info_upd_const const
             |> FunctionInfo.function_info_upd_definition def
             |> FunctionInfo.function_info_upd_corres_thm corres_thm
             |> FunctionInfo.function_info_upd_mono_thm NONE (* added later *)
          end) new_thms;
    in (new_infos, lthy') end;

  (* Do conversions in parallel. *)
  val converted_groups = AutoCorresUtil.par_convert convert existing_l2_infos l2_results add_trace;

  (* Sequence of new function_infos and intermediate lthys *)
  val def_results = FSeq.mk (fn _ =>
        (* If there's nothing to translate, we won't have a lthy to use *)
        if FSeq.null l2_results then NONE else
          let (* Get initial lthy from end of L2 defs *)
              val (l2_lthy, _) = FSeq.list_of l2_results |> List.last;
              val results = AutoCorresUtil.define_funcs_sequence
                              l2_lthy define existing_l2_infos existing_hl_infos converted_groups;
          in FSeq.uncons results end);

  (* Produce a mapping from each function group to its L1 phase_infos and the
   * earliest intermediate lthy where it is defined. *)
  val results =
        def_results
        |> FSeq.map (fn (lthy, f_defs) => let
              (* Add monad_mono proofs. These are done in parallel as well
               * (though in practice, they already run pretty quickly). *)
              val mono_thms = if FunctionInfo.is_function_recursive (snd (hd (Symtab.dest f_defs)))
                              then LocalVarExtract.l2_monad_mono lthy f_defs
                              else Symtab.empty;
              val f_defs' = f_defs |> Symtab.map (fn f =>
                    FunctionInfo.function_info_upd_mono_thm (Symtab.lookup mono_thms f));
              in (lthy, f_defs') end);
in results end

end
