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
fun get_expected_fn_state_type heap_info unliftable_functions fn_name =
  if Symset.contains unliftable_functions fn_name then
    #old_globals_type heap_info
  else
    #globals_type heap_info

(* Get a state translation function for the given function. *)
fun get_expected_st heap_info unliftable_functions fn_name =
  if Symset.contains unliftable_functions fn_name then
    @{mk_term "id :: ?'a => ?'a" ('a)} (#old_globals_type heap_info)
  else
    (#lift_fn_full heap_info)

(* Get the expected type of a function from its name. *)
fun get_expected_hl_fn_type prog_info fn_info (heap_info : HeapLiftBase.heap_info)
    unliftable_functions fn_name =
let
  val fn_def = FunctionInfo.get_function_def fn_info fn_name
  val fn_params_typ = map snd (#args fn_def)
  (* Fill in the measure argument and return type *)
  val globals_typ = get_expected_fn_state_type heap_info unliftable_functions fn_name
  val fn_ret_typ = #return_type fn_def
  val measure_typ = @{typ "nat"}
  val fn_typ = (measure_typ :: fn_params_typ)
                 ---> LocalVarExtract.mk_l2monadT globals_typ fn_ret_typ @{typ unit}
in
  fn_typ
end

(* Get the expected theorem that will be generated about a function. *)
fun get_expected_hl_fn_thm prog_info fn_info (heap_info : HeapLiftBase.heap_info)
    unliftable_functions ctxt fn_name function_free fn_args _ measure_var =
let
  (* Get L2 const *)
  val l2_def = FunctionInfo.get_function_def fn_info fn_name
  val l2_term = betapplys (#const l2_def, measure_var :: fn_args)

  (* Get expected HL const. *)
  val hl_term = betapplys (function_free, measure_var :: fn_args)
in
  @{mk_term "Trueprop (L2Tcorres ?st ?A ?C)" (st, A, C)}
    (get_expected_st heap_info unliftable_functions fn_name, hl_term, l2_term)
end

(* Get arguments passed into the function. *)
fun get_expected_hl_fn_args prog_info fn_info fn_name =
  #args (FunctionInfo.get_function_def fn_info fn_name)

(*
 * Use some heuristics to determine which functions cannot be lifted.
 *
 * For example, we probably can't lift functions that introspect the heap-type
 * data "hrs_htd".
 *)
fun get_unliftable_functions lthy prog_info fn_info =
let
  (* Determine if everything in term "t" appears valid for lifting. *)
  fun can_lift_term t =
  let
    val bad_consts = [@{const_name hrs_htd}, @{const_name hrs_htd_update}, @{const_name ptr_retyp}]
    fun term_contains_const_name c t =
      exists_Const (fn (const_name, _) => c = const_name) t
  in
    not (exists (fn c => term_contains_const_name c t) bad_consts)
  end

  (* Find all functions that are directly unliftable. *)
  val raw_unliftable_functions =
    AutoCorresUtil.map_all lthy fn_info (fn fn_name =>
        (fn_name,
            FunctionInfo.get_function_def fn_info fn_name
            |> #definition
            |> Thm.prop_of
            |> Utils.rhs_of
            |> can_lift_term))
    |> filter (not o snd)
    |> map fst
in
  Symset.make raw_unliftable_functions
end

(*
 * Convert a cterm from the format "f a (b n) c" into "((f $ a) $ (b $ n)) $ c".
 *
 * Return a "thm" of the form "old = new".
 *)
fun mk_first_order ctxt ct =
let
  fun expand_conv ct =
    Utils.named_cterm_instantiate
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
 *
 *  * The syntax looks as terrible as c-parser's. Well, at least you won't need
 *    to subscript greek letters.
 *
 *  * Isabelle doesn't like overloaded syntax.
 *)

exception NO_GETTER_SETTER (* Not visible externally *)

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

    val getter_mixfix = Mixfix ("_[_]\<rightarrow>" ^ (Syntax_Ext.escape field_pname), [1000], 1000)
    val setter_mixfix = Mixfix ("_[_\<rightarrow>" ^ (Syntax_Ext.escape field_pname) ^ " := _]", [1000], 1000)

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

    val getter_mixfix = Mixfix ("_[_]", [1000], 1000)
    val setter_mixfix = Mixfix ("_[_ := _]", [1000], 1000)

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

(* Convert a program to use a lifted heap. *)
fun system_heap_lift
    (filename : string)
    (fn_info : FunctionInfo.fn_info)
    (no_heap_abs : string list)
    (force_heap_abs : string list)
    (make_lifted_globals_field_name : string -> string)
    (heap_abs_syntax : bool)
    (keep_going : bool)
    (trace_funcs : string list)
    (do_opt : bool)
    (trace_opt : bool)
    (hl_function_name : string -> string)
    (gen_word_heaps : bool)
    lthy =
let
  val prog_info = ProgramInfo.get_prog_info lthy filename

  (* Create base definitions for the new program, including a new
   * "globals" record with a lifted heap. *)
  val (heap_info, lthy) = HeapLiftBase.setup prog_info fn_info make_lifted_globals_field_name gen_word_heaps lthy

  (* Do some extra lifting and create syntax (see field_syntax comment). *)
  val (syntax_lift_rules, lthy) =
    if not heap_abs_syntax then
      ([], lthy)
    else
      Utils.exec_background_result (fn lthy =>
        let
            fun optcat xs = List.concat (map the_list xs)

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

            (* Name the thms. *)
            val (_, lthy) = Utils.define_lemmas "heap_abs_simps" thms lthy

            (* Rewrite rules for converting the program. *)
            val getter_thms = Symtab.dest new_getters |> map (#4 o snd) |> optcat
            val setter_thms = Symtab.dest new_setters |> map (#4 o snd) |> optcat
            val eta_setter_thms = map (eta_rhs lthy) setter_thms
            val rewrite_thms = map (fn thm => @{thm symmetric} OF [thm])
                                   (getter_thms @ eta_setter_thms)
        in (rewrite_thms, lthy) end) lthy

  (* Extract the abstract term out of a L2Tcorres thm. *)
  fun dest_L2Tcorres_term_abs (_ $ _ $ t $ _ ) = t
  fun get_body_of_thm ctxt thm =
      Thm.concl_of (Drule.gen_all (Variable.maxidx_of ctxt) thm)
      |> HOLogic.dest_Trueprop
      |> dest_L2Tcorres_term_abs

  (* Determine which functions cannot be lifted. *)
  val unliftable_functions =
        get_unliftable_functions lthy prog_info fn_info
        |> Symset.union (Symset.make no_heap_abs)
        |> Symset.subtract (Symset.make force_heap_abs)

  (* TODO: explain why each function in the list isn't being lifted. *)
  val _ =
    if Symset.card unliftable_functions > 0 then
      writeln ("HL: Functions cannot be lifted: "
          ^ (commas (Symset.dest unliftable_functions)))
    else
      ()

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
             ((rtac @{thm valid_typ_heapI} 1) THEN (
                 REPEAT (subgoal_solver_tac (#context params))))))

  (* Make thms for all types. *)
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
         let val _ = Syntax.check_term lthy prop in
         [Goal.prove_future lthy [] [] prop
            (fn params =>
               (rtac @{thm valid_struct_fieldI} 1) THEN
               (* Need some extra thms from the records package for our struct type. *)
               (EqSubst.eqsubst_tac lthy [0]
                  [hd (Proof_Context.get_thms lthy (struct_name ^ "_idupdates")) RS @{thm sym}] 1
                  THEN asm_full_simp_tac lthy 1) THEN
               (FIRST (Proof_Context.get_thms lthy (struct_name ^ "_fold_congs")
                       |> map (fn t => rtac (t OF @{thms refl refl}) 1))
                  THEN asm_full_simp_tac lthy 1) THEN
               (REPEAT (subgoal_solver_tac (#context params))))]
         end handle _ => [])

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
               (rtac @{thm valid_struct_field_legacyI} 1) THEN (
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
    @{mk_term "Trueprop (valid_globals_field ?st ?old_get ?old_set ?new_get ?new_set)" (st, old_get, old_set, new_get, new_set)}
      (#lift_fn_full heap_info,
        Symtab.lookup (#global_field_getters heap_info) name |> the |> fst,
        Symtab.lookup (#global_field_setters heap_info) name |> the |> fst,
        Symtab.lookup (#global_field_getters heap_info) name |> the |> snd,
        Symtab.lookup (#global_field_setters heap_info) name |> the |> snd)
    |> (fn prop => Goal.prove_future lthy [] [] prop (fn params => subgoal_solver_tac (#context params)))
  val valid_global_field_thms = map (#1 #> mk_valid_globals_field_thm) (#global_fields heap_info)

  (*
   * Fetch rules from the theory, instantiating any rule with
   * "valid_globals_field", "valid_typ_heap" etc with the predicates generated
   * above.
   *)
  val base_rules = HeapAbsThms.get lthy
  (* FIXME: make an attribute for these rules? *)
  val base_nolift_rules = @{thms struct_rewrite_expr_id}
  val [rules, nolift_rules] =
    map (fn rules =>
      cross_instantiate rules [
        valid_typ_heap_thms,
        valid_field_thms,
        valid_global_field_thms]
    |> filter (Thm.prop_of #> exists_subterm (fn x => case x of Const (@{const_name "valid_globals_field"}, _) => true | _ => false) #> not)
    |> filter (Thm.prop_of #> exists_subterm (fn x => case x of Const (@{const_name "valid_struct_field"}, _) => true | _ => false) #> not)
    |> filter (Thm.prop_of #> exists_subterm (fn x => case x of Const (@{const_name "valid_struct_field_legacy"}, _) => true | _ => false) #> not)
    |> filter (Thm.prop_of #> exists_subterm (fn x => case x of Const (@{const_name "valid_typ_heap"}, _) => true | _ => false) #> not)
       ) [base_rules, base_nolift_rules]

  (*val _ = map (fn r => @{trace} r) rules*)

  (* Convert to new heap format. *)
  fun convert ctxt fn_name callee_terms measure_var fn_args =
  let
    val thy = Proof_Context.theory_of ctxt

    (* Fetch the function definition. *)
    val fn_def = FunctionInfo.get_function_def fn_info fn_name
    val l2_body_def =
        #definition fn_def
        (* Instantiate the arguments. *)
        |> Utils.inst_args (map (Thm.cterm_of ctxt) (measure_var :: fn_args))
    val l2_body = Utils.rhs_of (Thm.prop_of l2_body_def)

    (* Get L2 body definition with function arguments. *)
    val l2_term = betapplys (#const fn_def, measure_var :: fn_args)

    (* Get our state translation function. *)
    val st = get_expected_st heap_info unliftable_functions fn_name

    (* Generate a schematic goal. *)
    val goal = @{mk_term "Trueprop (L2Tcorres ?st ?A ?C)" (st, C)}
        (st, l2_term)
        |> Thm.cterm_of ctxt
        |> Goal.init
        |> Utils.apply_tac "unfold RHS" (EqSubst.eqsubst_tac ctxt [0] [l2_body_def] 1)

    val callee_mono_thms = Symtab.dest callee_terms |> map fst
        |> List.mapPartial (fn callee =>
               if FunctionInfo.is_function_recursive fn_info callee
               then SOME (FunctionInfo.get_function_def fn_info callee |> #mono_thm)
               else NONE)
    val rules = rules @ (map (snd #> #3) (Symtab.dest callee_terms)) @ callee_mono_thms
    val rules = if Symset.contains unliftable_functions fn_name
                then rules @ nolift_rules else rules
    val fo_rules = HeapAbsFOThms.get ctxt

    (* Apply a conversion to the concrete side of the given L2T term.
     * By convention, the concrete side is the last argument (index ~1). *)
    fun l2t_conc_body_conv conv =
      Conv.params_conv (~1) (K (Conv.arg_conv (Utils.nth_arg_conv (~1) conv)))

    (* Standard tactics. *)
    val print_debug = fn_name = ""
    fun rtac_all r n = (APPEND_LIST (map (fn thm =>
                          rtac thm n THEN (fn x =>
                            (if print_debug then @{trace} thm else ();
                            Seq.succeed x))) r))

    fun print1_tac label t =
      (@{trace} (
         label ^ ": subgoal 1 of " ^ Int.toString (Logic.count_prems (term_of_thm t)),
         Logic.get_goal (term_of_thm t) 1 |> Thm.cterm_of lthy);
       all_tac t)

    (* Convert the concrete side of the given L2T term to/from first-order form. *)
    val l2t_to_fo_tac = CONVERSION (Drule.beta_eta_conversion then_conv l2t_conc_body_conv (mk_first_order ctxt) ctxt)
    val l2t_from_fo_tac = CONVERSION (l2t_conc_body_conv (dest_first_order ctxt then_conv Drule.beta_eta_conversion) ctxt)
    val fo_tac = ((l2t_to_fo_tac THEN' rtac_all fo_rules) THEN_ALL_NEW l2t_from_fo_tac) 1

    (* If debugging enabled, print goal states when we backtrack. *)
    val error_printed = ref 0
    fun print_n_tac printed_ref t =
      (if false orelse (!printed_ref >= ML_Options.get_print_depth ()) then
        all_tac
      else
        (printed_ref := (!printed_ref) + 1; print_tac ctxt "Error solving subgoal")) t

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
    fun solve_tac n =
      (if print_debug then print1_tac fn_name else all_tac) THEN
      DETERM ((SOLVES (
          ((K (CHANGED ((rtac_all rules 1) APPEND (fo_tac)))) THEN_ALL_NEW solve_tac) 1))
            ORELSE (print_n_tac error_printed THEN no_tac))

    val tactics = map (fn rule => (rule, rtac rule 1)) rules
                  @ [(@{thm fun_app_def}, fo_tac)]
    val replay_failure_start = 1
    val replay_failures = Unsynchronized.ref replay_failure_start
    val (thm, trace) =
         case AutoCorresTrace.maybe_trace_solve_tac ctxt (member (op =) trace_funcs fn_name)
                true false (K tactics) goal NONE replay_failures of
            NONE => (* intentionally generate a TRACE_SOLVE_TAC_FAIL *)
                    (AutoCorresTrace.trace_solve_tac ctxt false false (K tactics) goal NONE (Unsynchronized.ref 0);
                     (* never reached *) error "heap_lift fail tac: impossible")
          | SOME (thm, [trace]) => (Goal.finish ctxt thm, trace)
    val _ = if !replay_failures < replay_failure_start then
              @{trace} (fn_name ^ " HL: reverted to slow replay " ^
                        Int.toString(replay_failure_start - !replay_failures) ^ " time(s)") else ()

    (* DEBUG: make sure that all uses of field_lvalue and c_guard are rewritten.
     *        Also make sure that we cleaned up internal constants. *)
    fun contains_const name = let
          fun check (Const (n, _)) = n = name
            | check (Abs (_, _, t)) = check t
            | check (f $ x) = check f orelse check x
            | check _ = false
        in check end
    fun const_gone term name =
        if not (contains_const name term) then ()
        else Utils.TERM_non_critical keep_going
               ("Heap lift: could not remove " ^ name ^ " in " ^ fn_name ^ ".") [term]
    fun const_old_heap term name =
        if not (contains_const name term) then ()
        else warning ("Heap lift: could not remove " ^ name ^ " in " ^ fn_name ^
                      ". Output program may be unprovable.")
    val _ = if Symset.contains unliftable_functions fn_name then []
            else (map (const_gone (term_of_thm thm))
                      [@{const_name "heap_lift__h_val"}];
                  map (const_old_heap (term_of_thm thm))
                      [@{const_name "field_lvalue"}, @{const_name "c_guard"}]
                 )

    (* Gather statistics. *)
    val _ = Statistics.gather ctxt "HL" fn_name
        (Thm.prop_of thm |> HOLogic.dest_Trueprop |> (fn t => Utils.term_nth_arg t 1))

    (* Apply peephole optimisations to the theorem. *)
    val _ = writeln ("Simplifying (HL) " ^ fn_name)
    val (thm, opt_traces) = L2Opt.cleanup_thm_tagged ctxt thm (if do_opt then 0 else 2) 2 trace_opt "HL"

    (* If we created extra heap wrappers, apply them now.
     * Our simp rules don't seem to be enough for L2Opt,
     * so we cannot change the program before that. *)
    val thm = Raw_Simplifier.rewrite_rule ctxt syntax_lift_rules thm

    (* Gather post-simplification statistics. *)
    val _ = Statistics.gather ctxt "HLsimp" fn_name
        (Thm.prop_of thm |> HOLogic.dest_Trueprop |> (fn t => Utils.term_nth_arg t 1))
  in
    (get_body_of_thm ctxt thm, Drule.gen_all (Variable.maxidx_of ctxt) thm,
     (if member (op =) trace_funcs fn_name then [("HL", AutoCorresData.RuleTrace trace)] else []) @ opt_traces)
  end

  (* Save the heap info to the theory data. *)
  val lthy = Local_Theory.background_theory (
	  HeapInfo.map (fn tbl =>
	    Symtab.update (filename, heap_info) tbl)) lthy

  (* Update function information. *)
  fun update_function_defs lthy fn_def =
    FunctionInfo.fn_def_update_const (Utils.get_term lthy (hl_function_name (#name fn_def))) fn_def
    |> FunctionInfo.fn_def_update_definition (
        (the (AutoCorresData.get_def (Proof_Context.theory_of lthy)
            filename "HLdef" (#name fn_def))))
in
  AutoCorresUtil.do_translation_phase
    "HL" filename prog_info fn_info
    (get_expected_hl_fn_type prog_info fn_info heap_info unliftable_functions)
    (get_expected_hl_fn_thm prog_info fn_info heap_info unliftable_functions)
    (get_expected_hl_fn_args prog_info fn_info)
    hl_function_name
    convert
    LocalVarExtract.l2_monad_mono
    update_function_defs
    @{thm L2Tcorres_recguard_0}
    lthy
end

end
