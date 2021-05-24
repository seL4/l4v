(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

signature CALCULATE_STATE =
sig

  type var_info = ProgramAnalysis.var_info
  type csenv = ProgramAnalysis.csenv
  type 'a ctype = 'a Absyn.ctype
  type ecenv = Absyn.ecenv
  type 'a rcd_env = 'a ProgramAnalysis.rcd_env
  type nm_info = ProgramAnalysis.nm_info

  val define_enum_consts : ecenv -> theory -> theory

  type staterep
  val globals_all_addressed : bool Config.T
  val populate_globals : bool Config.T
  val record_globinits : bool Config.T
  val current_C_filename : string Config.T

  val ctype_to_typ : theory * int ctype -> typ
  datatype var_sort = Local of string
                    | NSGlobal
                    | AddressedGlobal
                    | UntouchedGlobal

  val create_state : csenv -> staterep

  val mk_thy_types :
      csenv -> bool -> theory ->
      theory *
      (string * (string * typ * int ctype) list) list

  val mk_thy_decls :
      staterep -> {mstate_ty : typ,gstate_ty : typ, owners : string list} ->
      theory ->
      theory *
      (nm_info * typ * int ctype option * var_sort) list *
      (typ,term,thm list)Element.ctxt list

  val gen_umm_types_file : csenv -> string -> unit

  type mungedb = (MString.t * typ * int ctype option * var_sort) CNameTab.table
  val mk_mungedb : (nm_info * typ * int ctype option * var_sort) list ->
                   mungedb


  (* storing csenv's in the theory *)
  val store_csenv : string * csenv -> theory -> theory
  val get_csenv : theory -> string -> csenv option
  (* storing ghost-state types in the theory *)
  val store_ghostty : string * typ -> theory -> theory
  val get_ghostty : theory -> string -> typ option
  (* storing mungedb's in the theory *)
  val store_mungedb : string * mungedb -> theory -> theory
  val get_mungedb : theory -> string -> mungedb option

  val get_globals_data : typ -> typ -> theory -> {acc : term, upd : term,
    fields : (string * typ) list}
  val get_standard_globals : typ -> typ -> theory
    -> {hp: ((term * term) * (term * term)),
        phantom: ((term * term) * (term * term)),
        ghost: ((term * term) * (term * term))}

(*
   The isa_decl type corresponds to a program variable in a form that will be
   easy for Isabelle to process.

      vdecl (nm, ty, vsort)  nm is the name of a variable of type ty,
                             declared in function f if fname is Local
                             f, or a global: UntouchedGlobal if it is never
                             modified or addressed, NSGlobal if its
                             address is not taken, or AddressedGlobal
                             if it is.

   [create_state intinfo vars] returns a sequence of abstract Isabelle
   variable information.

   [mk_thy_decls decls] translates such a series into an operation on
   an Isabelle theory, creating various records ('myvars', 'globals',
   with fields corresponding to the variables

*)

end;


structure CalculateState : CALCULATE_STATE =
struct

open Basics Absyn TermsTypes NameGeneration ProgramAnalysis Feedback

val (globals_all_addressed, populate_globals, record_globinits,
     current_C_filename) =
    let
      val (gconfig, gsetup) =
        Attrib.config_bool (Binding.make ("globals_all_addressed",@{here})) (K false)
      val (pconfig, psetup) =
        Attrib.config_bool (Binding.make ("populate_globals",@{here})) (K false)
      val (rconfig, rsetup) =
        Attrib.config_bool (Binding.make ("record_globinits",@{here})) (K false)
      val (Cfile_config, csetup) =
        Attrib.config_string (Binding.make ("current_C_filename",@{here})) (K "")
    in
      Context.>>(Context.map_theory gsetup o Context.map_theory psetup o
                 Context.map_theory rsetup o Context.map_theory csetup);
      (gconfig, pconfig, rconfig, Cfile_config)
    end

fun define_enum_consts (CE {enumenv, ...}) thy = let
  fun define1 (nm, (value, tyname_opt)) (acc,lthy) = let
    val rhs_v = IntInfo.numeral2w (Signed Int) value
    val typeinfo = case tyname_opt of NONE => "" | SOME s => " (of type "^s^")"
    val _ = informStr(2, "Defining enumeration constant "^nm^typeinfo^
                         " to have value "^
                         Int.toString value^" (signed int)")
    val nm' = NameGeneration.enum_const_name nm
    val binding = Binding.make (nm',@{here})
    val ((_, (_, th)), lthy) =
        Local_Theory.define ((binding, NoSyn),
                             ((Thm.def_binding binding, []), rhs_v))
                            lthy
    fun upd th t = th :: t
    val acc = case tyname_opt of
                NONE => acc
              | SOME nm => Symtab.map_default (nm, []) (upd th) acc
  in
    (acc, lthy)
  end
  val sfx = NameGeneration.enum_const_summary_lemma_sfx
  fun group_lemma (tynm, ths) lthy =
      (informStr (2, "Adding "^Int.toString (length ths)^
                     " enum definitions for type "^ tynm);
       #2 (Local_Theory.note ((Binding.make (tynm ^ sfx, @{here}), []), ths) lthy))
  val lthy = Named_Target.theory_init thy
  val (tythms, lthy) = Symtab.fold define1 enumenv (Symtab.empty, lthy)
  val lthy = Symtab.fold group_lemma tythms lthy
in
  Local_Theory.exit_global lthy
end

datatype isa_type = refty of (isa_type option * int ctype)
                  | recd of (string * int ctype)
                  | array of isa_type * int * int ctype
                  | existing of typ * int ctype
type isa_senv = isa_type rcd_env

datatype var_sort =
  Local of string
| NSGlobal
| AddressedGlobal
| UntouchedGlobal

type isa_var = (nm_info * isa_type * var_sort)
datatype isa_decl = vdecl of nm_info * isa_type * var_sort
type staterep = isa_decl list Symtab.table

fun isa_type_to_cty (refty (_, c)) = c
  | isa_type_to_cty (recd(_, c)) = c
  | isa_type_to_cty (array (_, _, c)) = c
  | isa_type_to_cty (existing(_, c)) = c

fun translate_inttype (ty : int ctype) =
  case ty of
    Signed x => existing (IntInfo.ity2wty (Signed x), ty)
  | Unsigned x => existing (IntInfo.ity2wty (Unsigned x), ty)
  | PlainChar => existing (IntInfo.ity2wty PlainChar, ty)
  | Bool => existing (IntInfo.ity2wty Bool, ty)
  | Ptr Void => refty (NONE, ty)
  | Ptr (Function _) => refty (NONE, ty)
  | Ptr ty0 => refty (SOME (translate_inttype ty0), ty)
  | Array(ty0, SOME sz) => array (translate_inttype ty0, sz, ty)
  | Array(_, NONE) => raise Fail "translate_inttype: incomplete array!"
  | StructTy s => recd (s, ty)
  | EnumTy _ => translate_inttype (Signed Int)
  | Ident _ => raise Fail "Should never happen: translate out typedefs"
  | Void => raise Fail "Values of bare void type illegal"
  | Bitfield _ => raise Fail "Can't cope with bitfields"
  | _ =>
    raise Fail ("translate_type: can't cope with "^tyname ty)

val translate_type = translate_inttype

(* translate_vi creates a list of variables that need to be declared
   in the isabelle environment.  The information provided is the name
   of the variable, the "isa type", the name of the enclosing function
   (can be NONE to represent a global var, and the structure
   environment.

   For struct types, additional type declarations need to be made (the
   Isabelle record types need to be declared).  For pointer types,
   additional global variables need to be declared, these will be of a
   function type from a reference type to the type pointed to by the
   variable, and represent the heap.  This augmentation is done by
   augment_decls below.

 *)
fun translate_vi csenv =
  let
    val untoucheds = calc_untouched_globals csenv
    fun doit vi =
      (case get_vi_type vi of
        Function _ => NONE
      | ty =>
          let
            val isaty = translate_type ty
            val k = get_mname vi
            val var_sort =
                case get_vi_fname vi of
                  SOME s => Local s
                | NONE =>
                  (if MSymTab.defined (get_addressed csenv) k then
                      AddressedGlobal
                    else if MSymTab.defined untoucheds k then
                      UntouchedGlobal
                    else
                      NSGlobal)
          in
            SOME (get_vi_nm_info csenv vi, isaty, var_sort)
          end)
  in
    doit
  end

fun isa_type_to_typ ctxt (ity : isa_type) = let
  fun m s = let
    val thy = Proof_Context.theory_of ctxt
    val known = (Syntax.parse_typ ctxt s; true) handle ERROR _ => false
    val f = if known then Sign.intern_type thy else Sign.full_name thy o Binding.name
  in
    f s
  end
  fun mk_array_size_ty sz =
    if sz = ArchArrayMaxCount.array_max_count
      then @{typ "array_max_count_ty"}
      else mk_numeral_type sz
in
  case ity of
    refty (NONE, _) => mk_ptr_ty unit
  | refty (SOME ity0, _) => mk_ptr_ty (isa_type_to_typ ctxt ity0)
  | recd (s, _) => Type (m s, [])
  | array (ity, sz, _) =>
    Type("Arrays.array", [isa_type_to_typ ctxt ity, mk_array_size_ty sz])
  | existing (ty, _) => ty
end

fun ctype_to_typ (thy,c0ty) =
    isa_type_to_typ (thy2ctxt thy) (translate_inttype c0ty)

(*
 * Program analysis return a table of variable occurences indexed by the variable name,
 * We want a table of variable names, indexed by the function name they occur in.
 *)
fun create_state cse =
  let
    fun innerfold (vi, tab) =
        case translate_vi cse vi of
          NONE => tab
        | SOME (v as (_,_,lorg)) =>
            let
              val f =
                case lorg of
                  Local f => f
                | _ => "<global>"
            in
              Symtab.cons_list (f,vdecl v) tab
            end
    fun outerfold (_,vlist) acc = List.foldl innerfold acc vlist
    val tab = Symtab.fold outerfold (get_vars cse) Symtab.empty
  in
    tab
  end

fun split_vars ctxt tab =
  let
    fun translate_vdecl (vdecl (s, ty, vsort)) =
      (s, isa_type_to_typ ctxt ty, SOME (isa_type_to_cty ty), vsort);
    val gvars = Symtab.lookup_list tab "<global>" |> map translate_vdecl
    val lvars = Symtab.delete_safe "<global>" tab |> Symtab.map (K (map translate_vdecl))
  in
    (lvars, gvars)
  end

fun listvars f vns =
    case vns of
        [vn] => f vn
      | vn::rest => f vn ^ ", " ^ listvars f rest
      | [] => "<none>"

fun locale_params owners = let
  fun mk_fix (Free(n,ty)) = (Binding.name n, SOME ty, NoSyn)
    | mk_fix _ = raise Fail "locale_params.mk_fix: should never happen"
  val ownership_fixes =
      map (fn oid => mk_fix(Free(oid, nat))) owners
  val fixes =
      Element.Fixes (mk_fix symbol_table :: ownership_fixes)
in
  [fixes]
end

datatype umm_decl = umm_array of int ctype * int
                  | umm_struct of string * (string * int ctype) list
structure UMMKey =
struct
  type key = umm_decl
  fun ord (umm_array _, umm_struct _) = LESS
    | ord (umm_array p1, umm_array p2) = pair_compare
                                             (ctype_compare Int.compare, Int.compare)
                                             (p1, p2)
    | ord (umm_struct _, umm_array _) = GREATER
    | ord (umm_struct (s1, _), umm_struct (s2, _)) = String.compare (s1,s2)
end
structure UMMTab = Table(UMMKey)
local
  structure UMMFlip = FlipTable(structure Table = UMMTab)
in
val ummflip = UMMFlip.flip
end

(*
 * Perform a topological sort of structures such that "parent" structures
 * appear after "child" structures (where a "parent" has a pointer to or
 * includes a "child" structure).
 *
 * Structures may be mutulally dependent; in this case, the structures will
 * appear in the same list in the output.
 *)
fun get_sorted_structs cse =
let
  val rcds = get_senv cse
  val sorted_structs =
      if null rcds then []
      else let
          val (rcdmap,rcdnames) =
              List.foldl (fn (r as (s,_),(tab,nms)) =>
                             (Symtab.update (s, r) tab, s::nms))
                         (Symtab.empty, [])
                         rcds
          fun rcd_neighbours ((s, flds), acc) = let
            fun struct_refs (cty, acc) =
                case cty of
                  Ptr ty' => struct_refs (ty', acc)
                | StructTy s' => Symtab.cons_list (s,s') acc
                | Array(ty', _) => struct_refs (ty', acc)
                | _ => acc
          in
            List.foldl (fn ((_,ty),acc) => struct_refs (ty,acc)) acc flds
          end
          val inclusion_graph = List.foldl rcd_neighbours Symtab.empty rcds
          val inverse_graph = flip_symtab inclusion_graph
          open Topo_Sort
          val sorted0 = topo_sort {cmp = String.compare,
                                   graph = Symtab.lookup_list inclusion_graph,
                                   converse = Symtab.lookup_list inverse_graph}
                                  rcdnames
        in
          map (map (valOf o Symtab.lookup rcdmap)) sorted0
        end
in
  sorted_structs
end

(*
 * Generate an output file "umm_types.txt" that contains information about
 * structures in the input C file.
 *
 * This is required by certain external tools, such as the bitfield generator.
 *)
fun gen_umm_types_file cse outfile =
let
  val num_ty_string = Word_Lib.dest_binT #> string_of_int

  fun write_one strm (recname, flds) = let
    fun isa_to_string (refty (NONE, _)) = "Ptr Unit"
      | isa_to_string (refty (SOME ty, _)) = "Ptr " ^ isa_to_string ty
      | isa_to_string (recd (s, _)) = s
      | isa_to_string (array (ty, n, _)) = "Array " ^ (isa_to_string ty) ^
                                           " " ^ (Int.toString n)
      | isa_to_string (existing (Type(@{type_name "word"},
                                  [Type (@{type_name "Signed_Words.signed"}, [n])]), _)) =
            "Signed_Word " ^ num_ty_string n
      | isa_to_string (existing (Type(@{type_name "word"},
                                      [n]), _)) = "Word " ^ num_ty_string n
      | isa_to_string _ = error "Unexpected type in isa_to_string"

    fun do_one_fld (fldname, fldty) =
        TextIO.output (strm, "\t" ^ fldname ^ ":" ^
                             isa_to_string (translate_type fldty) ^ "\n")

    val _ = TextIO.output (strm, recname ^ "\n")
    val _ = app do_one_fld flds
  in
    TextIO.output (strm, "\n")
  end

  val sorted_structs = get_sorted_structs cse
  val outstrm = TextIO.openOut outfile
  val _ = app (app (write_one outstrm)) sorted_structs
  val _ = TextIO.closeOut outstrm
in
  ()
end

val outfilnameN = "umm_types.txt"

fun mk_thy_types cse install thy = let
  (* Make the necessary theory declarations to make the C file's types work
     in Isabelle.  There are two phases.

     Phase 0:
       For arrays, declaration of the numCopy types corresponding to
       the sizes of the various arrays.  This can be done before
       anything else happens, as it is not dependent on any other types.

       For structs, the basic declaration of the corresponding record
       type, using the RecursiveRecordPackage.  This is complicated by the
       fact that multiple structs may be mutually recursive.  So you
       have to figure out which ones, and declare them all together.
       This requires a topological sort of the struct declarations.
       This phase is also dependent on array sizes having been
       declared correctly because a struct's field may be an array,
       and this requires that array's size type to be declared
       already.

     Phase1:
       UMM property proofs.  These have to happen in the order of
       declaration from the C file (which is reflected in the "state"
       parameter).

     Also return a list of all the record declarations that were made
     for consumption by later phases of the translation.

  *)
  val rcds = get_senv cse
  val sorted_structs = get_sorted_structs cse

  open MemoryModelExtras
  open UserTypeDeclChecking
  val umm_prfstate = initial_state
  fun new_rcdinfo (recname,flds) thy = let
    fun fldtys (fldname, cty) = (fldname, ctype_to_typ (thy,cty), cty)
  in
    (recname, map fldtys flds)
  end

  fun rcddecls_phase0 (recflds, thy) = let
  in
    if install then let
        val _ =
            informStr(2, "Defining isabelle type(s) corresponding to \
                         \struct group:")
        val _ = app (fn (recname,flds) =>
                        informStr (2, "  struct " ^ recname^ ", with fields: " ^
                                      listvars #1 flds))
                    recflds

        fun mk_rp_fld thy (fldname,cty) = {fldname = fldname,
                                           fldty = ctype_to_typ (thy,cty)}
        fun mk_rp_recd thy (recname, flds) =
            {record_name = recname, fields = map (mk_rp_fld thy) flds}
        fun mk_ctype_instance (recname, _) thy = let
          val recty = Syntax.read_typ_global thy recname

          (* establish the new type as a c_type, which requires no proof, as
             there are no axioms attached to c_type *)
          val c_type_instance_t =
              Logic.mk_of_class(recty, "CTypesDefs.c_type")
          val c_type_instance_ct = Thm.cterm_of (thy2ctxt thy) c_type_instance_t
          val is_c_type_thm =
              Goal.prove_internal (thy2ctxt thy) [] c_type_instance_ct
                                  (fn _ => Class.intro_classes_tac (thy2ctxt thy) [])
          val thy = Axclass.add_arity is_c_type_thm thy

          val _ =
              informStr (2, "Proved  instance "^
                            Syntax.string_of_typ (thy2ctxt thy) recty^
                            " :: c_type")
        in
          thy
        end
      in
        thy |> RecursiveRecordPackage.define_record_type (map (mk_rp_recd thy) recflds)
            |> Basics.fold mk_ctype_instance recflds
      end
    else
      thy
  end

  val thy = List.foldl rcddecls_phase0 thy sorted_structs

  (* Yuck, sorry *)
  val _ = gen_umm_types_file cse outfilnameN

  val arrays = List.filter (fn (_, sz) => sz <> 0)
                           (Binaryset.listItems (get_array_mentions cse))
  val umm_events = let
    val evs = map umm_array arrays @ map umm_struct rcds
  in
    if null evs then []
    else let
        val umm_struct_map =
            List.foldl (fn (r as (s,_),acc) => Symtab.update (s,umm_struct r) acc)
                       Symtab.empty
                       rcds
        val umm_array_set =
            List.foldl (fn (a,acc) => Binaryset.add(acc,umm_array a))
                       (Binaryset.empty UMMKey.ord)
                       arrays
        fun toEv ty =
            case ty of
              Array (ty, SOME sz) => let
                val u = umm_array(ty,sz)
              in
                if Binaryset.member(umm_array_set, u) then SOME u else NONE
              end
          | StructTy s => Symtab.lookup umm_struct_map s
          | _ => NONE
        fun umm_included uev =
            case uev of
              umm_array (ty, _) => [ty]
            | umm_struct(_, flds) => map #2 flds
        val inclusion =
            List.foldl
                (fn (u,acc) => UMMTab.update
                                   (u,List.mapPartial toEv (umm_included u))
                                   acc)
                UMMTab.empty
                evs
        val converse = ummflip inclusion
        val sorted_evs = Topo_Sort.topo_sort {graph = UMMTab.lookup_list inclusion,
                                              converse = UMMTab.lookup_list converse,
                                              cmp = UMMKey.ord}
                                             evs
        val _ = List.all (fn l => length l = 1) sorted_evs orelse
                error "Topological sort of object inclusion includes a loop"
      in
        map hd sorted_evs
      end
  end

  fun rcddecl_phase1 (p as (recname, _ (* flds *)), (thy, st, rcdacc)) = let
    val rcdinfo = new_rcdinfo p thy
    val (st, thy1) =
        if install then
          (informStr (2, "Proving UMM properties for struct "^recname);
           struct_type cse {struct_type = rcdinfo, state = st}
                       thy)
        else (st, thy)
  in
    (thy1, st, rcdinfo :: rcdacc)
  end

  fun arraytype_phase1 ((cty, n), (thy, st, rcdacc)) = let
      val (st', thy') =
          if install then
              array_type cse
                         {element_type = ctype_to_typ(thy,cty), array_size =  n,
                          state = st}
                         thy
          else
              (st, thy)
  in
      (thy', st', rcdacc)
  end
  fun phase1 (idecl, acc) =
      case idecl of
        umm_array ai => arraytype_phase1 (ai, acc)
      | umm_struct ri => rcddecl_phase1 (ri, acc)

  val (thy, final_state, rcdinfo0)
    = List.foldl phase1 (thy, umm_prfstate, []) umm_events
  val thy = if install then UserTypeDeclChecking.finalise final_state thy
            else thy
in
  (thy, List.rev rcdinfo0)
end

fun simple s = {isa_name = MString.mk s, src_name = s, alias = false}

fun pretty_recdef ctxt nm vars =
  Pretty.big_list
    ("Defining record: " ^ nm ^ " =")
    (map
      (fn (field_nm, field_typ) =>
        Pretty.str (field_nm ^ " :: " ^ Syntax.string_of_typ ctxt field_typ))
      vars)
  |> Pretty.string_of
  |> tracing;

fun categorise_globals (alladdressed, popglobs) l = let
  fun recurse (acc as (ut, ns, ad)) l =
    case l of
      [] => acc
    | (g as (_, _, _, vsort)) :: rest => let
      in
        if not alladdressed orelse not popglobs then let
            val vsort = if alladdressed then AddressedGlobal else vsort
          in
            case vsort of
              Local _ => raise Fail "categorise_globals: This can't happen"
            | UntouchedGlobal => recurse (g::ut,      ns,    ad) rest
            | NSGlobal =>        recurse (   ut, g :: ns,    ad) rest
            | AddressedGlobal => recurse (   ut,      ns, g::ad) rest
          end
        else
          case vsort of
              Local _ => raise Fail "categorise_globals: This can't happen #2"
            | UntouchedGlobal => recurse (g::ut,      ns, g::ad) rest
            | NSGlobal =>        recurse (   ut, g :: ns, g::ad) rest
            | AddressedGlobal => recurse (   ut,      ns, g::ad) rest
      end
in
  recurse ([],[],[]) l
end

fun mk_thy_decls all_vars {owners,mstate_ty=pmstate_ty,gstate_ty} thy = let
  fun declare_vars thy = let
    val (lvars, gvars) = split_vars (thy2ctxt thy) all_vars

    val local_vars_collected =
      Symtab.fold
        (fn (_, vs) =>
          fold
            (fn ({isa_name,...},T,_,_) =>
              Symtab.update (Hoare.varname (MString.dest isa_name), T))
            vs)
        lvars
        Symtab.empty

    open NameGeneration
    fun mk_globals_rcd thy = let
      val (_ (* utglobs *), nsglobs, _ (* adglobs *)) =
          (* untouched globals, Norbert Schirmer Globals, addressed globals *)
          categorise_globals (Config.get_global thy globals_all_addressed,
                              Config.get_global thy populate_globals)
                             gvars
      fun extract_nm_typ (a,b,_,_) =
        (a, b) |>> #isa_name |>> MString.dest
      val _ =
        if not (null gvars)
        then nsglobs |> map extract_nm_typ |> pretty_recdef (thy2ctxt thy) "globals"
        else ()
      val gflds =
          [(Binding.make (global_heap_var,@{here}), MemoryModelExtras.extended_heap_ty, NoSyn),
           (Binding.make (global_var phantom_state_name,@{here}), pmstate_ty, NoSyn),
           (Binding.make (global_var ghost_state_name,@{here}), gstate_ty, NoSyn)] @
          map (fn ({isa_name,...}, ty, _, _) =>
                  (Binding.make (global_var (MString.dest isa_name),@{here}), ty, NoSyn))
              nsglobs @
          (if null owners then []
           else [(Binding.make (global_var owned_by_fn_name,@{here}), nat, NoSyn)])
      val thy =
          Record.add_record {overloaded=false}
                           ([], Binding.make (NameGeneration.global_rcd_name,@{here})) NONE
                            gflds thy
      val fullrecname = Sign.intern_type thy NameGeneration.global_ext_type
      val thy'' = MemoryModelExtras.check_global_record_type fullrecname thy
    in
      (thy'', locale_params owners)
    end

    type frame_info = {name : string, vars: (string * string * typ) list}
    val frames : frame_info list =
      Symtab.fold
        (fn (fnname,vars) => fn frames =>
          let
            val vars =
              map
                (fn ({isa_name,src_name,...},typ,_,_) =>
                  (HoarePackage.varname (MString.dest isa_name),
                    HoarePackage.varname src_name,
                    typ))
                vars
          in
            { name = prefix "Frame_" fnname, vars = vars } :: frames
          end)
        lvars
        []

    val frame_name = "frame"

    (* Take the lvar table and create the frame datatype from it.
     * The frame datatype has a variant per each function, which contain values for each local
     * variable in that function.
     *)
    val mk_frame_dattyp =
      let
        val datatyp = (([], Binding.make (frame_name, @{here})), NoSyn)
        val bindings =
          map
            (fn {name, vars} =>
              let
                val frame_binding = Binding.make (name, @{here})
                val field_bindings =
                  map
                    (fn (isa_name,_,typ) =>
                      (Binding.make (isa_name, @{here})
                        |> Binding.qualify true frame_name,
                      typ))
                    vars
              in
                (((Binding.empty, frame_binding), field_bindings), NoSyn)
              end)
            frames
        val frame_spec =
          [( ((datatyp, bindings), (Binding.empty, Binding.empty, Binding.empty)), [] )]
      in
        BNF_FP_Def_Sugar.co_datatypes
          BNF_FP_Rec_Sugar_Util.Least_FP
          BNF_LFP.construct_lfp
          (Ctr_Sugar.default_ctr_options, frame_spec)
      end

    fun mk_frame_updator (vname,T) lthy =
      let
        val frameT = Proof_Context.read_typ lthy frame_name
        val updT = (T --> T) --> frameT --> frameT
        val var_upd_fn_name = vname ^ Record.updateN
        val var_upd_fn_binding =
          Binding.make (var_upd_fn_name, @{here})
          |> Binding.qualify true frame_name
        val free_fn_name = Free (var_upd_fn_name, updT)
        fun mk_eqn {name = constr_nm, vars} =
          let
            val constr = Proof_Context.read_const {proper = false, strict = false} lthy constr_nm
            val lhs_pattern = fold (fn (_,n,T) => fn t => t $ Free (n, T)) vars constr
            val lhs = free_fn_name $ Free ("f", T --> T) $ lhs_pattern
            val rhs =
              fold
                (fn (isa_nm,n,T) => fn t =>
                  let
                    val s =
                      if vname = isa_nm
                      then
                        (Free ("f", T --> T) $ Free (n, T))
                      else
                        Free (n, T)
                  in
                    t $ s
                  end)
                vars
                constr
          in
            (((Binding.empty, []), HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs))), [], [])
          end
        val frame_eqns = map mk_eqn frames
        val (_,lthy) =
          BNF_LFP_Rec_Sugar.primrec
            false (* debug prints *)
            [] (* config options; i.e. transfer/nonexaustive/plugins *)
            [ (var_upd_fn_binding, SOME updT, NoSyn) ] (* name of the function *)
            frame_eqns (* equations *)
            lthy
      in
        lthy
      end

    (* Lifts the accessor and updator functions to work with the local state. *)
    fun mk_frame_state_fns local_vars_collected lthy =
      let
        val frameT = Proof_Context.read_typ lthy "frame"
        val stackT = Proof_Context.read_typ lthy "frame stack"

        val stack_get =
          Proof_Context.read_const {proper = false, strict = false} lthy "stack_'"
        val stack_update =
          Proof_Context.read_const {proper = false, strict = false} lthy "stack_'_update"

        val update_top_frame =
          Const
            (@{const_name top_frame_update_stack},
            (frameT --> frameT) --> stackT --> stackT)
        val get_top_frame =
          Const
            (@{const_name get_top_frame_stack},
            stackT --> frameT)

        fun getter t =
          HOLogic.mk_comp (HOLogic.mk_comp (t, get_top_frame), stack_get)
        fun updator t =
          HOLogic.mk_comp (HOLogic.mk_comp (stack_update, update_top_frame), t)

        fun inner_fold (vname,_) lthy =
          let
            val acc_t =
              vname
              |> Long_Name.qualify frame_name
              |> Proof_Context.read_const {proper = false, strict = false} lthy
              |> getter
              |> Logic.unvarify_types_global
            val acc_b =
              Binding.make ("state_" ^ vname, @{here})
              |> Binding.qualify false frame_name
            val acc_def_b =
              Binding.make ("state_" ^ vname ^ "_def", @{here})
              |> Binding.qualify false frame_name

            val upd_s =
              "state_" ^ vname ^ Record.updateN
            val upd_b =
              Binding.make (upd_s, @{here})
              |> Binding.qualify false "frame"
            val upd_t =
              vname ^ Record.updateN
              |> Long_Name.qualify frame_name
              |> Proof_Context.read_const {proper = false, strict = false} lthy
              |> updator
              |> Logic.unvarify_types_global
            val upd_def_b =
              Binding.make (upd_s ^ "_def", @{here})
              |> Binding.qualify false frame_name

            val lthy =
              lthy
              |> Local_Theory.define ((acc_b, NoSyn), ((acc_def_b, []), acc_t)) |> snd
              |> Local_Theory.define ((upd_b, NoSyn), ((upd_def_b, []), upd_t)) |> snd
          in
            lthy
          end
      in
        Symtab.fold inner_fold local_vars_collected lthy
      end

    fun mk_frame_lemmas local_vars_collected lthy =
      let
        fun inner_fold (nm, _) lthy =
          let
            val upd =
              nm
              |> suffix Record.updateN
              |> prefix "state_"
              |> Long_Name.qualify "frame"
            val upd_t =
              Proof_Context.read_const {proper = false, strict = false} lthy upd

            val stripped_state_typ =
              upd_t
              |> Term.type_of
              |> Term.strip_type
            val state_T = snd stripped_state_typ
            val globals_T =
              nth (state_T |> Term.dest_Type |> snd) 0
            val vx = Term.Var (("x",0), state_T)
            val vf = Term.Var (("f",0), nth (fst stripped_state_typ) 0)
            val globals_t = Const ("StateSpace.state.globals", state_T --> globals_T)
            val lemma_t =
              HOLogic.mk_eq (globals_t $ (upd_t $ vf $ vx), globals_t $ vx)

            val lemma_ct =
              lemma_t
              |> HOLogic.mk_Trueprop
              |> Thm.cterm_of lthy
            val upd_def = Proof_Context.get_thm lthy (upd ^ "_def")
            val lemma_th =
              lemma_ct
              |> Goal.init
              |> simp_tac (lthy addsimps [upd_def]) 1 |> Seq.pull |> the |> fst
              |> Goal.finish lthy
          in
            lthy
            |> Local_Theory.declaration
                {pervasive=false, syntax=false}
                (K (Simplifier.map_ss (fn ss => ss addsimps [lemma_th])))
          end
      in
        Symtab.fold inner_fold local_vars_collected lthy
      end

    (* create update aliases *)
    (* In the past, the first variable named `x` got its own field named
       `x_'` in the local variables record. If there was another local later in
       the source in another function, also named `x` but of a different type
       `T`, then it would be put in a record field named `x___T_'`. Since this
       was source-order-dependent, we changed the record to only contain the
       full, type-qualified names.

       Of course, a lot of proofs were written under the "some names short,
       other names long" convention, and it's a very useful shorthand for e.g.
       all the `int i` loop index variables, so we recreate those aliases here.

       This works because of how record syntax is implemented. It looks up the
       access/update functions *by string* instead of by checking the context,
       so as long as appropriately named definitions are in scope it'll "just
       work". *)
    fun mk_locals_aliases thy =
      let
        val ctxt = thy2ctxt thy
        (* Returns a list of `(name, target)` pairs. We want to use the
           `definition` command to alias `target` with `name`. For example, if
           `unsigned x` and `int x` appear in the source (in that order), the
           output should include

           - `(x_', x___unsigned_')`, and
           - `(x_'_update, x___unsigned_'_update)`

           but shouldn't include anything for the `int` case. *)

        (* make abbreviations for the long name variable accessor and updator functions. *)
        fun make_aliases acc acc_alias upd upd_alias thy =
          let
            (* state aliases *)
            val var_acc_st =
              acc
              |> Long_Name.qualify NameGeneration.local_rcd_name
              |> Proof_Context.read_const {proper = false, strict = false} ctxt
            val b_acc_alias_st =
              Binding.make (acc_alias, @{here})
              |> Binding.qualify false NameGeneration.local_rcd_name

            val var_upd_st =
              upd
              |> Long_Name.qualify NameGeneration.local_rcd_name
              |> Proof_Context.read_const {proper = false, strict = false} ctxt
            val b_upd_alias_st =
              Binding.make (upd_alias, @{here})
              |> Binding.qualify false NameGeneration.local_rcd_name

            (* frame aliases *)
            val var_acc_fm =
              "state_" ^ acc
              |> Long_Name.qualify frame_name
              |> Proof_Context.read_const {proper = false, strict = false} ctxt
            val b_acc_alias_fm =
              Binding.make ("state_" ^ acc_alias, @{here})
              |> Binding.qualify true frame_name

            val var_upd_fm =
              "state_" ^ upd
              |> Long_Name.qualify frame_name
              |> Proof_Context.read_const {proper = false, strict = false} ctxt
            val b_upd_alias_fm =
              Binding.make ("state_" ^ upd_alias, @{here})
              |> Binding.qualify false frame_name
          in
            thy
            |> Sign.add_abbrev "" (b_acc_alias_st, var_acc_st) |> snd
            |> Sign.add_abbrev "" (b_upd_alias_st, var_upd_st) |> snd
            |> Sign.add_abbrev "" (b_acc_alias_fm, var_acc_fm) |> snd
            |> Sign.add_abbrev "" (b_upd_alias_fm, var_upd_fm) |> snd
          end

        (* make abbreviations for the long name variable accessor and updator functions. *)
        fun define_aliases vs thy =
          List.foldl
            (fn (({src_name, isa_name = mangled_name, alias},_,_,_), (seen,thy)) =>
                let
                  val acc = HoarePackage.varname (MString.dest mangled_name)
                  val acc_alias = HoarePackage.varname src_name

                  val upd = acc ^ Record.updateN
                  val upd_alias = acc_alias ^ Record.updateN
                in
                  if not alias orelse member (op =) seen src_name
                  then
                    (seen, thy)
                  else
                    (src_name :: seen,
                      make_aliases acc acc_alias upd upd_alias thy)
                end)
              ([], thy)
              vs
              |> snd
      in
        thy |> define_aliases (Symtab.dest_list lvars |> map snd)
      end

      fun mk_locals_rcd thy =
        let
          (* the state information accumulated so far allows for local
             variables of the same name and type to be declared in different
             functions.  When we come to make an Isabelle record definition
             we want to have just one field of the given name *)
          fun map_elim_name_inner ({isa_name,...}, ty, _, _) (seen,out) =
            let
              val nm' = HoarePackage.varname (MString.dest isa_name)
            in
              if member (op =) seen nm'
              then
                (seen,out)
              else
                (nm' :: seen, (Binding.make (nm',@{here}),ty,NoSyn) :: out)
            end

        fun map_elim_name (_,vs) (seen,out) =
          fold map_elim_name_inner vs (seen,out)

        val stackT = Syntax.parse_typ (thy2ctxt thy) "frame stack"

        val additional_flds =
          [ (simple global_exn_var_name, c_exntype_ty, NONE, Local "cparser'internal"),
          (simple "stack", stackT, NONE, Local "cparser'internal") ]

        val lflds =
          snd (Symtab.fold map_elim_name lvars ([],[])) @
          snd (fold map_elim_name_inner additional_flds ([],[]))

        (* trace the fields for reference *)
        val _ =
          lflds
          |> map (fn (a,b,_) => (Binding.name_of a,b))
          |> pretty_recdef (thy2ctxt thy) NameGeneration.local_rcd_name

        (* define the record as an extension of state *)
        val thy =
          Record.add_record
            {overloaded=false}
            ([("'g",["HOL.type"])], Binding.make (NameGeneration.local_rcd_name,@{here}))
            (SOME([TFree("'g", ["HOL.type"])], "StateSpace.state"))
            lflds
            thy
      in
        thy
      end

    val (thy, globs) =
      thy
      |> Named_Target.theory_map
        (mk_frame_dattyp
          #> Symtab.fold mk_frame_updator local_vars_collected)
      |> mk_locals_rcd
      |> Named_Target.theory_map (mk_frame_state_fns local_vars_collected)
      |> Named_Target.theory_map (mk_frame_lemmas local_vars_collected)
      |> mk_locals_aliases
      |> mk_globals_rcd
    val flat_lvars = lvars |> Symtab.dest_list |> map snd
  in
    (thy, flat_lvars @ gvars, globs)
  end
in
  declare_vars thy
end

type mungedb = (MString.t * typ * int ctype option * var_sort) CNameTab.table

fun mk_mungedb l = let
  open CNameTab
  fun foldthis ((nmi,ty,cty,vsort), tab) = let
    val fnm_opt = case vsort of Local s => SOME s | _ => NONE
  in
    update ({varname = #isa_name nmi, fnname = fnm_opt},
            (#isa_name nmi, ty, cty,vsort))
           tab
  end
in
  List.foldl foldthis empty l
end

structure csenvData = Theory_Data(
  type T = csenv Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
)

fun store_csenv (s,cse) =
    csenvData.map (Symtab.update(s,cse))
val get_csenv = Symtab.lookup o csenvData.get

structure ghostData = Theory_Data(
  type T = typ Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
)

fun store_ghostty (s, ty) =
    ghostData.map (Symtab.update(s,ty))
val get_ghostty = Symtab.lookup o ghostData.get

structure mungeDBs = Theory_Data(
  type T = mungedb Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.merge (K true)
)

fun store_mungedb (s, ty) = mungeDBs.map (Symtab.update (s,ty))
val get_mungedb = Symtab.lookup o mungeDBs.get

fun get_globals_data statety globty thy = let
    val acc = Sign.intern_const thy "globals"
    val upd = Sign.intern_const thy (suffix Record.updateN "globals")
    val acc = Const (acc, statety --> globty)
    val upd = Const (upd, (globty --> globty) --> statety --> statety)
    val (flds, _) = Record.get_recT_fields thy globty
  in {acc = acc, upd = upd, fields = flds} end

fun get_standard_globals statety globty thy = let
    val data = get_globals_data statety globty thy
    fun fld nm = let
        val flds = filter (fn (fnm, ty) => Long_Name.base_name fnm = nm)
          (#fields data)
        val (fldnm, ty) = case flds of [v] => v
          | [] => error ("could not find " ^ nm ^ " in global fields.")
          | _ => error ("multiple match for " ^ nm ^ " in global fields.")
        val acc = Const (fldnm, globty --> ty)
        val upd = Const (fldnm ^ Record.updateN,
            (ty --> ty) --> globty --> globty)
        val acc' = Abs ("s", statety, acc $ (#acc data $ Bound 0))
        val upd' = Abs ("u", ty --> ty, #upd data $ (upd $ Bound 0))
      in ((acc, upd), (acc', upd')) end
  in {hp = fld global_heap_var,
    phantom = fld (global_var phantom_state_name),
    ghost = fld (global_var ghost_state_name)}
  end

end (* struct *)

(* the string "local variables:" that appears a few lines above this was
   confusing emacs.  By adding the form-feed character below, I ensure that
   this no longer happens.  In other words, don't delete the form-feed! *)


(* Local variables: *)
(* End: *)
