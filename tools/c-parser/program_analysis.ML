(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature PROGRAM_ANALYSIS =
sig

  type 'ce ctype = 'ce Absyn.ctype
  type expr = Absyn.expr
  type ecenv = Absyn.ecenv
  type s2s_config = {anon_vars : bool, owners : string list,
                     allow_underscore_idents : bool,
                     munge_info_fname : string option}

  type 'a rcd_env = (string * (string * 'a) list) list
  type senv = int ctype rcd_env


  (* the "isa_name" is the munged name, but in the form without trailing
     _' suffixes *)
  type nm_info = {src_name : string, isa_name : MString.t}

  type var_info
  val is_global : var_info -> bool
  val srcname : var_info -> string
  val fullname : var_info -> string
  val get_mname : var_info -> MString.t
  val get_vi_fname : var_info -> string option
  val get_vi_type : var_info -> int ctype
  val get_vi_senv : var_info -> senv
  val get_vi_attrs : var_info -> StmtDecl.gcc_attribute list
  val declpos : var_info -> Region.t
  val vi_compare : var_info * var_info -> order
  val vi_nm_info : var_info -> nm_info

  datatype modify_var = M of var_info | TheHeap | PhantomState
    | GhostState | AllGlobals
  val mvar_compare : modify_var * modify_var -> order
  val mvar_toString : modify_var -> string
  structure MVar_Table : TABLE where type key = modify_var

  datatype fncall_type = DirectCall of string
                       | FnPtrCall of int ctype * int ctype list
  val fncall_cmp : fncall_type * fncall_type -> order

  type csenv
  val cse2ecenv : csenv -> ecenv
  val get_array_mentions : csenv -> (int ctype * int) Binaryset.set
  val get_senv : csenv -> senv
  val get_rettype : string -> csenv -> int ctype option
  val get_heaptypes : csenv -> int ctype Binaryset.set
  val compute_callgraphs : csenv ->
                           {callgraph: string Binaryset.set Symtab.table,
                            callers : string Binaryset.set Symtab.table}
  val get_addressed : csenv -> expr list MSymTab.table
  val get_callers   : csenv -> string Binaryset.set Symtab.table
  val get_typedefs  : csenv -> int ctype Symtab.table list
  val get_vars      : csenv -> var_info list Symtab.table
  val get_globals   : csenv -> var_info list
  val get_globinits : csenv -> Absyn.expr MSymTab.table
  val get_params : string -> csenv -> var_info list option
  val get_embedded_fncalls : csenv -> fncall_type Binaryset.set
  val get_addressed_vis : csenv -> var_info list
  val get_modifies : csenv -> string -> modify_var Binaryset.set option
  val get_functions : csenv -> string list
  val get_fninfo : csenv -> (int ctype * bool * var_info list) Symtab.table
  val get_hpfninfo : csenv -> Absyn.ext_decl Symtab.table
  val update_hpfninfo0 : Absyn.ext_decl -> Absyn.ext_decl Symtab.table ->
                         Absyn.ext_decl Symtab.table
  val get_defined_functions : csenv -> Region.Wrap.region Symtab.table
  val get_read_globals : csenv -> modify_var Binaryset.set Symtab.table
  val is_recursivefn : csenv -> string -> bool
  val mvar_traverse : csenv -> csenv
  val get_modified_global_locns : csenv -> string Binaryset.set MVar_Table.table
  val calc_untouched_globals : csenv -> int ctype MSymTab.table

  val fndes_callinfo : csenv -> expr -> fncall_type * (int ctype * int ctype list)

  val fns_by_type : csenv -> int ctype * int ctype list -> string list

  val cse_typing : csenv -> expr -> int ctype

  val process_decls : s2s_config -> Absyn.ext_decl list ->
                      ((Absyn.ext_decl list * Absyn.statement list) * csenv)
  val function_specs : csenv -> Absyn.fnspec list Symtab.table
  val sizeof : csenv -> int ctype -> int
  val alignof : csenv -> int ctype -> int
  val offset : csenv -> int ctype list -> int -> int
               (* [offset csenv flds i]
                  given flds, a list of types (a structure's fields),
                  return offset in bytes of field with number i (indexing from
                  zero).  offset env flds 0 always equals 0. *)

  type asm_stmt_elements = (string * bool * expr option * expr list)
  val split_asm_stmt : Absyn.statement_node -> asm_stmt_elements
  val merge_asm_stmt : asm_stmt_elements -> Absyn.statement_node

  val get_globals_rcd : csenv -> senv
  val export_mungedb : csenv -> unit

end

structure ProgramAnalysis : PROGRAM_ANALYSIS =
struct

open Absyn NameGeneration

type program = ext_decl list
type s2s_config = {anon_vars : bool, owners : string list,
                   allow_underscore_idents : bool, munge_info_fname : string option}

fun fname_str NONE = NameGeneration.initialisation_function
  | fname_str (SOME f) = f

(* ----------------------------------------------------------------------
    Collect all of a program's variables

    The variables collected will be analysed to generate an appropriate
    VCG environment state-space
   ---------------------------------------------------------------------- *)


type 'a rcd_env = (string * (string * 'a) list) list
type senv = int ctype rcd_env
datatype var_info =
         VI of {name : string,
                return_var : bool,
                vtype : int ctype,
                struct_env : senv,
                fname : string option,
                proto_param : bool,
                munged_name : MString.t,
                declared_at : Region.t,
                attrs : gcc_attribute list}

type nm_info = {src_name : string, isa_name : MString.t}
fun vi_nm_info (VI {name, munged_name, ...}) : nm_info =
  {src_name = name, isa_name = munged_name}
fun viToString (VI {name, fname,...}) =
    case fname of
      NONE => "global "^name
    | SOME f => name ^ " (in " ^ f ^")"
val fullname = viToString
fun srcname (VI{name,...}) = name

fun get_mname (VI {munged_name, ...}) = munged_name
fun get_vi_fname (VI {fname,...}) = fname
fun get_vi_type (VI {vtype,...}) = vtype
fun get_vi_senv (VI {struct_env,...}) = struct_env
fun declpos (VI {declared_at,...}) = declared_at

fun vi_compare(VI vi1, VI vi2) = let
  val ocmp = option_compare and pcmp = pair_compare and scmp = String.compare
  val mscmp = MString.compare
in
  pcmp (ocmp scmp, pcmp (scmp, mscmp))
       ((#fname vi1, (#name vi1, #munged_name vi1)),
        (#fname vi2, (#name vi2, #munged_name vi2)))
end

(* name will be NameGeneration.return_var_name if the variable is a
   "return" variable. There will be at least one such per function,
   unless the function returns "void".

   fname is NONE if the variable is global, "return" variables are not
   global.

   The struct_env is the structure type environment that is in force at the
   point of the variable's declaration.  This allows the consumer of this
   data to figure out what is meant by a Struct s type.

   return_var is true if the variable is a return variable.

   proto_param is true if the variable has been created from a
   prototype function declaration; such names can be overridden if a
   function definition later occurs.

*)

fun is_global (VI r) = case #fname r of NONE => true | _ => false

fun fnToString NONE = "at global level"
  | fnToString (SOME s) = "in function "^s

fun types_compatible globp ty1 ty2 =
    if not globp then ty1 = ty2
    else
      case (ty1, ty2) of
        (Array(ty1', sz1), Array(ty2', sz2)) =>
          (ty1' = ty2') andalso (sz1 = sz2 orelse sz1 = NONE orelse sz2 = NONE)
      | _ => ty1 = ty2

fun max_type ty1 ty2 =
    (* assumes types are compatible *)
    case (ty1, ty2) of
      (Array(_, NONE), _) => ty2
    | (_, Array(_, NONE)) => ty1
    | _ => ty1

fun vars_compatible vi1 vi2 =
    get_mname vi1 <> get_mname vi2 orelse
    is_global vi1 <> is_global vi2 orelse
    types_compatible (is_global vi1) (get_vi_type vi1) (get_vi_type vi2)

(* ----------------------------------------------------------------------

    vars field contains list of all variables of a given original name
    that are encountered.

    scope contains a stack of varinfo information, where top element
    of the stack is the current scope (innermost block).

    variables in these tables are indexed by their original names.

   ---------------------------------------------------------------------- *)

datatype modify_var = M of var_info | TheHeap | PhantomState
  | GhostState | AllGlobals
(* the AllGlobals summary is used in initial analysis of function bodies.
Underspecified operations modify AllGlobals rather than listing all the
actual globals, so that globals which are never *explicitly* modified can
still be candidates for const promotion. AllGlobals is expanded out once that
is done. *)

fun mvar_compare (mv1, mv2) = let
    fun mvid (M _) = 1
      | mvid TheHeap = 2
      | mvid PhantomState = 3
      | mvid GhostState = 4
      | mvid AllGlobals = 5
    fun mvc2 (M vi1, M vi2) = vi_compare (vi1, vi2)
      | mvc2 _ = EQUAL
    val id1 = mvid mv1
    val id2 = mvid mv2
  in if id1 < id2 then LESS else (if id1 > id2
    then GREATER
    else mvc2 (mv1, mv2)) end

fun mvar_toString TheHeap = "<the heap>"
  | mvar_toString (M vi) = MString.dest (get_mname vi)
  | mvar_toString PhantomState = "<phantom state>"
  | mvar_toString GhostState = "<ghost state>"
  | mvar_toString AllGlobals = "<*>"

structure MVar_Table = Table(struct type key = modify_var
                                    val ord = mvar_compare
                             end)



datatype fncall_type = DirectCall of string
                     | FnPtrCall of int ctype * int ctype list

val tycmp = ctype_compare Int.compare
val funtycmp =  pair_compare (tycmp, list_compare tycmp)
fun fncall_cmp (f1,f2) =
    case (f1, f2) of
      (DirectCall s1, DirectCall s2) => String.compare(s1, s2)
    | (DirectCall _, _) => LESS
    | (_, DirectCall _) => GREATER
    | (FnPtrCall x, FnPtrCall y) => funtycmp (x,y)

structure TypesTab = Table(struct type key = int ctype * int ctype list
                                  val ord = funtycmp
                           end)

datatype csenv (* CalculateState environment *) =
         CSE of {senv : senv, allow_underscore_idents : bool,
                 anon_vars : bool,
                 fninfo : (int ctype * bool * var_info list) Symtab.table,
                 hpfninfo : Absyn.ext_decl Symtab.table,
                 vars : var_info list Symtab.table,
                 scope : var_info Symtab.table list,
                 array_mentions : (int ctype * int) Binaryset.set,
                 enumenv : string wrap list *
                           (IntInf.int * string option) Symtab.table,
                 globinits : Absyn.expr MSymTab.table,
                 heaptypes : int ctype Binaryset.set,
                 call_info : fncall_type Binaryset.set Symtab.table,
                 caller_info : string Binaryset.set Symtab.table,
                 addressed : expr list MSymTab.table,
                 embedded_fncalls : fncall_type Binaryset.set,
                 recursive_functions : string Binaryset.set,
                 defined_functions : Region.Wrap.region Symtab.table,
                 modifies : modify_var Binaryset.set Symtab.table,
                 modify_locs : string Binaryset.set MVar_Table.table,
                 read_globals : modify_var Binaryset.set Symtab.table,
                 typedefs : int ctype Symtab.table list,
                 fnspecs : fnspec list Symtab.table,
                 owners : string list,
                 munge_info_fname : string option}
fun get_vars (CSE {vars,...}) = vars
fun get_senv (CSE {senv,...}) = senv
fun get_scope (CSE {scope,...}) = scope
fun get_fulleenv (CSE {enumenv,...}) = enumenv
fun get_globinits (CSE {globinits,...}) = globinits
fun get_enumenv cse = #2 (get_fulleenv cse)
fun get_fninfo (CSE {fninfo, ...}) = fninfo
fun get_hpfninfo (CSE {hpfninfo, ...}) = hpfninfo
fun get_rettype fnname (CSE {fninfo,...}) =
    Option.map #1 (Symtab.lookup fninfo fnname)
fun get_params fname (CSE {fninfo,...}) =
    Option.map #3 (Symtab.lookup fninfo fname)
fun get_callgraph (CSE {call_info,...}) = call_info
fun get_callers (CSE {caller_info,...}) = caller_info
fun get_modifies (CSE {modifies,...}) fname = Symtab.lookup modifies fname
fun get_defined_functions (CSE {defined_functions = d, ...}) = d
fun get_typedefs (CSE {typedefs,...}) = typedefs
fun get_read_globals (CSE {read_globals,...}) = read_globals
fun get_anon_vars (CSE {anon_vars, ...}) = anon_vars
fun get_owners (CSE{owners,...}) = owners
fun get_allow_underscores(CSE{allow_underscore_idents = aui,...}) = aui

fun get_fields cse s = valOf (StrictCBasics.assoc(get_senv cse, s))
                       handle Option =>
                              raise Fail ("get_fields: no fields for "^s)
fun get_array_mentions (CSE {array_mentions,...}) = array_mentions

fun get_heaptypes (CSE {heaptypes,...}) = heaptypes
fun get_addressed (CSE {addressed,...}) = addressed
fun get_embedded_fncalls (CSE {embedded_fncalls, ...}) = embedded_fncalls

fun get_globals (CSE {vars,...}) = let
  fun innerfold (vi,acc) =
      if is_global vi andalso not (function_type (get_vi_type vi)) then
        vi::acc
      else acc
  fun foldthis (_, vilist) acc = List.foldl innerfold acc vilist
in
  List.rev (Symtab.fold foldthis vars [])
end

fun get_functions (CSE {fninfo,...}) = Symtab.keys fninfo
fun function_specs (CSE {fnspecs,...}) = fnspecs

fun is_recursivefn (CSE {recursive_functions,...}) s =
    Binaryset.member(recursive_functions, s)

fun get_modified_global_locns (CSE {modify_locs,...}) = modify_locs

fun emptycse ({anon_vars,owners,allow_underscore_idents = aui,munge_info_fname,...} : s2s_config)=
    CSE {senv = [], anon_vars = anon_vars, allow_underscore_idents = aui,
         vars = Symtab.empty, scope = [Symtab.empty],
         fninfo = Symtab.empty, hpfninfo = Symtab.empty,
         enumenv = ([],Symtab.empty),
         heaptypes = Binaryset.empty (ctype_compare Int.compare),
         array_mentions = Binaryset.empty (pair_compare
                                               (ctype_compare Int.compare,
                                                Int.compare)),
         call_info = Symtab.empty,
         caller_info = Symtab.empty,
         addressed = MSymTab.empty,
         defined_functions = Symtab.empty,
         embedded_fncalls = Binaryset.empty fncall_cmp,
         recursive_functions = Binaryset.empty String.compare,
         modifies = Symtab.empty, modify_locs = MVar_Table.empty,
         typedefs = [], fnspecs = Symtab.empty, read_globals = Symtab.empty,
         globinits = MSymTab.empty, owners = owners, munge_info_fname = munge_info_fname}

fun cons h t = h::t

fun get_addressed_vis (CSE {vars, addressed, ...}) = let
  fun innerfold (vi,acc) =
      if is_global vi andalso MSymTab.defined addressed (get_mname vi) then
        vi::acc
      else acc
  fun foldthis (_, vis) acc = List.foldl innerfold acc vis
in
  Symtab.fold foldthis vars []
end



local
  open FunctionalRecordUpdate
  (* see http://mlton.org/FunctionalRecordUpdate *)
  fun cse_makeUpdate z = makeUpdate24 z
  fun update_CSE z = let
    fun from senv aui anon_vars fninfo hpfninfo vars scope enumenv array_mentions
             heaptypes call_info addressed embedded_fncalls modifies
             defined_functions recursive_functions caller_info
             modify_locs typedefs fnspecs read_globals globinits owners munge_info_fname =
        {senv = senv, anon_vars = anon_vars, fninfo = fninfo, vars = vars,
         hpfninfo = hpfninfo,
         scope = scope, enumenv = enumenv, array_mentions = array_mentions,
         heaptypes = heaptypes, call_info = call_info, addressed = addressed,
         embedded_fncalls = embedded_fncalls, modifies = modifies,
         defined_functions = defined_functions, allow_underscore_idents = aui,
         recursive_functions = recursive_functions, caller_info = caller_info,
         modify_locs = modify_locs, typedefs = typedefs, fnspecs = fnspecs,
         read_globals = read_globals, globinits = globinits, owners = owners,
         munge_info_fname = munge_info_fname}
    (* fields in reverse order to above *)
    fun from' munge_info_fname owners globinits read_globals fnspecs typedefs modify_locs caller_info
              recursive_functions defined_functions modifies embedded_fncalls
              addressed call_info heaptypes array_mentions enumenv scope vars
              hpfninfo fninfo anon_vars aui senv =
        {senv = senv, anon_vars = anon_vars, fninfo = fninfo, vars = vars, scope = scope,
         hpfninfo = hpfninfo,
         allow_underscore_idents = aui,
         enumenv = enumenv, array_mentions = array_mentions,
         heaptypes = heaptypes, call_info = call_info, addressed = addressed,
         embedded_fncalls = embedded_fncalls, modifies = modifies,
         defined_functions = defined_functions,
         recursive_functions = recursive_functions, caller_info = caller_info,
         modify_locs = modify_locs, typedefs = typedefs, fnspecs = fnspecs,
         read_globals = read_globals, globinits = globinits, owners = owners,
         munge_info_fname = munge_info_fname}

    fun to f {senv, anon_vars, fninfo, vars, scope, enumenv, array_mentions, heaptypes,
              hpfninfo, munge_info_fname,
              call_info, addressed, embedded_fncalls, modifies,
              defined_functions, recursive_functions, caller_info,
              modify_locs, typedefs, fnspecs, read_globals, globinits,owners,
              allow_underscore_idents = aui} =
        f senv aui anon_vars fninfo hpfninfo vars scope enumenv array_mentions
          heaptypes call_info addressed embedded_fncalls modifies
          defined_functions recursive_functions caller_info
          modify_locs typedefs fnspecs read_globals globinits owners munge_info_fname
  in
    cse_makeUpdate (from, from', to)
  end z

  fun vi_makeUpdate z = makeUpdate9 z
  fun update_VI z = let
    fun from name return_var vtype struct_env fname proto_param
            munged_name declared_at attrs =
        {name = name, return_var = return_var, vtype = vtype,
         struct_env = struct_env, fname = fname, declared_at = declared_at,
         proto_param = proto_param, munged_name = munged_name,
         attrs = attrs}
    fun from' attrs declared_at munged_name proto_param fname struct_env
              vtype return_var name =
        {name = name, return_var = return_var, vtype = vtype,
         struct_env = struct_env, fname = fname, declared_at = declared_at,
         proto_param = proto_param, munged_name = munged_name,
         attrs = attrs}
    fun to f {name, return_var, vtype, struct_env, fname, proto_param,
              munged_name, declared_at, attrs} =
        f name return_var vtype struct_env fname proto_param
          munged_name declared_at attrs
  in
    vi_makeUpdate (from, from', to)
  end z

in
fun cse_fupdvars f (CSE cse) =
    CSE (update_CSE cse (U #vars (f (#vars cse))) $$)
fun cse_fupdfninfo f (CSE cse) =
    CSE (update_CSE cse (U #fninfo (f (#fninfo cse))) $$)
fun cse_fupdhpfninfo f (CSE cse) =
    CSE (update_CSE cse (U #hpfninfo (f (#hpfninfo cse))) $$)
fun cse_fupdscope f (CSE cse) =
    CSE (update_CSE cse (U #scope (f (#scope cse))) $$)
fun cse_fupdsenv f (CSE cse) =
    CSE (update_CSE cse (U #senv (f (#senv cse))) $$)
fun cse_fupdenumenv f (CSE cse) =
    CSE (update_CSE cse (U #enumenv (f (#enumenv cse))) $$)
fun cse_fupdarray_mentions f (CSE cse) =
    CSE (update_CSE cse (U #array_mentions (f (#array_mentions cse))) $$)
fun cse_fupdheaptypes f (CSE cse) =
    CSE (update_CSE cse (U #heaptypes (f (#heaptypes cse))) $$)
fun cse_fupdcallgraph f (CSE cse) =
    CSE (update_CSE cse (U #call_info (f (#call_info cse))) $$)
fun cse_fupdcaller_info f (CSE cse) =
    CSE (update_CSE cse (U #caller_info (f (#caller_info cse))) $$)
fun cse_fupdaddressed f (CSE cse) =
    CSE (update_CSE cse (U #addressed (f (#addressed cse))) $$)
fun cse_fupdembedded_fncalls f (CSE cse) =
    CSE (update_CSE cse (U #embedded_fncalls (f (#embedded_fncalls cse))) $$)
fun cse_fupdmodifies f (CSE cse) =
    CSE (update_CSE cse (U #modifies (f (#modifies cse))) $$)
fun cse_fupdmodifylocs f (CSE cse) =
    CSE (update_CSE cse (U #modify_locs (f (#modify_locs cse))) $$)
fun cse_fupdread_globals f (CSE cse) =
    CSE (update_CSE cse (U #read_globals (f (#read_globals cse))) $$)
fun cse_fupddefined_functions f (CSE cse) =
    CSE (update_CSE cse (U #defined_functions (f (#defined_functions cse))) $$)
fun cse_fupdrecursive_functions f (CSE cse) =
    CSE (update_CSE cse (U #recursive_functions (f (#recursive_functions cse))) $$)
fun cse_fupdfnspecs f (CSE cse) =
    CSE (update_CSE cse (U #fnspecs (f (#fnspecs cse))) $$)
fun cse_fupdglobinits f (CSE cse) =
    CSE (update_CSE cse (U #globinits (f (#globinits cse))) $$)


fun upd_mname mname (VI vi) =
    VI (update_VI vi (U #munged_name mname) $$)
fun vi_upd_type ty (VI vi) =
    VI (update_VI vi (U #vtype ty) $$)

end;

fun get_vi_attrs (VI vi) = #attrs vi

fun fns_by_type cse (retty, ptyps) = let
  val fninfo = get_fninfo cse
  fun listcmp x =
      case x of
        ([], []) => true
      | (ctyp::ctyps, vi::vis) => ctyp = get_vi_type vi andalso
                                  listcmp (ctyps, vis)
      | _ => false
  fun foldthis (nm, (nm_retty, _, ps)) acc =
      if nm_retty = retty andalso listcmp (ptyps, ps) then nm::acc
      else acc
in
  Symtab.fold foldthis fninfo []
end

fun new_call {caller, callee} cse = let
  val cse' = cse_fupdcallgraph
                 (Symtab.map_default (caller, Binaryset.empty fncall_cmp)
                                     (fn s => Binaryset.add(s,callee)))
                 cse
in
  case callee of
    DirectCall somefn =>
    cse_fupdcaller_info
        (Symtab.map_default (somefn, Binaryset.empty String.compare)
                            (fn s => Binaryset.add(s,caller))) cse'
  | _ => cse'
end

fun mk_recursive f =
    cse_fupdrecursive_functions (fn s => Binaryset.add(s,f))

fun new_embedded_fncall s cse =
    cse_fupdembedded_fncalls (fn set => Binaryset.add(set,s)) cse

fun new_addressed vi expr =
    cse_fupdaddressed (MSymTab.map_default (get_mname vi, []) (cons expr))


fun new_array tysz =
    cse_fupdarray_mentions (fn s => Binaryset.add(s,tysz))

fun add_heaptype ty env = let
  val htypes = get_heaptypes env
in
  if Binaryset.member(htypes, ty) then env
  else let
      val env' = cse_fupdheaptypes (fn s => Binaryset.add(s, ty)) env
    in
      case ty of
        Ptr ty0 => add_heaptype ty0 env'
      | Array(ty0, _) => add_heaptype ty0 env'
      | StructTy s => let
        in
          case StrictCBasics.assoc (get_senv env', s) of
            NONE => (* do nothing for the moment, thus env, not env' *) env
          | SOME flds =>
            List.foldl (fn ((_, fldty), env) => add_heaptype fldty env)
                       env'
                       flds
        end
      | _ => env'
    end
end


fun update_hpfninfo0 d tab =
    case d of
        FnDefn((_, fname), _, _, _) => Symtab.update(node fname,d) tab
      | Decl d0 => let
        in
          case node d0 of
            ExtFnDecl(ed0 as {name = name_w,...}) => let
              val name = node name_w
            in
              case Symtab.lookup tab name of
                NONE => Symtab.update(name, d) tab
              | SOME (FnDefn _) => tab
              | SOME (Decl d1) => let
                in
                  case node d1 of
                    ExtFnDecl {specs,name,rettype,params} => let
                      val newd0 = {rettype=rettype,name=name,params=params,
                                   specs=merge_specs (#specs ed0) specs}
                      val newd = wrap(ExtFnDecl newd0, left d0, right d0)
                    in
                      Symtab.update (node name, Decl newd) tab
                    end
                  | _ => tab
                end
            end
          | _ => tab
        end

fun update_hpfninfo d = cse_fupdhpfninfo (update_hpfninfo0 d)

fun insert_fnretty (s, ty, env) = let
  open Feedback
  fun upd tab =
      case Symtab.lookup tab (node s) of
        NONE => (informStr (6, "Recording return type of "^ tyname ty^
                               " for function "^ node s);
                 Symtab.update(node s,(ty,true,[])) tab)
                (* insert dummy values for parameters *)
      | SOME (ty',_,_) => if ty = ty' then tab
                          else
                            (Feedback.errorStr'(left s, right s,
                                                "Incompatible return type");
                             tab)
in
  cse_fupdfninfo upd env
end

fun new_defined_fn s =
    cse_fupddefined_functions (Symtab.update(node s, Region.Wrap.region s))

fun set_proto_params fname ps env = let
  fun upd tab =
      case Symtab.lookup tab fname of
        NONE => raise Fail "set_proto_params: This should never happen"
      | SOME(retty,protop,_) => if not protop then tab
                                else Symtab.update(fname,(retty,true,ps)) tab
in
  cse_fupdfninfo upd env
end

fun set_defn_params fname ps env = let
  fun upd tab =
      case Symtab.lookup tab fname of
        NONE => raise Fail "set_defn_params: This should never happen"
      | SOME (retty,_,_) => Symtab.update(fname, (retty,false,ps)) tab
in
  cse_fupdfninfo upd env
end

fun add_modification fname vi env = let
  val dflt = Binaryset.empty mvar_compare
  val dflt_locs = Binaryset.empty String.compare
  fun add e set = Binaryset.add(set,e)
in
  (cse_fupdmodifies (Symtab.map_default (fname, dflt) (add vi)) o
   cse_fupdmodifylocs (MVar_Table.map_default (vi,dflt_locs) (add fname)))
  env
end

fun add_read fname mvi env = let
  val dflt = Binaryset.empty mvar_compare
  fun add e set = Binaryset.add(set, e)
in
  cse_fupdread_globals (Symtab.map_default (fname,dflt) (add mvi)) env
end

fun calc_untouched_globals cse = let
  open MSymTab
  fun mydelete (t,e) = delete_safe e t
  val all_globals = let
    fun foldthis (vi as VI vr, tab) =
        if #return_var vr then tab
        else
          update (get_mname vi, get_vi_type vi) tab
  in
    List.foldl foldthis empty (get_globals cse)
  end
  val remove_modified = let
    fun foldthis (mvar, _) set =
        case mvar of
          M vi => mydelete(set, get_mname vi)
        | _ => set
  in
    MVar_Table.fold foldthis (get_modified_global_locns cse)
  end
  val remove_addressed = let
    fun foldthis (k, _) set = mydelete(set, k)
  in
    MSymTab.fold foldthis (get_addressed cse)
  end
in
  all_globals
      |> remove_modified
      |> remove_addressed
end

(* ML computation of alignment and type sizes *)
val ti  = IntInf.toInt
fun ialignof ity = let
  open ImplementationNumbers
in
  case ity of
    Char => ti 1
  | Short => ti (shortWidth div CHAR_BIT)
  | Int => ti (intWidth div CHAR_BIT)
  | Long => ti (longWidth div CHAR_BIT)
  | LongLong => ti (llongWidth div CHAR_BIT)
end

fun roundup base n = if n mod base = 0 then n else (n div base + 1) * base
fun maxl [] = 0
  | maxl (h::t) = let val m = maxl t in if h > m then h else m end

fun alignof cse ty : Int.int = let
  open ImplementationNumbers
in
  case ty of
    Signed i => ialignof i
  | Unsigned i => ialignof i
  | PlainChar => 1
  | Ptr _ => IntInf.toInt (ptrWidth div CHAR_BIT)
  | StructTy s => maxl (map (alignof cse o #2) (get_fields cse s))
  | Array(base, _) => alignof cse base
  | EnumTy _ => alignof cse (Signed Int)
  | Ident _ => raise Fail "ProgramAnalysis.alignof: typedefs need to be \
                          \compiled out"
  | Function _ => raise Fail "ProgramAnalysis.alignof: functions have no \
                             \alignment"
  | Bitfield _ => raise Fail "ProgramAnalysis.alignof: bitfields have no \
                             \alignment"
  | Void => raise Fail "ProgramAnalysis.alignof: void has no alignment"
  | _ => raise Fail ("ProgramAnalysis.alignof: no alignment for "^tyname ty)
end

fun offset cse tylist n = let
  val offset = offset cse
in
  if n = 0 then 0
  else if length tylist <= n then 0
  else let
      val offn' = offset tylist (n - 1)
      val tyn' = List.nth(tylist, n - 1)
      val tyn = List.nth(tylist, n)
      val b = offn' + sizeof cse tyn'
    in
      roundup (alignof cse tyn) b
    end
end
and strsize cse s : Int.int = let
    val flds = map #2 (get_fields cse s)
    val a = maxl (map (alignof cse) flds)
    val lastn = length flds - 1
    val lastty = List.last flds
    val off = offset cse flds lastn
  in
    roundup a (off + sizeof cse lastty)
  end
and sizeof cse ty = Absyn.sizeof (strsize cse) ty

fun cse2ecenv cse = CE {enumenv = get_enumenv cse,
                        typing = cse_typing cse,
                        structsize = strsize cse}
and cse_typing cse e = let
  val scopes = get_scope cse
  fun var_typing [] _ = NONE
    | var_typing (tab::rest) s =
      case Symtab.lookup tab s of
        NONE => var_typing rest s
      | SOME vi => SOME (get_vi_type vi)
                    handle Empty => raise Fail "Empty vi-list in cse_typing"
in
  ExpressionTyping.expr_type (cse2ecenv cse)
                              (get_senv cse)
                              (var_typing scopes)
                              e
end

fun fndes_callinfo cse e =
    case (cse_typing cse e, enode e) of
      (Function x, Var(s, _)) => let
      in
        (DirectCall s, x)
      end
    | (ty, _) => let
      in
        case ty of
          Function x => (FnPtrCall x, x)
        | Ptr (Function x) => (FnPtrCall x, x)
        | _ => raise eFail (e, "Function designator has bad type ("^
                               tyname ty ^ ")")
      end


fun process_enumdecl (enameopt_w,econsts) env = let
  fun mk_ecenv (set, enum_tab) = CE {enumenv = enum_tab,
          typing = cse_typing env, structsize = strsize env}
  fun foldthis ((ecn_w, eopt), (i, set, enum_tab)) =
      case List.find (fn sw => node sw = node ecn_w) set of
        SOME first => (Feedback.errorStr'(left ecn_w, right ecn_w,
                                          "Re-using enum const (" ^ node ecn_w ^
                                          ") from "^
                                          Region.toString
                                              (Region.Wrap.region first));
                       (i, set, enum_tab))
      | NONE => let
          val e_val = case eopt of
                        NONE => i
                      | SOME e => consteval (mk_ecenv (set, enum_tab)) e
          val tab' = Symtab.update(node ecn_w, (e_val, node enameopt_w)) enum_tab
        in
          (e_val + 1, ecn_w::set, tab')
        end
  val (set0, enum_tab0) = get_fulleenv env
  val (_, set', enum_tab') = List.foldl foldthis (0,set0,enum_tab0) econsts
in
  cse_fupdenumenv (K (set', enum_tab')) env
end

fun process_type (posrange as (l,r)) (ty, env) =
    case ty of
      Array(elty, sz_opt) => let
        val env' = process_type posrange (elty, env)
        val ecenv = cse2ecenv env
        val ti = IntInf.toInt
      in
        case sz_opt of
          NONE => env'
        | SOME sz_e => let
            val sz_i = ti (consteval ecenv sz_e)
          in
            if sz_i < 1 then let
                val region = Region.make{left=l,right=r}
              in
                raise Fail ("Array in area "^Region.toString region^
                            " has non-positive size "^Int.toString sz_i)
              end
            else
              new_array (constify_abtype ecenv elty, sz_i) env'
          end
      end
    | Ptr ty' => let
        val ty'' = constify_abtype (cse2ecenv env) ty'
      in
        process_type posrange (ty',add_heaptype ty'' env)
      end
    | _ => env


fun check_uscore_ok s = let
  val s = NameGeneration.rmUScoreSafety s
in
  s <> "" andalso String.sub(s,0) <> #"_"
end

fun newstr_decl (nm, flds0 : (expr ctype * string wrap) list) cse = let
  open NameGeneration
  fun foldthis ((cty,fldnm),acc) =
      process_type (left fldnm, right fldnm) (cty, acc)
  val cse = List.foldl foldthis cse flds0
  val ecenv = cse2ecenv cse
  fun uscore_check i nmty s =
      if get_allow_underscores cse orelse check_uscore_ok (node s) then ()
      else
        Feedback.errorStr'(left s, right s,
                           rmUScoreSafety (i (node s)) ^
                           " is an illegal name for a structure " ^nmty)
  val flds =
      map (fn (ty,s) =>
              ((uscore_check unC_field_name "field" s; node s),
               remove_enums (constify_abtype ecenv ty)))
          flds0
  val _ = uscore_check unC_struct_name "tag" nm
in
  cse_fupdsenv (fn rest => (node nm, flds) :: rest) cse
end


fun find_scoped_vdecl name scope = let
  fun recurse i scope =
    case scope of
      [] => NONE
    | (db::rest) => let
      in
        case Symtab.lookup db name of
          NONE => recurse (i + 1) rest
        | SOME vi => let
            val fnm = case get_vi_fname vi of NONE => "<global>" | SOME s => s
          in
            Feedback.informStr(10, "find_scoped_vdecl: Found "^fnm^":"^name^
                                   " at depth "^Int.toString i);
            SOME (i,vi)
          end
      end
in
  recurse 0 scope
end

val new_scope = cse_fupdscope (fn l => Symtab.empty :: l)
val pop_scope = cse_fupdscope tl
fun fupd_hd _ [] = raise Fail "fupd_hd: empty list"
  | fupd_hd f (h :: t) = f h :: t
fun fupd_last _ [] = raise Fail "fupd_last: empty list"
  | fupd_last f [h] = [f h]
  | fupd_last f (h1::t) = h1::fupd_last f t

fun pluck _ [] = NONE
  | pluck P (h::t) = if P h then SOME(h,t)
                     else case pluck P t of
                            NONE => NONE
                          | SOME (e,rest) => SOME (e, h::rest)

(* munge_insert adds a newly declared variable to the list of
   all seen variables, and to the current scope.  It is there that
   the all seen variables list is consulted to see if a name-change is
   going to be necessary *)
fun munge_insert (v as VI vrec) cse = let
  val v_table = get_vars cse
  fun merge_insert (n,vi) tab = Symtab.map_default (n,[]) (fn t => vi::t) tab
  val name = #name vrec
  fun merge_vis v1 v2 = let
    val ty1 = get_vi_type v1
    val ty2 = get_vi_type v2
  in
    vi_upd_type (max_type ty1 ty2) v1
  end
  fun same_global v' =
    is_global v' andalso srcname v' = name andalso get_mname v' = get_mname v

  fun vars_add v1 vlist =
      if not (is_global v1) then merge_insert(name,v1)
      else
        case pluck same_global vlist of
          NONE => Symtab.update(name, v::vlist)
        | SOME (v2, rest) => Symtab.update(name, merge_vis v1 v2::rest)
  fun scope_add v1 tab =
      if not (is_global v1) then Symtab.update(name, v1) tab
      else
        case Symtab.lookup tab name of
          NONE => Symtab.update(name, v1) tab
        | SOME v2 => Symtab.update(name, merge_vis v1 v2) tab
  val scope = fupd_hd
in
  if not (get_anon_vars cse) orelse is_global v orelse #return_var vrec then
    case Symtab.lookup v_table name of
      NONE => (v, (cse_fupdvars (Symtab.update(name, [v])) o
                   cse_fupdscope (scope (Symtab.update(name, v)))) cse)
    | SOME vlist => let
        val _ = Feedback.informStr(10,  "Found vlist for "^name^" of length "^
                                        Int.toString (length vlist))
      in
        case List.find (fn v' => not (vars_compatible v v')) vlist of
          NONE => (v, (cse_fupdvars (vars_add v vlist) o
                       cse_fupdscope (scope (scope_add v))) cse)
        | SOME badv => let
            open Feedback
            val _ = if is_global v andalso is_global badv then
                      errorStr(declpos v,
                               "Global variable "^viToString v^
                               " not compatible with previous declaration at "^
                               Region.toString (declpos badv))
                    else
                      informStr(4, Region.toString (declpos v)^ ": variable "^
                                   viToString v^ " not compatible with previous "^
                                   viToString badv^ " ("^
                                   Region.toString (declpos badv) ^
                                   ") -- renaming")
            val newname =
                tag_name_with_type {name = name,
                                    typname = tyname (get_vi_type v)}
                  |> MString.mk
            val new_vi = upd_mname newname v
          in
            (new_vi, (cse_fupdvars (merge_insert(name, new_vi)) o
                      cse_fupdscope (scope (Symtab.update(name, new_vi)))) cse)
          end
      end
  else (* "anonymous" local variables *) let
      val allvars_in_scope = List.concat (map (map #2 o Symtab.dest) (get_scope cse))
      val varprefix = tyname (get_vi_type v) ^ "'local"
      fun foldthis (vi, c) =
          if String.isPrefix varprefix (MString.dest (get_mname vi)) then c + 1 else c
      val numdups = List.foldl foldthis 0 allvars_in_scope
      val new_vi = upd_mname (MString.mk (varprefix ^ Int.toString numdups)) v
    in
      (new_vi, (cse_fupdvars (merge_insert(name, new_vi)) o
                cse_fupdscope (fupd_hd (Symtab.update(name, new_vi)))) cse)
    end
end


fun insert_var (v as VI {name, vtype, fname, ...}, e as CSE cse) = let
  open Symtab
  val scopes = #scope cse
  val _ = Feedback.informStr(10,
                             "insert_var: Inserting "^name^"("^tyname vtype^
                             ") at scope depth "^
                             Int.toString (length scopes))
in
  case find_scoped_vdecl name scopes of
    NONE => munge_insert v e
  | SOME (i,_) => let
    in
      case dest_embret (get_mname v) of
        NONE => if i = length scopes - 1 (* i.e., a global *) then
                  munge_insert v e
                else
                  raise Fail ("Variable "^name^ " " ^ fnToString fname ^
                              " declared twice (no scope-masking allowed)")
      | SOME _ => (v,e)
    end
end

fun inits_to_elist f (InitE e) acc = List.rev (f e :: acc)
  | inits_to_elist f (InitList dis) acc =
       foldl (fn ((_,i),a) => inits_to_elist f i a) acc dis

structure TypeTab = Table(type key = int ctype
                          val ord = ctype_compare Int.compare);

datatype lvstate = LV | RV



(* fname is a string option; NONE corresponds to an expression appearing at
   the global level, as can happen in the initialisation of a global *)
fun process_expr lvstate fname (env as CSE {senv, ...}) e = let
  fun inc ((fm,greads), k) = (TypeTab.map_default (k,0) (fn i => i + 1) fm, greads)
  (* count_fncalls not only counts function calls in the accompanying fmap,
     but is also a general traversal of the expression, where other stuff
     can be done too *)
  datatype addr_status = Rvalue | BrackLeft | UnderAddr | BL_Addr | Lvalue
                       | BrackLeftLV | SzOf
  fun lvadstat BrackLeftLV = true | lvadstat Lvalue = true | lvadstat _ = false
  datatype eact = E of expr | RAS of addr_status (* Restore Address Status *)
  fun rval (env,fmap,_) = (env,fmap,Rvalue)
  fun count_fncalls (ef as (env,fmap,_)) elist =
      case elist of
        [] => (env,fmap)
      | E e :: es => count_fncall ef e es
      | RAS b :: es => count_fncalls (env,fmap,b) es
  and count_fncall (ef as (env,fmap,adstat)) e es =
      case enode e of
        BinOp(bop, e1, e2) => let
          val scp = bop = LogAnd orelse bop = LogOr
          val acc = if scp andalso eneeds_sc_protection e2 andalso
                       adstat <> SzOf
                    then
                      (env,inc(fmap,Signed Int),adstat)
                    else rval ef
        in
          count_fncalls acc (E e1::E e2::es)
        end
      | UnOp(uop, e1) => let
        in
          case uop of
            Addr => count_fncalls (env,fmap,UnderAddr) (E e1::RAS adstat :: es)
          | _ => count_fncalls (rval ef) (E e1::es)
        end
      | CondExp(e1,e2,e3) => let
          val acc =
              if adstat <> SzOf andalso
                 (eneeds_sc_protection e2 orelse eneeds_sc_protection e3)
              then let
                  val ty1 = cse_typing env e2
                  val ty2 = cse_typing env e3
                  val common = unify_types (ty1, ty2)
                      handle Fail _ =>
                             (Feedback.errorStr'(eleft e2,
                                                 eright e3,
                                                 "Types of conditional exp \
                                                 \branches (" ^ tyname ty1 ^
                                                 ", " ^ tyname ty2 ^
                                                 ") not compatible");
                              ty1)
                in
                  (env,inc(fmap,common),adstat)
                end
              else rval ef
        in
          count_fncalls acc (E e1::E e2::E e3::es)
        end
      | Constant _ => count_fncalls ef es
      | Var(s,vinfo_ref) => let
        in
          case find_scoped_vdecl s (get_scope env) of
            NONE => let
            in
              case Symtab.lookup (get_enumenv env) s of
                NONE => let
                in
                  case get_rettype s env of
                    NONE => (Feedback.errorStr'(eleft e, eright e,
                                                "Undeclared variable: "^s);
                             count_fncalls ef es)
                  | SOME retty => let
                      val ptys = map get_vi_type (valOf (get_params s env))
                    in
                      vinfo_ref := SOME (Function(retty, ptys), FunctionName);
                      count_fncalls ef es
                    end
                end
              | SOME _ => (vinfo_ref := SOME (Signed Int, EnumC);
                           count_fncalls ef es)
            end
          | SOME (_, vi) => let
              val ty = get_vi_type vi
              fun addifglob env (fm as (fmap, greads)) =
                  if is_global vi andalso isSome fname andalso adstat <> SzOf
                  then
                    (add_read (valOf fname) (M vi) env,
                     (fmap, Binaryset.add(greads, e)))
                  else (env, fm)
              val (env,fmap) =
                  case adstat of
                    Rvalue => if array_type ty then
                                (new_addressed vi e env, fmap)
                              else addifglob env fmap
                  | BL_Addr => if aggregate_type ty then (new_addressed vi e env, fmap)
                               else (env, fmap)
                  | UnderAddr => if function_type ty then (env, fmap)
                                 else (new_addressed vi e env, fmap)
                  | BrackLeft => if ptr_type ty andalso isSome fname then
                                   let
                                     val (env, fmap) = addifglob env fmap
                                   in
                                     (add_read (valOf fname) TheHeap env, fmap)
                                   end
                                 else addifglob env fmap
                  | BrackLeftLV => (env, fmap)
                  | Lvalue => (env, fmap)
                  | SzOf => (env, fmap)
              val info =
                  if function_type ty then FunctionName
                  else
                    MungedVar
                      { munge = get_mname vi,
                        owned_by = StmtDecl.get_owned_by (get_vi_attrs vi)
                      }

            in
              vinfo_ref := SOME (ty, info);
              count_fncalls (env,fmap,adstat) es
            end
        end
      | StructDot(e1, _) => let
          val ty = cse_typing env e
        in
          if adstat = Rvalue andalso array_type ty then
            count_fncalls (env,fmap,UnderAddr) (E e1::RAS adstat::es)
          else let
              val env =
                  if adstat = BrackLeft andalso ptr_type ty andalso
                     isSome fname
                  then add_read (valOf fname) TheHeap env
                  else env
            in
              count_fncalls (env, fmap, adstat) (E e1::es)
            end
        end
      | ArrayDeref(e1,e2) => let
          val ty = cse_typing env e
          val ty1 = cse_typing env e1
          val env = if ptr_type ty1 andalso isSome fname andalso
                       not (lvadstat adstat) andalso adstat <> SzOf
                    then
                      add_read (valOf fname) TheHeap env
                    else env
        in
          case adstat of
            UnderAddr => count_fncalls (env,fmap,BL_Addr)
                                       (E e1::RAS Rvalue::E e2::RAS adstat::es)
          | Rvalue => let
            in
              if array_type ty then
                count_fncalls (env,fmap,BL_Addr)
                              (E e1::RAS Rvalue::E e2::RAS adstat::es)
              else
                count_fncalls (env,fmap,BrackLeft) (E e1::RAS Rvalue::E e2::es)
            end
          | BrackLeft => count_fncalls (env,fmap,BrackLeft)
                                       (E e1::RAS Rvalue::E e2::es)
          | BL_Addr => count_fncalls (env,fmap,BL_Addr)
                                     (E e1::RAS Rvalue::E e2::RAS adstat::es)
          | Lvalue => count_fncalls (env,fmap,BrackLeftLV)
                                    (E e1::RAS Rvalue::E e2::RAS Lvalue::es)
          | BrackLeftLV =>
            count_fncalls (env,fmap,BrackLeftLV)
                          (E e1::RAS Rvalue::E e2::RAS BrackLeftLV::es)
          | SzOf => count_fncalls (env,fmap,SzOf) (E e1::E e2::es)
        end
      | Deref e1 => let
          val env = if isSome fname andalso adstat <> Lvalue andalso
                       adstat <> SzOf
                    then
                      add_read (valOf fname) TheHeap env
                    else env
          val stat' = if adstat = SzOf then SzOf else Rvalue
        in
          count_fncalls (env,fmap,stat') (E e1::RAS adstat:: es)
        end
      | TypeCast(ty, e1) =>
          count_fncalls (process_type (left ty, right ty)
                                      (node ty, env),
                         fmap, Rvalue)
                        (E e1::es)
      | Sizeof e1 => count_fncalls (env,fmap,SzOf) (E e1::RAS adstat::es)
          (* sizeof expressions aren't evaluated - so ignore e1 *)
      | SizeofTy ty => count_fncalls (process_type (left ty, right ty)
                                                   (node ty,env), fmap,
                                      Rvalue) es
      | EFnCall(fn_e, args) => let
          val (callee, (rettyp, _)) = fndes_callinfo env fn_e
          val env = if adstat <> SzOf then
                      new_call {caller = fname_str fname, callee = callee} env
                    else env
          val env = if adstat <> SzOf then new_embedded_fncall callee env
                    else env
          val stat' = if adstat <> SzOf then Rvalue else SzOf
        in
          count_fncalls (env,inc(fmap,rettyp),stat')
                        (map E (fn_e :: args) @ es)
        end
      | CompLiteral (ty, dis) =>
          count_fncalls (process_type (eleft e, eright e) (ty,env),
                         fmap, adstat)
                        (inits_to_elist E (InitList dis) es)
      | Arbitrary ty =>
          count_fncalls (process_type (eleft e, eright e) (ty,env),
                         fmap, adstat)
                        es
      | _ => raise eFail (e, "count_fncall: Can't handle expr type: "^
                             expr_string e)

  val (env', (counts, globalreads)) =
      count_fncalls (env, (TypeTab.empty, Binaryset.empty expr_compare),
                     if lvstate = LV then Lvalue else Rvalue)
                    [E e]
  fun foldthis (rettype,count) (acc : csenv) =
      if count <= 0 then acc
      else let
          val nm = embret_var_name (tyname rettype, count)
          val retvar =
              VI {name = MString.dest nm, munged_name = nm, vtype = rettype,
                  struct_env = senv, proto_param = false,
                  fname = SOME "", return_var = true, attrs = [],
                  declared_at = Region.bogus}
        in
          foldthis (rettype, count - 1) (#2 (insert_var(retvar, acc)))
        end
in
  (TypeTab.fold foldthis counts env', globalreads)
end

fun get_modified env e = let
  (* e is an lvalue expression on the left of an assignment.  Return the
     base modified var_info for e if something in the global memory might be
     changing *)
  datatype s = BrackLeft | Normal
  fun recurse state e =
      case enode e of
        Var (s,ref (SOME (ty, MungedVar {munge = mnm, ...}))) => let
          fun check vi = srcname vi = s andalso get_mname vi = mnm
        in
          case find_scoped_vdecl s (get_scope env) of
            NONE => raise Fail ("Munged Variable "^s^", "^MString.dest mnm^
                                " not in environment")
          | SOME (_, vi) => let
              val isptr = case ty of Ptr _ => true | _ => false
            in
              if check vi then
                case (is_global vi, state = BrackLeft, isptr) of
                  (_, true, true) => SOME TheHeap
                | (true, _, _) => SOME (M vi)
                | _ => NONE
              else raise Fail ("Munged Variable "^s^", "^MString.dest mnm^
                               " not in environment")
            end
        end
      | Var (s, ref NONE) => let
          open Region
          val msg = toString (make {left = eleft e, right = eright e}) ^
                    "no info attached for variable " ^ s
        in
          raise Fail msg
        end
      | Var _ => NONE
      | StructDot (e', _) => let
        in
          case cse_typing env e of
            Ptr _ => if state = BrackLeft then SOME TheHeap
                     else recurse state e'
          | _ => recurse state e'
        end
      | ArrayDeref (e', _) => recurse BrackLeft e'
      | Deref _ => SOME TheHeap
      | _ => NONE
in
  recurse Normal e
end

(* ignore the global reads performed by the initializer *)
fun process_initializer fname (env : csenv) (i : initializer) : csenv =
    List.foldl (fn (ex, env) => #1 (process_expr RV fname env ex))
               env
               (inits_to_elist I i [])



fun fold_pipe (f : 'env -> 'a -> 'b * 'env) (env0 : 'env) (items : 'a list) =
    let
      fun foldthis (i, (acc, env)) = let
        val (i', env') = f env i
      in
        (i'::acc, env')
      end
      val (items0, env') = List.foldl foldthis ([], env0) items
    in
      (List.rev items0, env')
    end


(* fname is a string option : NONE corresponds to a declaration at the global
   level *)
fun process_decl fname (d:declaration wrap) (e as CSE {senv,...}) = let
  val ecenv = cse2ecenv e
  fun puredecl d = {decl = d, localinits = [], globalinits = []}
in
  case node d of
    VarDecl (ty,s,storage_specs,iopt,attrs) => let
      val s = if node s = phantom_state_name then
                (Feedback.errorStr'
                     (left s, right s,
                      "Not allowed to use this as a variable name");
                 wrap(node s ^ "'", left s, right s))
              else s
      val str = node s
      val str = let
        val err =
            "You may not use \"" ^ str ^ "\" as a variable name; \
            \you might try turning on the \"allow_underscore_idents\"\n\
            \config variable to get around this error."
      in
        if get_allow_underscores e orelse check_uscore_ok str then str
        else (Feedback.errorStr'(left s, right s, err); str)
      end
      val is_extern = is_extern storage_specs
      val is_static = is_static storage_specs
      val _ = if is_static andalso is_extern then
                Feedback.errorStr'(left s, right s,
                                   "Var can't be declared static *and* extern")
              else ()
      val _ = if is_extern andalso isSome fname andalso isSome iopt then
                Feedback.errorStr'(left s, right s,
                                   "Can't initialise block-local extern")
              else ()
      val fname = if is_extern then NONE else fname

      val ty = fparam_norm ty
      val ty =
          (* calculate the size of an initialised incomplete array *)
          case ty of
            Array(elty, NONE) => let
            in
              case iopt of
                NONE => let
                in
                  case fname of
                    SOME fnm => if not is_extern then
                                  raise Fail ("Array "^str^" in function "^fnm^
                                              " must be given a size or an \
                                              \initialiser")
                                else ty
                  | NONE => ty
                end
              | SOME (InitE _) =>
                  raise Fail ("Array "^str^" initialised with non-constant "^
                              "expression")
              | SOME (InitList ilist) => let
                  val sz = complit.find_ilist_size ecenv ilist
                  val _ = if sz = 0 then
                            raise Fail "Array given empty initializer"
                          else ()
                in
                  Array(elty, SOME (expr_int (IntInf.fromInt sz)))
                end
            end
          | _ => ty
      val e = process_type (left d, right d) (ty, e)
      val vty = constify_abtype ecenv ty

      val (fname, munged_name) =
          if is_static andalso isSome fname then
            (NONE, mk_localstatic {fname = valOf fname, vname = str})
          else (fname, MString.mk str)

      val vi = VI {name = str, vtype = vty, attrs = attrs,
                   munged_name = munged_name, struct_env = senv,
                   proto_param = false,
                   fname = fname, return_var = false,
                   declared_at = Region.make{left = left s, right = right s}}
      val (vi, e) = insert_var (vi, e)
      (* inserting vi may force further munging if the name is already being
         used at a different type *)
      val munged_name = get_mname vi
      val bogus = SourcePos.bogus
      val mvinfo = MungedVar {munge = munged_name,
                              owned_by = StmtDecl.get_owned_by attrs}
      val var_e = ewrap(Var (str, ref (SOME (vty, mvinfo))), left s, right s)
      val (inits, proc_expr_opt, e) =
          case iopt of
            NONE => let
            in
              case fname of
                NONE => ([], NONE, e)
              | SOME _ => ([swrap(LocalInit var_e, left s, right s)],
                           NONE,
                           e)
            end
          | SOME (InitE exp) => let
              fun w s0 = swrap (s0, left s, eright exp)
            in
              case enode exp of
                EFnCall(e_fn,args) => let
                  val called =
                      case (enode e_fn, cse_typing e e_fn) of
                        (Var(s, _), Function _) => DirectCall s
                      | (_, ty) => let
                          val fty = case ty of
                                      Ptr (Function x) => x
                                    | Function x => x
                                    | _ => raise eFail (e_fn,
                                                        "Function designator\
                                                        \has bad type ("^
                                                        tyname ty^")")
                        in
                          FnPtrCall fty
                        end
                  val e = new_call{caller = fname_str fname, callee = called} e
                  val () = case fname of
                            NONE =>
                              raise eFail (exp, "Can't initialise a global with a \
                                                \function call")
                          | SOME _ => ()
                in
                  ([w (AssignFnCall(SOME var_e, e_fn, args))],
                   case args of
                     [] => NONE
                   | h :: t => let
                       fun foldthis (e,acc) = ebogwrap(BinOp(Plus,e,acc))
                     in
                       SOME (List.foldl foldthis h t)
                     end,
                   e)
                end
              | _ => let
                  val e = case fname of
                            NONE => cse_fupdglobinits (MSymTab.update (munged_name, exp)) e
                          | _ => e
                in
                  ([w (Assign(var_e, exp))], SOME exp, e)
                end
            end
          | SOME (InitList ilist) => let
              fun w s0 = swrap (s0, left s, bogus)
              val exp = ewrap(CompLiteral(ty, ilist), bogus, bogus)
              val e =
                  case fname of
                    NONE => cse_fupdglobinits (MSymTab.update (munged_name, exp)) e
                  | _ => e
            in
              ([w (Assign(var_e, exp))], SOME exp, e)
            end
      val d' = wrap(VarDecl(ty,s,storage_specs,NONE,attrs), left d, right d)
      val e =
          case proc_expr_opt of
              NONE => e
            | SOME exp => #1 (process_expr RV fname e exp)
                          (* ignore global reads done by initialiser *)
      val (globalinits, localinits) =
          case fname of
              NONE => (inits, [])
            | SOME _ => ([], inits)
    in
      ({decl = d', localinits = localinits, globalinits = globalinits}, e)
    end
  | StructDecl s => (puredecl d, newstr_decl s e)
  | TypeDecl _ => raise Fail "collect_vars: TypeDecl unexpected, \
                             \translate these out!"
  | ExtFnDecl {rettype = rettype0,name = fname0,params,specs,...} => let
      val _ = if get_allow_underscores e orelse check_uscore_ok (node fname0)
              then ()
              else Feedback.errorStr'(left fname0, right fname0,
                                      rmUScoreSafety (node fname0) ^
                                      " is an illegal name for a function")
      val e = List.foldl (process_type (left d, right d))
                         e
                         (rettype0 :: map #1 params)
      val rettype = fparam_norm (constify_abtype ecenv rettype0)
      val fname = node fname0
      val e = insert_fnretty (fname0, rettype, e)
      val ret_vname = return_var_name rettype
      fun do_ret e =
          if rettype = Void then e
          else let
              val retvar = VI {name = MString.dest ret_vname,
                               munged_name = ret_vname,
                               vtype = rettype, proto_param = false,
                               struct_env = senv,
                               fname = SOME fname, return_var = true,
                               attrs = [], declared_at = Region.bogus}
            in
              #2 (insert_var (retvar, e))
            end
      fun to_vi (i, (ty,pnameopt)) (acc, e) = let
        val name = case pnameopt of
                     NONE => fake_param fname i
                   | SOME s => s
        val var =
            VI {name = name, vtype = param_norm (constify_abtype ecenv ty),
                munged_name = MString.mk name, attrs = [],
                struct_env = senv, proto_param = true,
                fname = SOME fname, return_var = false,
                declared_at = Region.bogus}
        val (var',e') = insert_var (var, e)
      in
        (var'::acc, e')
      end
      val paramtypes = map (param_norm o constify_abtype ecenv o #1) params
      val ftype = Function(rettype, paramtypes)
      val fvi = VI {name = fname, vtype = ftype, munged_name = MString.mk fname,
                    proto_param = false, struct_env = senv,
                    fname = NONE, return_var = false, attrs = [],
                    declared_at = Region.Wrap.region d}
      val (_, e) = insert_var (fvi, e)
      val e = do_ret (new_scope e)
      val (pm_vis0, e) = fold_index to_vi params ([], e)
      val e = (* check for modifies assertions *)
          case List.find (fn fn_modifies _ => true | _ => false) specs of
            NONE => e
          | SOME (fn_modifies slist) => let
              fun doit (varname, e) =
                  case Symtab.lookup (get_vars e) varname of
                    NONE => let
                    in
                      if varname = phantom_state_name then
                        add_modification fname PhantomState e
                      else if varname = ghost_state_name then
                        add_modification fname GhostState e
                      else
                        (Feedback.errorStr'(left fname0, right fname0,
                                            "MODIFIES spec for function "^fname^
                                            " mentions non-existent variable "^
                                            varname);
                         e)
                    end
                  | SOME vis => let
                    in
                      case List.find is_global vis of
                        NONE =>
                        (Feedback.errorStr'(left fname0, right fname0,
                                            "MODIFIES spec for function "^fname^
                                            " mentions non-global variable "^
                                            varname); e)
                      | SOME vi => add_modification fname (M vi) e
                    end
            in
              if null slist then
                cse_fupdmodifies
                    (Symtab.update (fname, Binaryset.empty mvar_compare))
                    e
              else List.foldl doit e slist
            end
          | SOME _ => e (* can't happen, but here to squish compiler warning *)
      val e = (* add fnspecs *) let
        fun U s1 s2 = merge_specs s1 s2
      in
        cse_fupdfnspecs (Symtab.map_default (fname, []) (U specs)) e
      end
      val e = update_hpfninfo (Decl d) e
    in
      (puredecl d, pop_scope (set_proto_params fname (List.rev pm_vis0) e))
    end
  | EnumDecl eninfo => (puredecl d, process_enumdecl eninfo e)
end

type asm_stmt_elements = (string * bool * expr option * expr list)

fun split_asm_stmt (AsmStmt dets) = let
  open Feedback
  val rets = #mod1 (#asmblock dets)
  fun str_so NONE = "NONE" | str_so (SOME s) = "SOME (" ^ s ^ ")"
  fun str_trio (so, s, _) = "(" ^ str_so so ^ ", " ^ s ^ ")"
  val _ = List.app (K () o (fn (so, s, ex) =>
    (so = NONE andalso (s = "=r" orelse s = "=&r"))
    orelse raise Fail ("Can not handle asm lval specifier: "
            ^ str_trio (so, s, ex)))) rets
  fun str_trios [] = ""
    | str_trios [tr] = str_trio tr
    | str_trios (tr :: trs) = str_trio tr ^ ", " ^ str_trios trs
  val _ = K () (length rets <= 1
    orelse raise Fail ("Can not handle multiple asm lval specifiers: ["
            ^ str_trios rets ^ "]"))
  val ret = case rets of [] => NONE | [(_, _, r)] => SOME r
    | _ => NONE
  val args = #mod2 (#asmblock dets)
  val _ = List.app (K () o (fn (so, s, ex) => (so = NONE andalso s = "r")
    orelse raise Fail ("Can not handle asm rval specifier: "
            ^ str_trio (so, s, ex)))) args
  val args = map #3 args
in
  (#head (#asmblock dets), #volatilep dets, ret, args)
end
  | split_asm_stmt st = raise Fail
    ("split_asm_stmt: " ^ stmt_type (sbogwrap st))

fun merge_asm_stmt (nm, vol, ret, args) = let
in
  AsmStmt {volatilep = vol, asmblock = {head = nm,
    mod1 = (case ret of NONE => [] | SOME expr => [(NONE, "=r", expr)]),
    mod2 = map (fn expr => (NONE, "r", expr)) args,
    mod3 = []}}
end

fun treat_as_emb_fcall env (NONE,fn_e,args) = false
  | treat_as_emb_fcall env (SOME lv,fn_e,args) = let
    val (callee, (rettyp, _)) = fndes_callinfo env fn_e
    val lvtyp = cse_typing env lv
    val lv_plain = case enode lv of Var _ => true | _ => false
  in not lv_plain orelse lvtyp <> rettyp end

fun process_blockitem fname e bi = let
in
  case bi of
    BI_Stmt s => apfst (map BI_Stmt) (process_stmt fname e s)
  | BI_Decl d =>
    let
      val ({decl,localinits,globalinits}, e') = process_decl (SOME fname) d e
    in
      (* throw away globalinits for the moment *)
      (BI_Decl decl :: map BI_Stmt localinits, e')
    end
end
and process_stmt fname e (stmt : statement) = let
  fun pex e exp = process_expr RV (SOME fname) e exp
  fun pexlv e exp = process_expr LV (SOME fname) e exp
  fun pst e st = process_stmt fname e st
  fun pbil e blist = process_blockitems fname e blist
  fun w s0 = swrap(s0, sleft stmt, sright stmt)
  val retty = get_rettype fname e
  fun lift_stmts stmts =
      case stmts of
          [] => w EmptyStmt
        | [s] => s
        | _ => w(Block (map BI_Stmt stmts))
  val owners = get_owners e
  val mk_chaos_stmts =
      if null owners then fn _ => []
      else
        fn grs =>
           let
             fun foldthis (e, acc) =
                 case enode e of
                     Var(nm, ref (SOME (_, MungedVar {owned_by = NONE,...}))) =>
                     (Feedback.informStr'(5, sleft stmt, sright stmt,
                                          "Found that "^nm^" is not owned.");
                      w (Chaos e) :: acc)
                   | _ => acc
           in
             Binaryset.foldl foldthis [] grs
           end
  fun prechaos grs stmts = mk_chaos_stmts grs @ stmts
in
  case snode stmt of
    While(g, i, s) => let
      val (e,grs) = pex e g
      val cstmts = mk_chaos_stmts grs
      val (s', e) = pst e s
    in
      (cstmts @ [w (While(g,i,lift_stmts (s' @ cstmts)))], e)
    end
  | Trap(traptype, s) => let
      val (s',e) = pst e s
    in
      ([w (Trap(traptype, lift_stmts s'))], e)
    end
  | IfStmt(g,s1,s2) => let
      val (e, grs) = pex e g
      val (s1',e) = pst e s1
      val (s2',e) = pst e s2
    in
      (prechaos grs [w (IfStmt(g,lift_stmts s1',lift_stmts s2'))], e)
    end
  | Block b =>
      apfst (single o w o Block) (apsnd pop_scope (pbil (new_scope e) b))
  | Chaos lv_expr =>
    let
      val (e,grs) = pexlv e lv_expr
      val modified = get_modified e lv_expr
      val e =
          case modified of
              NONE => e
            | SOME m => add_modification fname m e
    in
      (prechaos grs [stmt], e)
    end
  | Switch(g,cases) => let
      (* deal with guard *)
      val (e, grs) = apfst new_scope (pex e g)
      fun label_fold (NONE, env) = env
        | label_fold (SOME exp, env) = #1 (pex env exp)
            (* should be no global reads in a case label *)
      fun one_case e (eoptlist, bis) = let
        val e = List.foldl label_fold e eoptlist
      in
        apfst (fn y => (eoptlist,y)) (pbil e bis)
      end
    in
      apfst (fn cs => prechaos grs [w (Switch(g,cs))])
            (apsnd pop_scope (fold_pipe one_case e cases))
    end
  | Assign(e1,e2) =>
    let
      val (e, grs1) = pexlv e e1
      val (e, grs2) = pex e e2
      val grs = Binaryset.union(grs1,grs2)
      val modified = get_modified e e1
      val e =
          case modified of
            NONE => e
          | SOME m => add_modification fname m e
    in
      (prechaos grs [stmt], e)
    end
  | AssignFnCall(eopt,fn_e,args) => if treat_as_emb_fcall e (eopt,fn_e,args)
    then let
      val lv = case eopt of SOME lv => lv
        | NONE => raise Fail "Trying to embed fcall without lval."
    in pst e (w (Assign(lv,ebogwrap (EFnCall(fn_e,args))))) end
    else let
      val (callee, _) = fndes_callinfo e fn_e
      (* the arguments need to be considered as being part of one big
         expression (rather than independently) in order for the
         embedded function call analysis to work, so we create one fake
         expression embodying them all to be analysed by pex *)
      val e = new_call {caller = fname, callee = callee} e
      val (e,grs1) =
          case eopt of
              NONE => (e,Binaryset.empty expr_compare)
            | SOME exp => let
                  val (e,grs) = pexlv e exp
                in
                  case get_modified e exp of
                    NONE => (e,grs)
                  | SOME m => (add_modification fname m e, grs)
                end
      val (e,grs2) = pex e (foldl (fn (a,exp) => ebogwrap (BinOp(Plus,a,exp)))
                                  fn_e
                                  args)
      val grs = Binaryset.union(grs1,grs2)
    in
      (prechaos grs [stmt], e)
    end
  | Return NONE => let
    in
      case retty of
        NONE => ([stmt], e) (* probably really an error *)
      | SOME Void => ([stmt], e)
      | _ => raise stmt_fail (stmt, "Null-return in function with return-type")
    end
  | Return (SOME ex) => let
    in
      case retty of
        NONE => raise stmt_fail (stmt, "Returning a value in a void function")
      | SOME ty => let
          val etyp = cse_typing e ex
        in
          if ExpressionTyping.assignment_compatible (ty, etyp, ex) then
            let
              val (e,grs) = pex e ex
            in
              (prechaos grs [stmt], e)
            end
          else
            raise stmt_fail (stmt,
                             "Type of returned expression ("^tyname etyp^
                             ") incompatible with that of containing function ("^
                             tyname ty^")")
        end
    end
  | ReturnFnCall(fn_e, args) => let
      val (callee, _) = fndes_callinfo e fn_e
      val e = new_call {caller = fname, callee = callee} e
      val (e,grs) = pex e (foldl (fn (e,acc) => ebogwrap(BinOp(Plus,e,acc)))
                                 fn_e
                                 args)
    in
      (prechaos grs [stmt], e)
    end
  | AsmStmt {asmblock = {mod1,mod2,...}, ...} =>
    let
      fun handle_mod ((_,_,exp) : namedstringexp, (e0, grs0)) =
        let
          val (e,newgrs) = pex e0 exp
        in
          (e,Binaryset.union(newgrs,grs0))
        end
      val (e,grs) = List.foldl handle_mod (e, Binaryset.empty expr_compare) mod1
      val (e,grs) = List.foldl handle_mod (e, grs) mod2
    in
      (prechaos grs [stmt],
       fold (add_modification fname) [TheHeap, PhantomState, AllGlobals] e)
    end
  | Ghostupd _ => ([stmt], add_modification fname GhostState e)
  | _ => ([stmt], e)
end
and process_blockitems (fname : string) (env : csenv) bis =
    apfst List.concat (fold_pipe (process_blockitem fname) env bis)

fun delete_earlier_fvars fname env = let
  fun vitest (VI vinfo) =
      #fname vinfo <> SOME fname orelse
      #return_var vinfo
  fun allvars_upd (vname,vlist) newtab =
      case List.filter vitest vlist of
        [] => newtab
      | x => Symtab.update (vname, x) newtab
  fun scope_upd (vname, vi) newtab =
      if vitest vi then Symtab.update (vname, vi) newtab
      else newtab
  fun allvarupd tab = Symtab.fold allvars_upd tab Symtab.empty
  val scopes_upd = map (fn tab => Symtab.fold scope_upd tab Symtab.empty)
in
  (cse_fupdscope scopes_upd o cse_fupdvars allvarupd) env
end

fun split_decls (ds, is) bis =
    case bis of
      [] => (List.rev ds, List.rev is)
    | BI_Stmt s :: rest => split_decls (ds, s :: is) rest
    | BI_Decl d :: rest => split_decls (Decl d :: ds, is) rest


fun process_one_extdecl (env0 : csenv) edec =
    case edec of
      Decl d => let
        val ({decl, localinits, globalinits}, e) = process_decl NONE d env0
      in
        (([Decl decl], globalinits), e)
      end
    | FnDefn((rettype0, s), params, specs, body) => let
        val _ =
            if get_allow_underscores env0 orelse check_uscore_ok (node s) then ()
                else Feedback.errorStr'(left s, right s,
                                        rmUScoreSafety (node s) ^
                                        " is an illegal name for a function")
        val _ =
            case get_modifies env0 (node s) of
              NONE => ()
            | SOME _ => Feedback.warnStr'
                            (left s, right s,
                             "Ignoring previous MODIFIES spec for function "^
                             node s)
        val ecenv = cse2ecenv env0
        val rettype = fparam_norm (constify_abtype ecenv rettype0)
        val fname = SOME (node s)
        val senv = get_senv env0
        val env = delete_earlier_fvars (node s)
                                       (insert_fnretty (s,rettype, env0))
        val env = new_defined_fn s env
        val rv_nm = return_var_name rettype
        val retvar =
            VI {name = MString.dest rv_nm, munged_name = rv_nm, attrs = [],
                vtype = rettype, proto_param = false,
                struct_env = senv,
                fname = SOME (node s), return_var = true,
                declared_at = Region.bogus}
        val paramtypes = map (param_norm o constify_abtype ecenv o #1) params
        val ftype = Function(rettype, paramtypes)
        val fvi = VI {name = node s, vtype = ftype,
                      munged_name = MString.mk (node s),
                      proto_param = false, struct_env = senv,
                      fname = NONE, return_var = false, attrs = [],
                      declared_at = Region.Wrap.region s}
        val (_, env) = insert_var(fvi,env)
        fun to_vi (ty,pname) =
            VI{name = node pname,
               munged_name = MString.mk (node pname),
               attrs = [],
               vtype = param_norm (constify_abtype ecenv ty),
               struct_env = senv, proto_param = false,
               fname = fname, return_var = false,
               declared_at =
                 Region.make{left = left pname, right = right pname}}
        val env = new_scope env (* new scope for parameters and body *)
        val (params0,env) = let
          fun foldthis (p,(accps,env)) = let
            val (vi,env) = insert_var (to_vi p, env)
          in
            (vi::accps, env)
          end
        in
          List.foldl foldthis ([], env) params
        end
        val env = set_defn_params (node s) (List.rev params0) env
        val env = if rettype <> Void then #2 (insert_var (retvar, env))
                  else env
        val (body0, env) = process_blockitems (node s) env (node body)
        val body' = wrap (body0, left body, right body)
        val env = (* add fnspecs *) let
          val U = merge_specs
        in
          cse_fupdfnspecs (Symtab.map_default (node s, []) (U specs)) env
        end
        val env = pop_scope env
      in
        (([FnDefn((rettype0, s), params, specs, body')], []), env)
      end

fun compute_callgraphs env = let
  val funs_by_type = let
    fun foldthis (fname, (retty, _, args)) tytab = let
      val ty_key = (retty, map get_vi_type args)
    in
      TypesTab.map_default (ty_key, Binaryset.empty String.compare)
                           (fn s => Binaryset.add(s, fname))
                           tytab
    end
  in
    Symtab.fold foldthis (get_fninfo env) TypesTab.empty
  end
  val (callgraph, converse) = let
    fun setfoldthis caller (fncall, acc) =
        case fncall of
          DirectCall nm => Binaryset.add(acc, nm)
        | FnPtrCall fty => let
            val potential_callees =
                case TypesTab.lookup funs_by_type fty of
                  NONE => (Feedback.informStr(1, "Function "^caller^
                                                 " makes fnptr call to a \
                                                 \function type\nthat isn't in \
                                                 \the sources");
                           Binaryset.empty String.compare)
                | SOME s => s
          in
            Binaryset.union(acc, potential_callees)
          end
    fun foldthis (fname, called) (callgraph,converse) = let
      val called' = Binaryset.foldl (setfoldthis fname)
                                    (Binaryset.empty String.compare)
                                    called
      val cg' = Symtab.update (fname, called') callgraph
      fun setfold (callee, acc) =
          Symtab.map_default (callee, Binaryset.empty String.compare)
                             (fn s => Binaryset.add(s, fname))
                             acc
      val conv' = Binaryset.foldl setfold converse called'
    in
      (cg',conv')
    end
  in
    Symtab.fold foldthis (get_callgraph env) (Symtab.empty, Symtab.empty)
  end
in
  {callgraph = callgraph, callers = converse}
end

fun mvar_traverse env = let
  val fnames = get_functions env
  val defined_fns = Symtab.keys (get_defined_functions env)
  val empty_sset = Binaryset.empty String.compare
  val empty_mvset = Binaryset.empty mvar_compare
  (* first set all modifies entries for defined functions to be the empty set
     (if they don't already have a value) *)
  val env = let
    fun foldthis (f, tab) = Symtab.map_default (f, empty_mvset) I tab
    fun updtab tab = List.foldl foldthis tab defined_fns
  in
    (cse_fupdmodifies updtab o cse_fupdread_globals updtab) env
  end
  fun mv_munge mvi =
      case mvi of
        M vi => let
        in
          case MSymTab.lookup (get_addressed env) (get_mname vi) of
            NONE => mvi
          | SOME _ => TheHeap
        end
      | _ => mvi

  fun map_mungeset _ set = let
    fun foldthis (mvi, set) = Binaryset.add(set, mv_munge mvi)
  in
    Binaryset.foldl foldthis empty_mvset set
  end
  val env = (cse_fupdmodifies (Symtab.map map_mungeset) o
             cse_fupdread_globals (Symtab.map map_mungeset)) env

  fun lift f fnm = case Symtab.lookup f fnm of
                     NONE => []
                   | SOME s => Binaryset.listItems s
  val {callgraph,callers = converse} = compute_callgraphs env

  val sorted = Topo_Sort.topo_sort {cmp = String.compare,
                                    graph = lift callgraph,
                                    converse = lift converse}
                                   fnames
  nonfix union
  fun process (fnlist, env) =
      case fnlist of
        [] => raise Fail "topological sort produced empty component??"
      | [x] => let
          val callees = lift callgraph x
          val env = if member (op =) callees x then mk_recursive x env else env
          fun do_callees (callees, acc) =
              case callees of
                [] => acc
              | c::cs => let
                  fun union s1 s2 = Binaryset.union (s1, s2)
                in
                  case get_modifies acc c of
                    NONE => acc |> cse_fupdmodifies (Symtab.delete_safe x)
                                |> cse_fupdread_globals (Symtab.delete_safe x)
                  | SOME modset => let
                      fun upd set = Symtab.map_entry x (union set)
                      val acc = cse_fupdmodifies (upd modset) acc
                      val reads_db = get_read_globals acc
                    in
                      case Symtab.lookup reads_db c of
                        NONE => let
                          val fspecs =
                              valOf (Symtab.lookup (function_specs env) c)
                              handle Option => []
                          val acc =
                              if isSome
                                 (Absyn.has_IDattribute (fn s => s = "noreturn")
                                                        fspecs)
                              then acc
                              else
                                cse_fupdread_globals (Symtab.delete_safe x) acc
                        in
                          do_callees (cs, acc)
                        end
                      | SOME rset => let
                          val acc = cse_fupdread_globals (upd rset) acc
                        in
                          do_callees (cs, acc)
                        end
                    end
                end
        in
          case get_modifies env x of
            NONE => env
          | SOME _ => do_callees (callees, env)
        end
      | _ => let
          (* we know that these functions form a strongly connected component
             in the call graph, so each will have modifies data. *)
          open Binaryset
          val all_callees = let  (* will include elements of fnlist *)
            fun foldthis (nm, acc) =
                case Symtab.lookup callgraph nm of
                  NONE => acc
                | SOME set => union (acc, set)
          in
            List.foldl foldthis empty_sset fnlist
          end
          val read_db = get_read_globals env
          fun do_callees (callees, acc as (mods,reads)) =
              case callees of
                [] => acc
              | c::cs => let
                  fun updmods ms =
                      case get_modifies env c of
                        NONE => NONE
                      | SOME modset => SOME (union (ms, modset))
                  fun updreads rs =
                      case Symtab.lookup read_db c of
                        NONE => let
                          val fspecs =
                              valOf (Symtab.lookup (function_specs env) c)
                              handle Option => []
                        in
                          if isSome
                                 (Absyn.has_IDattribute (fn s => s = "noreturn")
                                                        fspecs)
                          then
                            SOME rs
                          else NONE
                        end
                      | SOME rset => SOME (union (rs, rset))
                  fun omj _ NONE = NONE
                    | omj f (SOME x) = (case f x of NONE => NONE | y => y)
                  val acc = (omj updmods mods, omj updreads reads)
                in
                  do_callees (cs, acc)
                end
          val (ms,rs) = do_callees (listItems all_callees,
                                    (SOME empty_mvset, SOME empty_mvset))
          fun del f csemod = csemod (Symtab.delete f)
          fun ins f csemod s = csemod (Symtab.update (f,s))
          fun update_at f cmod setopt =
              case setopt of
                NONE => del f cmod
              | SOME s => ins f cmod s
          fun foldthis (f,env) =
              env |> mk_recursive f
                  |> update_at f cse_fupdmodifies ms
                  |> update_at f cse_fupdread_globals rs
        in
          List.foldl foldthis env fnlist
        end
in
  List.foldl process env sorted
end

fun mvar_finalise env = let
    open Binaryset
    val (CSE {modifies, ...}) = env
    val un = Binaryset.union

    fun mk xs = addList (empty mvar_compare, xs)

    val addressed = get_addressed_vis env
        |> map M |> mk

    val all_modified = get_modified_global_locns env
        |> MVar_Table.dest
        |> List.filter (fn (_, mset) => not (isEmpty mset))
        |> map (fn (m, _) => m)
        |> List.filter (fn M v => true | _ => false)
        |> mk

    val mod_not_addr = difference (all_modified, addressed)

    fun upd modif = if member (modif, AllGlobals)
      then delete (un (mod_not_addr, modif), AllGlobals)
      else modif
  in
    cse_fupdmodifies (Symtab.map (K upd)) env
  end

fun process_decls cfg (p : program) = let
  fun recurse (ds, is) (env, edecs) =
      case edecs of
        [] => ((List.rev ds, List.rev is), env)
      | e :: es => let
          val ((ds0, is0), env') = process_one_extdecl env e
        in
          recurse (List.revAppend(ds0,ds), List.revAppend(is0, is)) (env', es)
        end
  val (i, env) = recurse ([], []) (emptycse cfg, p)
in
  (i, mvar_finalise (mvar_traverse env))
end

fun get_globals_rcd cse =
let
  val advis = get_addressed_vis cse
in
  if null advis then []
  else
    [(adglob_rcd_tyname, map (fn vi => (srcname vi, get_vi_type vi)) advis)]
end

fun export_mungedb (c as CSE cse) =
  case #munge_info_fname cse of
    NONE => ()
  | SOME fname =>
    let
      val outstrm = TextIO.openOut fname
      fun tab_foldthis (vinfo,acc) =
        let
          val srcnm = srcname vinfo
          val mnm = get_mname vinfo
          val fopt = get_vi_fname vinfo
        in
          ((case fopt of NONE => "" | SOME f => f) ^ "::" ^ srcnm ^ " -> " ^
           MString.dest mnm ^ "\n") :: acc
        end
      fun foldthis (_, vinfos) acc = List.foldl tab_foldthis acc vinfos
      fun recurse tab = Symtab.fold foldthis tab []
      val data0 = recurse (get_vars c)
      val data = Library.sort String.compare data0
    in
      List.app (fn s => TextIO.output(outstrm, s)) data;
      TextIO.closeOut outstrm
    end

end (* struct *)

(* Local variables: *)
(* mode: sml *)
(* End: *)
