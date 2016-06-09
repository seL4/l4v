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
 * Information about functions in the program we are translating,
 * and the call-graph between them.
 * To support incremental translation, we store the function information
 * for every intermediate phase as well.
 *)
signature FUNCTION_INFO =
sig
  (*** Basic data types ***)
  type fn_info;
  datatype phase = CP | L1 | L2 | HL | WA | TS;
  val string_of_phase : phase -> string;
  val phase_ord : phase * phase -> order;
  structure Phasetab : TABLE;

  (* Function info for a single phase. *)
  type phase_info = {
    phase : phase,
    args : (string * typ) list,
    return_type : typ,
    const : term,
    raw_const : term,
(*
    callees : string list,
    rec_callees : string list,
*)
    definition : thm,
    mono_thm : thm option
  };
  val phase_info_upd_phase       : phase               -> phase_info -> phase_info;
  val phase_info_upd_args        : (string * typ) list -> phase_info -> phase_info;
  val phase_info_upd_return_type : typ                 -> phase_info -> phase_info;
  (* also updates raw_const *)
  val phase_info_upd_const       : term                -> phase_info -> phase_info;
(*
  val phase_info_upd_callees     : string list         -> phase_info -> phase_info;
  val phase_info_upd_rec_callees : string list         -> phase_info -> phase_info;
*)
  val phase_info_upd_definition  : thm                 -> phase_info -> phase_info;
  val phase_info_upd_mono_thm    : thm option          -> phase_info -> phase_info;

  (* Function info for a single function. *)
  type function_info = {
    name : string,
    invented_body : bool,
    is_simpl_wrapper : bool,
    phases : phase_info Phasetab.table
  };
  val function_info_upd_name             : string -> function_info -> function_info;
  val function_info_upd_invented_body    : bool   -> function_info -> function_info;
  val function_info_upd_is_simpl_wrapper : bool   -> function_info -> function_info;
  val function_info_add_phase            : phase_info -> function_info -> function_info;

  (*** Whole-program info ***)
  val init_fn_info : Proof.context -> string -> fn_info;

  (*** fn_info accesses ***)
  val get_all_functions : fn_info -> function_info Symtab.table;
  val get_function_info : fn_info -> string -> function_info;
  val get_phase_info : fn_info -> phase -> string -> phase_info;
  val get_1_phase_info : function_info -> phase -> phase_info;
  val get_function_from_const : fn_info -> term -> function_info option;

  val get_function_callees : fn_info -> string -> string list;
  val get_topo_sorted_functions : fn_info -> string list list;

  val is_function_recursive : fn_info -> string -> bool;
  val get_recursive_group : fn_info -> string -> string list;
  val get_recursive_functions : fn_info -> string list;

  (*** fn_info updaters. These automatically recalculate auxillary info ***)
  (* Add info from a translation phase. NONE = leave untouched *)
  val add_phases : (string -> function_info -> phase_info option) -> fn_info -> fn_info;
  (* Translate function infos. NONE = forget function *)
  val map_fn_info : (function_info -> function_info option) -> fn_info -> fn_info;
end;

structure FunctionInfo : FUNCTION_INFO =
struct

(* List of AutoCorres phases.
 * "CP" represents the initial definition we get from the C parser. *)
datatype phase = CP | L1 | L2 | HL | WA | TS;
fun string_of_phase CP = "CP"
  | string_of_phase L1 = "L1"
  | string_of_phase L2 = "L2"
  | string_of_phase HL = "HL"
  | string_of_phase WA = "WA"
  | string_of_phase TS = "TS";
fun encode_phase CP = 0
  | encode_phase L1 = 1
  | encode_phase L2 = 2
  | encode_phase HL = 3
  | encode_phase WA = 4
  | encode_phase TS = 5;
val phase_ord = int_ord o apply2 encode_phase;
structure Phasetab = Table(
  type key = phase
  val ord = phase_ord);

type phase_info = {
    (* The translation phase for this definition. *)
    phase : phase,

    (* Arguments of the function, in order, excluding measure variables. *)
    args : (string * typ) list,

    (* Return type of the function ("unit" is used for void). *)
    return_type : typ,

    (* Constant for the function, which can be inserted as a call to the
     * function. Unlike "raw_const", this includes any locale parameters
     * required by the function. *)
    const: term,

    (* Raw constant for the function. Existence of this constant in another
     * function's body indicates that that function calls this one. *)
    raw_const: term,

    (* Definition of the function. *)
    definition : thm,

    (* monad_mono theorem for the function, if it is recursive. *)
    mono_thm : thm option
};

type function_info = {
    (* Name of the function. *)
    name : string,

    (* Is this function actually being translated, or are we just wrapping the SIMPL code? *)
    is_simpl_wrapper : bool,

    (* Is this function generated by AutoCorres as a placeholder for
     * a function we didn't have the source code to? *)
    invented_body : bool,

    (* All versions of the function that we have generated so far. *)
    phases : phase_info Phasetab.table
};

(* FunctionalRecordUpdate instances *)
open FunctionalRecordUpdate;
local
  fun from args return_type const raw_const definition mono_thm phase =
    { args = args,
      return_type = return_type,
      const = const,
      raw_const = raw_const,
      definition = definition,
      mono_thm = mono_thm,
      phase = phase };
  fun from' phase mono_thm definition raw_const const return_type args =
    { args = args,
      return_type = return_type,
      const = const,
      raw_const = raw_const,
      definition = definition,
      mono_thm = mono_thm,
      phase = phase };
  fun to f { args,
             return_type,
             const,
             raw_const,
             definition,
             mono_thm,
             phase } =
        f args return_type const raw_const definition mono_thm phase;
  fun update x = makeUpdate7 (from, from', to) x;
in
  fun phase_info_upd_args args pinfo = update pinfo (U#args args) $$;
  fun phase_info_upd_return_type return_type pinfo = update pinfo (U#return_type return_type) $$;
  fun phase_info_upd_definition definition pinfo = update pinfo (U#definition definition) $$;
  fun phase_info_upd_mono_thm mono_thm pinfo = update pinfo (U#mono_thm mono_thm) $$;
  fun phase_info_upd_phase phase pinfo = update pinfo (U#phase phase) $$;

  fun phase_info_upd_const_ const pinfo = update pinfo (U#const const) $$;
  fun phase_info_upd_raw_const_ raw_const pinfo = update pinfo (U#raw_const raw_const) $$;
  fun phase_info_upd_const t = phase_info_upd_const_ t o phase_info_upd_raw_const_ (head_of t);
end;

fun function_info_upd_name name finfo = {
  name = name,
  is_simpl_wrapper = #is_simpl_wrapper finfo,
  invented_body = #invented_body finfo,
  phases = #phases finfo };
fun function_info_upd_invented_body invented_body finfo = {
  name = #name finfo,
  is_simpl_wrapper = #is_simpl_wrapper finfo,
  invented_body = invented_body,
  phases = #phases finfo };
fun function_info_upd_is_simpl_wrapper is_simpl_wrapper finfo = {
  name = #name finfo,
  is_simpl_wrapper = is_simpl_wrapper,
  invented_body = #invented_body finfo,
  phases = #phases finfo };
fun function_info_add_phase phase finfo = {
  name = #name finfo,
  is_simpl_wrapper = #is_simpl_wrapper finfo,
  invented_body = #invented_body finfo,
  phases = Phasetab.update_new (#phase phase, phase) (#phases finfo) };


datatype fn_info = FunctionInfo of {
  (* Database of "function_info" records. *)
  function_info : function_info Symtab.table,

  (* Functions directly called by a particular function. *)
  function_callees : string list Symtab.table,

  (* Mapping from "const" back to the function name. (cache) *)
  const_to_function : string Termtab.table,

  (* Topologically sorted functions, based on call graph. (cache) *)
  topo_sorted_functions : string list list,

  (* List of recursive calls a function makes. (cache) *)
  recursive_functions : string list Symtab.table
  };

(*
 * Construct a "fn_info" from a dictionary of function names to "function_def"
 * records.
 *
 * We pre-calculate some information here to avoid having to
 * do it several times later.
 *)
fun precalc_function_info const_to_function fn_info_dict function_callees =
let
  (*
   * Get a topologically sorted list of functions, based on the call graph.
   *)
  val topo_sorted_functions = let
    (* Get callees and callers of each function, also adding an edge from each
     * function to itself. *)
    val fn_callees =
          function_callees
          |> Symtab.map (fn k => fn l => k :: l)
    val fn_callers = flip_symtab fn_callees
  in
    Topo_Sort.topo_sort {
      cmp = String.compare,
      graph = Symtab.lookup fn_callees #> the,
      converse = Symtab.lookup fn_callers #> the
    } (Symtab.keys fn_callees |> sort String.compare)
    |> map (sort String.compare)
  end

  (* Does a function call itself? *)
  fun is_self_recursive f =
    member (op =) (Symtab.lookup function_callees f |> the) f

  (* Get a dictionary of recursive functions. *)
  val recursive_functions = map (fn x =>
    let
      val in_recursive_group = length x > 1
    in
      if in_recursive_group orelse is_self_recursive (hd x) then
        (map (fn y => (y, x)) x)
      else
        ([(hd x, [])])
    end) topo_sorted_functions
    |> (fn x => fold (fn a => fn b => b @ a) x [])
    |> Symtab.make
in
  FunctionInfo {
    function_info = fn_info_dict,
    function_callees = function_callees,
    const_to_function = const_to_function,
    topo_sorted_functions = topo_sorted_functions,
    recursive_functions = recursive_functions
  }
end

fun mk_function_info (fn_info_dict : function_info Symtab.table) =
let
  (* Construct a dictionary from the constant names of a function to its name. *)
  val const_to_function =
    Symtab.dest fn_info_dict
    |> maps (fn (name, finfo) => Phasetab.dest (#phases finfo)
               |> map (fn (phase, pinfo) => (#raw_const pinfo, name)))
    (* If HL or WA are disabled, they reuse the L2 defs,
     * so we ignore duplicates with the same function name. *)
    |> sort_distinct (prod_ord Term_Ord.fast_term_ord fast_string_ord)
    |> Termtab.make

  (* Get a function's direct callees, based on the list of constants that appear
   * in its definition. *)
  fun get_direct_callees finfo =
  let
    val SOME (_, latest_phase) = Phasetab.max (#phases finfo);
    val body =
      #definition latest_phase
      |> Thm.concl_of
      |> Utils.rhs_of
  in
    (* Ignore the bodies of SIMPL wrappers. *)
    if #is_simpl_wrapper finfo then [] else
    Term.fold_aterms (fn t => fn a =>
          (Termtab.lookup const_to_function t
          |> Option.map single
          |> the_default []) @ a) body []
    |> distinct (op =)
  end
  val function_callees =
    fn_info_dict
    |> Symtab.dest
    |> map (apsnd get_direct_callees)
    |> Symtab.make
in precalc_function_info const_to_function fn_info_dict function_callees end


(* Generate a "function_info" from the C Parser's output. *)
fun init_fn_info ctxt filename =
let
  val thy = Proof_Context.theory_of ctxt
  val prog_info = ProgramInfo.get_prog_info ctxt filename
  val csenv = #csenv prog_info

  (* Get information about a single function. *)
  fun gen_fn_info name (return_ctype, _, carg_list) =
  let
    (* Convert C Parser return type into a HOL return type. *)
    val return_type =
      if return_ctype = Absyn.Void then
        @{typ unit}
      else
        CalculateState.ctype_to_typ (thy, return_ctype);

    (* Convert arguments into a list of (name, HOL type) pairs. *)
    val arg_list = map (fn v => (
        ProgramAnalysis.get_mname v |> MString.dest,
        CalculateState.ctype_to_typ (thy, ProgramAnalysis.get_vi_type v)
        )) carg_list

    (*
     * Get constant, type signature and definition of the function.
     *
     * The definition may not exist if the function is declared "extern", but
     * never defined. In this case, we replace the body of the function with
     * what amounts to a "fail" command. Any C body is a valid refinement of
     * this, allowing our abstraction to succeed.
     *)
    val const = Utils.get_term ctxt (name ^ "_'proc")
    val myvars_typ = #state_type prog_info
    val (definition, invented) =
        (Proof_Context.get_thms ctxt (name ^ "_body_def"), false)
        handle ERROR _ =>
          ([Thm.instantiate ([((("'a", 0), ["HOL.type"]), Thm.ctyp_of ctxt myvars_typ)], [])
                            @{thm undefined_function_body_def}], true)
  in
    { name = name,
      is_simpl_wrapper = false,
      invented_body = invented,
      phases = Phasetab.make [(CP,
          {
            args = arg_list,
            return_type = return_type,
            const = const,
            raw_const = const,
            definition = hd definition,
            mono_thm = NONE,
            phase = CP
          })]
    }
  end
in
  ProgramAnalysis.get_fninfo csenv
  |> Symtab.dest
  |> map (uncurry gen_fn_info)
  |> map (fn x => (#name x, x))
  |> Symtab.make
  |> mk_function_info
end

(*
 * Misc getters for function information.
 *)

fun get_all_functions (FunctionInfo x) = (#function_info x);

fun get_function_info fn_info name =
    Symtab.lookup (get_all_functions fn_info) name
    |> Utils.the' ("Function " ^ quote name ^ " does not exist")

fun get_1_phase_info info phase =
    Phasetab.lookup (#phases info) phase
    |> Utils.the' ("Phase " ^ string_of_phase phase ^ " does not exist for function " ^ quote (#name info))

fun get_phase_info fn_info phase name = get_1_phase_info (get_function_info fn_info name) phase

fun get_function_from_const (fn_info as FunctionInfo x) term =
    Termtab.lookup (#const_to_function x) term
    |> Option.map (get_function_info fn_info)

fun map_fn_info f (FunctionInfo x) =
  #function_info x
  |> Symtab.dest
  |> List.mapPartial (fn (name, info) => Option.map (fn info' => (name, info')) (f info))
  |> Symtab.make
  |> mk_function_info;

fun add_phases f =
  map_fn_info (fn info => case f (#name info) info of
                              NONE => SOME info
                            | SOME pinfo' => SOME (function_info_add_phase pinfo' info));

(* Get a list of functions called by the given function. *)
fun get_function_callees (FunctionInfo functions) fn_name =
  Symtab.lookup (#function_callees functions) fn_name
  |> Utils.the' ("Function " ^ quote fn_name ^ " does not exist.")

(* Get recursive calls made by a function. *)
fun get_recursive_group (FunctionInfo functions) fn_name =
  Symtab.lookup (#recursive_functions functions) fn_name
  |> Utils.the' ("Function " ^ quote fn_name ^ " does not exist.")

(* Is the given function recursive? *)
fun is_function_recursive fn_info fn_name =
  length (get_recursive_group fn_info fn_name) > 0

(* Get recursive calls made by a function. *)
fun get_recursive_functions (FunctionInfo functions) =
  Symtab.dest (#recursive_functions functions)
  |> filter (fn (_, x) => length x <> 0)
  |> map fst

(* Get a list of functions sorted in topological order. Mutually recursive
 * functions remain in the same list. *)
fun get_topo_sorted_functions (FunctionInfo functions) =
  #topo_sorted_functions functions

end

(* Save function information into the theory. *)
structure AutoCorresFunctionInfo = Theory_Data(
  type T = FunctionInfo.fn_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge (l, r) =
    Symtab.merge (fn _ => true) (l, r);
)
