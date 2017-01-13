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
 * Functions for extracting information from the C parser in a format more
 * convenient for us to work with.
 *)
structure ProgramInfo =
struct

(* Program information type. *)
type prog_info =
{
  (* C environment from the C parser *)
  csenv : ProgramAnalysis.csenv,

  state_type : typ,
  globals_type : typ,
  gamma : term,

  var_getters : term Symtab.table,
  var_setters : term Symtab.table,
  var_types : typ Symtab.table,
  globals_getter : term,

  global_var_getters : term Symtab.table,
  global_var_setters : term Symtab.table,
  t_hrs_getter : term,
  t_hrs_setter : term
}

(* Internal name of the "globals variable" in the "myvars" record. *)
val globals_record = "globals'"

(*
 * Get the HOL constant names for the getter/setter for variable
 * "varname" of the record "record_typ".
 *)
fun get_record_getter_setter ctxt record_typ varname =
let
  val consts = Proof_Context.consts_of ctxt;
  val getter_varname = varname |> Consts.intern consts;
  val setter_varname = varname ^ Record.updateN |> Consts.intern consts;
  val getter_term = Const (getter_varname, record_typ --> dummyT)
        |> Syntax.check_term ctxt
  val setter_term = Const (setter_varname, [dummyT, dummyT] ---> record_typ)
        |> Syntax.check_term ctxt
in
   (getter_term, setter_term)
end

(*
 * Extract useful information about the given local variable from the
 * c-parser "vinfo" structure.
 *)
fun get_local_variable_info ctxt state_typ csenv_var =
let
  val thy = Proof_Context.theory_of ctxt
  val munged_name = ProgramAnalysis.get_mname csenv_var;
  val pretty_name = ProgramAnalysis.srcname csenv_var;
  val hol_type = CalculateState.ctype_to_typ
      (thy, ProgramAnalysis.get_vi_type csenv_var)
  val (getter, setter) = get_record_getter_setter
      ctxt state_typ (HoarePackage.varname (MString.dest munged_name))
in
  (munged_name, pretty_name, hol_type, getter, setter)
end

(*
 * Extract useful information about the given global variable from the
 * c-parser "vinfo" structure.
 *)
fun get_global_variable_info ctxt csenv_var =
let
  val thy = Proof_Context.theory_of ctxt
  val munged_name = ProgramAnalysis.get_mname csenv_var;
  val pretty_name = ProgramAnalysis.srcname csenv_var;
  val hol_type = CalculateState.ctype_to_typ (thy, ProgramAnalysis.get_vi_type csenv_var)
in
  (munged_name, pretty_name, hol_type)
end

(* Given a record field name, guess the original variable name. *)
fun guess_var_name x =
  case (Long_Name.base_name x) of
      "globals" => globals_record
    | x => unsuffix "_'" x

(* Given a record field updater function, guess the original variable name. *)
fun guess_var_name_from_setter x =
  case (Long_Name.base_name x) of
      "globals" => globals_record
    | x => unsuffix Record.updateN x |> guess_var_name

fun guess_var_name_type_from_setter_term setter =
let
  (* We have a term of the form (Const "foo_'_update"). Extract the name
   * of the constant. *)
  val (setter_name, setter_type) = Term.dest_Const setter

  (* Guess the variable name by stripping off the suffix. *)
  val var_name = (guess_var_name_from_setter setter_name)
    handle Fail _ => (Utils.invalid_term "local variable update function" setter)

  (* Get the variable type: @{typ "(TYPE --> X) --> X --> X"} *)
  val var_type = dest_Type setter_type |> snd |> hd |> dest_Type |> snd |> hd
in
  (var_name, var_type)
end

(*
 * Demangle a name mangled by the C parser.
 *)
fun demangle_name m =
  if NameGeneration.rmUScoreSafety m <> m
  then (* ignore the "StrictC'" prefix when decoding, but we need to re-mangle it in
        * so that the resulting name is legal in Isabelle *)
       NameGeneration.mkIdentUScoreSafe (demangle_name (NameGeneration.rmUScoreSafety m))
  else case NameGeneration.dest_embret (MString.mk m) of
           (* Return variable for function f *)
           SOME (_, n) => "ret" ^ (if n > 1 then string_of_int n else "")
           (* Ordinary variable. Split the type suffix off if there is one. *)
         | NONE => let
             val delim = "___" (* NameGeneration.tag_name_with_type *)
             val (prefix, _) = apply2 Substring.string (Utils.positionr delim (Substring.full m))
             in prefix end

val _ = assert (demangle_name "c___ret_int" = "c") ""
val _ = assert (demangle_name "ret_eret_2" = "ret2") ""
val _ = assert (demangle_name "StrictC'__reserved___int" = "StrictC'__reserved") ""


(*
 * Extract details from the c-parser about the given program.
 *)
fun get_prog_info ctxt filename : prog_info =
  let
    val thy = Proof_Context.theory_of ctxt
    val csenv = CalculateState.get_csenv thy filename |> the;

    (* Get the type of the state record and the globals record. *)
    fun expand_type_abbrevs t = Thm.typ_of (Thm.ctyp_of ctxt t)
    val globals_type = Type (Sign.intern_type thy "globals", []) |> expand_type_abbrevs
    val state_type = Type (Sign.intern_type thy "myvars", [globals_type]) |> expand_type_abbrevs

    (* Get the gamma variable, mapping function numbers to function bodies in
     * SIMPL. *)
    val gamma =
      (Const (Consts.intern (Proof_Context.consts_of ctxt) "\<Gamma>", dummyT)
       |> Syntax.check_term ctxt)
      handle TERM _ => error "autocorres: could not find any functions -- \<Gamma> is not defined."

    (*
     * Return a Const term of the local-variable getters/setters for the given
     * variable name.
     *
     * For instance, if "x" was passed in, we might return:
     *     SOME (Const ("Kernel_C.myvars.x_'", "globals myvars => nat"))
     *)
    val var_getters = Record.get_recT_fields thy state_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x, Const (x, state_type --> T)))
      |> Symtab.make
    val var_setters = Record.get_recT_fields thy state_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x,
          Const (x ^ Record.updateN, (T --> T) --> state_type --> state_type)))
      |> Symtab.make

    (* Return the type for a particular variable. *)
    val var_types = Record.get_recT_fields thy state_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x, T))
      |> Symtab.make

    (* Get the "globals" getter from "myvars". *)
    val globals_getter = case (Symtab.lookup var_getters globals_record) of
        SOME x => x
      | NONE => raise Utils.InvalidInput "'myvars' doesn't appear to have a 'globals' field."

    (* Get global getters/setters. *)
    val global_var_getters = Record.get_recT_fields thy globals_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x, Const (x, globals_type --> T)))
      |> Symtab.make
    val global_var_setters = Record.get_recT_fields thy globals_type
      |> fst
      |> map (fn (x, T) => (guess_var_name x,
          Const (x ^ Record.updateN, (T --> T) --> globals_type --> globals_type)))
      |> Symtab.make

    (* Get the "t_hrs_'" getter/setter from "myvars". *)
    val t_hrs_getter = case (Symtab.lookup global_var_getters "t_hrs") of
        SOME x => x
      | NONE => raise Utils.InvalidInput "'globals' doesn't appear to have a \"t_hrs_'\" field."
    val t_hrs_setter = case (Symtab.lookup global_var_setters "t_hrs") of
        SOME x => x
      | NONE => raise Utils.InvalidInput "'globals' doesn't appear to have a \"t_hrs_'\" field."
  in
    {
      csenv = csenv,

      state_type = state_type,
      globals_type = globals_type,
      gamma = gamma,

      var_getters = var_getters,
      var_setters = var_setters,
      var_types = var_types,
      globals_getter = globals_getter,

      global_var_getters = global_var_getters,
      global_var_setters = global_var_setters,
      t_hrs_getter = t_hrs_getter,
      t_hrs_setter = t_hrs_setter
    }
  end

(* Is the given term the "t_hrs_'" constant? *)
fun is_t_hrs_const (prog_info : prog_info) t =
  (t = #t_hrs_getter prog_info)
fun is_t_hrs_update_const (prog_info : prog_info) t =
  (t = #t_hrs_setter prog_info)

end
