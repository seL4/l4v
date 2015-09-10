(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature NAME_GENERATION =
sig

  val initialisation_function : string
  val return_var_name : int Absyn.ctype -> MString.t
  val embret_var_name : string * int -> MString.t
  val dest_embret : MString.t -> (string * int) option
  val C_global_var : MString.t -> MString.t
  val global_var : string -> string
  val global_addr : string -> string
  val fake_param : string -> int -> string
  val tag_name_with_type : {name: string, typname:string} -> string

  val adglob_rcd_tyname : string
  val adglob_struct_var : string

  val naming_scheme_name : string

  val enum_const_name : string -> string
  val enum_const_summary_lemma_sfx : string
  val untouched_global_name : MString.t -> MString.t
  val global_initializer_name : MString.t -> MString.t
  val global_data_name : string -> string

  val global_rcd_name : string
  val global_ext_type : string
  val global_exn_var_name : string
  val global_exn_var : string
  val global_heap : string
  val global_heap_var : string
  val local_rcd_name : string

  val C_struct_name : string -> string
  val unC_struct_name : string -> string
  val C_field_name : string -> string
  val unC_field_name : string -> string

  val internalAnonStructPfx : string
  val mkAnonStructName : int -> string

  val mkIdentUScoreSafe : string -> string
  val rmUScoreSafety : string -> string

  val apt_string : string -> string

  val gensym : string -> string

  val numCopyN : string

  val phantom_state_name : string
  val ghost_state_name : string
  val owned_by_fn_name : string

  val mk_localstatic : {fname : string, vname : string } -> MString.t
end;

(*

  [initialisation_function] is the name of the implicit initialisation
  function responsible for initialising global variables.

  [return_var_name ty] is the 'name' of the variable that stands for a
  function's return value, given the type of the value returned by the
  function.

  [tag_name_with_type {name,typname}] combines the two strings to create
  a new variable name.  Used when two local variables are requested and
  have different types. (The Hoare environment can't cope with this, so
  one or both variables need to pick up new names.)

  [embret_var_name(f,i)] is the name of the variable that stands for
  the ith return value from a function f that is called while embedded
  in some expression.

  [dest_embret s] returns SOME(f,i) if embret_var_name(f,i) = s, NONE
  if there is no such f and i.

  [global_var s] translates a global variable to an Isabelle variable
  name.  Note that the only variables so treated are special Hoare
  environments like the heap, and the well-typedness environment -
  there aren't any C global variables treated this way.

  [C_global_var s] translates a C global variable name.

  [global_addr s] translates a global C variable name into the name of an
  Isabelle constant that will hold that variable's address in the heap.

  [fake_param s i] gives a name for a parameter based on the name of the
  function and the number of the parameter in the list.

  [adglob_rcd_tyname] is the name of the C struct type that
  contains the global variables that are addressed.

  [adglob_rcd_addr] is the name of the Isabelle variable (it will be a
  locale parameter) containing the address of the addressed globals
  struct in the heap.

  [enum_const_name s] gives back the Isabelle name of the constant
  that will correspond to the enumeration constant s.

  [enum_const_summary_lemma_sfx] is the suffix appended to the name of
  an enumeration type to generate the name of the lemma that lists all
  of the definitions for that type's constants.

  [global_heap_var] is the name of the global variable corresponding to
  the program's heap, which will be of type (addr -> byte x heap_typ_desc).
  This includes both components in the same variable to provide serialisation
  of updates.

  [global_rcd_name] is the name of the record type that stores the
  program's global variables.  May need to be turned into a fully-qualified
  name through the use of Sign.intern_tycon

  [global_ext_type] is similar, but gives the type name suitable for
  axiomatic type class instantiation.

  [local_rcd_name] is the name of the (polymorphic) record type that
  contains all the local variables, and is an extension of the
  StateSpace.state record type.

  [global_exn_var_name] is the name of the local variable that contains the
  current type of exception (Break|Return|Continue).

  [global_exn_var] is the name of the local variable accessor that gets the
  current type of exception (Break|Return|Continue).

  [C_struct_name s] "munges" the name s of a C struct type into a form
  that is acceptable for the Isabelle verification.

  [C_field_name s] "munges" the name s of a field in a C struct type
  into a form that is acceptable for the Isabelle verification.

  [apt_string] translates a term representing a term to one that will have
  the _quote parse translation applied to it in read_cterm.

  [gensym s] returns a string prefixed by s which hasn't been returned by
  gensym before.  It does this by appending a "_<n>" where <n> is the string
  corresponding to a so-far unused integer.

*)

structure NameGeneration :> NAME_GENERATION =
struct

val initialisation_function = "___special___init"


fun embret_var_name (f,i) =
    if i < 1 then raise Fail "embret_var_name: i < 1"
    else if i = 1 then MString.mk ("ret__" ^ f)
    else MString.mk (f ^ "_eret_" ^ Int.toString i)

fun dest_embret s0 =
  let
    val s = MString.dest s0
  in
    if String.isPrefix "ret__" s then
      SOME (String.extract(s,5,NONE), 1)
    else let
        open Substring
        val (pfx, digsfx) = splitr Char.isDigit (full s)
      in
        if isEmpty digsfx then NONE
        else if isSuffix "_eret_" pfx then
          SOME (string (trimr 6 pfx), valOf (Int.fromString (string digsfx)))
        else
          NONE
      end
  end

fun return_var_name ty = embret_var_name (Absyn.tyname ty, 1)

fun tag_name_with_type {name: string, typname:string} = name ^ "___" ^ typname


fun fake_param f i = f ^ "_param_" ^ Int.toString i
fun ext_type t = t ^ "_ext"

fun enum_const_name s = s
val enum_const_summary_lemma_sfx = "_defs"

fun fix_underscore s = if String.isPrefix "_" s
  then "underscore" ^ s else s

fun untouched_global_name s =
  s |> MString.dest |> fix_underscore |> MString.mk

fun global_initializer_name s =
  fix_underscore (MString.dest s) ^ "_global_initializer" |> MString.mk
fun global_data_name s = fix_underscore s ^ "_global_data"

val global_rcd_name = "globals"
val global_ext_type = ext_type global_rcd_name
val global_exn_var_name = "global_exn_var"
val global_exn_var = global_exn_var_name ^ "_'"
val local_rcd_name = "myvars"

fun C_global_var s = s
fun global_var s = Hoare.varname s
fun global_addr s = s ^"_addr"
fun global_upd s = global_var s ^ "_upd"

val global_heap = "t_hrs"
val global_heap_var = global_var global_heap

fun apt_string s = "[.[" ^ s ^ "].]"

val gs_n = ref 1
fun gensym s = (s ^ "_" ^ Int.toString (!gs_n) before
                gs_n := !gs_n + 1)

val numCopyN = "tyCopy"

fun C_struct_name s = s ^ "_C"
fun unC_struct_name s =
    if String.isSuffix "_C" s then
      String.extract(s,0,SOME(size s - 2))
    else s
fun C_field_name s = s ^ "_C"
fun unC_field_name s =
    if String.isSuffix "_C" s then
      String.extract(s,0,SOME(size s - 2))
    else s

val adglob_rcd_tyname = "adglobs_struct"
val adglob_struct_var = "adglobs"

val phantom_state_name = "phantom_machine_state"
val ghost_state_name = "ghost'state"

val naming_scheme_name = "\\" ^ "<Gamma>_naming"
val owned_by_fn_name = "owner'ship"

val internalAnonStructPfx = "ISA_anon_struct|"
fun mkAnonStructName i = "AnonStruct" ^ Int.toString i ^ "'"

(* mkIdentUScoreSafe is injective on identifiers that can be
   generated by the lexer *)
val ussafe_pfx = "StrictC'"
fun mkIdentUScoreSafe s =
    if String.sub(s, 0) = #"_" then ussafe_pfx^s
    else s

fun rmUScoreSafety s =
    if String.isPrefix ussafe_pfx s then
      String.extract(s, String.size ussafe_pfx, NONE)
    else s

fun mk_localstatic {fname, vname} =
  MString.mk ("static'" ^ fname ^ "'" ^ vname)



end;
