(*
 * Copyright 2024, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
  Requalify constants, types and facts into the current naming.
  Includes command variants that support implicitly using the L4V_ARCH environment variable.
*)

text \<open>See theory @{text "test/Requalify_Test.thy"} for commented examples and usage scenarios.\<close>

theory Requalify
imports Main
keywords "requalify_facts" :: thy_decl
     and "requalify_types" :: thy_decl
     and "requalify_consts" :: thy_decl
     and "global_naming" :: thy_decl
     and "arch_requalify_facts" :: thy_decl
     and "arch_requalify_types" :: thy_decl
     and "arch_requalify_consts" :: thy_decl
     and "arch_global_naming" :: thy_decl
begin

ML \<open>

local

fun all_facts_of ctxt =
  Proof_Context.theory_of ctxt
  |> Global_Theory.facts_of
  |> Facts.dest_static false [];

fun tl' (_ :: xs) = xs
  | tl' _ = []

(* Alias binding to fully-qualified name "name" in both global and local context *)
fun bind_alias global_alias_fn local_alias_fn binding (name : string) =
  Local_Theory.declaration {syntax = false, pos = Position.none, pervasive = true} (fn phi =>
    let val binding' = Morphism.binding phi binding;
    in Context.mapping (global_alias_fn binding' name) (local_alias_fn binding' name) end);

(* Instantiate global and local aliasing functions for consts, types and facts *)
val const_alias = bind_alias Sign.const_alias Proof_Context.const_alias;
val type_alias = bind_alias Sign.type_alias Proof_Context.type_alias;
val alias_fact = bind_alias Global_Theory.alias_fact Proof_Context.alias_fact;

(* Locate global fact matching supplied name.
   When we specify a fact name that resolves to a global name, return the normal fact lookup result.
   Note: Locale_Name.fact_name outside the locale resolves to a global name.

   When we are inside a locale, the lookup is more interesting. Supplying "short_name" will result
   in "local.short_name", which we then need to match to some name in the global context. We do
   this by going through *all* the fact names in the current context, searching for matches
   of the form "X.Y.short_name", where we hope X is some theory, and Y is some locale.

   Since "X.Y.short_name" is not sufficiently unique, we must also check that the theorems under
   the discovered name match the ones under "local.short_name". *)
fun global_fact ctxt nm =
let
   val facts = Proof_Context.facts_of ctxt;
   val {name, thms, ...} = (Facts.retrieve (Context.Proof ctxt) facts (nm, Position.none));

   fun matches suffix (global_name, global_thms) =
     suffix = (Long_Name.explode global_name |> tl' |> tl' |> Long_Name.implode)
     andalso eq_list (Thm.equiv_thm (Proof_Context.theory_of ctxt)) (thms, global_thms)
in
  case Long_Name.dest_local name of
    NONE => (name, thms)
  | SOME suffix =>
     (case (find_first (matches suffix) (all_facts_of ctxt)) of
        SOME x => x
      | NONE => raise Fail ("Couldn't find global equivalent of local fact: " ^ nm))
end

val alias = Parse.reserved "aliasing" >> K true
val alias_default = false

(* (aliasing) only *)
val generic_options = Scan.optional (Args.parens alias >> (fn x => (x, ""))) (alias_default, "")

(* e.g. ARM, ARM_A, ARM_H *)
val arch_suffix = ((Parse.reserved "A" || Parse.reserved "H") >> (fn s =>  "_" ^ s))
fun arch_prefix suffix = getenv_strict "L4V_ARCH" ^ suffix

(* ([aliasing][,] [A|H]) in that order *)
val arch_options =
  Scan.optional (
   Args.parens (
     (alias --| Parse.$$$ "," -- arch_suffix)
     || (alias >> (fn x => (x, "")))
     || (arch_suffix >> (fn x => (alias_default, x)))
   )) (alias_default, "")

val arch_global_opts = Scan.optional (Args.parens arch_suffix) ""

in

fun gen_requalify get_proper_nm parse_nm check_parsed_nm alias_fn arch =
let
  val options = if arch then arch_options else generic_options
in
  (Parse.opt_target -- options --  Scan.repeat1 (Parse.position (Scan.ahead parse_nm -- Parse.name))
   >> (fn ((target, (aliasing, arch_suffix)), names) =>
       Toplevel.local_theory NONE target (fn lthy =>
       let
         val global_ctxt = Proof_Context.theory_of lthy |> Proof_Context.init_global

         fun requalify_entry ((entry, orig_name), pos) lthy =
         let
           val name = if arch then arch_prefix arch_suffix ^ "." ^ orig_name else orig_name
           val local_name = get_proper_nm lthy name;
           val _ = check_parsed_nm lthy (entry, (local_name, pos));

           (* Check whether the short (base) name is already available in theory context if no
              locale target is supplied and the "aliasing" option is not supplied.
              Note: currently no name collision warning when exporting into locale *)
           val base_name = Long_Name.base_name name;
           val global_base = try (get_proper_nm global_ctxt) (Long_Name.base_name name);
           val _ = (case (global_base, target, aliasing) of
                      (SOME _, NONE, false) => warning ("Name \"" ^ base_name
                                                        ^ "\" already exists in theory context")
                    | _ => ())

           val b = Binding.make (base_name, pos)
           val lthy' = lthy |> alias_fn b local_name
         in lthy' end
       in fold requalify_entry names lthy end)))
end

local

val get_const_nm = ((fst o dest_Const) oo (Proof_Context.read_const {proper = true, strict = false}))
val get_type_nm = ((fst o dest_Type) oo (Proof_Context.read_type_name {proper = true, strict = false}))
val get_fact_nm = (fst oo global_fact)

(* For a theorem name, we want to additionally make sure that global fact names found by
   global_fact are accessible in the current context. *)
fun check_fact lthy (_, (nm, pos)) = Proof_Context.get_fact lthy (Facts.Named ((nm,pos), NONE))

(* replace text in all Text nodes in YXML-encoded string entry with new_text *)
fun replace_yxml_text new_text =
let
  fun tree_text (XML.Text _) = XML.Text new_text
    | tree_text (XML.Elem (node, trees)) = (XML.Elem (node, map tree_text trees))
in
  YXML.string_of o tree_text o YXML.parse
end

(* These versions, prior to resolving the const/type name, override that name in the parsed
   YXML-encoded string entry with a name that will actually resolve to something, while preserving
   other parse data such as parsed document location.
   This updates the document markup at the original parse location of entry with a reference to the
   const/type named by "name", allowing the user to ctrl+click to jump to the const/type definition.

   For example, if the user requested "arch_requalify_consts (A) some_const", then they are
   targeting something like "ARM_A.some_const", and expect to be able to jump to its definition.

   This isn't necessary for facts, as those use parsed position of "name" directly via
   Proof_Context.get_fact, which appears not available for read_const/read_type_name. *)
fun arch_const_nm lthy entry name = get_const_nm lthy (replace_yxml_text name entry)
fun arch_type_nm lthy entry name = get_type_nm lthy (replace_yxml_text name entry)

in

val _ =
  Outer_Syntax.command @{command_keyword requalify_consts} "alias const with current naming"
    (gen_requalify get_const_nm Parse.const (fn lthy => fn (e, _) => get_const_nm lthy e) const_alias
                   false)

val _ =
  Outer_Syntax.command @{command_keyword requalify_types} "alias type with current naming"
    (gen_requalify get_type_nm Parse.typ (fn lthy => fn (e, _) => get_type_nm lthy e) type_alias
                   false)

val _ =
  Outer_Syntax.command @{command_keyword requalify_facts} "alias fact with current naming"
    (gen_requalify get_fact_nm Parse.thm check_fact alias_fact false)

val _ =
  Outer_Syntax.command @{command_keyword global_naming} "change global naming of context block"
    (Parse.binding >> (fn naming =>
      Toplevel.local_theory NONE NONE
        (Local_Theory.map_background_naming (Name_Space.parent_path
                                             #> Name_Space.qualified_path true naming))))

(* Arch variants use the L4V_ARCH variable and an additional A/H option, so that when L4V_ARCH=ARM
   "arch_requalify_consts (H) const" becomes "requalify_consts ARM_H.const"
   This allows them to be used in a architecture-generic theory.

   For consts and types, we need to perform text replacement in the YXML entry to combine the parse
   location with the right const/type name (see arch_const_nm and arch_type_nm). *)

val _ =
  Outer_Syntax.command @{command_keyword arch_requalify_consts}
    "alias const with current naming, but prepend \"($L4V_ARCH)_[A|H].\" using env. variable"
    (gen_requalify get_const_nm Parse.const (fn lthy => fn (e, (nm, _)) => arch_const_nm lthy e nm)
                   const_alias true)

val _ =
  Outer_Syntax.command @{command_keyword arch_requalify_types}
    "alias type with current naming, but prepend \"($L4V_ARCH)_[A|H].\" using env. variable"
    (gen_requalify get_type_nm Parse.typ (fn lthy => fn (e, (nm, _)) => arch_type_nm lthy e nm)
                   type_alias true)

val _ =
  Outer_Syntax.command @{command_keyword arch_requalify_facts}
    "alias fact with current naming, but prepend \"($L4V_ARCH)_[A|H].\" using env. variable"
    (gen_requalify get_fact_nm Parse.thm check_fact alias_fact true)

val _ =
  Outer_Syntax.command @{command_keyword arch_global_naming}
    "change global naming of context block to \"($L4V_ARCH)_[A|H]\" using env. variable"
    (arch_global_opts  >> (fn arch_suffix =>
      Toplevel.local_theory NONE NONE
        (Local_Theory.map_background_naming
          (Name_Space.parent_path
           #> Name_Space.qualified_path true (Binding.make (arch_prefix arch_suffix, @{here}))))))

end

end
\<close>

end
