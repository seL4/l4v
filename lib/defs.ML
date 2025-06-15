(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* This is a slightly modified and simplified version of the old Isabelle "defs" command.
   It still uses Global_Theory.add_def as "defs" did.

   The modifications are:
     - "overloading" and "unchecked" are removed
     - no attributes for the definition theorem
     - only one equation per "defs" command
     - deprecation warning removed
*)

signature OLD_DEFS=
sig
end

structure Old_Defs : OLD_DEFS =
struct

fun read ctxt (b, str) =
  Syntax.read_prop ctxt str handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in definition " ^ Binding.print b);

fun add_def ctxt (b, str) thy = Global_Theory.add_def (b, read ctxt (b, str)) thy

fun syntax_alias global_alias local_alias b name =
  Local_Theory.declaration {syntax = true, pos = Position.none, pervasive = true} (fn phi =>
    let val b' = Morphism.binding phi b
    in Context.mapping (global_alias b' name) (local_alias b' name) end);

val const_alias = syntax_alias Sign.const_alias Proof_Context.const_alias;

(* Proof_Context.fact_alias doesn't work here, so we need to play a few tricks to get the right fact name *)

val _ =
  Outer_Syntax.command @{command_keyword defs} "define constants"
    (Parse.opt_target -- (Parse.binding -- (Parse.$$$ ":" |-- Parse.prop))
      >> (fn (target, (b, str)) => Toplevel.local_theory NONE target (fn lthy =>
          let
               val b' = Binding.suffix_name "__internal__" b
               val (thm, lthy') = Local_Theory.background_theory_result (add_def lthy (b', str)) lthy;
               val (_, lthy'') = Local_Theory.note ((b,[]), [thm]) lthy'
               val lthy''' = Local_Theory.raw_theory
                               (Global_Theory.hide_fact true (Thm_Name.short (Thm.derivation_name thm))) lthy''
          in lthy''' end)));


val _ =
  Outer_Syntax.command @{command_keyword consts'} "localized consts declaration"
    (Parse.opt_target -- Scan.repeat1 Parse.const_binding >>
      (fn (target, bs) => Toplevel.local_theory NONE target (fn lthy =>
         fold (fn (b, raw_typ, mixfix) => fn lthy =>
           let val (Const (nm, _), lthy') = Local_Theory.background_theory_result
             (Sign.declare_const lthy ((b, Syntax.read_typ lthy raw_typ), mixfix)) lthy;
          in const_alias b nm lthy' end) bs lthy)))
end
