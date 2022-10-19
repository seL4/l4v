(*
 * Copyright 2022, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Tactics/methods related to instantiating variables in multiple thms. *)

theory Rules_Tac
imports Main
begin

ML \<open>
structure Multi_Rule_Insts = struct

(* copied verbatim from rule_insts.ML *)
val named_insts =
  Parse.and_list1
    (Parse.position Args.var -- (Args.$$$ "=" |-- Parse.!!! Parse.embedded_inner_syntax))
    -- Parse.for_fixes

(* copied from rule_insts.ML, modified to allow instantiation in multiple rules simultanously *)
fun method inst_tac tac =
  Args.goal_spec -- Scan.optional (Scan.lift (named_insts --| Args.$$$ "in")) ([], []) --
  Attrib.thms >> (fn ((quant, (insts, fixes)), thms) => fn ctxt => METHOD (fn facts =>
    if null insts andalso null fixes
    then quant (Method.insert_tac ctxt facts THEN' tac ctxt thms)
    else
      map (fn thm => quant (Method.insert_tac ctxt facts THEN' inst_tac ctxt insts fixes thm)) thms
      |> FIRST))

(* Instantiate a single named variable in thms with a value, apply to inst_tac *)
fun single_instantiate_tac inst_tac var_name syn_value fixes thms ctxt facts =
  let
    val var = Option.valOf (Lexicon.read_variable var_name)
    val insts = [((var, Position.none), syn_value)]
  in
    map (fn thm => HEADGOAL (Method.insert_tac ctxt facts THEN' inst_tac ctxt insts fixes thm)) thms
    |> FIRST
  end

(* Example of how use embed single_instantiate_tac in a method *)
fun single_instantiate_method inst_tac var_name thms =
  Scan.lift Parse.embedded_inner_syntax -- Scan.lift Parse.for_fixes
  >> (fn (syn, fixes) => fn ctxt =>
        METHOD (single_instantiate_tac inst_tac var_name syn fixes thms ctxt))

end\<close>

method_setup rules_tac = \<open>Multi_Rule_Insts.method Rule_Insts.res_inst_tac resolve_tac\<close>
  "apply rule (dynamic instantiation for multiple thms containing same variable)"

(* see Rules_Tac_Test.thy for examples/demo *)

end
