(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WP_Pre
imports
  Main
  Eisbach_Tools.Trace_Schematic_Insts
  "HOL-Eisbach.Eisbach_Tools"
begin

ML \<open>
structure WP_Pre = struct

val wp_trace = Attrib.setup_config_bool @{binding wp_trace} (K false);
val wp_trace_instantiation =
  Attrib.setup_config_bool @{binding wp_trace_instantiation} (K false);

fun append_used_rule ctxt used_thms_ref tag used_thm insts =
  let
    val name = Thm.get_name_hint used_thm
    val inst_term =
      if Config.get ctxt wp_trace_instantiation
      then Trace_Schematic_Insts.instantiate_thm ctxt used_thm insts
      else Thm.prop_of used_thm
  in used_thms_ref := !used_thms_ref @ [(name, tag, inst_term)] end

fun trace_rule' trace ctxt callback tac rule =
  if trace
  then Trace_Schematic_Insts.trace_schematic_insts_tac ctxt callback tac rule
  else tac rule;

fun trace_rule trace ctxt used_thms_ref tag tac rule =
  trace_rule' trace ctxt
    (fn rule_insts => fn _ => append_used_rule ctxt used_thms_ref tag rule rule_insts)
    tac rule;

fun rtac ctxt rule = resolve_tac ctxt [rule]

fun pre_tac trace ctxt pre_rules used_thms_ref i t = let
    fun apply_rule t = trace_rule trace ctxt used_thms_ref "wp_pre" (rtac ctxt) t i
    val t2 = FIRST (map apply_rule pre_rules) t |> Seq.hd
    val etac = TRY o eresolve_tac ctxt [@{thm FalseE}]
    fun dummy_t2 _ _ = Seq.single t2
    val t3 = (dummy_t2 THEN_ALL_NEW etac) i t |> Seq.hd
  in if Thm.nprems_of t3 <> Thm.nprems_of t2
    then Seq.empty else Seq.single t2 end
    handle Option => Seq.empty

val method =
  let
    val used_thms_ref = Unsynchronized.ref [] : (string * string * term) list Unsynchronized.ref
  in
    Attrib.thms >> (fn thms => fn ctxt =>
      Method.SIMPLE_METHOD' (pre_tac (Config.get ctxt wp_trace) ctxt thms used_thms_ref))
  end
end
\<close>

(* This method takes a list of theorems as parameter.
   See wp_pre definition below for an example use. *)
method_setup pre_tac = \<open>WP_Pre.method\<close>

named_theorems wp_pre
method wp_pre0 = pre_tac wp_pre
method wp_pre = wp_pre0?

definition
  test_wp_pre :: "bool \<Rightarrow> bool \<Rightarrow> bool"
where
  "test_wp_pre P Q = (P \<longrightarrow> Q)"

lemma test_wp_pre_pre[wp_pre]:
  "test_wp_pre P' Q \<Longrightarrow> (P \<Longrightarrow> P')
    \<Longrightarrow> test_wp_pre P Q"
  by (simp add: test_wp_pre_def)

lemma demo:
  "test_wp_pre P P"
  (* note that wp_pre0 applies, but only once *)
  apply wp_pre0+
   apply (simp add: test_wp_pre_def, rule imp_refl)
  apply simp
  done

end
