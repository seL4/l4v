(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WP_Pre
imports
  Main
  "HOL-Eisbach.Eisbach_Tools"
begin

named_theorems wp_pre

ML \<open>
structure WP_Pre = struct

fun append_used_thm thm used_thms = used_thms := !used_thms @ [thm]

fun pre_tac ctxt pre_rules used_ref_option i t = let
    fun append_thm used_thm thm =
      if Option.isSome used_ref_option
      then Seq.map (fn thm => (append_used_thm used_thm (Option.valOf used_ref_option); thm)) thm
      else thm;
    fun apply_rule t thm = append_thm t (resolve_tac ctxt [t] i thm)
    val t2 = FIRST (map apply_rule pre_rules) t |> Seq.hd
    val etac = TRY o eresolve_tac ctxt [@{thm FalseE}]
    fun dummy_t2 _ _ = Seq.single t2
    val t3 = (dummy_t2 THEN_ALL_NEW etac) i t |> Seq.hd
  in if Thm.nprems_of t3 <> Thm.nprems_of t2
    then Seq.empty else Seq.single t2 end
    handle Option => Seq.empty

fun tac used_ref_option ctxt = let
    val pres = Named_Theorems.get ctxt @{named_theorems wp_pre}
  in pre_tac ctxt pres used_ref_option end

val method
    = Args.context >> (fn _ => fn ctxt => Method.SIMPLE_METHOD' (tac NONE ctxt));
end
\<close>

method_setup wp_pre0 = \<open>WP_Pre.method\<close>
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
