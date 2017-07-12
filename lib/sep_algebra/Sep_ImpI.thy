(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Sep_ImpI
imports Sep_Provers Sep_Cancel_Set Sep_Tactic_Helpers
begin

lemma sep_wand_lens: "(\<And>s. T s = Q s) \<Longrightarrow> ((P \<longrightarrow>* T) \<and>* R) s \<Longrightarrow> ((P \<longrightarrow>* Q) \<and>* R) s"
  apply (sep_erule_full refl_imp)
  apply (clarsimp simp: sep_impl_def)
  done

lemma sep_wand_lens': "(\<And>s. T s = Q s) \<Longrightarrow> ((T \<longrightarrow>* P) \<and>* R) s \<Longrightarrow> ((Q \<longrightarrow>* P) \<and>* R) s"
  apply (sep_erule_full refl_imp, erule sep_curry[rotated])
  apply (clarsimp)
  apply (erule sep_mp)
  done

(* Removing wands from the conclusions *)

ML {*

fun sep_wand_lens ctxt = resolve_tac ctxt[@{thm sep_wand_lens}]
fun sep_wand_lens' ctxt = resolve_tac ctxt [@{thm sep_wand_lens'}]

fun sep_wand_rule_tac tac ctxt =
  let
    val r = rotator' ctxt
  in
    tac |> r (sep_wand_lens' ctxt) |> r (sep_wand_lens ctxt) |> r (sep_select ctxt)
  end

fun sep_wand_rule_tac' thms ctxt =
  let
    val r = rotator' ctxt
  in
    eresolve_tac ctxt thms |> r (sep_wand_lens ctxt) |> r (sep_select ctxt) |> r (sep_asm_select ctxt)
  end

fun sep_wand_rule_method thms ctxt = SIMPLE_METHOD' (sep_wand_rule_tac thms ctxt)
fun sep_wand_rule_method' thms ctxt = SIMPLE_METHOD' (sep_wand_rule_tac' thms ctxt)

*}


lemma sep_wand_match:
  "(\<And>s. Q s \<Longrightarrow> Q' s)  \<Longrightarrow> (R \<longrightarrow>* R') s    ==>  (Q \<and>* R \<longrightarrow>* Q' \<and>* R') s"
  apply (erule sep_curry[rotated])
  apply (sep_select_asm 1 3)
  apply (sep_drule (direct) sep_mp_frame)
  apply (sep_erule_full refl_imp, clarsimp)
  done

lemma sep_wand_trivial:    "(\<And>s. Q s \<Longrightarrow> Q' s) \<Longrightarrow> R' s            ==>   (Q \<longrightarrow>* Q' \<and>* R') s"
  apply (erule sep_curry[rotated])
  apply (sep_erule_full refl_imp)
  apply (clarsimp)
  done

lemma sep_wand_collapse:  "(P \<and>* Q \<longrightarrow>* R) s \<Longrightarrow> (P \<longrightarrow>* Q \<longrightarrow>* R) s "
  apply (erule sep_curry[rotated])+
  apply (clarsimp simp: sep_conj_assoc)
  apply (erule sep_mp)
 done

lemma sep_wand_match_less_safe:
  assumes drule: " \<And>s. (Q' \<and>* R) s \<Longrightarrow> ((P \<longrightarrow>* R') \<and>* Q' \<and>* R'' ) s "
  shows "(Q' \<and>* R) s \<Longrightarrow> (\<And>s. Q' s \<Longrightarrow> Q s) \<Longrightarrow> ((P \<longrightarrow>* Q \<and>* R') \<and>* R'') s"
  apply (drule drule)
  apply (sep_erule_full refl_imp)
  apply (erule sep_conj_sep_impl)
  apply (clarsimp simp: sep_conj_assoc)
  apply (sep_select_asm 1 3)
  apply (sep_drule (direct) sep_mp_frame, sep_erule_full refl_imp)
  apply (clarsimp)
 done

ML {*
fun sep_match_trivial_tac ctxt =
  let
    fun flip f a b = f b a
    val sep_cancel = flip (sep_apply_tactic ctxt) (SepCancel_Rules.get ctxt |> rev)
    fun f x = x |> rotate_prems ~1 |> (fn x => [x]) |> eresolve0_tac |> sep_cancel
    val sep_thms = map f [@{thm sep_wand_trivial}, @{thm sep_wand_match}]
  in
    sep_wand_rule_tac (resolve0_tac [@{thm sep_rule}] THEN' FIRST' sep_thms) ctxt
  end

fun sep_safe_method ctxt = SIMPLE_METHOD' (sep_match_trivial_tac ctxt)
*}

method_setup sep_safe = {*
  Scan.succeed (sep_safe_method)
*}

end
