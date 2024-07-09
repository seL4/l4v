(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
Hoare reasoning and WP (weakest-precondition) generator rules for the reader option monad.

This list is almost certainly incomplete; add rules here as they are needed.
*)

theory Reader_Option_VCG
imports
  Reader_Option_Monad
  WPSimp
begin

(* Hoare triples.
   TODO: design a sensible syntax for them. *)

(* Partial correctness. *)
definition ovalid :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool"
  ("\<lblot>_\<rblot>/ _ /\<lblot>_\<rblot>") where
  "\<lblot>P\<rblot> f \<lblot>Q\<rblot> \<equiv> \<forall>s r. P s \<and> f s = Some r \<longrightarrow> Q r s"

(* Total correctness. *)
definition ovalidNF :: "('s \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> 'a option) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool" where
  "ovalidNF P f Q \<equiv> \<forall>s. P s \<longrightarrow> (f s \<noteq> None \<and> (\<forall>r. f s = Some r \<longrightarrow> Q r s))"
(* Termination. *)
definition no_ofail where "no_ofail P f \<equiv> \<forall>s. P s \<longrightarrow> f s \<noteq> None"

(*
This rule lets us apply ovalidNF machinery for proving no_ofail.
However, we ought to eventually write working wp rules for no_ofail (see below).
*)
lemma no_ofail_is_ovalidNF: "no_ofail P f \<equiv> ovalidNF P f (\<lambda>_ _. True)"
  by (simp add: no_ofail_def ovalidNF_def)
lemma ovalidNF_combine: "\<lbrakk> ovalid P f Q; no_ofail P f \<rbrakk> \<Longrightarrow> ovalidNF P f Q"
  by (auto simp: ovalidNF_def ovalid_def no_ofail_def)

(* use ovalid with f s = Some r *)
lemma use_ovalidE:
  "\<lbrakk>ovalid P f Q; P s; f s = Some r; Q r s \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (clarsimp simp: ovalid_def)

lemma use_ovalid:
  "\<lbrakk>ovalid P f Q; f s = Some r; P s \<rbrakk> \<Longrightarrow> Q r s"
  by (clarsimp simp: ovalid_def)

(* Annotating programs with loop invariant and measure. *)
definition owhile_inv ::
  "('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'a option) \<Rightarrow> 'a
   \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> nat) \<Rightarrow> 's \<Rightarrow> 'a option"
  where "owhile_inv C B x I M = owhile C B x"

lemmas owhile_add_inv = owhile_inv_def[symmetric]


(* WP rules for ovalid. *)
lemma ovalid_post_taut[wp]:
  "\<lblot>P\<rblot> f \<lblot>\<top>\<top>\<rblot>"
  by (simp add: ovalid_def)

lemma ovalid_inv[wp]:
  "ovalid P f (\<lambda>_. P)"
  by (simp add: ovalid_def)

lemma obind_wp[wp]:
  "\<lbrakk> \<And>r. ovalid (R r) (g r) Q; ovalid P f R \<rbrakk> \<Longrightarrow> ovalid P (obind f g) Q"
  by (simp add: ovalid_def obind_def split: option.splits, fast)

lemma oreturn_wp[wp]:
  "ovalid (P x) (oreturn x) P"
  by (simp add: ovalid_def)

lemma ocondition_wp[wp]:
  "\<lbrakk> ovalid L l Q; ovalid R r Q \<rbrakk>
   \<Longrightarrow> ovalid (\<lambda>s. if C s then L s else R s) (ocondition C l r) Q"
  by (auto simp: ovalid_def ocondition_def)

lemma ofail_wp[wp]:
  "ovalid (\<lambda>_. True) ofail Q"
  by (simp add: ovalid_def ofail_def)

lemma ask_wp[wp]:
  "\<lblot>\<lambda>s. P s s\<rblot> ask \<lblot>P\<rblot>"
  by (clarsimp simp: ovalid_def)

lemma asks_wp[wp]:
  "ovalid (\<lambda>s. P (f s) s) (asks f) P"
  by (simp add: split_def asks_def oreturn_def obind_def ovalid_def)

(* more direct form *)
lemma asks_SomeD:
  "\<lbrakk>asks f s = Some r; Q (f s) s\<rbrakk> \<Longrightarrow> Q r s"
  by (rule use_ovalid[OF asks_wp])

lemma oassert_wp[wp]:
  "\<lblot>\<lambda>s. Q \<longrightarrow> P () s\<rblot> oassert Q \<lblot>P\<rblot>"
  apply (simp add: oassert_def)
  apply (intro conjI; wpsimp)
  done

lemma ogets_wp[wp]:
  "ovalid (\<lambda>s. P (f s) s) (ogets f) P"
  by wp

lemma oguard_wp[wp]:
  "ovalid (\<lambda>s. f s \<longrightarrow> P () s) (oguard f) P"
  by (simp add: ovalid_def oguard_def)

lemma oskip_wp[wp]:
  "ovalid (\<lambda>s. P () s) oskip P"
  by (simp add: ovalid_def oskip_def)

lemma ovalid_if_split:
  "\<lbrakk> P \<Longrightarrow> \<lblot>Q\<rblot> f \<lblot>S\<rblot>; \<not>P \<Longrightarrow> \<lblot>R\<rblot> g \<lblot>S\<rblot> \<rbrakk> \<Longrightarrow> \<lblot>\<lambda>s. (P \<longrightarrow> Q s) \<and> (\<not>P \<longrightarrow> R s)\<rblot> if P then f else g \<lblot>S\<rblot>"
  by simp

lemma reader_case_option_wp[wp]:
  "\<lbrakk>\<And>x. \<lblot>P x\<rblot> m x \<lblot>Q\<rblot>; \<lblot>P'\<rblot> m' \<lblot>Q\<rblot>\<rbrakk>
   \<Longrightarrow> \<lblot>\<lambda>s. (x = None \<longrightarrow> P' s) \<and> (\<forall>y. x = Some y \<longrightarrow> P y s)\<rblot> case_option m' m x \<lblot>Q\<rblot>"
  by (cases x; simp)

lemma ovalid_case_prod[wp]:
  assumes "(\<And>x y. ovalid (P x y) (B x y) Q)"
  shows "ovalid (case v of (x, y) \<Rightarrow> P x y) (case v of (x, y) \<Rightarrow> B x y) Q"
  using assms unfolding ovalid_def by auto

lemma owhile_ovalid[wp]:
  "\<lbrakk>\<And>a. ovalid (\<lambda>s. I a s \<and> C a s) (B a) I;
    \<And>a s. \<lbrakk>I a s; \<not> C a s\<rbrakk> \<Longrightarrow> Q a s\<rbrakk>
   \<Longrightarrow> ovalid (I a) (owhile_inv C B a I M) Q"
  unfolding owhile_inv_def owhile_def ovalid_def
  apply clarify
  apply (frule (1) option_while_rule[where I = "\<lambda>a. I a s" for s])
   apply auto
  done

lemma oassert_opt_ovalid[wp]:
  "\<lblot>\<lambda>s. \<forall>y. x = Some y \<longrightarrow> Q y s\<rblot> oassert_opt x \<lblot>Q\<rblot>"
  unfolding oassert_opt_def
  by (case_tac x; wpsimp)

definition ovalid_property where "ovalid_property P x = (\<lambda>s f. (\<forall>r. Some r = x s f \<longrightarrow> P r s))"

lemma ovalid_is_triple[wp_trip]:
  "ovalid P f Q = triple_judgement P f (ovalid_property Q (\<lambda>s f. f s))"
  by (auto simp: triple_judgement_def ovalid_def ovalid_property_def)


lemma ovalid_wp_comb1[wp_comb]:
  "\<lbrakk> ovalid P' f Q; ovalid P f Q'; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> ovalid P f (\<lambda>r s. Q r s \<and> Q' r s)"
  by (simp add: ovalid_def)

lemma ovalid_wp_comb2[wp_comb]:
  "\<lbrakk> ovalid P f Q; \<And>s. P' s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> ovalid P' f Q"
  by (auto simp: ovalid_def)

lemma ovalid_wp_comb3[wp_comb]:
  "\<lbrakk> ovalid P f Q; ovalid P' f Q' \<rbrakk> \<Longrightarrow> ovalid (\<lambda>s. P s \<and> P' s) f (\<lambda>r s. Q r s \<and> Q' r s)"
  by (auto simp: ovalid_def)


(* WP rules for ovalidNF. *)
lemma obind_NF_wp[wp]:
  "\<lbrakk> \<And>r. ovalidNF (R r) (g r) Q; ovalidNF P f R \<rbrakk> \<Longrightarrow> ovalidNF P (obind f g) Q"
  by (auto simp: ovalidNF_def obind_def split: option.splits)

lemma oreturn_NF_wp[wp]:
  "ovalidNF (P x) (oreturn x) P"
  by (simp add: ovalidNF_def oreturn_def)

lemma ocondition_NF_wp[wp]:
  "\<lbrakk> ovalidNF L l Q; ovalidNF R r Q \<rbrakk>
   \<Longrightarrow> ovalidNF (\<lambda>s. if C s then L s else R s) (ocondition C l r) Q"
  by (simp add: ovalidNF_def ocondition_def)

lemma ofail_NF_wp[wp]:
  "ovalidNF (\<lambda>_. False) ofail Q"
  by (simp add: ovalidNF_def ofail_def)

lemma ogets_NF_wp[wp]:
  "ovalidNF (\<lambda>s. P (f s) s) (ogets f) P"
  by (simp add: ovalidNF_def ogets_def)

lemma oguard_NF_wp[wp]:
  "ovalidNF (\<lambda>s. f s \<and> P () s) (oguard f) P"
  by (simp add: ovalidNF_def oguard_def)

lemma oskip_NF_wp[wp]:
  "ovalidNF (\<lambda>s. P () s) oskip P"
  by (simp add: ovalidNF_def oskip_def)

lemma ovalid_NF_case_prod[wp]:
  assumes "(\<And>x y. ovalidNF (P x y) (B x y) Q)"
  shows "ovalidNF (case v of (x, y) \<Rightarrow> P x y) (case v of (x, y) \<Rightarrow> B x y) Q"
  using assms unfolding ovalidNF_def by auto

lemma owhile_NF[wp]:
  "\<lbrakk>\<And>a. ovalidNF (\<lambda>s. I a s \<and> C a s) (B a) I;
    \<And>a m. ovalid (\<lambda>s. I a s \<and> C a s \<and> M a s = m) (B a) (\<lambda>r s. M r s < m);
    \<And>a s. \<lbrakk>I a s; \<not> C a s\<rbrakk> \<Longrightarrow> Q a s\<rbrakk>
   \<Longrightarrow> ovalidNF (I a) (owhile_inv C B a I M) Q"
  unfolding owhile_inv_def ovalidNF_def ovalid_def
  apply clarify
  apply (rule owhile_rule[where I = I and M = "measure (\<lambda>r. M r s)" and s = s for s])
       apply fastforce
      apply fastforce
     apply fastforce
    apply blast+
  done

definition ovalidNF_property where
  "ovalidNF_property P x = (\<lambda>s f. (x s f \<noteq> None \<and> (\<forall>r. Some r = x s f \<longrightarrow> P r s)))"

lemma ovalidNF_is_triple[wp_trip]:
  "ovalidNF P f Q = triple_judgement P f (ovalidNF_property Q (\<lambda>s f. f s))"
  by (auto simp: triple_judgement_def ovalidNF_def ovalidNF_property_def)


lemma ovalidNF_wp_comb1[wp_comb]:
  "\<lbrakk> ovalidNF P' f Q; ovalidNF P f Q'; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> ovalidNF P f (\<lambda>r s. Q r s \<and> Q' r s)"
  by (simp add: ovalidNF_def)

lemma ovalidNF_wp_comb2[wp_comb]:
  "\<lbrakk> ovalidNF P f Q; \<And>s. P' s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> ovalidNF P' f Q"
  by (simp add: ovalidNF_def)

lemma ovalidNF_wp_comb3[wp_comb]:
  "\<lbrakk> ovalidNF P f Q; ovalidNF P' f Q' \<rbrakk> \<Longrightarrow> ovalidNF (\<lambda>s. P s \<and> P' s) f (\<lambda>r s. Q r s \<and> Q' r s)"
  by (simp add: ovalidNF_def)


(* FIXME: WP rules for no_ofail, which might not be correct. *)
lemma no_ofailD:
  "\<lbrakk> no_ofail P m; P s \<rbrakk> \<Longrightarrow> \<exists>y. m s = Some y"
  by (simp add: no_ofail_def)

lemma no_ofail_obind2[simp]:
  assumes f: "no_ofail P f"
  assumes v: "ovalid Q f R"
  assumes g: "\<And>r. no_ofail (R r) (g r)"
  shows "no_ofail (P and Q) (f |>> g)"
  using v g
  by (fastforce simp: no_ofail_def obind_def pred_conj_def ovalid_def dest: no_ofailD [OF f])

lemma no_ofail_ofail[wp]:
  "no_ofail \<bottom> ofail"
  by (simp add: no_ofail_def)

lemma no_ofail_ask[wp]:
  "no_ofail \<top> ask"
  by (simp add: no_ofail_def)

lemma no_ofail_asks_simp[simp]:
  "no_ofail P (asks f)"
  unfolding asks_def oreturn_def obind_def no_ofail_def
  by simp

lemma no_ofail_asks[wp]:
  "no_ofail \<top> (asks f)"
  by simp

lemma no_ofail_ogets[wp]:
  "no_ofail \<top> (ogets f)"
  by simp

lemma no_ofail_obind[wp]:
  "\<lbrakk> \<And>r. no_ofail (R r) (g r); \<lblot>Q\<rblot> f \<lblot>R\<rblot>; no_ofail P f \<rbrakk> \<Longrightarrow> no_ofail (P and Q) (f |>> g)"
  by (auto simp: no_ofail_def obind_def ovalid_def)

lemma no_ofail_oguard[wp]:
  "no_ofail (\<lambda>s. f s) (oguard f)"
  by (auto simp: no_ofail_def oguard_def)

lemma no_ofail_ocondition[wp]:
  "\<lbrakk> no_ofail L l; no_ofail R r \<rbrakk>
     \<Longrightarrow> no_ofail (\<lambda>s. if C s then L s else R s) (ocondition C l r)"
  by (simp add: no_ofail_def ocondition_def)

lemma no_ofail_oreturn[wp]:
  "no_ofail (\<lambda>_. True) (oreturn x)"
  by (simp add: no_ofail_def oreturn_def)

lemma no_ofail_oskip[wp]:
  "no_ofail (\<lambda>_. True) oskip"
  by (simp add: no_ofail_def oskip_def)

lemma no_ofail_oassert_opt[simp, wp]:
  "no_ofail (\<lambda>_. P \<noteq> None) (oassert_opt P)"
  by (simp add: no_ofail_def oassert_opt_def split: option.splits)

lemma no_ofail_if[wp]:
  "\<lbrakk> P \<Longrightarrow> no_ofail Q f; \<not> P \<Longrightarrow> no_ofail R g \<rbrakk>
   \<Longrightarrow> no_ofail (if P then Q else R) (if P then f else g)"
  by simp

lemma no_ofail_owhen[wp]:
  "(P \<Longrightarrow> no_ofail Q f) \<Longrightarrow> no_ofail (if P then Q else \<top>) (owhen P f)"
  by (simp add: no_ofail_def owhen_def)

lemma no_ofail_ounless[wp]:
  "(\<not>P \<Longrightarrow> no_ofail Q f) \<Longrightarrow> no_ofail (if P then \<top> else Q) (ounless P f)"
  by (simp add: no_ofail_def ounless_def)

lemma no_ofail_oassert[simp, wp]:
  "no_ofail (\<lambda>_. P) (oassert P)"
  by (simp add: oassert_def no_ofail_def)

lemma no_ofail_is_triple[wp_trip]:
  "no_ofail P f = triple_judgement P f (\<lambda>s f. f s \<noteq> None)"
  by (auto simp: triple_judgement_def no_ofail_def)

lemma no_ofail_wp_comb1[wp_comb]:
  "\<lbrakk> no_ofail P f; \<And>s. P' s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> no_ofail P' f"
  by (simp add: no_ofail_def)

lemma no_ofail_wp_comb2[wp_comb]:
  "\<lbrakk> no_ofail P f; no_ofail P' f \<rbrakk> \<Longrightarrow> no_ofail (\<lambda>s. P s \<and> P' s) f"
  by (simp add: no_ofail_def)


(* Some extra lemmas for our predicates. *)
lemma ovalid_grab_asm:
  "(G \<Longrightarrow> ovalid P f Q) \<Longrightarrow> ovalid (\<lambda>s. G \<and> P s) f Q"
  by (simp add: ovalid_def)

lemma ovalidNF_grab_asm:
  "(G \<Longrightarrow> ovalidNF P f Q) \<Longrightarrow> ovalidNF (\<lambda>s. G \<and> P s) f Q"
  by (simp add: ovalidNF_def)

lemma no_ofail_grab_asm:
  "(G \<Longrightarrow> no_ofail P f) \<Longrightarrow> no_ofail (\<lambda>s. G \<and> P s) f"
  by (simp add: no_ofail_def)

lemma ovalid_assume_pre:
  "(\<And>s. P s \<Longrightarrow> ovalid P f Q) \<Longrightarrow> ovalid P f Q"
  by (auto simp: ovalid_def)

lemma ovalidNF_assume_pre:
  "(\<And>s. P s \<Longrightarrow> ovalidNF P f Q) \<Longrightarrow> ovalidNF P f Q"
  by (simp add: ovalidNF_def)

lemma no_ofail_assume_pre:
  "(\<And>s. P s \<Longrightarrow> no_ofail P f) \<Longrightarrow> no_ofail P f"
  by (simp add: no_ofail_def)

lemma ovalid_pre_imp:
  "\<lbrakk> \<And>s. P' s \<Longrightarrow> P s; ovalid P f Q \<rbrakk> \<Longrightarrow> ovalid P' f Q"
  by (simp add: ovalid_def)

lemma ovalidNF_pre_imp:
  "\<lbrakk> \<And>s. P' s \<Longrightarrow> P s; ovalidNF P f Q \<rbrakk> \<Longrightarrow> ovalidNF P' f Q"
  by (simp add: ovalidNF_def)

lemma no_ofail_pre_imp[wp_pre]:
  "\<lbrakk> no_ofail P f; \<And>s. P' s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> no_ofail P' f"
  by (simp add: no_ofail_def)

lemma ovalid_post_imp:
  "\<lbrakk> \<And>r s. Q r s \<Longrightarrow> Q' r s; ovalid P f Q \<rbrakk> \<Longrightarrow> ovalid P f Q'"
  by (simp add: ovalid_def)

lemma ovalidNF_post_imp:
  "\<lbrakk> \<And>r s. Q r s \<Longrightarrow> Q' r s; ovalidNF P f Q \<rbrakk> \<Longrightarrow> ovalidNF P f Q'"
  by (simp add: ovalidNF_def)

lemma ovalid_post_imp_assuming_pre:
  "\<lbrakk> \<And>r s. \<lbrakk> P s; Q r s \<rbrakk> \<Longrightarrow> Q' r s; ovalid P f Q \<rbrakk> \<Longrightarrow> ovalid P f Q'"
  by (simp add: ovalid_def)

lemma ovalidNF_post_imp_assuming_pre:
  "\<lbrakk> \<And>r s. \<lbrakk> P s; Q r s \<rbrakk> \<Longrightarrow> Q' r s; ovalidNF P f Q \<rbrakk> \<Longrightarrow> ovalidNF P f Q'"
  by (simp add: ovalidNF_def)

end
