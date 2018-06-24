(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory list_reverse_norm
imports "CParser.CTranslation" "$L4V_ARCH/imports/MachineWords"
begin

declare sep_conj_ac [simp add]
declare hrs_simps [simp add]

primrec
  list :: "machine_word typ_heap \<Rightarrow> machine_word list \<Rightarrow> machine_word ptr \<Rightarrow> bool"
where
  "list h [] i = (i = Ptr 0)"

| "list h (x#xs) i =
  (\<exists>j. ptr_val i = x \<and> x\<noteq>0 \<and> h i = Some j \<and> list h xs (Ptr j))"

lemma list_empty [simp]:
  "list h xs (Ptr 0) = (xs = [])"
  by (induct xs) auto

lemma list_ptr_aligned:
  "list (lift_t_c s) xs p \<Longrightarrow> ptr_aligned p"
  by (induct xs) (auto dest: lift_t_g c_guard_ptr_aligned)

lemma list_in [simp]:
  "\<And>p. \<lbrakk> list h xs p; p \<noteq> Ptr 0 \<rbrakk> \<Longrightarrow> ptr_val p \<in> set xs"
  by (induct xs) auto

lemma list_non_NULL:
  "ptr_val p \<noteq> 0 \<Longrightarrow>
  list h xs p = (\<exists>ys q. xs=ptr_val p#ys \<and> h p=Some q \<and> list h ys (Ptr q))"
  by (cases xs) auto

lemma list_unique:
  "\<And>ys p. list h xs p \<Longrightarrow> list h ys p \<Longrightarrow> xs = ys"
  by (induct xs) (auto simp add: list_non_NULL)

lemma list_append_Ex:
  "\<And>p ys. list h (xs@ys) p \<Longrightarrow> (\<exists>q. list h ys q)"
  by (induct xs) auto

lemma list_distinct [simp]:
  "\<And>p. list h xs p \<Longrightarrow> distinct xs"
  apply (induct xs)
   apply simp
  apply (clarsimp dest!: split_list)
  apply (frule list_append_Ex)
  apply (auto dest: list_unique)
  done

lemma in_list_Some:
  "\<And>p. \<lbrakk> list h xs p; ptr_val q \<in> set xs \<rbrakk> \<Longrightarrow> \<exists>x. h q = Some x"
  by (induct xs) auto

lemma in_list_valid [simp]:
  "\<lbrakk> list (lift_t_c (h,d)) xs p; ptr_val q \<in> set xs \<rbrakk>
  \<Longrightarrow> d \<Turnstile>\<^sub>t (q::machine_word ptr)"
  by (auto dest: in_list_Some simp: lift_t_if split: if_split_asm)

lemma list_restrict:
  "\<And>s S h. Ptr`set ps \<subseteq> S \<Longrightarrow> list (h|`S) ps s = list h ps s"
  by (induct ps) (auto simp: restrict_map_def)

lemma list_restrict_dom:
  "list (h|`(Ptr`set ps)) ps s = list h ps s"
  by (simp add: list_restrict)

lemma list_heapE:
  "\<lbrakk> list h xs p; h'|`(Ptr`set xs) = h|`(Ptr`set xs) \<rbrakk> \<Longrightarrow> list h' xs p"
  by (subst list_restrict_dom [symmetric]) (simp add: list_restrict_dom)

lemma list_heap_update_ignore [simp]:
  "ptr_val x \<notin> set xs \<Longrightarrow> list (h (x := Some v)) xs p = list h xs p"
  by (cases x) (auto elim: list_heapE)

declare typ_simps [simp]

external_file "list_reverse_norm.c"
install_C_file "list_reverse_norm.c"

lemma (in list_reverse_norm_global_addresses) reverse_correct:
  shows "reverse_spec"
apply (unfold reverse_spec_def)
apply (hoare_rule HoarePartial.ProcNoRec1)
apply (hoare_rule anno = "reverse_invs_body zs" in HoarePartial.annotateI)
 prefer 2
 apply (simp add: whileAnno_def reverse_invs_body_def)
apply (subst reverse_invs_body_def)
apply (fold lift_def)
apply vcg
  prefer 2
  apply (clarsimp simp del: distinct_rev)
  apply (case_tac xs, fastforce)
  apply (clarsimp simp: lift_t_g ucast_id)
  apply (rule_tac x=lista in exI)
  apply auto
done

end
