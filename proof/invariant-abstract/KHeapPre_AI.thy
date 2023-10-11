(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KHeapPre_AI
imports Machine_AI
begin

primrec
  same_caps :: "Structures_A.kernel_object \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
  "same_caps val (CNode sz cs)       = (val = CNode sz cs)"
| "same_caps val (TCB tcb)           = (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb))"
| "same_caps val (Endpoint ep)       = is_ep val"
| "same_caps val (Notification ntfn) = is_ntfn val"
| "same_caps val (SchedContext sc n) = (\<exists>sc'. val = SchedContext sc' n)"
| "same_caps val (Reply r)           = is_reply val"
| "same_caps val (ArchObj ao)        = (\<exists>ao'. val = ArchObj ao')"


lemma same_caps_more_simps[simp]:
 "same_caps (CNode sz cs) val       = (val = CNode sz cs)"
 "same_caps (TCB tcb)     val       = (\<exists>tcb'. val = TCB tcb'
                                         \<and> (\<forall>(getF, t) \<in> ran tcb_cap_cases. getF tcb' = getF tcb))"
 "same_caps (Endpoint ep) val       = is_ep val"
 "same_caps (Notification ntfn) val = is_ntfn val"
 "same_caps (SchedContext sc n) val   = (\<exists>sc'. val = SchedContext sc' n)"
 "same_caps (Reply r) val           = is_reply val"
 "same_caps (ArchObj ao) val        = (\<exists>ao'. val = ArchObj ao')"
 by (cases val, (fastforce simp: is_obj_defs)+)+

lemma dmo_return [simp]:
  "do_machine_op (return x) = return x"
  by (simp add: do_machine_op_def select_f_def return_def gets_def get_def
                bind_def modify_def put_def)

lemma get_object_sp:
  "\<lbrace>P\<rbrace> get_object p \<lbrace>\<lambda>r. P and ko_at r p\<rbrace>"
  apply (simp add: get_object_def gets_the_def read_object_def)
  apply wp
  apply (auto simp add: obj_at_def)
  done

definition non_arch_obj :: "kernel_object \<Rightarrow> bool" where
  "non_arch_obj \<equiv> \<lambda>ko. \<forall>ako. ko \<noteq> ArchObj ako"

lemma non_arch_objs[intro]:
  "non_arch_obj (Endpoint ep)"
  "non_arch_obj (SchedContext sc n)"
  "non_arch_obj (Reply reply)"
  "non_arch_obj (CNode sz cnode_contents)"
  "non_arch_obj (TCB tcb)"
  "non_arch_obj (Notification notification)"
  by (auto simp add: non_arch_obj_def)

definition arch_obj_pred :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> bool" where
  "arch_obj_pred P \<equiv>
    \<forall>ko ko'. non_arch_obj ko \<longrightarrow> non_arch_obj ko' \<longrightarrow>
      P ko = P ko'"

lemma arch_obj_predE:
  "\<lbrakk>arch_obj_pred P; non_arch_obj ko; non_arch_obj ko'\<rbrakk> \<Longrightarrow> P ko = P ko'"
  apply (unfold arch_obj_pred_def)
  apply (erule allE[where ?x="ko"])
  apply (erule allE[where ?x="ko'"])
  by blast

lemmas arch_obj_pred_defs = non_arch_obj_def arch_obj_pred_def

lemma arch_obj_pred_a_type[intro, simp]: "arch_obj_pred (\<lambda>ko. a_type ko = AArch T)"
  by (auto simp add: arch_obj_pred_defs a_type_def split: kernel_object.splits)

lemma
  arch_obj_pred_arch_obj_l[intro, simp]: "arch_obj_pred (\<lambda>ko. ArchObj ako = ko)" and
  arch_obj_pred_arch_obj_r[intro, simp]: "arch_obj_pred (\<lambda>ko. ko = ArchObj ako)"
  by (auto simp add: arch_obj_pred_defs)

lemma arch_obj_pred_fun_lift: "arch_obj_pred (\<lambda>ko. F (arch_obj_fun_lift P N ko))"
  by (simp add: arch_obj_pred_defs)

lemmas arch_obj_pred_fun_lift_id[simp]
  = arch_obj_pred_fun_lift[where F=id, simplified]

lemmas arch_obj_pred_fun_lift_k[intro]
  = arch_obj_pred_fun_lift[where F="K R" for R, simplified]

lemmas arch_obj_pred_fun_lift_el[simp]
  = arch_obj_pred_fun_lift[where F="\<lambda> S. x \<in> S" for x, simplified]

lemma arch_obj_pred_const_conjI[intro]:
  "arch_obj_pred P \<Longrightarrow>
    arch_obj_pred P' \<Longrightarrow>
    arch_obj_pred (\<lambda>ko. P ko \<and> P' ko)"
  apply (simp only: arch_obj_pred_def)
  apply blast
  done

lemma arch_obj_pred_fI:
  "(\<And>x. arch_obj_pred (P x)) \<Longrightarrow> arch_obj_pred (\<lambda>ko. f (\<lambda>x :: 'a :: type. P x ko))"
  apply (simp only: arch_obj_pred_def)
  apply (intro allI impI)
  apply (rule arg_cong[where f=f])
  by blast

declare
  arch_obj_pred_fI[where f=All, intro]
  arch_obj_pred_fI[where f=Ex, intro]

locale arch_only_obj_pred =
  fixes P :: "kernel_object \<Rightarrow> bool"
  assumes arch_only: "arch_obj_pred P"

lemma set_object_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p' s)\<rbrace>
  set_object p ko \<lbrace>\<lambda>rv s. P (typ_at T p' s)\<rbrace>"
  apply (simp add: set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: obj_at_def)
  done

lemma set_object_neg_ko:
  "\<lbrace>not ko_at ko' p' and K (p = p' \<longrightarrow> ko \<noteq> ko')\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_ s. \<not> ko_at ko' p' s\<rbrace>"
  apply (simp add: set_object_def get_object_def)
  apply wp
  apply (simp add: pred_neg_def obj_at_def)
  done

lemma get_tcb_SomeD: "get_tcb t s = Some v \<Longrightarrow> kheap s t = Some (TCB v)"
  apply (case_tac "kheap s t", simp_all add: get_tcb_def read_object_def)
  apply (case_tac a, simp_all)
  done

lemma get_tcb_read_object_Some:
  "get_tcb t s = Some tcb \<longleftrightarrow> read_object t s = Some (TCB tcb)"
  by (rule iffI;
      clarsimp simp: get_tcb_def split: option.splits kernel_object.split_asm)

lemma the_get_tcb_kheap_Some[simp]:
  "kheap s p = Some (TCB tcb) \<Longrightarrow> the (get_tcb p s) = tcb"
  by (clarsimp simp: get_tcb_def obind_def read_object_def)

lemma get_tcb_at: "tcb_at t s \<Longrightarrow> (\<exists>tcb. get_tcb t s = Some tcb)"
  by (simp add: tcb_at_def)

lemma typ_at_same_type:
  assumes "typ_at T p s" "a_type k = a_type ko" "kheap s p' = Some ko"
  shows "typ_at T p (s\<lparr>kheap := (kheap s)(p' \<mapsto> k)\<rparr>)"
  using assms
  by (clarsimp simp: obj_at_def)


lemma hoare_to_pure_kheap_upd:
  assumes hoare[rule_format]:
    "\<And>f. (\<And>P p T. \<lbrace>\<lambda>s. P (typ_at (AArch T) p s)\<rbrace>
      f \<lbrace>\<lambda>r s. P (typ_at (AArch T) p s)\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  assumes typ_eq: "a_type k = a_type ko"
  assumes valid: "P (s :: ('z :: state_ext) state)"
  assumes at: "ko_at ko p s"
  shows "P (s\<lparr>kheap := (kheap s)(p \<mapsto> k)\<rparr>)"
  apply (rule use_valid[where f="
      do
        s' <- get;
        assert (s' = s);
        (modify (\<lambda>s. s\<lparr>kheap := (kheap s)(p \<mapsto> k)\<rparr>));
        return undefined
      od", OF _ hoare valid])
  apply (fastforce simp add: simpler_modify_def get_def bind_def
                             assert_def return_def[abs_def] fail_def)[1]
  apply wp
  apply (insert typ_eq at)
  apply clarsimp
  apply (erule_tac P=P in rsubst)
  by (auto simp add: obj_at_def a_type_def split: kernel_object.splits if_splits)

lemma set_object_wp:
  "\<lbrace>\<lambda>s. Q (s\<lparr> kheap := (kheap s) (p \<mapsto> v)\<rparr>) \<rbrace> set_object p v \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (simp add: set_object_def get_object_def)
  apply wp
  apply blast
  done

lemma get_object_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at ko p s \<longrightarrow> Q ko s\<rbrace> get_object p \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: get_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def)
  done

lemma get_tcb_rev:
  "kheap s p = Some (TCB t)\<Longrightarrow> get_tcb p s = Some t"
  by (clarsimp simp:get_tcb_def read_object_def)

lemma get_tcb_obj_atE[elim!]:
  "\<lbrakk> get_tcb t s = Some tcb; get_tcb t s = Some tcb \<Longrightarrow> P (TCB tcb) \<rbrakk> \<Longrightarrow> obj_at P t s"
  by (clarsimp dest!: get_tcb_SomeD simp: obj_at_def)

lemma a_type_TCB[simp]:
  "a_type (TCB x) = ATCB"
  by (simp add: a_type_def)

(* FIXME: move *)
lemma hoare_strengthen_pre_via_assert_forward:
  assumes pos: "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>"
  assumes rel: "\<And>s. S s \<Longrightarrow> P s \<or> N s"
  assumes neg: "\<lbrace> N \<rbrace> f \<lbrace> \<bottom>\<bottom> \<rbrace>"
  shows "\<lbrace> S \<rbrace> f \<lbrace> Q \<rbrace>"
  apply (rule hoare_weaken_pre)
   apply (rule hoare_strengthen_post)
    apply (rule hoare_vcg_disj_lift[OF pos neg])
   apply simp
  apply (erule rel)
  done

lemma hoare_set_object_weaken_pre:
  assumes "\<lbrace>P\<rbrace> set_object p v \<lbrace>\<lambda>_. Q\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>ko. ko_at ko p s \<longrightarrow> (a_type v = a_type ko) \<longrightarrow> P s\<rbrace>
         set_object p v
         \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (rule hoare_strengthen_pre_via_assert_forward
                [OF assms, where N="\<lambda>s. \<forall>ko. ko_at ko p s \<longrightarrow> a_type ko \<noteq> a_type v"])
  apply fastforce
  apply (simp add: set_object_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (rule hoare_seq_ext[OF _ assert_sp])
  apply (fastforce intro: hoare_weaken_pre[OF hoare_pre_cont])
  done

lemmas set_object_wp_strong = hoare_set_object_weaken_pre[OF set_object_wp]

end
