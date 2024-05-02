(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory DetSchedInvs_AI
imports ArchDeterministic_AI
begin

lemma get_etcb_rev:
  "ekheap s p = Some etcb \<Longrightarrow> get_etcb p s = Some etcb"
   by (clarsimp simp: get_etcb_def)

lemma get_etcb_SomeD: "get_etcb ptr s = Some v \<Longrightarrow> ekheap s ptr = Some v"
  apply (case_tac "ekheap s ptr", simp_all add: get_etcb_def)
  done

definition obj_at_kh where
"obj_at_kh P ref kh \<equiv> obj_at P ref ((undefined :: det_ext state)\<lparr>kheap := kh\<rparr>)"

lemma obj_at_kh_simp[simp]: "obj_at_kh P ref (kheap st) = obj_at P ref st"
  apply (simp add: obj_at_def obj_at_kh_def)
  done


definition st_tcb_at_kh where
"st_tcb_at_kh test \<equiv> obj_at_kh (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (tcb_state tcb))"

lemma st_tcb_at_kh_simp[simp]: "st_tcb_at_kh test t (kheap st) = st_tcb_at test t st"
  apply (simp add: pred_tcb_at_def st_tcb_at_kh_def)
  done


definition is_etcb_at' where
"is_etcb_at' ref ekh \<equiv> ekh ref \<noteq> None"

abbreviation is_etcb_at:: "obj_ref \<Rightarrow> det_ext state \<Rightarrow> bool" where
"is_etcb_at ref s \<equiv> is_etcb_at' ref (ekheap s)"

lemmas is_etcb_at_def = is_etcb_at'_def

definition etcb_at' :: "(etcb \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<Rightarrow> etcb option) \<Rightarrow> bool" where
"etcb_at' P ref ekh \<equiv> case ekh ref of Some x \<Rightarrow> P x | _ \<Rightarrow> True"

abbreviation etcb_at :: "(etcb \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> det_ext state \<Rightarrow> bool" where
"etcb_at P ref s \<equiv> etcb_at' P ref (ekheap s)"

lemmas etcb_at_def = etcb_at'_def

lemma etcb_at_taut[simp]: "etcb_at' \<top> ref ekh"
  apply (simp add: etcb_at'_def split: option.split)
  done

lemma etcb_at_conj_is_etcb_at:
  "(is_etcb_at' t ekh \<and> etcb_at' P t ekh)
     = (case ekh t of None \<Rightarrow> False | Some x \<Rightarrow> P x)"
  by (simp add: is_etcb_at_def etcb_at_def split: option.splits)

definition valid_etcbs_2 :: "(obj_ref \<Rightarrow> etcb option) \<Rightarrow> (obj_ref \<Rightarrow> kernel_object option) \<Rightarrow> bool"where
"valid_etcbs_2 ekh kh \<equiv> \<forall>ptr. (st_tcb_at_kh \<top> ptr kh) = (is_etcb_at' ptr ekh)"


abbreviation valid_etcbs :: "det_ext state \<Rightarrow> bool" where
"valid_etcbs s \<equiv> valid_etcbs_2 (ekheap s) (kheap s)"

lemmas valid_etcbs_def = valid_etcbs_2_def


definition
  valid_idle_etcb_2 :: "(obj_ref \<Rightarrow> etcb option) \<Rightarrow> bool"
where
  "valid_idle_etcb_2 ekh \<equiv> etcb_at' (\<lambda>etcb. tcb_domain etcb = default_domain) idle_thread_ptr ekh"

abbreviation valid_idle_etcb :: "det_ext state \<Rightarrow> bool" where
  "valid_idle_etcb s \<equiv> valid_idle_etcb_2 (ekheap s)"

lemmas valid_idle_etcb_def = valid_idle_etcb_2_def


definition not_queued_2 where
  "not_queued_2 qs t \<equiv> \<forall>d p. t \<notin> set (qs d p)"

abbreviation not_queued :: "obj_ref \<Rightarrow> det_ext state \<Rightarrow> bool" where
  "not_queued t s \<equiv> not_queued_2 (ready_queues s) t"

definition valid_queues_2 where
  "valid_queues_2 queues ekh kh \<equiv> (\<forall>d p.
     (\<forall>t \<in> set (queues d p). is_etcb_at' t ekh
                           \<and> etcb_at' (\<lambda>t. tcb_priority t = p \<and> tcb_domain t = d) t ekh
                           \<and> st_tcb_at_kh runnable t kh)
   \<and> distinct (queues d p))"

abbreviation valid_queues :: "det_ext state \<Rightarrow> bool" where
"valid_queues s \<equiv> valid_queues_2 (ready_queues s) (ekheap s) (kheap s)"

lemmas valid_queues_def = valid_queues_2_def

lemma valid_queues_def2:
  "valid_queues_2 queues ekh kh =
     (\<forall>d p. (\<forall>t \<in> set (queues d p).
              is_etcb_at' t ekh \<and>
              (case ekh t of None \<Rightarrow> False | Some x \<Rightarrow> tcb_priority x = p \<and> tcb_domain x = d) \<and>
              st_tcb_at_kh runnable t kh) \<and>
              distinct (queues d p))"
  by (clarsimp simp: valid_queues_def
                     conj_assoc[where P="is_etcb_at' t ekh \<and> (case ekh t of
                                           None \<Rightarrow> False |
                                           Some x \<Rightarrow> tcb_priority x = p \<and> tcb_domain x = d)"]
                     etcb_at_conj_is_etcb_at[symmetric])

definition valid_blocked_2 where
   "valid_blocked_2 queues kh sa ct \<equiv>
    (\<forall>t st. not_queued_2 queues t \<longrightarrow> st_tcb_at_kh ((=) st) t kh \<longrightarrow>
            t \<noteq> ct \<longrightarrow> sa \<noteq> switch_thread t \<longrightarrow> (\<not> active st))"

abbreviation valid_blocked :: "det_ext state \<Rightarrow> bool" where
 "valid_blocked s \<equiv> valid_blocked_2 (ready_queues s) (kheap s) (scheduler_action s) (cur_thread s)"

lemmas valid_blocked_def = valid_blocked_2_def

definition valid_blocked_except_2 where
   "valid_blocked_except_2 thread queues kh sa ct \<equiv>
    (\<forall>t st. t \<noteq> thread \<longrightarrow> not_queued_2 queues t \<longrightarrow> st_tcb_at_kh ((=) st) t kh \<longrightarrow>
            t \<noteq> ct \<longrightarrow> sa \<noteq> switch_thread t \<longrightarrow> (\<not> active st))"

abbreviation valid_blocked_except :: "obj_ref \<Rightarrow> det_ext state \<Rightarrow> bool" where
 "valid_blocked_except t s \<equiv> valid_blocked_except_2 t (ready_queues s) (kheap s) (scheduler_action s) (cur_thread s)"

lemmas valid_blocked_except_def = valid_blocked_except_2_def

lemma valid_blocked_except_cur_thread[simp]:
  "valid_blocked_except_2 (cur_thread s) queues kh sa (cur_thread s)
   = valid_blocked_2 queues kh sa (cur_thread s)"
  by (fastforce simp: valid_blocked_except_2_def valid_blocked_2_def)

definition in_cur_domain_2 where
  "in_cur_domain_2 thread cdom ekh \<equiv> etcb_at' (\<lambda>t. tcb_domain t = cdom) thread ekh"

abbreviation in_cur_domain :: "obj_ref \<Rightarrow> det_ext state \<Rightarrow> bool" where
  "in_cur_domain thread s \<equiv> in_cur_domain_2 thread (cur_domain s) (ekheap s)"

lemmas in_cur_domain_def = in_cur_domain_2_def

definition ct_in_cur_domain_2 where
  "ct_in_cur_domain_2 thread thread' sa cdom ekh \<equiv>
     sa = resume_cur_thread \<longrightarrow> thread = thread' \<or> in_cur_domain_2 thread cdom ekh"

abbreviation ct_in_cur_domain where
  "ct_in_cur_domain s \<equiv> ct_in_cur_domain_2 (cur_thread s) (idle_thread s) (scheduler_action s) (cur_domain s) (ekheap s)"

lemmas ct_in_cur_domain_def = ct_in_cur_domain_2_def

definition is_activatable_2 where
"is_activatable_2 thread sa kh \<equiv> sa = resume_cur_thread \<longrightarrow> st_tcb_at_kh activatable thread kh"

abbreviation is_activatable :: "obj_ref \<Rightarrow> det_ext state \<Rightarrow> bool"  where
"is_activatable thread s \<equiv> is_activatable_2 thread (scheduler_action s) (kheap s)"

lemmas is_activatable_def = is_activatable_2_def

definition weak_valid_sched_action_2 where
  "weak_valid_sched_action_2 sa ekh kh \<equiv>
    \<forall>t. sa = switch_thread t \<longrightarrow> st_tcb_at_kh runnable t kh"

abbreviation weak_valid_sched_action:: "det_ext state \<Rightarrow> bool" where
  "weak_valid_sched_action s \<equiv> weak_valid_sched_action_2 (scheduler_action s) (ekheap s) (kheap s)"

lemmas weak_valid_sched_action_def = weak_valid_sched_action_2_def

definition switch_in_cur_domain_2 where
  "switch_in_cur_domain_2 sa ekh cdom \<equiv>
    \<forall>t. sa = switch_thread t \<longrightarrow> in_cur_domain_2 t cdom ekh"

abbreviation switch_in_cur_domain:: "det_ext state \<Rightarrow> bool" where
  "switch_in_cur_domain s \<equiv> switch_in_cur_domain_2 (scheduler_action s) (ekheap s) (cur_domain s)"

lemmas switch_in_cur_domain_def = switch_in_cur_domain_2_def

definition valid_sched_action_2 where
  "valid_sched_action_2 sa ekh kh ct cdom \<equiv>
     is_activatable_2 ct sa kh \<and> weak_valid_sched_action_2 sa ekh kh \<and> switch_in_cur_domain_2 sa ekh cdom"

abbreviation valid_sched_action :: "det_ext state \<Rightarrow> bool" where
  "valid_sched_action s \<equiv> valid_sched_action_2 (scheduler_action s) (ekheap s) (kheap s) (cur_thread s) (cur_domain s)"

lemmas valid_sched_action_def = valid_sched_action_2_def



abbreviation ct_not_queued where
  "ct_not_queued s \<equiv> not_queued (cur_thread s) s"

definition
  "ct_not_in_q_2 queues sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> not_queued_2 queues ct"

abbreviation ct_not_in_q :: "det_ext state \<Rightarrow> bool" where
  "ct_not_in_q s \<equiv> ct_not_in_q_2 (ready_queues s) (scheduler_action s) (cur_thread s)"

lemmas ct_not_in_q_def = ct_not_in_q_2_def

definition valid_sched_2 where
  "valid_sched_2 queues ekh sa cdom kh ct it \<equiv>
      valid_etcbs_2 ekh kh \<and> valid_queues_2 queues ekh kh \<and> ct_not_in_q_2 queues sa ct \<and> valid_sched_action_2 sa ekh kh ct cdom \<and> ct_in_cur_domain_2 ct it sa cdom ekh \<and> valid_blocked_2 queues kh sa ct \<and> valid_idle_etcb_2 ekh"

abbreviation valid_sched :: "det_ext state \<Rightarrow> bool" where
  "valid_sched s \<equiv> valid_sched_2 (ready_queues s) (ekheap s) (scheduler_action s) (cur_domain s) (kheap s) (cur_thread s) (idle_thread s)"

lemmas valid_sched_def = valid_sched_2_def


abbreviation einvs :: "det_ext state \<Rightarrow> bool" where
  "einvs \<equiv> invs and valid_list and valid_sched"


definition not_cur_thread_2 :: "obj_ref \<Rightarrow> scheduler_action \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "not_cur_thread_2 thread sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> thread \<noteq> ct"

abbreviation not_cur_thread :: "obj_ref \<Rightarrow> det_ext state \<Rightarrow> bool" where
  "not_cur_thread thread s \<equiv> not_cur_thread_2 thread (scheduler_action s) (cur_thread s)"

lemmas not_cur_thread_def = not_cur_thread_2_def


definition simple_sched_action_2 :: "scheduler_action \<Rightarrow> bool" where
  "simple_sched_action_2 action \<equiv> (case action of switch_thread t \<Rightarrow> False | _ \<Rightarrow> True)"

abbreviation simple_sched_action :: "det_state \<Rightarrow> bool" where
  "simple_sched_action s \<equiv> simple_sched_action_2 (scheduler_action s)"

lemmas simple_sched_action_def = simple_sched_action_2_def


definition schact_is_rct :: "det_ext state \<Rightarrow> bool" where
  "schact_is_rct s \<equiv> scheduler_action s = resume_cur_thread"

lemma schact_is_rct[elim!]: "schact_is_rct s \<Longrightarrow> scheduler_action s = resume_cur_thread"
  apply (simp add: schact_is_rct_def)
  done

lemma schact_is_rct_simple[elim]: "schact_is_rct s \<Longrightarrow> simple_sched_action s"
  apply (simp add: simple_sched_action_def schact_is_rct_def)
  done

definition scheduler_act_not_2 where
"scheduler_act_not_2 sa t \<equiv> sa \<noteq> switch_thread t"


abbreviation scheduler_act_not :: "obj_ref \<Rightarrow> det_ext state  \<Rightarrow> bool" where
"scheduler_act_not t s \<equiv> scheduler_act_not_2 (scheduler_action s) t"

abbreviation scheduler_act_sane :: "det_ext state \<Rightarrow> bool" where
"scheduler_act_sane s \<equiv> scheduler_act_not_2 (scheduler_action s) (cur_thread s)"


lemmas scheduler_act_sane_def = scheduler_act_not_2_def
lemmas scheduler_act_not_def = scheduler_act_not_2_def



lemmas ct_not_queued_lift = hoare_lift_Pf2[where f="cur_thread" and P="not_queued"]

lemmas sch_act_sane_lift = hoare_lift_Pf2[where f="cur_thread" and P="scheduler_act_not"]

lemmas not_queued_def = not_queued_2_def


lemma valid_etcbs_lift:
  assumes a: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
    shows "\<lbrace>valid_etcbs\<rbrace> f \<lbrace>\<lambda>rv. valid_etcbs\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ekheap s", OF _ b])
  apply (simp add: valid_etcbs_def)
  apply (simp add: tcb_at_st_tcb_at[symmetric] tcb_at_typ)
  apply (wp hoare_vcg_all_lift a)
  done

lemma valid_queues_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
    shows "\<lbrace>valid_queues\<rbrace> f \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ekheap s", OF _ c])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ready_queues s", OF _ d])
  apply (simp add: valid_queues_def)
  apply (wp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift a)
  done

lemma valid_sched_valid_queues[elim!]:
  "valid_sched s \<Longrightarrow> valid_queues s"
  by (clarsimp simp: valid_sched_def)

lemma typ_at_st_tcb_at_lift:
  assumes typ_lift: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>r s. P (typ_at T p s)\<rbrace>"
  assumes st_lift: "\<And>P. \<lbrace>st_tcb_at P t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> st_tcb_at P t s\<rbrace> f \<lbrace>\<lambda>r s. \<not> st_tcb_at P t s\<rbrace>"

  apply (simp add: valid_def obj_at_def st_tcb_at_def)
  apply clarsimp
  apply (case_tac "kheap s t")
   apply (cut_tac P="\<lambda>x. \<not> x" and p=t and T="ATCB" in typ_lift)
   apply (simp add: valid_def obj_at_def)
   apply force
  apply (cut_tac P="\<lambda>x. x" and p=t and T="a_type aa" in typ_lift)
  apply (cut_tac P="\<lambda>t. \<not> P t" in st_lift)
  apply (simp add: valid_def obj_at_def st_tcb_at_def)
  apply (drule_tac x=s in spec)
  apply simp
  apply (drule_tac x="(a,b)" in bspec)
   apply simp
  apply simp
  apply (subgoal_tac "a_type aa = ATCB")
   apply (erule a_type_ATCBE)
   apply simp
   apply force
  apply simp
  done

lemma valid_blocked_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes t: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
    shows "\<lbrace>valid_blocked\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (rule hoare_pre)
   apply (wps c e d)
   apply (simp add: valid_blocked_def)
   apply (wp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift hoare_weak_lift_imp a)
   apply (rule hoare_convert_imp)
    apply (rule typ_at_st_tcb_at_lift)
     apply (wp a t)+
  apply (simp add: valid_blocked_def)
  done

lemma ct_not_in_q_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
    shows "\<lbrace>ct_not_in_q\<rbrace> f \<lbrace>\<lambda>rv. ct_not_in_q\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ a])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ready_queues s", OF _ b])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", OF _ c])
  apply wp
  done

lemma ct_in_cur_domain_lift:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
    shows "\<lbrace>ct_in_cur_domain\<rbrace> f \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ekheap s", OF _ a])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ b])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s", OF _ c])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", OF _ d])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. idle_thread s", OF _ e])
  apply wp
  done

lemma weak_valid_sched_action_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
    shows "\<lbrace>weak_valid_sched_action\<rbrace> f \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ c])
  apply (simp add: weak_valid_sched_action_def)
  apply (wp hoare_vcg_all_lift hoare_weak_lift_imp a)
  done

lemma switch_in_cur_domain_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. etcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at Q t s\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
    shows "\<lbrace>switch_in_cur_domain\<rbrace> f \<lbrace>\<lambda>rv. switch_in_cur_domain\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ b])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s", OF _ c])
  apply (simp add: switch_in_cur_domain_def in_cur_domain_def)
  apply (wp hoare_vcg_all_lift hoare_weak_lift_imp a c)
  done

lemma valid_sched_action_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes b: "\<And>Q t. \<lbrace>\<lambda>s. etcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at Q t s\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes e: "\<And>Q t. \<lbrace>\<lambda>s. Q (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. Q (cur_domain s)\<rbrace>"
    shows "\<lbrace>valid_sched_action\<rbrace> f \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", OF _ d])
  apply (simp add: valid_sched_action_def)
  apply (rule hoare_vcg_conj_lift)
   apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ c])
   apply (simp add: is_activatable_def)
   apply (wp weak_valid_sched_action_lift switch_in_cur_domain_lift hoare_weak_lift_imp a b c d e)+
  done

lemma valid_sched_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes b: "\<And>Q t. \<lbrace>\<lambda>s. etcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at Q t s\<rbrace>"
  assumes c: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (ekheap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ekheap s)\<rbrace>"
  assumes e: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
  assumes g: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes h: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes i: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
    shows "\<lbrace>valid_sched\<rbrace> f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  apply (wp valid_etcbs_lift valid_queues_lift ct_not_in_q_lift ct_in_cur_domain_lift
            valid_sched_action_lift valid_blocked_lift a b c d e f g h i hoare_vcg_conj_lift)
  done

lemma valid_sched_valid_etcbs[elim!]:
  "valid_sched s \<Longrightarrow> valid_etcbs s"
  by (clarsimp simp: valid_sched_def)

lemma valid_etcbs_tcb_etcb:
  "\<lbrakk> valid_etcbs s; kheap s ptr = Some (TCB tcb) \<rbrakk> \<Longrightarrow> \<exists>etcb. ekheap s ptr = Some etcb"
  by (force simp: valid_etcbs_def is_etcb_at_def st_tcb_at_def obj_at_def)

lemma valid_etcbs_get_tcb_get_etcb:
  "\<lbrakk> valid_etcbs s; get_tcb ptr s = Some tcb \<rbrakk> \<Longrightarrow> \<exists>etcb. get_etcb ptr s = Some etcb"
  apply (clarsimp simp: valid_etcbs_def st_tcb_at_def obj_at_def is_etcb_at_def get_etcb_def get_tcb_def
                  split: option.splits if_split)
  apply (erule_tac x=ptr in allE)
  apply (clarsimp simp: get_etcb_def split: option.splits kernel_object.splits)+
  done

lemma valid_etcbs_ko_etcb:
  "\<lbrakk> valid_etcbs s; kheap s ptr = Some ko \<rbrakk> \<Longrightarrow> \<exists>tcb. (ko = TCB tcb = (\<exists>etcb. ekheap s ptr = Some etcb))"
  apply (clarsimp simp: valid_etcbs_def st_tcb_at_def obj_at_def is_etcb_at_def)
  apply (erule_tac x="ptr" in allE)
  apply auto
  done

lemma ekheap_tcb_at:
  "\<lbrakk>ekheap s x = Some y; valid_etcbs s\<rbrakk> \<Longrightarrow> tcb_at x s"
  by (fastforce simp: valid_etcbs_def is_etcb_at_def st_tcb_at_def obj_at_def is_tcb_def)

lemma tcb_at_is_etcb_at:
  "\<lbrakk>tcb_at t s; valid_etcbs s\<rbrakk> \<Longrightarrow> is_etcb_at t s"
  by (simp add: valid_etcbs_def tcb_at_st_tcb_at)

lemma tcb_at_ekheap_dom:
  "\<lbrakk>tcb_at x s; valid_etcbs s\<rbrakk> \<Longrightarrow> (\<exists>etcb. ekheap s x = Some etcb)"
  by (auto simp: is_etcb_at_def dest: tcb_at_is_etcb_at)

lemma ekheap_kheap_dom:
  "\<lbrakk>ekheap s x = Some etcb; valid_etcbs s\<rbrakk>
    \<Longrightarrow> \<exists>tcb. kheap s x = Some (TCB tcb)"
  by (fastforce simp: valid_etcbs_def st_tcb_at_def obj_at_def is_etcb_at_def)

end
