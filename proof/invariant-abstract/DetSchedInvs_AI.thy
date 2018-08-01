(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory DetSchedInvs_AI
imports "$L4V_ARCH/ArchDeterministic_AI"
begin

(* etcb fields used to be in a separate part of the state. A lot of the following development
   relies on this separation, so we emalate it here by projecting out those parts from tcbs *)
record etcb =
 etcb_priority :: "priority"
 etcb_domain :: "domain"

definition etcb_of :: "tcb \<Rightarrow> etcb"
  where
  "etcb_of t = \<lparr> etcb_priority = tcb_priority t, etcb_domain = tcb_domain t \<rparr>"

definition
  obj_at_kh :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "obj_at_kh P ref kh \<equiv> \<exists>ko. kh ref = Some ko \<and> P ko"

lemma obj_at_kh_simp[simp]: "obj_at_kh P ref (kheap st) = obj_at P ref st"
  apply (simp add: obj_at_def obj_at_kh_def)
  done


definition st_tcb_at_kh where
  "st_tcb_at_kh test \<equiv> obj_at_kh (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (tcb_state tcb))"

lemma st_tcb_at_kh_simp[simp]: "st_tcb_at_kh test t (kheap st) = st_tcb_at test t st"
  apply (simp add: pred_tcb_at_def st_tcb_at_kh_def)
  done

(* RT: extend obj_at_kh for tcb_sched_context *)
definition bound_sc_tcb_at_kh where
  "bound_sc_tcb_at_kh test \<equiv> obj_at_kh (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (tcb_sched_context tcb))"

lemma bound_sc_tcb_at_kh_simp[simp]: "bound_sc_tcb_at_kh test t (kheap st) = bound_sc_tcb_at test t st"
  apply (simp add: pred_tcb_at_def bound_sc_tcb_at_kh_def)
  done

definition
  etcbs_of':: "(obj_ref \<Rightarrow> kernel_object option) \<Rightarrow> obj_ref \<Rightarrow> etcb option"
where
  "etcbs_of' kh \<equiv> \<lambda>p. case kh p of Some (TCB t) \<Rightarrow> Some (etcb_of t) | _ \<Rightarrow> None"

abbreviation
  "etcbs_of \<equiv> \<lambda>s. etcbs_of' (kheap s)"

definition etcb_at' :: "(etcb \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<Rightarrow> etcb option) \<Rightarrow> bool" where
  "etcb_at' P ref ekh \<equiv> case ekh ref of Some x \<Rightarrow> P x | _ \<Rightarrow> True"

abbreviation etcb_at :: "(etcb \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "etcb_at P ref s \<equiv> etcb_at' P ref (etcbs_of s)"

lemmas etcb_at_def = etcb_at'_def

definition
  "is_etcb_at' t ekh \<equiv> ekh t \<noteq> None"

lemmas is_etcb_at_def = is_etcb_at'_def

lemma etcb_at_taut[simp]: "etcb_at' \<top> ref ekh"
  apply (simp add: etcb_at'_def split: option.split)
  done

lemma etcb_at_conj_is_etcb_at:
  "(is_etcb_at' t ekh \<and> etcb_at' P t ekh)
     = (case ekh t of None \<Rightarrow> False | Some x \<Rightarrow> P x)"
  by (simp add: is_etcb_at_def etcb_at_def split: option.splits)

definition
  valid_idle_etcb_2 :: "(obj_ref \<Rightarrow> etcb option) \<Rightarrow> bool"
where
  "valid_idle_etcb_2 ekh \<equiv> etcb_at' (\<lambda>etcb. etcb_domain etcb = default_domain) idle_thread_ptr ekh"

abbreviation valid_idle_etcb :: "'z state \<Rightarrow> bool" where
  "valid_idle_etcb s \<equiv> valid_idle_etcb_2 (etcbs_of s)"

lemmas valid_idle_etcb_def = valid_idle_etcb_2_def


definition not_queued_2 where
  "not_queued_2 qs t \<equiv> \<forall>d p. t \<notin> set (qs d p)"

abbreviation not_queued :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_queued t s \<equiv> not_queued_2 (ready_queues s) t"

definition valid_queues_2 where
  "valid_queues_2 queues kh \<equiv> (\<forall>d p.
     (\<forall>t \<in> set (queues d p). is_etcb_at' t (etcbs_of' kh)
                           \<and> etcb_at' (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d) t (etcbs_of' kh)
                           \<and> st_tcb_at_kh runnable t kh)
   \<and> distinct (queues d p))"

abbreviation valid_queues :: "'z state \<Rightarrow> bool" where
"valid_queues s \<equiv> valid_queues_2 (ready_queues s) (kheap s)"

lemmas valid_queues_def = valid_queues_2_def

lemma valid_queues_def2:
  "valid_queues_2 queues kh =
     (\<forall>d p. (\<forall>t \<in> set (queues d p).
              is_etcb_at' t (etcbs_of' kh) \<and>
              (case etcbs_of' kh t of None \<Rightarrow> False | Some x \<Rightarrow> etcb_priority x = p \<and> etcb_domain x = d) \<and>
              st_tcb_at_kh runnable t kh) \<and>
              distinct (queues d p))"
  by (clarsimp simp: valid_queues_def etcb_at_conj_is_etcb_at[symmetric])

definition valid_blocked_2 where
   "valid_blocked_2 queues kh sa ct \<equiv>
    (\<forall>t st. not_queued_2 queues t \<longrightarrow> st_tcb_at_kh ((=) st) t kh \<longrightarrow>
            t \<noteq> ct \<longrightarrow> sa \<noteq> switch_thread t \<longrightarrow> (\<not> active st))"

abbreviation valid_blocked :: "'z state \<Rightarrow> bool" where
 "valid_blocked s \<equiv> valid_blocked_2 (ready_queues s) (kheap s) (scheduler_action s) (cur_thread s)"

lemmas valid_blocked_def = valid_blocked_2_def

definition valid_blocked_except_2 where
   "valid_blocked_except_2 thread queues kh sa ct \<equiv>
    (\<forall>t st. t \<noteq> thread \<longrightarrow> not_queued_2 queues t \<longrightarrow> st_tcb_at_kh ((=) st) t kh \<longrightarrow>
            t \<noteq> ct \<longrightarrow> sa \<noteq> switch_thread t \<longrightarrow> (\<not> active st))"

abbreviation valid_blocked_except :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
 "valid_blocked_except t s \<equiv> valid_blocked_except_2 t (ready_queues s) (kheap s) (scheduler_action s) (cur_thread s)"

lemmas valid_blocked_except_def = valid_blocked_except_2_def

definition in_cur_domain_2 where
  "in_cur_domain_2 thread cdom ekh \<equiv> etcb_at' (\<lambda>t. etcb_domain t = cdom) thread ekh"

abbreviation in_cur_domain :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "in_cur_domain thread s \<equiv> in_cur_domain_2 thread (cur_domain s) (etcbs_of s)"

lemmas in_cur_domain_def = in_cur_domain_2_def

definition ct_in_cur_domain_2 where
  "ct_in_cur_domain_2 thread thread' sa cdom ekh \<equiv>
     sa = resume_cur_thread \<longrightarrow> thread = thread' \<or> in_cur_domain_2 thread cdom ekh"

abbreviation ct_in_cur_domain where
  "ct_in_cur_domain s \<equiv> ct_in_cur_domain_2 (cur_thread s) (idle_thread s) (scheduler_action s) (cur_domain s) (etcbs_of s)"

lemmas ct_in_cur_domain_def = ct_in_cur_domain_2_def

definition is_activatable_2 where
"is_activatable_2 thread sa kh \<equiv> sa = resume_cur_thread \<longrightarrow> st_tcb_at_kh activatable thread kh"

abbreviation is_activatable :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool"  where
"is_activatable thread s \<equiv> is_activatable_2 thread (scheduler_action s) (kheap s)"

lemmas is_activatable_def = is_activatable_2_def

definition weak_valid_sched_action_2' where
  "weak_valid_sched_action_2' sa ekh kh \<equiv>
    \<forall>t. sa = switch_thread t \<longrightarrow> st_tcb_at_kh runnable t kh"
(*
definition
  schedulable_tcb_at_kh :: "32 word \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "schedulable_tcb_at_kh t kh \<equiv>
   obj_at_kh (\<lambda>ko. \<exists>tcb. ko = TCB tcb
              \<and> (\<exists>scp. tcb_sched_context tcb = Some scp
                 \<and> obj_at_kh (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                                    \<and> sc_refill_max sc > 0) scp kh)) t kh"
*)
definition
  schedulable_tcb_at_kh :: "32 word \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "schedulable_tcb_at_kh t kh \<equiv>
    bound_sc_tcb_at_kh (\<lambda>ko. \<exists>scp. ko = Some scp
                 \<and> obj_at_kh (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                                    \<and> sc_refill_max sc > 0) scp kh) t kh"

definition
  schedulable_tcb_at :: "32 word \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "schedulable_tcb_at t \<equiv> (\<lambda>s.
    bound_sc_tcb_at (\<lambda>ko. \<exists>scp. ko = Some scp
                 \<and> obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                                    \<and> sc_refill_max sc > 0) scp s) t s)"

lemma schedulable_tcb_at_kh_simp[simp]:
  "schedulable_tcb_at_kh t (kheap s) = schedulable_tcb_at t s"
  by (clarsimp simp: schedulable_tcb_at_kh_def schedulable_tcb_at_def)

lemma dmo_schedulable_tcb_at [wp]:
  "\<lbrace>schedulable_tcb_at t\<rbrace> do_machine_op f \<lbrace>\<lambda>_. schedulable_tcb_at t\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: schedulable_tcb_at_def pred_tcb_at_def obj_at_def)
  done

lemma schedulable_tcb_at_set_object_no_change_tcb:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x;
    \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
     \<Longrightarrow> \<lbrace>schedulable_tcb_at t and ko_at (TCB tcb) tptr\<rbrace> set_object tptr (TCB (f tcb)) \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  apply (wpsimp simp: schedulable_tcb_at_def pred_tcb_at_def set_object_def)
  apply (clarsimp simp: obj_at_def)
  by (rule conjI; clarsimp; rule_tac x=scp in exI, clarsimp)

lemma schedulable_tcb_at_set_object_no_change_sc:
  "\<lbrakk>\<And>x. sc_refill_max (f x) = sc_refill_max x\<rbrakk>
     \<Longrightarrow> \<lbrace>schedulable_tcb_at t and ko_at (SchedContext sc n) tptr\<rbrace> set_object tptr (SchedContext (f sc) n) \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  apply (wpsimp simp: schedulable_tcb_at_def pred_tcb_at_def set_object_def)
  apply (clarsimp simp: obj_at_def)
  by (rule conjI; clarsimp; rule_tac x=scp in exI, clarsimp)

lemma schedulable_tcb_at_update_sched_context_no_change:
  "\<lbrakk>\<And>x. sc_refill_max (f x) = sc_refill_max x\<rbrakk>
     \<Longrightarrow> \<lbrace>schedulable_tcb_at t\<rbrace> update_sched_context scp f \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
  apply (clarsimp simp: schedulable_tcb_at_def update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: schedulable_tcb_at_def update_sched_context_def set_object_def wp: get_object_wp)
  apply (clarsimp simp: obj_at_def pred_tcb_at_def)
  apply (rule conjI; clarsimp)
  apply (rule_tac x=scpa in exI, clarsimp)
  done

lemma schedulable_tcb_at_thread_set_no_change:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x;
       \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
         \<Longrightarrow> \<lbrace>schedulable_tcb_at t\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv. schedulable_tcb_at t\<rbrace>"
   apply (clarsimp simp: thread_set_def)
    apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
    by (fastforce intro: schedulable_tcb_at_set_object_no_change_tcb)

definition weak_valid_sched_action_2 where
  "weak_valid_sched_action_2 sa kh release_q\<equiv>
    \<forall>t. sa = switch_thread t \<longrightarrow>
    st_tcb_at_kh runnable t kh \<and> (*bound_sc_tcb_at_kh bound t kh*)
    schedulable_tcb_at_kh t kh \<and> \<not> t \<in> set release_q"
(*
obj_at_kh (\<lambda>ko. \<exists>tcb. ko = TCB tcb
                      \<and> (\<exists>scp. tcb_sched_context tcb = Some scp
                             \<and> obj_at_kh (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
                                             \<and> sc_refill_max sc > 0) scp kh)) t kh*)

abbreviation weak_valid_sched_action:: "'z state \<Rightarrow> bool" where
  "weak_valid_sched_action s \<equiv> weak_valid_sched_action_2 (scheduler_action s) (kheap s) (release_queue s)"

lemmas weak_valid_sched_action_def = weak_valid_sched_action_2_def

definition switch_in_cur_domain_2 where
  "switch_in_cur_domain_2 sa ekh cdom \<equiv>
    \<forall>t. sa = switch_thread t \<longrightarrow> in_cur_domain_2 t cdom ekh"

abbreviation switch_in_cur_domain:: "'z state \<Rightarrow> bool" where
  "switch_in_cur_domain s \<equiv> switch_in_cur_domain_2 (scheduler_action s) (etcbs_of s) (cur_domain s)"

lemmas switch_in_cur_domain_def = switch_in_cur_domain_2_def

definition valid_sched_action_2 where
  "valid_sched_action_2 sa kh ct cdom rq\<equiv>
     is_activatable_2 ct sa kh \<and> weak_valid_sched_action_2 sa kh rq \<and> switch_in_cur_domain_2 sa (etcbs_of' kh) cdom"

abbreviation valid_sched_action :: "'z state \<Rightarrow> bool" where
  "valid_sched_action s \<equiv> valid_sched_action_2 (scheduler_action s) (kheap s) (cur_thread s) (cur_domain s) (release_queue s)"

lemmas valid_sched_action_def = valid_sched_action_2_def



abbreviation ct_not_queued where
  "ct_not_queued s \<equiv> not_queued (cur_thread s) s"

definition
  "ct_not_in_q_2 queues sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> not_queued_2 queues ct"

abbreviation ct_not_in_q :: "'z state \<Rightarrow> bool" where
  "ct_not_in_q s \<equiv> ct_not_in_q_2 (ready_queues s) (scheduler_action s) (cur_thread s)"

lemmas ct_not_in_q_def = ct_not_in_q_2_def

definition valid_sched_2 where
  "valid_sched_2 queues sa cdom kh ct it rq \<equiv>
    valid_queues_2 queues kh \<and> ct_not_in_q_2 queues sa ct \<and>
    valid_sched_action_2 sa kh ct cdom rq \<and> ct_in_cur_domain_2 ct it sa cdom (etcbs_of' kh) \<and>
    valid_blocked_2 queues kh sa ct \<and> valid_idle_etcb_2 (etcbs_of' kh)"

abbreviation valid_sched :: "'z state \<Rightarrow> bool" where
  "valid_sched s \<equiv>
    valid_sched_2 (ready_queues s) (scheduler_action s) (cur_domain s) (kheap s) (cur_thread s)
                  (idle_thread s) (release_queue s)"

lemmas valid_sched_def = valid_sched_2_def


definition not_cur_thread_2 :: "obj_ref \<Rightarrow> scheduler_action \<Rightarrow> obj_ref \<Rightarrow> bool" where
  "not_cur_thread_2 thread sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> thread \<noteq> ct"

abbreviation not_cur_thread :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_cur_thread thread s \<equiv> not_cur_thread_2 thread (scheduler_action s) (cur_thread s)"

lemmas not_cur_thread_def = not_cur_thread_2_def


definition simple_sched_action_2 :: "scheduler_action \<Rightarrow> bool" where
  "simple_sched_action_2 action \<equiv> (case action of switch_thread t \<Rightarrow> False | _ \<Rightarrow> True)"

abbreviation simple_sched_action :: "det_state \<Rightarrow> bool" where
  "simple_sched_action s \<equiv> simple_sched_action_2 (scheduler_action s)"

lemmas simple_sched_action_def = simple_sched_action_2_def


definition schact_is_rct :: "'z state \<Rightarrow> bool" where
  "schact_is_rct s \<equiv> scheduler_action s = resume_cur_thread"

lemma schact_is_rct[elim!]: "schact_is_rct s \<Longrightarrow> scheduler_action s = resume_cur_thread"
  apply (simp add: schact_is_rct_def)
  done

lemma schact_is_rct_simple[elim]: "schact_is_rct s \<Longrightarrow> simple_sched_action s"
  apply (simp add: simple_sched_action_def schact_is_rct_def)
  done

definition scheduler_act_not_2 where
"scheduler_act_not_2 sa t \<equiv> sa \<noteq> switch_thread t"


abbreviation scheduler_act_not :: "obj_ref \<Rightarrow> 'z state  \<Rightarrow> bool" where
"scheduler_act_not t s \<equiv> scheduler_act_not_2 (scheduler_action s) t"

abbreviation scheduler_act_sane :: "'z state \<Rightarrow> bool" where
"scheduler_act_sane s \<equiv> scheduler_act_not_2 (scheduler_action s) (cur_thread s)"


lemmas scheduler_act_sane_def = scheduler_act_not_2_def
lemmas scheduler_act_not_def = scheduler_act_not_2_def



lemmas ct_not_queued_lift = hoare_lift_Pf2[where f="cur_thread" and P="not_queued"]

lemmas sch_act_sane_lift = hoare_lift_Pf2[where f="cur_thread" and P="scheduler_act_not"]

lemmas not_queued_def = not_queued_2_def

lemma valid_queues_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
    shows "\<lbrace>valid_queues\<rbrace> f \<lbrace>\<lambda>rv. valid_queues\<rbrace>"
  apply (simp add: valid_queues_def)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. ready_queues s", OF _ c])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. etcbs_of s", OF _ b])
  apply (wp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift a)
  done

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
   apply (wp hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift static_imp_wp a)
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
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
    shows "\<lbrace>ct_in_cur_domain\<rbrace> f \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. etcbs_of s", OF _ a])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ b])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s", OF _ c])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", OF _ d])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. idle_thread s", OF _ e])
  apply wp
  done

lemma weak_valid_sched_action_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes b: "\<And>t. \<lbrace>\<lambda>s. schedulable_tcb_at t s\<rbrace> f \<lbrace>\<lambda>rv s. schedulable_tcb_at t s\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s)\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
    shows "\<lbrace>weak_valid_sched_action\<rbrace> f \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. release_queue s", OF _ d])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ c])
  apply (simp add: weak_valid_sched_action_def)
  apply (wp hoare_vcg_all_lift static_imp_wp a b)
  done

lemma switch_in_cur_domain_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. etcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at Q t s\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
    shows "\<lbrace>switch_in_cur_domain\<rbrace> f \<lbrace>\<lambda>rv. switch_in_cur_domain\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ b])
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_domain s", OF _ c])
  apply (simp add: switch_in_cur_domain_def in_cur_domain_def)
  apply (wp hoare_vcg_all_lift static_imp_wp a c)
  done

lemma valid_sched_action_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes a': "\<And>t. \<lbrace>\<lambda>s. schedulable_tcb_at t s\<rbrace> f \<lbrace>\<lambda>rv s. schedulable_tcb_at t s\<rbrace>"
  assumes b: "\<And>Q t. \<lbrace>\<lambda>s. etcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at Q t s\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes e: "\<And>Q. \<lbrace>\<lambda>s. Q (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. Q (cur_domain s)\<rbrace>"
  assumes f: "\<And>Q. \<lbrace>\<lambda>s. Q (release_queue s)\<rbrace> f \<lbrace>\<lambda>rv s. Q (release_queue s)\<rbrace>"
    shows "\<lbrace>valid_sched_action\<rbrace> f \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (rule hoare_lift_Pf[where f="\<lambda>s. cur_thread s", OF _ d])
  apply (simp add: valid_sched_action_def)
  apply (rule hoare_vcg_conj_lift)
   apply (rule hoare_lift_Pf[where f="\<lambda>s. scheduler_action s", OF _ c])
   apply (simp add: is_activatable_def)
   apply (wp weak_valid_sched_action_lift switch_in_cur_domain_lift static_imp_wp a a' b c d e f)+
  done

lemma valid_sched_lift:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes a': "\<And>t. \<lbrace>\<lambda>s. schedulable_tcb_at t s\<rbrace> f \<lbrace>\<lambda>rv s. schedulable_tcb_at t s\<rbrace>"
  assumes c: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s)\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
  assumes e: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s)\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s)\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
  assumes g: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes h: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes i: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  assumes j: "\<And>Q. \<lbrace>\<lambda>s. Q (release_queue s)\<rbrace> f \<lbrace>\<lambda>rv s. Q (release_queue s)\<rbrace>"
    shows "\<lbrace>valid_sched\<rbrace> f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  apply (wp valid_queues_lift ct_not_in_q_lift ct_in_cur_domain_lift
            valid_sched_action_lift valid_blocked_lift a a' c d e f g h i j hoare_vcg_conj_lift)
  done

end
