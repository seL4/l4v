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

lemma st_tcb_at_kh_eq_commute:
  "st_tcb_at_kh ((=) x) a b = st_tcb_at_kh (\<lambda>y. y = x) a b"
  by (fastforce simp: st_tcb_at_kh_def obj_at_kh_def)

(* RT: extend obj_at_kh for tcb_sched_context *)
definition bound_sc_tcb_at_kh where
  "bound_sc_tcb_at_kh test \<equiv> obj_at_kh (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (tcb_sched_context tcb))"

lemma bound_sc_tcb_at_kh_simp[simp]: "bound_sc_tcb_at_kh test t (kheap st) = bound_sc_tcb_at test t st"
  apply (simp add: pred_tcb_at_def bound_sc_tcb_at_kh_def)
  done

definition bound_sc_ntfn_at_kh where
  "bound_sc_ntfn_at_kh test \<equiv> obj_at_kh (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> test (ntfn_sc ntfn))"

(* active_sc_tcb_at ::
      the thread has an initialised (sc_refill_max > 0) scheduling context *)
definition
  test_sc_refill_max_kh :: "obj_ref \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "test_sc_refill_max_kh sp kh \<equiv>
     case kh sp of
       Some (SchedContext sc _) \<Rightarrow> (sc_refill_max sc > 0)
     | _ \<Rightarrow> False"

lemma test_sc_refill_max_kh_simp[simp]:
  "test_sc_refill_max_kh scp (kheap s) = test_sc_refill_max scp s"
  by (clarsimp simp: test_sc_refill_max_def test_sc_refill_max_kh_def)

definition
  active_sc_tcb_at_kh :: "32 word \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "active_sc_tcb_at_kh t kh \<equiv>
    bound_sc_tcb_at_kh (\<lambda>ko. \<exists>scp. ko = Some scp \<and> test_sc_refill_max_kh scp kh) t kh"

definition
  active_sc_ntfn_at_kh :: "32 word \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "active_sc_ntfn_at_kh t kh \<equiv>
    bound_sc_ntfn_at_kh (\<lambda>ko. \<exists>scp. ko = Some scp \<and> test_sc_refill_max_kh scp kh) t kh"

abbreviation
  active_sc_ntfn_at :: "32 word \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "active_sc_ntfn_at t s \<equiv> active_sc_ntfn_at_kh t (kheap s)"

lemmas active_sc_ntfn_at_def = active_sc_ntfn_at_kh_def

definition
  active_sc_tcb_at :: "32 word \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "active_sc_tcb_at t \<equiv> (\<lambda>s.
    bound_sc_tcb_at (\<lambda>ko. \<exists>scp. ko = Some scp \<and> test_sc_refill_max scp s) t s)"

lemmas active_sc_tcb_at_defs
       = active_sc_tcb_at_def active_sc_tcb_at_kh_def test_sc_refill_max_kh_def
         test_sc_refill_max_def pred_tcb_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
         obj_at_def

lemma active_sc_tcb_at_kh_simp[simp]:
  "active_sc_tcb_at_kh t (kheap s) = active_sc_tcb_at t s"
  by (clarsimp simp: active_sc_tcb_at_defs)

lemma dmo_active_sc_tcb_at [wp]:
  "\<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: active_sc_tcb_at_def pred_tcb_at_def obj_at_def test_sc_refill_max_def)
  done

lemma active_sc_tcb_at_set_object_no_change_tcb:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x;
    \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
     \<Longrightarrow> \<lbrace>(\<lambda>s. P (active_sc_tcb_at t s)) and ko_at (TCB tcb) tptr\<rbrace>
             set_object tptr (TCB (f tcb)) \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (wpsimp simp: active_sc_tcb_at_def pred_tcb_at_def set_object_def)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: obj_at_def test_sc_refill_max_def split: option.splits if_splits)
  apply (intro conjI impI)
  by (rule_tac x=scp in exI, fastforce)+

lemma active_sc_tcb_at_set_object_no_change_sc:
  "\<lbrakk>\<And>x. sc_refill_max (f x) > 0 \<longleftrightarrow> sc_refill_max x > 0\<rbrakk>
     \<Longrightarrow> \<lbrace>(\<lambda>s. P (active_sc_tcb_at t s)) and ko_at (SchedContext sc n) scptr\<rbrace>
            set_object scptr (SchedContext (f sc) n) \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (wpsimp simp: active_sc_tcb_at_def pred_tcb_at_def set_object_def)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: obj_at_def test_sc_refill_max_def split: option.splits if_splits)
  by (intro conjI impI, fastforce+)

lemma active_sc_tcb_at_update_sched_context_no_change:
  "\<lbrakk>\<And>x. sc_refill_max (f x) > 0 \<longleftrightarrow> sc_refill_max x > 0\<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> update_sched_context scp f \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
  apply (clarsimp simp: update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: update_sched_context_def set_object_def wp: get_object_wp)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule iffI; clarsimp simp: active_sc_tcb_at_defs split: option.splits if_splits)
  by (intro conjI impI, fastforce+)

lemma active_sc_tcb_at_thread_set_no_change:
  "\<lbrakk>\<And>x. tcb_state (f x) = tcb_state x;
       \<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (active_sc_tcb_at t s)\<rbrace> thread_set f tptr  \<lbrace>\<lambda>_ s. P (active_sc_tcb_at t s)\<rbrace>"
   apply (clarsimp simp: thread_set_def)
    apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
    by (fastforce intro: active_sc_tcb_at_set_object_no_change_tcb)

lemma is_schedulable_opt_Some:
  "is_schedulable_opt t in_q s = Some X \<Longrightarrow>
          ((st_tcb_at runnable t s \<and> active_sc_tcb_at t s \<and> \<not> in_q) = X)"
  by (clarsimp simp: is_schedulable_opt_def pred_tcb_at_def active_sc_tcb_at_def obj_at_def
                  split: option.splits dest!: get_tcb_SomeD)

(* refill_ready & refill sufficient *)

definition is_refill_sufficient :: "obj_ref \<Rightarrow> time \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "is_refill_sufficient scp usage \<equiv>
      obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n \<and> sufficient_refills usage (sc_refills sc)) scp"

definition is_refill_ready :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "is_refill_ready scp \<equiv>
     (\<lambda>s. obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n
          \<and> (r_time (refill_hd sc)) \<le> (cur_time s) + kernelWCET_ticks) scp s)"

abbreviation
  budget_ready :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "budget_ready thread \<equiv>
    (\<lambda>s. bound_sc_tcb_at (\<lambda>ko. \<exists>scp. ko = Some scp \<and> is_refill_ready scp s) thread s)"

abbreviation
  budget_sufficient :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "budget_sufficient thread \<equiv>
    (\<lambda>s. bound_sc_tcb_at (\<lambda>ko. \<exists>scp. ko = Some scp \<and> is_refill_sufficient scp 0 s) thread s)"

definition refill_ready_kh :: "time \<Rightarrow> obj_ref \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "refill_ready_kh curtime scp kh \<equiv>
     case kh scp of
      Some (SchedContext sc _) \<Rightarrow> (r_time (refill_hd sc)) \<le> curtime + kernelWCET_ticks
    | _ \<Rightarrow> False"

abbreviation
  budget_ready_kh :: "time \<Rightarrow> obj_ref \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "budget_ready_kh curtime t kh \<equiv>
    bound_sc_tcb_at_kh (\<lambda>ko. \<exists>scp. ko = Some scp
                                \<and> refill_ready_kh curtime scp kh) t kh"

lemma refill_ready_kh_simp[simp]:
  "refill_ready_kh (cur_time s) scp (kheap s) = is_refill_ready  scp s"
  by (clarsimp simp: refill_ready_kh_def is_refill_ready_def obj_at_def
               split: option.splits kernel_object.splits)

lemma budget_ready_kh_simp[simp]:
  "budget_ready_kh (cur_time s) tptr (kheap s) = budget_ready tptr s"
  by (clarsimp simp: )

definition refill_sufficient_kh :: "obj_ref \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "refill_sufficient_kh scp kh \<equiv>
     case kh scp of
      Some (SchedContext sc _) \<Rightarrow> (sufficient_refills 0 (sc_refills sc))
    | _ \<Rightarrow> False"

abbreviation
  budget_sufficient_kh :: "obj_ref \<Rightarrow> (32 word \<Rightarrow> kernel_object option) \<Rightarrow> bool"
where
  "budget_sufficient_kh t kh \<equiv>
    bound_sc_tcb_at_kh (\<lambda>ko. \<exists>scp. ko = Some scp
                                \<and> refill_sufficient_kh scp kh) t kh"

lemma refill_sufficient_kh_simp[simp]:
  "refill_sufficient_kh scp (kheap s) = is_refill_sufficient scp 0 s"
  by (clarsimp simp: refill_sufficient_kh_def is_refill_sufficient_def obj_at_def
               split: option.splits kernel_object.splits)

lemma budget_sufficient_kh_simp[simp]:
  "budget_sufficient_kh tptr (kheap s) = budget_sufficient tptr s"
  by (clarsimp simp: )

lemmas budget_ready_defs
       = pred_tcb_at_def obj_at_def bound_sc_tcb_at_kh_def obj_at_kh_def
         refill_ready_kh_def is_refill_ready_def

lemmas budget_sufficient_defs
       = bound_sc_tcb_at_kh_def obj_at_kh_def pred_tcb_at_def obj_at_def
         refill_sufficient_kh_def is_refill_sufficient_def

lemmas refill_prop_defs = refill_sufficient_kh_def refill_ready_kh_def
                          is_refill_ready_def is_refill_sufficient_def

lemma is_refill_sufficient_machine_state_update[simp]:
  "is_refill_sufficient t u(s\<lparr>machine_state := param_a\<rparr>) = is_refill_sufficient t u s"
  by (clarsimp simp: is_refill_sufficient_def)

lemma is_refill_ready_machine_state_update[simp]:
  "is_refill_ready t (s\<lparr>machine_state := param_a\<rparr>) = is_refill_ready t s"
  by (clarsimp simp: is_refill_ready_def)

crunches do_machine_op
for is_refill_sufficient[wp]: "is_refill_sufficient t u"
and is_refill_ready[wp]: "is_refill_ready t"
and budget_ready[wp]: "\<lambda>s. P (budget_ready t s)"
and budget_sufficient[wp]: "\<lambda>s. P (budget_sufficient t s)"

lemma budget_ready_set_object_no_change_tcb:
  "\<lbrakk>\<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
     \<Longrightarrow> \<lbrace>(\<lambda>s. P (budget_ready t s)) and ko_at (TCB tcb) tptr\<rbrace>
    set_object tptr (TCB (f tcb)) \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (wpsimp simp: set_object_def pred_tcb_at_def obj_at_def)
  apply (rule conjI;
         clarsimp elim!: rsubst [where P=P] split: if_splits simp: is_refill_ready_def obj_at_def;
         rule iffI; clarsimp)
  by (rule_tac x=scp in exI, fastforce)+

lemma budget_sufficient_set_object_no_change_tcb:
  "\<lbrakk>\<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
     \<Longrightarrow> \<lbrace>(\<lambda>s. P (budget_sufficient t s)) and ko_at (TCB tcb) tptr\<rbrace>
    set_object tptr (TCB (f tcb)) \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  apply (wpsimp simp: set_object_def pred_tcb_at_def obj_at_def)
  apply (rule conjI;
         clarsimp elim!: rsubst [where P=P] split: if_splits simp: is_refill_sufficient_def obj_at_def;
         rule iffI; clarsimp)
  by (rule_tac x=scp in exI, fastforce)+

lemma budget_ready_set_object_no_change_sc:
  "\<lbrakk>\<And>x. sc_refills (f x) = sc_refills x\<rbrakk>
     \<Longrightarrow> \<lbrace>(\<lambda>s. P (budget_ready t s)) and ko_at (SchedContext sc n) tptr\<rbrace>
      set_object tptr (SchedContext (f sc) n) \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (wpsimp simp: pred_tcb_at_def set_object_def obj_at_def)
  apply (rule conjI; clarsimp elim!: rsubst [where P=P])
  apply (intro iffI; clarsimp simp: is_refill_ready_def obj_at_def split: if_split_asm)
  by (rule_tac x=scp in exI; fastforce)+

lemma budget_sufficient_set_object_no_change_sc:
  "\<lbrakk>\<And>x. sc_refills (f x) = sc_refills x\<rbrakk>
     \<Longrightarrow> \<lbrace>(\<lambda>s. P (budget_sufficient t s)) and ko_at (SchedContext sc n) tptr\<rbrace>
      set_object tptr (SchedContext (f sc) n) \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  apply (wpsimp simp: pred_tcb_at_def set_object_def obj_at_def)
  apply (rule conjI; clarsimp elim!: rsubst [where P=P])
  apply (intro iffI; clarsimp simp: is_refill_sufficient_def obj_at_def split: if_split_asm)
  by (rule_tac x=scp in exI; fastforce)+

lemma is_refill_ready_update_sched_context_no_change:
  "\<lbrakk>\<And>x. sc_refills (f x) = sc_refills x\<rbrakk>
     \<Longrightarrow> \<lbrace>is_refill_ready t\<rbrace> update_sched_context scp f \<lbrace>\<lambda>rv. is_refill_ready t\<rbrace>"
  apply (clarsimp simp: is_refill_ready_def update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: update_sched_context_def set_object_def wp: get_object_wp)
  by (clarsimp simp: obj_at_def pred_tcb_at_def test_sc_refill_max_def)

lemma is_refill_sufficient_update_sched_context_no_change:
  "\<lbrakk>\<And>x. sc_refills (f x) = sc_refills x\<rbrakk>
     \<Longrightarrow> \<lbrace>is_refill_sufficient t u\<rbrace> update_sched_context scp f \<lbrace>\<lambda>rv. is_refill_sufficient t u\<rbrace>"
  apply (clarsimp simp: is_refill_sufficient_def update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: update_sched_context_def set_object_def wp: get_object_wp)
  by (clarsimp simp: obj_at_def pred_tcb_at_def test_sc_refill_max_def)

lemma budget_ready_thread_set_no_change:
  "\<lbrakk>\<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
         \<Longrightarrow> \<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
   apply (clarsimp simp: thread_set_def)
    apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
    by (fastforce intro: budget_ready_set_object_no_change_tcb)

lemma budget_sufficient_thread_set_no_change:
  "\<lbrakk>\<And>x. tcb_sched_context (f x) = tcb_sched_context x\<rbrakk>
         \<Longrightarrow> \<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> thread_set f tptr \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
   apply (clarsimp simp: thread_set_def)
    apply (rule hoare_seq_ext[OF _ assert_get_tcb_ko'])
    by (fastforce intro: budget_sufficient_set_object_no_change_tcb)

lemma budget_sufficient_update_sched_context_no_change:
  "\<lbrakk>\<And>x. sc_refills (f x) = sc_refills x\<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (budget_sufficient t s)\<rbrace> update_sched_context scp f \<lbrace>\<lambda>rv s. P (budget_sufficient t s)\<rbrace>"
  apply (clarsimp simp:  update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: pred_tcb_at_def obj_at_def set_object_def wp: get_object_wp)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P])
  by (rule iffI conjI; fastforce simp: is_refill_sufficient_def obj_at_def split: if_split_asm)

lemma budget_ready_update_sched_context_no_change:
  "\<lbrakk>\<And>x. sc_refills (f x) = sc_refills x\<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P (budget_ready t s)\<rbrace> update_sched_context scp f \<lbrace>\<lambda>rv s. P (budget_ready t s)\<rbrace>"
  apply (clarsimp simp:  update_sched_context_def)
  apply (rule hoare_seq_ext[OF _ get_object_sp])
  apply (wpsimp simp: pred_tcb_at_def obj_at_def set_object_def wp: get_object_wp)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P])
  by (rule iffI conjI; fastforce simp: is_refill_ready_def obj_at_def split: if_split_asm)


(** etcbs_of **)

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
lemmas etcb_defs = etcbs_of'_def is_etcb_at'_def etcb_at'_def

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

definition in_queue_2 where
  "in_queue_2 qs t \<equiv> t \<in> set qs"

abbreviation in_release_q where
  "in_release_q t s \<equiv> in_queue_2 (release_queue s) t"

abbreviation in_ready_q where
  "in_ready_q t s \<equiv> \<exists>d p. in_queue_2 (ready_queues s d p) t"

lemmas in_release_q_def = in_queue_2_def
lemmas in_ready_q_def = in_queue_2_def

definition not_queued_2 where
  "not_queued_2 qs t \<equiv> \<forall>d p. \<not> in_queue_2 (qs d p) t" (* we could do without this *)

abbreviation not_queued :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_queued t s \<equiv> not_queued_2 (ready_queues s) t"
(* or alternatively:
  "not_queued t s \<equiv> \<forall>d p. \<not> in_queue_2 ((ready_queues s) d p) t"
  "not_queued t s \<equiv> \<not> in_ready_q t s"
*)

definition not_in_release_q_2 where
  "not_in_release_q_2 qs t \<equiv> \<not> in_queue_2 qs t" (* we could do without this *)

abbreviation not_in_release_q :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
  "not_in_release_q t s \<equiv> not_in_release_q_2 (release_queue s) t"

lemmas not_queued_def = not_queued_2_def[simplified in_queue_2_def]
lemmas not_in_release_q_def = not_in_release_q_2_def[simplified in_queue_2_def]

lemma not_in_release_q_simp[iff]: "\<not> in_release_q t s \<longleftrightarrow> not_in_release_q t s"
  by (clarsimp simp: in_release_q_def not_in_release_q_def)

lemma not_in_ready_q_simp[iff]: "\<not> in_ready_q t s \<longleftrightarrow> not_queued t s"
  by (clarsimp simp: in_ready_q_def not_queued_def)

definition valid_ready_qs_2 where
  "valid_ready_qs_2 queues curtime kh \<equiv> (\<forall>d p.
     (\<forall>t \<in> set (queues d p). etcb_at' (\<lambda>t. etcb_priority t = p \<and> etcb_domain t = d) t (etcbs_of' kh)
                           \<and> st_tcb_at_kh runnable t kh \<and> active_sc_tcb_at_kh t kh
                           \<and> budget_sufficient_kh t kh \<and> budget_ready_kh curtime t kh)
   \<and> distinct (queues d p))"

abbreviation valid_ready_qs :: "'z state \<Rightarrow> bool" where
"valid_ready_qs s \<equiv> valid_ready_qs_2 (ready_queues s) (cur_time s) (kheap s)"

lemmas valid_ready_qs_def = valid_ready_qs_2_def

lemma valid_ready_qs_def2:
  "valid_ready_qs_2 queues curtime kh =
   (\<forall>d p. (\<forall>t \<in> set (queues d p).
           (case etcbs_of' kh t of None \<Rightarrow> False | Some x \<Rightarrow> etcb_priority x = p \<and> etcb_domain x = d) \<and>
           st_tcb_at_kh runnable t kh \<and>
           active_sc_tcb_at_kh t kh \<and> budget_sufficient_kh t kh \<and> budget_ready_kh curtime t kh)
          \<and> distinct (queues d p))"
  apply (clarsimp simp: valid_ready_qs_def etcb_at_conj_is_etcb_at[symmetric])
  apply (fastforce simp: is_etcb_at'_def etcbs_of'_def st_tcb_at_kh_def obj_at_kh_def)
  done

definition valid_release_q_2 where
  "valid_release_q_2 queue kh =
   ((\<forall>t \<in> set queue. st_tcb_at_kh runnable t kh \<and> active_sc_tcb_at_kh t kh)
    \<and> distinct queue)"

abbreviation valid_release_q :: "'z state \<Rightarrow> bool" where
"valid_release_q s \<equiv> valid_release_q_2 (release_queue s) (kheap s)"

lemmas valid_release_q_def = valid_release_q_2_def

definition valid_release_q_except_set_2 where
   "valid_release_q_except_set_2 S queue kh \<equiv>
    ((\<forall>t \<in> set queue - S.
              st_tcb_at_kh runnable t kh \<and> active_sc_tcb_at_kh t kh)
              \<and> distinct queue)"

abbreviation valid_release_q_except_set :: "obj_ref set \<Rightarrow> 'z state \<Rightarrow> bool" where
 "valid_release_q_except_set S s \<equiv> valid_release_q_except_set_2 S (release_queue s) (kheap s)"

abbreviation valid_release_q_except :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
"valid_release_q_except t s \<equiv> valid_release_q_except_set_2 {t} (release_queue s) (kheap s)"

lemmas valid_release_q_except_set_def = valid_release_q_except_set_2_def
lemmas valid_release_q_except_def = valid_release_q_except_set_2_def

lemma valid_release_q_distinct[elim!]: "valid_release_q s \<Longrightarrow> distinct (release_queue s)"
  by (clarsimp simp: valid_release_q_def)

definition schedulable_ep_thread_2 where
  "schedulable_ep_thread_2 ep t ct it curtime kh =
       (st_tcb_at_kh (\<lambda>ts. case ep of RecvEP _ \<Rightarrow> \<exists>eptr r_opt. ts = BlockedOnReceive eptr r_opt
                                     | _ \<Rightarrow> \<exists>eptr pl. ts = BlockedOnSend eptr pl) t kh \<and>
          t \<noteq> ct \<and> t \<noteq> it \<and>
         (bound_sc_tcb_at_kh ((=) None) t kh \<or>
        active_sc_tcb_at_kh t kh \<and> budget_sufficient_kh t kh \<and> budget_ready_kh curtime t kh))"

primrec ep_queue :: "endpoint \<Rightarrow> obj_ref list" where
  "ep_queue IdleEP = []"
| "ep_queue (SendEP list) = list"
| "ep_queue (RecvEP list) = list"

definition schedulable_ep_q_2 where
  "schedulable_ep_q_2 epptr ct it curtime kh =
       (case kh epptr of Some (Endpoint ep) \<Rightarrow>
              (\<forall>t\<in>set (ep_queue ep). schedulable_ep_thread_2 ep t ct it curtime kh)
           | _ \<Rightarrow> True)"

abbreviation schedulable_ep_q :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "schedulable_ep_q eptr s \<equiv> schedulable_ep_q_2 eptr (cur_thread s) (idle_thread s) (cur_time s) (kheap s)"
(* do we really want to add this to valid_sched? do we want to talk about all the endpointers? *)

(* does this work? *)
definition valid_ep_q_2 where
  "valid_ep_q_2  ct it curtime kh =
       (\<forall>p. case kh p of Some (Endpoint ep) \<Rightarrow>
              (\<forall>t\<in>set (ep_queue ep). schedulable_ep_thread_2 ep t ct it curtime kh)
           | _ \<Rightarrow> True)"

abbreviation valid_ep_q :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_ep_q s \<equiv> valid_ep_q_2 (cur_thread s) (idle_thread s) (cur_time s) (kheap s)"
(* do we really want to add this to valid_sched? do we want to talk about all the endpointers? *)

lemmas valid_ep_q_def = valid_ep_q_2_def[simplified schedulable_ep_thread_2_def]

(*** valid_ntfn_q ***)

abbreviation has_budget_kh where
  "has_budget_kh t curtime kh \<equiv>
   bound_sc_tcb_at_kh ((=) None) t kh \<or>
   (active_sc_tcb_at_kh t kh \<and> budget_sufficient_kh t kh \<and> budget_ready_kh curtime t kh)"

primrec ntfn_waiting_queue :: "ntfn \<Rightarrow> obj_ref list" where
  "ntfn_waiting_queue IdleNtfn = []"
| "ntfn_waiting_queue (WaitingNtfn list) = list"
| "ntfn_waiting_queue (ActiveNtfn _) = []"

definition valid_ntfn_q_2 where
  "valid_ntfn_q_2 ct it curtime kh =
   (\<forall>p. case kh p of
        Some (Notification n) \<Rightarrow> (\<forall>t \<in> set (ntfn_waiting_queue (ntfn_obj n)). t \<noteq> ct \<and> t \<noteq> it \<and> has_budget_kh t curtime kh)
        | _ \<Rightarrow> True)"

abbreviation valid_ntfn_q :: "'z state \<Rightarrow> bool" where
  "valid_ntfn_q s \<equiv> valid_ntfn_q_2 (cur_thread s) (idle_thread s) (cur_time s) (kheap s)"

lemmas valid_ntfn_q_def = valid_ntfn_q_2_def

lemma bound_sc_maybe_active[simp]:
  "bound_sc_tcb_at bound t s \<Longrightarrow>
    (bound_sc_tcb_at ((=) None) t s \<or>
        active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s)
     = (active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s)"
  by (auto simp: pred_tcb_at_def obj_at_def)

lemma no_sc_no_active[simp]:
  "bound_sc_tcb_at ((=) None) t s \<Longrightarrow>
    (bound_sc_tcb_at ((=) None) t s \<or>
        active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s)
     = True"
  by auto

definition valid_blocked_2 where
   "valid_blocked_2 queues rlq kh sa ct \<equiv>
    (\<forall>t st. not_queued_2 queues t \<longrightarrow> not_in_release_q_2 rlq t \<longrightarrow> st_tcb_at_kh ((=) st) t kh \<longrightarrow>
            t \<noteq> ct \<longrightarrow> sa \<noteq> switch_thread t \<longrightarrow>
             (\<not> (active st \<and> active_sc_tcb_at_kh t kh)))"

abbreviation valid_blocked :: "'z state \<Rightarrow> bool" where
 "valid_blocked s \<equiv> valid_blocked_2 (ready_queues s) (release_queue s) (kheap s) (scheduler_action s) (cur_thread s)"

lemmas valid_blocked_def = valid_blocked_2_def

definition valid_blocked_except_set_2 where
   "valid_blocked_except_set_2 S queues rlq kh sa ct \<equiv>
    (\<forall>t st. t \<notin> S \<longrightarrow> not_queued_2 queues t \<longrightarrow> not_in_release_q_2 rlq t \<longrightarrow>
           st_tcb_at_kh ((=) st) t kh \<longrightarrow>
            t \<noteq> ct \<longrightarrow> sa \<noteq> switch_thread t \<longrightarrow> (\<not> active st \<or> \<not> active_sc_tcb_at_kh t kh))"

abbreviation valid_blocked_except_set :: "obj_ref set \<Rightarrow> 'z state \<Rightarrow> bool" where
 "valid_blocked_except_set S s \<equiv> valid_blocked_except_set_2 S (ready_queues s) (release_queue s) (kheap s) (scheduler_action s) (cur_thread s)"

abbreviation valid_blocked_except :: "obj_ref \<Rightarrow> 'z state \<Rightarrow> bool" where
"valid_blocked_except t s \<equiv> valid_blocked_except_set_2 {t} (ready_queues s) (release_queue s) (kheap s) (scheduler_action s) (cur_thread s)"

lemmas valid_blocked_except_set_def = valid_blocked_except_set_2_def
lemmas valid_blocked_except_def = valid_blocked_except_set_2_def

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

definition weak_valid_sched_action_2 where
  "weak_valid_sched_action_2 sa kh release_q\<equiv>
    \<forall>t. sa = switch_thread t \<longrightarrow>
    st_tcb_at_kh runnable t kh \<and>
    active_sc_tcb_at_kh t kh \<and> \<not> t \<in> set release_q"

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

abbreviation ct_not_in_release_q where
  "ct_not_in_release_q s \<equiv> not_in_release_q (cur_thread s) s"

definition
  "ct_not_in_q_2 queues sa ct \<equiv> sa = resume_cur_thread \<longrightarrow> not_queued_2 queues ct"

abbreviation ct_not_in_q :: "'z state \<Rightarrow> bool" where
  "ct_not_in_q s \<equiv> ct_not_in_q_2 (ready_queues s) (scheduler_action s) (cur_thread s)"

lemmas ct_not_in_q_def = ct_not_in_q_2_def

definition valid_sched_2 where
  "valid_sched_2 queues sa cdom ctime kh ct it rq \<equiv>
    valid_ready_qs_2 queues ctime kh \<and> valid_release_q_2 rq kh \<and> ct_not_in_q_2 queues sa ct \<and>
    valid_sched_action_2 sa kh ct cdom rq \<and> ct_in_cur_domain_2 ct it sa cdom (etcbs_of' kh) \<and>
    valid_blocked_2 queues rq kh sa ct \<and> valid_idle_etcb_2 (etcbs_of' kh)"

abbreviation valid_sched :: "'z state \<Rightarrow> bool" where
  "valid_sched s \<equiv>
    valid_sched_2 (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s) (kheap s) (cur_thread s)
                  (idle_thread s) (release_queue s)"

lemmas valid_sched_def = valid_sched_2_def

lemma valid_sched_valid_blocked:
  "valid_sched s \<Longrightarrow> valid_blocked s" by (clarsimp simp: valid_sched_def)

lemma valid_sched_valid_ready_qs:
  "valid_sched s \<Longrightarrow> valid_ready_qs s" by (clarsimp simp: valid_sched_def)

lemma valid_sched_valid_release_q:
  "valid_sched s \<Longrightarrow> valid_release_q s" by (clarsimp simp: valid_sched_def)

lemma valid_sched_valid_sched_action:
  "valid_sched s \<Longrightarrow> valid_sched_action s" by (simp add: valid_sched_def)

lemma valid_sched_weak_valid_sched_action:
  "valid_sched s \<Longrightarrow> weak_valid_sched_action s" by (simp add: valid_sched_def valid_sched_action_def)

lemma valid_sched_ct_in_cur_domain:
  "valid_sched s \<Longrightarrow> ct_in_cur_domain s" by (simp add: valid_sched_def)


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

definition valid_reply_scs where
  "valid_reply_scs \<equiv> \<lambda>s. (\<forall>a r. reply_tcb_reply_at (\<lambda>ropt. ropt = Some a) r s
                               \<longrightarrow> (bound_sc_tcb_at (\<lambda>a. a = None) a s \<or> active_sc_tcb_at a s)) \<and>
                         (\<forall>scptr r. reply_sc_reply_at (\<lambda>scopt. scopt = Some scptr) r s
                               \<longrightarrow> test_sc_refill_max scptr s)"

definition
  ready_or_released :: "'z state  \<Rightarrow> bool"
where
  "ready_or_released s \<equiv> \<forall>t d p. \<not> (t \<in> set (ready_queues s d p) \<and> t \<in> set (release_queue s))"

lemma ready_or_released_in_ready_qs[intro]:
  "ready_or_released s \<Longrightarrow> in_ready_q t s \<Longrightarrow> not_in_release_q t s"
  by (clarsimp simp: ready_or_released_def in_ready_q_def not_in_release_q_def)

lemma ready_or_released_in_release_queue[intro]:
  "ready_or_released s \<Longrightarrow> in_release_queue t s \<Longrightarrow> not_queued t s"
  by (fastforce simp: ready_or_released_def in_release_queue_def not_queued_def)

lemma valid_blocked_except_set_empty:
  "valid_blocked_except_set {} = valid_blocked"
  by (clarsimp simp: valid_blocked_except_set_def valid_blocked_def)

lemma BlockedOnReceive_reply_tcb_reply_at:
  "st_tcb_at ((=) (BlockedOnReceive epptr (Some rptr))) tptr s
   \<Longrightarrow> sym_refs (state_refs_of s) \<Longrightarrow> valid_objs s
   \<Longrightarrow> reply_tcb_reply_at (\<lambda>x. x = Some tptr) rptr s"
  apply (subgoal_tac "reply_at rptr s")
  apply (clarsimp simp: pred_tcb_at_eq_commute)
  apply (subgoal_tac "(tptr, ReplyTCB) \<in> (state_refs_of s) rptr")
  apply (clarsimp simp: state_refs_of_def  get_refs_def reply_tcb_reply_at_def
                        pred_tcb_at_def obj_at_def refs_of_def is_reply
                 split: option.splits)
  apply (erule sym_refsE)
  apply (clarsimp simp: state_refs_of_def pred_tcb_at_def obj_at_def)
  apply (clarsimp dest!: st_tcb_at_valid_st2 simp: valid_tcb_state_def)
  done

lemma valid_blocked_except_set_subset:
  "T \<subseteq> S \<Longrightarrow>
   valid_blocked_except_set T s \<Longrightarrow>
   valid_blocked_except_set S s"
  by (fastforce simp: valid_blocked_except_set_def)

lemma valid_blocked_except_set_weaken:
  "valid_blocked s \<Longrightarrow>
   valid_blocked_except_set S s"
  by (rule valid_blocked_except_set_subset[where T="{}"];
      clarsimp simp: fun_cong[OF valid_blocked_except_set_empty])

lemma valid_blocked_except_set_cur_thread:
  "valid_blocked_except_set {cur_thread s} s = valid_blocked s"
   by (auto simp: valid_blocked_except_set_def valid_blocked_def)

lemma valid_blocked_except_set_not_runnable:
  "valid_blocked_except_set {t} s \<Longrightarrow> st_tcb_at (\<lambda>st. \<not> runnable st) t s  \<Longrightarrow> valid_blocked s"
   apply (auto simp: valid_blocked_except_set_def valid_blocked_def pred_tcb_at_def obj_at_def)
   apply (case_tac "ta=t")
   apply (drule_tac x=ta in spec; simp)+
   done

(* simple_ko update *)

lemma st_tcb_at_simple_type_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      st_tcb_at_kh P t (kheap s(epptr \<mapsto> ko)) = st_tcb_at_kh P t (kheap s)"
  by (rule iffI;
      clarsimp simp: pred_tcb_at_def obj_at_def st_tcb_at_kh_def obj_at_kh_def
      split: option.splits if_splits)

lemma active_sc_tcb_at_simple_type_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      active_sc_tcb_at_kh t (kheap s(epptr \<mapsto> ko)) = active_sc_tcb_at t s"
  by (fastforce simp: active_sc_tcb_at_defs split: option.splits if_splits)

lemma budget_sufficient_simple_type_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      budget_sufficient_kh t (kheap s(epptr \<mapsto> ko)) = budget_sufficient t s"
 by (clarsimp simp: obj_at_def a_type_def; rename_tac ko2; case_tac ko2; cases ko;
        fastforce split: option.splits if_splits kernel_object.splits
                   simp: refill_prop_defs active_sc_tcb_at_defs)+

lemma budget_ready_simple_type_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      budget_ready_kh (cur_time s) t (kheap s(epptr \<mapsto> ko)) = budget_ready t s"
 by (clarsimp simp: obj_at_def a_type_def; rename_tac ko2; case_tac ko2; cases ko;
        fastforce split: option.splits if_splits kernel_object.splits
                   simp: refill_prop_defs active_sc_tcb_at_defs)+

lemma etcbs_of'_simple_type_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      etcbs_of' (kheap s(epptr \<mapsto> ko)) = etcbs_of' (kheap s)"
  by (rule ext; fastforce simp: obj_at_def etcbs_of'_def split: option.splits if_splits)


lemma valid_ready_qs_simple_type_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     valid_ready_qs_2 (ready_queues s) (cur_time s) (kheap s(epptr \<mapsto> ko)) = valid_ready_qs s"
  by (clarsimp simp: valid_ready_qs_def)
   (* I would prefer to write the LHS as
      "valid_ready_qs (s\<lparr>kheap := kheap s(epptr \<mapsto> Endpoint ep)\<rparr>)"
      but that makes the lemma less usable *)

lemma valid_release_q_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     valid_release_q_2 (release_queue s) (kheap s(epptr \<mapsto> ko)) = valid_release_q s"
  by (clarsimp simp: valid_release_q_def)

lemma is_activatable_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     is_activatable_2 (cur_thread s) (scheduler_action s)
      (kheap s(epptr \<mapsto> ko)) = is_activatable (cur_thread s) s"
  by (clarsimp simp: is_activatable_def)

lemma weak_valid_sched_action_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     weak_valid_sched_action_2 (scheduler_action s)
      (kheap s(epptr \<mapsto> ko)) (release_queue s) = weak_valid_sched_action s"
  by (clarsimp simp: weak_valid_sched_action_def)

lemma in_cur_domain_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     in_cur_domain_2 t (cur_domain s) (etcbs_of' (kheap s(epptr \<mapsto> ko))) = in_cur_domain t s"
  by (clarsimp simp: in_cur_domain_def)

lemma switch_in_cur_domain_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     switch_in_cur_domain_2 (scheduler_action s) (etcbs_of' (kheap s(epptr \<mapsto> ko))) (cur_domain s)
             = switch_in_cur_domain s"
  by (clarsimp simp: switch_in_cur_domain_def)

lemma valid_sched_action_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     valid_sched_action_2 (scheduler_action s)
      (kheap s(epptr \<mapsto> ko)) (cur_thread s) (cur_domain s)
      (release_queue s) = valid_sched_action s"
  by (clarsimp simp: valid_sched_action_def)

lemma valid_blocked_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     valid_blocked_2 (ready_queues s) (release_queue s)
      (kheap s(epptr \<mapsto> ko)) (scheduler_action s)
      (cur_thread s) = valid_blocked s"
  by (clarsimp simp: valid_blocked_def)

lemma ct_in_cur_domain_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     ct_in_cur_domain_2 (cur_thread s) (idle_thread s)
      (scheduler_action s) (cur_domain s)
      (etcbs_of' (kheap s(epptr \<mapsto> ko))) = ct_in_cur_domain s"
  by (clarsimp simp: ct_in_cur_domain_def)

lemma valid_idle_etcb_simple_ko_update[iff]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
     valid_idle_etcb_2 (etcbs_of' (kheap s(epptr \<mapsto> ko))) = valid_idle_etcb s"
  by (clarsimp simp: valid_idle_etcb_def)

lemma simple_ko_update_cong[simp]:
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
    valid_sched (s\<lparr>kheap := kheap s(epptr \<mapsto> ko)\<rparr>) = valid_sched s"
  by (clarsimp simp: valid_sched_def)

lemma simple_ko_update_cong':
  "\<lbrakk>obj_at (\<lambda>ko. is_simple_type ko) epptr s; is_simple_type ko\<rbrakk> \<Longrightarrow>
      valid_sched_2  (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s)
                 (kheap s(epptr \<mapsto> ko)) (cur_thread s) (idle_thread s) (release_queue s)
    = valid_sched_2 (ready_queues s) (scheduler_action s) (cur_domain s) (cur_time s)
                 (kheap s)(cur_thread s) (idle_thread s) (release_queue s)"
  by (clarsimp simp: valid_sched_def)
  (* this lemma will change if we add endpoint queue scheduling validity to valid_sched *)

(* lifting lemmas *)

lemmas ct_not_queued_lift = hoare_lift_Pf2[where f="cur_thread" and P="not_queued"]
lemmas ct_not_in_release_q_lift = hoare_lift_Pf2[where f="cur_thread" and P="not_in_release_q"]
lemmas sch_act_sane_lift = hoare_lift_Pf2[where f="cur_thread" and P="scheduler_act_not"]

lemma valid_ready_qs_lift_pre_conj:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes a': "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
  assumes r: "\<And>t. \<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
  assumes s: "\<And>t. \<lbrace>\<lambda>s. budget_sufficient t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_ready_qs s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_ready_qs\<rbrace>"
  apply (simp add: valid_ready_qs_def)
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. ready_queues s", OF _ c])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. etcbs_of s", OF _ b])
  apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift a a' s r)
  done

lemmas valid_ready_qs_lift = valid_ready_qs_lift_pre_conj[where R = \<top>, simplified]

lemma valid_release_q_lift_pre_conj:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes a': "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. (valid_release_q s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_release_q\<rbrace>"
  apply (simp only: valid_release_q_def)
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. release_queue s", OF _ c])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. etcbs_of s", OF _ b])
  apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_conj_lift
                    hoare_vcg_imp_lift a a')
  done

lemmas valid_release_q_lift = valid_release_q_lift_pre_conj[where R = \<top>, simplified]

lemma typ_at_st_tcb_at_lift:
  assumes typ_lift: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s) \<and> R s\<rbrace> f \<lbrace>\<lambda>r s. P (typ_at T p s)\<rbrace>"
  assumes st_lift: "\<And>P. \<lbrace>\<lambda>s. st_tcb_at P t s \<and> R s\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> st_tcb_at P t s \<and> R s\<rbrace> f \<lbrace>\<lambda>r s. \<not> st_tcb_at P t s\<rbrace>"
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

lemma valid_blocked_lift_pre_conj:
  assumes a: "\<And>P Q t. \<lbrace>\<lambda>s. (st_tcb_at Q t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. (st_tcb_at Q t s)\<rbrace>"
  assumes t: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and f: "\<And>Q. \<lbrace>\<lambda>s. Q (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q (release_queue s)\<rbrace>"
  assumes b: "\<And>P t. \<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_blocked s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ c])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. ready_queues s", OF _ d])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_thread s", OF _ e])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. release_queue s", OF _ f])
  apply (clarsimp simp add: valid_blocked_def imp_conv_disj conj_disj_distribR all_simps[symmetric]
                  simp del: disj_not1 all_simps)
  apply(rule hoare_vcg_all_lift)+
  apply (rule hoare_vcg_disj_lift typ_at_st_tcb_at_lift | wp a b t | fastforce)+
  done

lemmas valid_blocked_lift = valid_blocked_lift_pre_conj[where R = \<top>, simplified]

lemma valid_blocked_except_set_lift_pre_conj:
  assumes a: "\<And>P Q t. \<lbrace>\<lambda>s. (st_tcb_at Q t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. (st_tcb_at Q t s)\<rbrace>"
  assumes t: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and f: "\<And>Q. \<lbrace>\<lambda>s. Q (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q (release_queue s)\<rbrace>"
  assumes b: "\<And>P t. \<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_blocked_except_set S s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked_except_set S\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ c])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. ready_queues s", OF _ d])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_thread s", OF _ e])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. release_queue s", OF _ f])
  apply (clarsimp simp add: valid_blocked_except_set_def imp_conv_disj conj_disj_distribR
                            all_simps[symmetric]
                  simp del: disj_not1 all_simps)
  apply(rule hoare_vcg_all_lift)+
  apply (rule hoare_vcg_disj_lift typ_at_st_tcb_at_lift | wp a b t | fastforce)+
  done

lemmas valid_blocked_except_set_lift = valid_blocked_except_set_lift_pre_conj[where R=\<top>, simplified]

lemma ct_not_in_q_lift_pre_conj:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. ct_not_in_q s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. ct_not_in_q\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ a])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. ready_queues s", OF _ b])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_thread s", OF _ c])
  apply wpsimp
  done

lemmas ct_not_in_q_lift = ct_not_in_q_lift_pre_conj[where R=\<top>, simplified]

lemma ct_in_cur_domain_lift_pre_conj:
  assumes a: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
      and b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. ct_in_cur_domain s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. ct_in_cur_domain\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. etcbs_of s", OF _ a])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ b])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_domain s", OF _ c])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_thread s", OF _ d])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. idle_thread s", OF _ e])
  apply wpsimp
  done

lemmas ct_in_cur_domain_lift = ct_in_cur_domain_lift_pre_conj[where R=\<top>, simplified]

lemma weak_valid_sched_action_lift_pre_conj:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes b: "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. weak_valid_sched_action s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. weak_valid_sched_action\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. release_queue s", OF _ d])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ c])
  apply (simp add: weak_valid_sched_action_def)
  apply (wpsimp wp: hoare_vcg_all_lift static_imp_wp a b)
  done

lemmas weak_valid_sched_action_lift = weak_valid_sched_action_lift_pre_conj[where R = \<top>, simplified]

lemma switch_in_cur_domain_lift_pre_conj:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. etcb_at Q t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at Q t s\<rbrace>"
  assumes b: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. switch_in_cur_domain s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. switch_in_cur_domain\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ b])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_domain s", OF _ c])
  apply (simp add: switch_in_cur_domain_def in_cur_domain_def)
  apply (wpsimp wp: hoare_vcg_all_lift static_imp_wp a c)
  done

lemmas switch_in_cur_domain_lift = switch_in_cur_domain_lift_pre_conj[where R = \<top>, simplified]

lemma valid_sched_action_lift_pre_conj:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes a': "\<And>t. \<lbrace>\<lambda>s. active_sc_tcb_at t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. active_sc_tcb_at t s\<rbrace>"
  assumes b: "\<And>Q t. \<lbrace>\<lambda>s. etcb_at Q t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. etcb_at Q t s\<rbrace>"
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes e: "\<And>Q. \<lbrace>\<lambda>s. Q (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q (cur_domain s)\<rbrace>"
  assumes f: "\<And>Q. \<lbrace>\<lambda>s. Q (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q (release_queue s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_sched_action s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched_action\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_thread s" , OF _ d])
  apply (simp add: valid_sched_action_def)
  apply (rule_tac Q="\<lambda>s. (is_activatable x s \<and> R s) \<and>
              weak_valid_sched_action s \<and> switch_in_cur_domain s \<and> R s" in hoare_weaken_pre[rotated],
         clarsimp)
  apply (rule hoare_vcg_conj_lift)
   apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ c])
   apply (simp add: is_activatable_def)
   apply (wp weak_valid_sched_action_lift_pre_conj switch_in_cur_domain_lift_pre_conj static_imp_wp a a' b c d e f | simp)+
  done

lemmas valid_sched_action_lift = valid_sched_action_lift_pre_conj[where R = \<top>, simplified]

lemma valid_idle_etcb_lift_pre_conj:
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_idle_etcb s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_idle_etcb\<rbrace>"
  by (wpsimp wp: d)

lemmas valid_idle_etcb_lift = valid_idle_etcb_lift_pre_conj[where R = \<top>, simplified]

lemma valid_sched_lift_pre_conj:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. (st_tcb_at Q t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. (st_tcb_at Q t s)\<rbrace>"
  assumes a': "\<And>P t. \<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  assumes r: "\<And>t. \<lbrace>\<lambda>s. budget_ready t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_ready t s\<rbrace>"
  assumes s: "\<And>t. \<lbrace>\<lambda>s. budget_sufficient t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. budget_sufficient t s\<rbrace>"
  assumes c: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
  assumes d: "\<And>P. \<lbrace>\<lambda>s. P (etcbs_of s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (etcbs_of s)\<rbrace>"
  assumes e: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
  assumes g: "\<And>P. \<lbrace>\<lambda>s. P (cur_domain s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_domain s)\<rbrace>"
  assumes h: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
  assumes i: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (idle_thread s)\<rbrace>"
  assumes j: "\<And>Q. \<lbrace>\<lambda>s. Q (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. Q (release_queue s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_sched s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_sched\<rbrace>"
  apply (simp add: valid_sched_def)
  apply (wpsimp wp: valid_ready_qs_lift_pre_conj ct_not_in_q_lift_pre_conj ct_in_cur_domain_lift_pre_conj valid_release_q_lift_pre_conj
            valid_sched_action_lift_pre_conj  valid_blocked_lift_pre_conj
            a a' s r c d e f g h i j)
  done

lemmas valid_sched_lift = valid_sched_lift_pre_conj[where R = \<top>, simplified]

lemmas valid_sched_except_blocked_lift =
       valid_release_q_lift valid_ready_qs_lift ct_not_in_q_lift valid_sched_action_lift
       ct_in_cur_domain_lift valid_idle_etcb_lift

lemma valid_ntfn_q_lift:
  assumes A: "\<And>x2 p. f \<lbrace>\<lambda>s. ~ ko_at (Notification x2) p s\<rbrace>"
  assumes C: "\<And>t. f \<lbrace>\<lambda>s. t \<noteq> cur_thread s \<and>
                          t \<noteq> idle_thread s \<and>
                          (bound_sc_tcb_at ((=) None) t s \<or>
                           active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s)\<rbrace>"
  shows "f \<lbrace>valid_ntfn_q\<rbrace>"
  unfolding valid_ntfn_q_def
  apply (wpsimp wp: hoare_vcg_all_lift)
   apply (clarsimp simp: ko_at_fold split: kernel_object.splits option.splits)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_ball_lift A C)
  apply (fastforce simp: ko_at_fold[symmetric] split: option.splits)
  done

lemma valid_ep_q_lift_pre_conj:
  assumes A: "\<And>x2 p. \<lbrace>\<lambda>s. ~ ko_at (Endpoint x2) p s \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. ~ ko_at (Endpoint x2) p s\<rbrace>"
  assumes B: "\<And>P t. \<lbrace>\<lambda>s. st_tcb_at P t s \<and> R s\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  assumes C: "\<And>t. \<lbrace>\<lambda>s. t \<noteq> cur_thread s \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. t \<noteq> cur_thread s\<rbrace>"
  assumes D: "\<And>t. \<lbrace>\<lambda>s. t \<noteq> idle_thread s \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. t \<noteq> idle_thread s\<rbrace>"
  assumes E: "\<And>t. \<lbrace>\<lambda>s. (bound_sc_tcb_at ((=) None) t s \<or>
                         active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s) \<and> R s\<rbrace>
                   f
                   \<lbrace>\<lambda>s s. (bound_sc_tcb_at ((=) None) t s \<or>
                           active_sc_tcb_at t s \<and> budget_sufficient t s \<and> budget_ready t s)\<rbrace>"
  shows " \<lbrace>\<lambda>s. valid_ep_q s \<and> R s\<rbrace> f \<lbrace>\<lambda>_ s. valid_ep_q s\<rbrace>"
  unfolding valid_ep_q_def
  apply (wpsimp wp: hoare_vcg_all_lift)
   apply (clarsimp simp: ko_at_fold split: kernel_object.splits option.splits)
   apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_ball_lift A B C D E)
  apply (fastforce simp: ko_at_fold[symmetric] split: option.splits)
  done

lemmas valid_ep_q_lift = valid_ep_q_lift_pre_conj[where R = \<top>, simplified]

lemma valid_blocked_except_lift_pre_conj:
  assumes a: "\<And>Q t. \<lbrace>\<lambda>s. st_tcb_at Q t s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. st_tcb_at Q t s\<rbrace>"
  assumes b: "\<And>P t. \<lbrace>\<lambda>s. P (active_sc_tcb_at t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (active_sc_tcb_at t s)\<rbrace>"
  assumes t: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T t s)\<rbrace>"
      and c: "\<And>P. \<lbrace>\<lambda>s. P (scheduler_action s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (scheduler_action s)\<rbrace>"
      and e: "\<And>P. \<lbrace>\<lambda>s. P (cur_thread s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (cur_thread s)\<rbrace>"
      and d: "\<And>P. \<lbrace>\<lambda>s. P (ready_queues s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (ready_queues s)\<rbrace>"
      and f: "\<And>P. \<lbrace>\<lambda>s. P (release_queue s) \<and> R s\<rbrace> f \<lbrace>\<lambda>rv s. P (release_queue s)\<rbrace>"
    shows "\<lbrace>\<lambda>s. valid_blocked_except thread s \<and> R s\<rbrace> f \<lbrace>\<lambda>rv. valid_blocked_except thread\<rbrace>"
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. scheduler_action s", OF _ c])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. ready_queues s", OF _ d])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. cur_thread s", OF _ e])
  apply (rule hoare_lift_Pf_pre_conj[where f="\<lambda>s. release_queue s", OF _ f])
  apply (clarsimp simp add: valid_blocked_except_def imp_conv_disj conj_disj_distribR all_simps[symmetric]
                  simp del: disj_not1 all_simps)
  apply(rule hoare_vcg_all_lift)+
  apply (rule hoare_vcg_disj_lift typ_at_st_tcb_at_lift | wp a b t | fastforce)+
  done

lemmas valid_blocked_except_lift = valid_blocked_except_lift_pre_conj[where R=\<top>, simplified]

lemma valid_reply_scs_lift:
  assumes A: "\<And>b c. f \<lbrace>\<lambda>s. ~ reply_at_ppred reply_tcb b c s\<rbrace>"
  assumes D: "\<And>b c. f \<lbrace>\<lambda>s. ~ reply_at_ppred reply_sc b c s\<rbrace>"
  assumes B: "\<And>P t. f \<lbrace>bound_sc_tcb_at P t\<rbrace>"
  assumes C: "\<And>t. f \<lbrace>active_sc_tcb_at t\<rbrace>"
  assumes E: "\<And>c. f \<lbrace>\<lambda>s. test_sc_refill_max c s\<rbrace>"
  shows "f \<lbrace>valid_reply_scs\<rbrace>"
  unfolding valid_reply_scs_def
  by (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' hoare_vcg_disj_lift A B C D E)

abbreviation ct_schedulable where
  "ct_schedulable s \<equiv> active_sc_tcb_at (cur_thread s) s
      \<and> budget_ready (cur_thread s) s
      \<and> budget_sufficient (cur_thread s) s"

end
