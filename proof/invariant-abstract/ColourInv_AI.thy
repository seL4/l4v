(*
 * Copyright 2026, UNSW (ABN 57 195 873 179)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ColourInv_AI
  imports
    KernelInit_AI
    "$L4V_ARCH/ArchDetSchedSchedule_AI"
begin

section "Initialisation"
axiomatization
  colour_oracle :: "domain \<Rightarrow> obj_ref set"
  where
    colour_oracle_no_overlap: "x \<noteq> y \<Longrightarrow> (colour_oracle x \<inter> colour_oracle y = {})" and
    colour_oracle_no_zero: "0 \<notin> colour_oracle x" \<comment>\<open>and
    colour_oracle_domain_list: "(d, a)\<in> set (domain_list s) \<Longrightarrow> colour_oracle d = {}" and
    colour_oracle_cur_thread: "\<forall>s. cur_thread s \<in> (colour_oracle (cur_domain s))"\<close>

definition
  check_cap_ref :: "cap \<Rightarrow> obj_ref set \<Rightarrow> bool"
  where
    "check_cap_ref cap obj_set \<equiv> obj_refs cap \<subseteq> obj_set \<union> {0}"

fun tcb_state_ref :: "thread_state \<Rightarrow> obj_ref set"
  where
    "tcb_state_ref (BlockedOnReceive obj_ref _) = {obj_ref}"
  |"tcb_state_ref (BlockedOnSend obj_ref _) = {obj_ref}"
  |"tcb_state_ref (BlockedOnNotification obj_ref) = {obj_ref}"
  |"tcb_state_ref _  = {}"

fun
  check_tcb_state :: "thread_state \<Rightarrow> obj_ref set \<Rightarrow> bool"
  where
    "check_tcb_state (BlockedOnReceive obj_ref _) obj_dom = (obj_ref \<in> obj_dom \<union> {0})"
  |"check_tcb_state (BlockedOnSend obj_ref _) obj_dom = (obj_ref \<in> obj_dom \<union> {0})"
  |"check_tcb_state (BlockedOnNotification obj_ref) obj_dom = (obj_ref \<in> obj_dom \<union> {0})"
  |"check_tcb_state _ _ = True"

primrec
  kernel_object_ref :: "kernel_object \<Rightarrow> obj_ref set"
  where
    "kernel_object_ref (CNode _ cs) = \<Union> ((\<lambda>x. case (cs x) of Some cap \<Rightarrow> obj_refs cap | None \<Rightarrow> {}) ` {x. True})"
  | "kernel_object_ref (TCB t) =
        (obj_refs (tcb_ctable t) \<union>
        obj_refs (tcb_vtable t) \<union>
        obj_refs (tcb_reply t) \<union>
        obj_refs (tcb_caller t) \<union>
        obj_refs (tcb_ipcframe t) \<union>
        tcb_state_ref (tcb_state t) \<union>
        {tcb_ipc_buffer t} \<union>
        set_option (tcb_bound_notification t))"
  | "kernel_object_ref (Endpoint ep) = (case ep of IdleEP \<Rightarrow> {}
                                                 | SendEP s \<Rightarrow> set s
                                                 | RecvEP r \<Rightarrow> set r)"
  | "kernel_object_ref (Notification ntfn) =
    ((case (ntfn_obj ntfn) of WaitingNtfn l \<Rightarrow> set l |
                                          _ \<Rightarrow> {})
    \<union> (case (ntfn_bound_tcb ntfn) of Some tcb \<Rightarrow> {tcb}
                                   | None \<Rightarrow> {}))"
  | "kernel_object_ref (ArchObj ao) = (case ao of RISCV64_A.DataPage _ _ \<Rightarrow> {}
                                                | RISCV64_A.ASIDPool ap \<Rightarrow> \<Union> ((\<lambda>x. case (ap x) of Some obj_ref \<Rightarrow> {obj_ref} | None \<Rightarrow> {}) ` {x. True})
                                                | RISCV64_A.PageTable pt \<Rightarrow> \<Union> ((\<lambda>x. case (pt x) of RISCV64_A.InvalidPTE \<Rightarrow> {}
                                                                             | RISCV64_A.PagePTE ppn _ _ \<Rightarrow> {RISCV64_A.addr_from_ppn ppn}
                                                                             | RISCV64_A.PageTablePTE ppn _  \<Rightarrow> {RISCV64_A.addr_from_ppn ppn}) ` {x. True}))"

primrec
  check_kernel_object_ref :: "kernel_object \<Rightarrow> obj_ref set \<Rightarrow> bool"
  where
    "check_kernel_object_ref (CNode _ cs) obj_dom =
    (\<forall>x.
      case (cs x) of Some cap \<Rightarrow> check_cap_ref cap obj_dom
                   | None \<Rightarrow> True)"
  | "check_kernel_object_ref (TCB t) obj_dom =
    (check_cap_ref (tcb_ctable t) obj_dom \<and>
    check_cap_ref (tcb_vtable t) obj_dom \<and>
    check_cap_ref (tcb_reply t) obj_dom \<and>
    check_cap_ref (tcb_caller t) obj_dom \<and>
    check_cap_ref (tcb_ipcframe t) obj_dom \<and>
    check_tcb_state (tcb_state t) obj_dom \<and>
    tcb_ipc_buffer t \<in> obj_dom \<union> {0} \<and>
    set_option (tcb_bound_notification t) \<subseteq> obj_dom \<union> {0})"
  | "check_kernel_object_ref (Endpoint ep) obj_dom = (case ep of IdleEP \<Rightarrow> True
                                                             | SendEP s \<Rightarrow> (set s \<subseteq> obj_dom \<union> {0})
                                                             | RecvEP r \<Rightarrow>  (set r \<subseteq> obj_dom \<union> {0}))"
  | "check_kernel_object_ref (Notification ntfn) obj_dom =
    ((case (ntfn_obj ntfn) of WaitingNtfn l \<Rightarrow> set l \<subseteq> obj_dom \<union> {0}
                            | _ \<Rightarrow> True)
    \<and> (case (ntfn_bound_tcb ntfn) of Some tcb \<Rightarrow> tcb \<in> obj_dom \<union> {0}
                                   | None \<Rightarrow> True))"
  | "check_kernel_object_ref (ArchObj ao) obj_dom = (case ao of RISCV64_A.DataPage _ _ \<Rightarrow> True
                                                            | RISCV64_A.ASIDPool ap \<Rightarrow> (\<forall>x.
                                                                case (ap x) of Some obj_ref \<Rightarrow> obj_ref \<in> obj_dom \<union> {0}
                                                                             | None \<Rightarrow> True)
                                                            | RISCV64_A.PageTable pt \<Rightarrow> (\<forall>x.
                                                                case (pt x) of RISCV64_A.InvalidPTE \<Rightarrow> True
                                                                             | RISCV64_A.PagePTE ppn _ _ \<Rightarrow> RISCV64_A.addr_from_ppn ppn \<in> obj_dom \<union> {0}
                                                                             | RISCV64_A.PageTablePTE ppn _  \<Rightarrow> RISCV64_A.addr_from_ppn ppn \<in> obj_dom \<union> {0}))"

lemma kernel_object_ref_check:
  "check_kernel_object_ref kobj obj_dom \<equiv> kernel_object_ref kobj \<subseteq> (obj_dom \<union> {0})"
  apply (induct kobj)
      apply simp
      apply (subst check_cap_ref_def)
      apply (rule iffI)
       apply (safe)[1]
       apply (erule_tac x=xa in allE)
       apply (case_tac "x2a xa"; simp add: check_cap_ref_def)
       apply blast
      apply (rule allI)
      apply (case_tac "x2a x"; simp add: check_cap_ref_def)
      apply (simp add: Union_eq set_compre_unwrap)
      apply (rule subsetI)
      apply (erule_tac x=xa in allE)
      apply (erule impE)
       apply (rule_tac x=x in exI)
       apply (simp add: check_cap_ref_def)+
     apply (case_tac "tcb_state x"; simp, meson)
    apply (case_tac x; simp)
   apply simp
   apply (case_tac "ntfn_obj x"; case_tac "ntfn_bound_tcb x"; simp)
  apply safe
   apply (simp add: RISCV64_A.arch_kernel_obj.inject RISCV64_A.arch_kernel_obj.distinct split: RISCV64_A.arch_kernel_obj.split_asm)
    apply safe
    apply (erule_tac x=xb in allE)
    apply (case_tac "x1a xb")
     apply simp+
   apply (erule_tac x=xb in allE)
   apply (simp add: RISCV64_A.pte.simps split: RISCV64_A.pte.split_asm)
  apply (simp add: RISCV64_A.arch_kernel_obj.inject RISCV64_A.arch_kernel_obj.distinct split: RISCV64_A.arch_kernel_obj.split_asm RISCV64_A.arch_kernel_obj.split)
   apply safe
   apply (case_tac "x1 xa"; simp add: check_cap_ref_def)
   apply (simp add: Union_eq set_compre_unwrap)
   apply (erule_tac x=a in allE)
   apply (erule impE)
    apply (rule_tac x=xa in exI)
    apply (simp split: RISCV64_A.pte.split)+
  apply safe
   apply (simp add: Union_eq set_compre_unwrap)
   apply (erule_tac x="RISCV64_A.addr_from_ppn x21" in allE)
   apply (erule impE)
    apply (rule_tac x=xa in exI)
    apply (simp add: RISCV64_A.pte.case)+
  apply (simp add: Union_eq set_compre_unwrap)
  apply (erule_tac x=" RISCV64_A.addr_from_ppn x31" in allE)
  apply (erule impE)
   apply (rule_tac x=xa in exI)
   apply simp
  by (simp add: RISCV64_A.pte.case)+

definition colour_invariant
  where
    "colour_invariant s \<equiv> \<forall>ptr kobj. \<forall>(dom, _)\<in>(set (domain_list s)).
   (ko_at kobj ptr s \<and> ptr \<in> colour_oracle dom) \<longrightarrow>
   (check_kernel_object_ref kobj (colour_oracle dom) \<or> ptr = 0)"

definition valid_ptr_in_cur_domain
  where
    "valid_ptr_in_cur_domain ptr s \<equiv> ptr \<in> colour_oracle (cur_domain s) \<or> ptr = 0"

lemma valid_ptr_in_cur_domain_scheduler_action[simp]:
  "valid_ptr_in_cur_domain a (s\<lparr>scheduler_action := x\<rparr>) = valid_ptr_in_cur_domain a s"
  unfolding valid_ptr_in_cur_domain_def
  by simp

lemma valid_ptr_in_cur_domain_ready_queues[simp]:
  "valid_ptr_in_cur_domain a (s\<lparr>ready_queues := x\<rparr>) = valid_ptr_in_cur_domain a s"
  unfolding valid_ptr_in_cur_domain_def
  by simp

lemma valid_ptr_in_cur_domain_machine_state[simp]:
  "valid_ptr_in_cur_domain a (s\<lparr>machine_state := x\<rparr>) = valid_ptr_in_cur_domain a s"
  unfolding valid_ptr_in_cur_domain_def
  by simp

lemma valid_ptr_in_cur_domain_cdt[simp]:
  "valid_ptr_in_cur_domain a (s\<lparr>cdt := x\<rparr>) = valid_ptr_in_cur_domain a s"
  unfolding valid_ptr_in_cur_domain_def
  by simp

crunch do_machine_op
  for valid_ptr_in_cur_domain[wp]: "valid_ptr_in_cur_domain a"
  (wp: crunch_wps)

lemma colour_inv_cur_domain[intro]:
  "\<lbrakk>invs s; colour_invariant s; ptr' \<in> kernel_object_ref kobj; ko_at kobj ptr s;
     ptr \<in> colour_oracle (cur_domain s)\<rbrakk> \<Longrightarrow>
   valid_ptr_in_cur_domain ptr' s"
  unfolding valid_ptr_in_cur_domain_def
  apply (frule invs_cur_domain_list)
  apply (simp add: cur_domain_list_def colour_invariant_def)
  apply (erule exE)
  apply (erule_tac x=ptr in allE)
  apply (erule_tac x=kobj in allE)
  apply (erule_tac x="(cur_domain s, a)" in ballE; simp)
   apply safe
   apply (simp add: kernel_object_ref_check subset_iff)
   apply (erule_tac x=ptr' in allE)
   apply simp
  apply (frule invs_pspace_in_kernel_window)
  apply (simp add: RISCV64.pspace_in_kernel_window_def obj_at_def)
  apply (erule_tac x=0 in allE)
  apply (erule_tac x="kobj" in allE)
  apply (simp add: RISCV64.kernel_window_def)
  apply (frule RISCV64.invs_valid_uses)
  apply (simp add: RISCV64.valid_uses_def)
  apply (erule_tac x=0 in allE)
  apply (simp add: subset_eq)
  by (erule_tac x=0 in ballE; simp add: RISCV64_A.pptr_base_def RISCV64.pptrBase_def RISCV64.canonical_bit_def)

lemma ptr_no_domain_overlap:
  "\<lbrakk>valid_ptr_in_cur_domain ptr s; ptr \<in> colour_oracle a\<rbrakk> \<Longrightarrow> a = cur_domain s"
  apply (simp add: valid_ptr_in_cur_domain_def)
  apply safe
  using colour_oracle_no_overlap colour_oracle_no_zero by fastforce+

crunch as_user, set_cap, set_untyped_cap_as_full
  for valid_ptr_in_cur_domain[wp]: "\<lambda>s. valid_ptr_in_cur_domain a s"
  (simp: valid_ptr_in_cur_domain_def)

section "Current domain invariance"
crunch cap_insert, set_extra_badge for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (simp: crunch_simps
    wp: crunch_wps)

lemma transfer_caps_loop_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>
  transfer_caps_loop a b c d e f
\<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
  by (rule transfer_caps_loop_pres[OF cap_insert_cur_domain set_extra_badge_cur_domain])

lemma make_fault_msg_cur_domain[wp]:
  "\<lbrace>\<lambda>s. P (cur_domain s)\<rbrace>
      make_fault_msg fault thread
    \<lbrace>\<lambda>_ s. P (cur_domain s)\<rbrace>"
  apply (cases fault; wpsimp)
   apply (rule conjI)
    apply (rule impI)
  by (wpsimp wp: as_user_cur_domain RISCV64.make_arch_fault_msg_inv)+

crunch send_ipc for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  (simp: crunch_simps
    wp: crunch_wps)

section "KHeap_A Colour Invariant"
lemma set_object_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s. check_kernel_object_ref kobj (colour_oracle (cur_domain s)))\<rbrace>
   set_object ptr kobj
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: colour_invariant_def obj_at_update wp: set_object_wp)
  by (drule ptr_no_domain_overlap, simp+)

lemma thread_set_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s. let tcb = TCB (f $ the (get_tcb ptr s)) in check_kernel_object_ref tcb (colour_oracle (cur_domain s)))\<rbrace>
   thread_set f ptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: colour_invariant_def obj_at_update wp: thread_set_wp)
  by (drule ptr_no_domain_overlap, simp+)

lemma thread_set_priority_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_priority ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: thread_set_priority_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma thread_set_time_slice_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_time_slice ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: thread_set_time_slice_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma thread_set_domain_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_domain ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: thread_set_domain_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma set_mcpriority_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     set_mcpriority ref mcp
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: set_mcpriority_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma arch_thread_set_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s.
        let tcb = the $ get_tcb ptr s in
        let arch_tcb = f $ tcb_arch tcb in
        let new_tcb = TCB $ tcb \<lparr> tcb_arch := arch_tcb \<rparr> in
        check_kernel_object_ref new_tcb (colour_oracle (cur_domain s)))\<rbrace>
     arch_thread_set f ptr
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: colour_invariant_def obj_at_update wp: arch_thread_set_wp)
  by (drule ptr_no_domain_overlap, simp+)

lemma set_bound_notification_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s. (set_option ntfn) \<subseteq> colour_oracle (cur_domain s))\<rbrace>
   set_bound_notification ptr ntfn
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: set_bound_notification_thread_set colour_invariant_def obj_at_update wp: thread_set_wp)
  apply (drule ptr_no_domain_overlap)
   apply simp
  by fastforce

lemma set_simple_ko_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s.
        let kobj = the $ kheap s ptr in
          is_simple_type kobj \<longrightarrow>
          partial_inv f kobj \<noteq> None \<longrightarrow>
          check_kernel_object_ref (f ep) (colour_oracle (cur_domain s)))\<rbrace>
     set_simple_ko f ptr ep
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: set_simple_ko_def obj_at_update colour_invariant_def obj_at_def wp: get_object_wp set_object_wp)
  apply safe
  by (drule ptr_no_domain_overlap, simp+)+

lemma throw_on_false_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
      f
    \<lbrace>\<lambda>_ . colour_invariant\<rbrace>
   \<Longrightarrow>
   \<lbrace>colour_invariant\<rbrace>
      throw_on_false ex f
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (simp add: hoare_wp_splits(12) throw_on_false_wp)

lemma set_thread_state_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ref) and (\<lambda>s. check_tcb_state ts (colour_oracle (cur_domain s)))\<rbrace>
       set_thread_state ref ts
      \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp
    simp: set_thread_state_def Let_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def colour_invariant_def
    wp: thread_get_wp set_object_wp gets_the_wp
  )
  apply (simp add: obj_at_update obj_at_def del: check_kernel_object_ref.simps)
  apply (drule get_tcb_SomeD)
  apply (rule exI)
  using get_tcb_rev ptr_no_domain_overlap by fastforce

lemma as_user_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     as_user ptr f
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: as_user_def colour_invariant_def obj_at_update obj_at_def wp: set_object_wp, fastforce dest: get_tcb_SomeD)

\<comment>\<open>I suspect that a lot of the above can effectively be turned into crunches\<close>
crunch reschedule_required,
  possible_switch_to,
  set_thread_state_act,
  set_priority,
  set_scheduler_action,
  tcb_sched_action,
  set_tcb_queue,
  set_irq_state for colour_maintained[wp]: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)

section "Top-Down Colour Invariant Work"
crunch store_word_offs,
  set_extra_badge,
  set_cdt,
  update_cdt,
  set_message_info for colour_maintained[wp]: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)

lemma activate_thread_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (cur_thread s) s) and (\<lambda>s. tcb_at (cur_thread s) s)\<rbrace> \<comment>\<open>Try remove last precond\<close>
     activate_thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: activate_thread_def wp: set_thread_state_colour_maintained as_user_colour_maintained as_user_valid_ptr_in_cur_domain)
     apply (wpsimp simp: RISCV64_A.arch_activate_idle_thread_def)
    apply (wpsimp simp: get_thread_state_def)
    apply (wpsimp wp: thread_get_wp)+
  apply (simp add: tcb_at_def get_tcb_def obj_at_def is_tcb_def)
  using is_obj_defs(3) is_tcb_def
  by presburger

lemma set_cap_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain $ fst cs_ptr) and (\<lambda>s. check_cap_ref cap (colour_oracle (cur_domain s)))\<rbrace>
   set_cap cap cs_ptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: set_cap_def colour_invariant_def obj_at_update obj_at_def wp: set_object_wp get_object_wp)
  apply safe
  using ptr_no_domain_overlap by fastforce+

lemma set_untyped_cap_as_full_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain $ fst src_slot) and (\<lambda>s. check_cap_ref src_cap (colour_oracle (cur_domain s)))\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold set_untyped_cap_as_full_def)
  apply wpsimp
  by (simp add: check_cap_ref_def)

lemma cte_wp_at_check_cap_ref:
  "\<And>s cap.
         \<lbrakk>cte_wp_at ((=) cap) (a, b) s;
          colour_invariant s;
          valid_ptr_in_cur_domain a s;
          invs s\<rbrakk>
         \<Longrightarrow> check_cap_ref cap
               (colour_oracle (cur_domain s))"
  apply (simp add: cte_wp_at_cases2 valid_ptr_in_cur_domain_def)
  apply (safe; frule invs_cur_domain_list; simp add: colour_invariant_def obj_at_def cur_domain_list_def)
     apply safe
     apply (erule_tac x=a in allE,
           erule_tac x="CNode sz fun" in allE,
           erule_tac x="(cur_domain s, aa)" in ballE;
             simp)
     apply safe
      apply (erule_tac x=b in allE)
      apply (simp add: check_kernel_object_ref_def colour_oracle_no_zero)+
    apply (erule_tac x=a in allE;
           erule_tac x="CNode sz fun" in allE)
    apply (frule invs_pspace_in_kernel_window)
    apply (simp add: RISCV64.pspace_in_kernel_window_def)
    apply (erule_tac x=0 in allE;
           erule_tac x="CNode sz fun" in allE)
    apply (simp add: RISCV64.kernel_window_def)
    apply (frule RISCV64.invs_valid_uses)
    apply (simp add: RISCV64.valid_uses_def)
    apply (erule_tac x=0 in allE)
    apply (simp add: subset_eq)
    apply (erule_tac x=0 in ballE; simp add: RISCV64_A.pptr_base_def RISCV64.pptrBase_def RISCV64.canonical_bit_def)
   apply (erule_tac x=a in allE,
          erule_tac x="TCB tcb" in allE,
          erule_tac x="(cur_domain s, aa)" in ballE;
            simp)
   apply (frule_tac a=b and b=cap in ranI)
   apply (fastforce simp add: ran_tcb_cnode_map colour_oracle_no_zero)
  apply (erule_tac x=a in allE)
  apply (erule_tac x="TCB tcb" in allE)
  apply (erule_tac x="(cur_domain s, aa)" in ballE; simp)
  apply (frule invs_pspace_in_kernel_window)
  apply (simp add: RISCV64.pspace_in_kernel_window_def)
  apply (erule_tac x=0 in allE)
  apply (erule_tac x="TCB tcb" in allE)
  apply (simp add: RISCV64.kernel_window_def)
  apply (frule RISCV64.invs_valid_uses)
  apply (simp add: RISCV64.valid_uses_def)
  apply (erule_tac x=0 in allE)
  apply (simp add: subset_eq)
  by (erule_tac x=0 in ballE; simp add: RISCV64_A.pptr_base_def RISCV64.pptrBase_def RISCV64.canonical_bit_def)

lemma cap_insert_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s))) and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s) and (\<lambda>s. valid_ptr_in_cur_domain (fst dest_slot) s) and invs\<rbrace>
    cap_insert new_cap src_slot dest_slot
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (cases src_slot)
  apply (wpsimp simp: cap_insert_def update_cdt_def colour_invariant_def)
            apply safe
             apply (fold colour_invariant_def)
             apply (wpsimp wp: set_cdt_colour_maintained)+
  by (wpsimp simp: cte_wp_at_check_cap_ref wp: set_cdt_colour_maintained set_cap_colour_maintained set_untyped_cap_as_full_colour_maintained get_cap_wp set_untyped_cap_as_full_valid_ptr_in_cur_domain)+

crunch cap_insert, set_mrs, do_ipc_transfer, set_extra_badge
  for valid_ptr_in_cur_domain[wp]: "valid_ptr_in_cur_domain a"
  (wp: crunch_wps simp:crunch_simps valid_ptr_in_cur_domain_def)

lemma check_cap_ref_in_cur_domain:
  "check_cap_ref c (colour_oracle (cur_domain s)) \<equiv> \<forall>r\<in>obj_refs c. valid_ptr_in_cur_domain r s"
  unfolding check_cap_ref_def valid_ptr_in_cur_domain_def
  apply(rule eq_reflection)
  apply clarsimp
  by blast

lemmas check_cap_ref_def2 = check_cap_ref_in_cur_domain

lemma derive_cap_NullCap:
  "\<lbrace> \<lambda>s. is_Zombie cap \<or> is_ReplyCap cap \<or> cap = IRQControlCap \<or> cap = NullCap\<rbrace>
   derive_cap slot cap \<lbrace>\<lambda>rv s. rv = NullCap\<rbrace>, -"
  unfolding derive_cap_def RISCV64_A.arch_derive_cap_def
  apply wpsimp
  by fastforce

lemma derive_cap_non_NullCap:
  "\<lbrace> \<lambda>s. \<not>(is_Zombie cap \<or> is_ReplyCap cap \<or> cap = IRQControlCap \<or> cap = NullCap)\<rbrace>
   derive_cap slot cap \<lbrace>\<lambda>rv s. rv \<noteq> NullCap\<rbrace>, -"
  unfolding derive_cap_def RISCV64_A.arch_derive_cap_def
  apply wpsimp
  by fastforce

lemma derive_cap_check_cap_ref[wp]:
  "\<lbrace>\<lambda>s. check_cap_ref cap (colour_oracle (cur_domain s))\<rbrace>
   derive_cap (b, c) cap
   \<lbrace>\<lambda>rv s. check_cap_ref rv (colour_oracle (cur_domain s))\<rbrace>, -"
  unfolding derive_cap_def RISCV64_A.arch_derive_cap_def
  apply wpsimp
  by (auto simp:check_cap_ref_def RISCV64_A.aobj_ref.simps RISCV64_A.arch_cap.sel)

term get_cap
thm RISCV64.transfer_caps_loop_cte_wp_at
thm derive_cap_inv
thm derive_cap_is_derived
thm derive_cap_is_derived_foo

lemma hoare_vcg_imp_conj_liftE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q'' rv s) \<and> Q''' rv s\<rbrace>,-\<rbrakk> \<Longrightarrow>
   \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q' rv s \<and> Q'' rv s) \<and> Q''' rv s\<rbrace>,-"
  by (smt (verit, del_insts) case_prodE case_prodI2 inf_left_commute pred_conj_def(1)
    pred_top_right_neutral prod.sel(1,2) validE_R_valid_eq valid_def)

lemmas hoare_vcg_imp_conj_liftE_R' = hoare_vcg_imp_conj_liftE_R[where Q'''="\<top>\<top>", simplified]

thm transfer_caps_loop_valid_objs
thm transfer_caps_loop_invs

lemma transfer_caps_loop_colour_maintained: (* broken by invs *)
  "\<lbrace>colour_invariant and invs and
        (\<lambda>s.
            (
              (\<forall>(cap, o_ref, cni)\<in>(set caps).
                s \<turnstile> cap \<and>
                cte_wp_at (\<lambda>c. cap \<noteq> NullCap \<longrightarrow> c = cap) (o_ref, cni) s \<and>
                real_cte_at (o_ref, cni) s \<and>
                check_cap_ref cap (colour_oracle (cur_domain s)) \<and>
                \<comment> \<open>XXX: precond for transfer_caps_loop_cte_wp_at, actually doesn't apply here
                \<not> is_UntypedCap cap \<and>\<close>
                valid_ptr_in_cur_domain o_ref s)) \<and>
              (\<forall>slot\<in>set slots. valid_ptr_in_cur_domain (fst slot) s \<and>
                ex_cte_cap_wp_to is_cnode_cap slot s \<and>
                real_cte_at slot s \<and>
                cte_wp_at (\<lambda>c. c = NullCap) slot s
                \<comment> \<open>XXX: actually we should be able to get this from derive_cap_is_derived etc
                cte_wp_at (\<lambda>c. \<not> is_UntypedCap c) slot s \<comment> \<open>XXX: this isn't telling us enough\<close>
                \<comment> \<open>(\<exists>cap. tcb_cap_valid cap slot s)\<close>\<close>)
            )
   \<rbrace>
     transfer_caps_loop ep rcv_buffer n caps slots mi
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
proof (induct caps arbitrary: ep rcv_buffer n slots mi)
  case Nil
  then show ?case by wpsimp
next
  case (Cons a caps)
  note Cons.hyps[wp]
  show ?case
    apply (cases a)
    apply wpsimp
    apply safe
         apply (wpsimp wp: set_extra_badge_colour_maintained)
          apply(wpsimp wp:hoare_vcg_conj_lift)
           apply (wpsimp simp: set_extra_badge_def)
          apply(wpsimp wp:hoare_vcg_op_lift)
         apply fastforce
        apply(wpsimp wp:hoare_vcg_op_lift cap_insert_weak_cte_wp_at)
           (*apply (wpsimp simp: derive_cap_def RISCV64_A.arch_derive_cap_def)
          apply (wpsimp wp: derive_cap_inv)*) (* <- stuff below seems to increase cases... may want to delete from line below till safe (exclusive) *)
         apply (wpsimp wp: hoare_vcg_if_lift_ER)
         apply(strengthen cap_irqs_appropriate_strengthen)
         apply(strengthen real_cte_tcb_valid)
         apply (wpsimp wp:hoare_vcg_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:derive_cap_valid_cap)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_drop_impE_R)
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          (* DOWN TO HERE.
             FIXME: will need to bring the antecedent in to make this axiom usable:
          apply(wpsimp wp:arch_derive_cap_objrefs_iszombie)
          *)
          apply(wpsimp wp:derive_cap_is_derived_foo)
          (*
          apply(rule hoare_drop_impE_R)
          apply(wpsimp simp:Ball_def wp:hoare_vcg_all_liftE_R)
           apply(wpsimp wp:derive_cap_is_derived_foo)
          apply(wpsimp wp:hoare_vcg_all_liftE_R hoare_vcg_conj_liftE_R hoare_vcg_imp_liftE_R)
          *)
         apply(wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:derive_cap_is_derived)
         apply(wpsimp wp:derive_cap_is_derived_foo)
(*
         apply(wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:hoare_vcg_imp_liftE_R')
          apply(wpsimp wp:derive_cap_is_derived_foo)
         apply(wpsimp wp:hoare_vcg_imp_liftE_R' hoare_vcg_all_liftE_R)
           apply(wpsimp wp:derive_cap_is_derived_foo)
          apply(wpsimp wp:derive_cap_is_derived_foo)
         apply (wpsimp wp:hoare_vcg_conj_liftE_R')
          apply(wpsimp wp:derive_cap_is_derived_foo)
*)
        apply clarsimp
        apply(clarsimp simp:check_cap_ref_in_cur_domain split_beta)
        apply(rule conjI)
         apply(metis (mono_tags, lifting) cap_irqs_simps ex_cte_cap_wp_to_weakenE is_cap_simps(1)
           list.set_sel(1))
        apply(rule conjI)
         apply clarsimp
         (* broken because we should've used arch_derive_cap_objrefs_iszombie
            to get rid of this when it was a postcondition earlier, I think.

        apply safe[1]
          (* XXX: hmm but setting \<top> is too permissive because we need it to be equal to NullCap*)
          apply(clarsimp simp:cte_wp_at_def)
          oops
        apply safe[1] (*slow, >250 cases *)
                          apply (simp add: split_beta)
                          apply clarsimp
                          apply (erule_tac x="hd slots" in ballE)
                          apply clarsimp
                          apply (rule conjI)
                          apply (simp add: valid_ptr_in_cur_domain_def)
                          apply (simp add: crunch_simps(1))
                          apply (rule conjI|rule impI)+
                          apply (simp add: valid_ptr_in_cur_domain_def)
                          apply (erule conjE)+
                          apply (simp add: list.set_sel(2)
                              valid_ptr_in_cur_domain_def)
                          apply simp
                          apply safe
                          apply wpsimp
                          apply (wp add: set_extra_badge_colour_maintained)
                          apply (simp add: set_extra_badge_def valid_ptr_in_cur_domain_def)
                          apply wpsimp
                          apply (simp add: valid_ptr_in_cur_domain_def)
*)
    oops
    by wpsimp+
qed

lemma resolve_address_bits_ret_colour:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref (fst args) (colour_oracle (cur_domain s))) and invs\<rbrace>
    resolve_address_bits args
    \<lbrace>\<lambda>rv s. ((\<exists>x. rv = ((c, d), x)) \<longrightarrow>
      (\<forall>cap. cte_wp_at ((=) cap)
        (c, d) s \<longrightarrow>
          check_cap_ref cap (colour_oracle (cur_domain s)) \<and>
          valid_ptr_in_cur_domain c s
      ))
\<rbrace>,-"
  unfolding resolve_address_bits_def
proof (induct args arbitrary: c d rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
    apply (simp add: validE_R_def)
    apply (rule use_spec)
    apply (subst resolve_address_bits'.simps)
    apply (cases cap, simp_all split del: if_split)
               defer 6 (* CNode *)
               apply (wp+)[11]
    apply (simp add: split_def cong: if_cong split del: if_split)
    apply (rule hoare_pre_spec_validE)
     apply (wp hoare_strengthen_postE_R [OF "1.hyps"])
                 apply (simp add: in_monad)+
        apply (wpsimp wp: get_cap_wp)+
    apply safe
    by ((rule cte_wp_at_check_cap_ref; simp add: check_cap_ref_def; clarsimp simp add: valid_ptr_in_cur_domain_def)|clarsimp simp add: check_cap_ref_def valid_ptr_in_cur_domain_def)+
qed

lemma resolve_address_bits_ret_valid:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref (fst args) (colour_oracle (cur_domain s))) and invs\<rbrace>
resolve_address_bits args
\<lbrace>\<lambda>rv s. \<forall>a. (\<exists>b.
rv = ((a, b), [])) \<longrightarrow> valid_ptr_in_cur_domain a s
\<rbrace>,-"
  unfolding resolve_address_bits_def
proof (induct args rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
    apply (simp add: validE_R_def)
    apply (rule use_spec)
    apply (subst resolve_address_bits'.simps)
    apply (cases cap, simp_all split del: if_split)
               defer 6 (* CNode *)
               apply (wp+)[11]
    apply (simp add: split_def cong: if_cong split del: if_split)
    apply (rule hoare_pre_spec_validE)
     apply (wp hoare_strengthen_postE_R [OF "1.hyps"])
                 apply (simp add: in_monad)+
        apply (wpsimp wp: get_cap_wp)+
    apply safe
    by ((rule cte_wp_at_check_cap_ref; simp add: check_cap_ref_def; clarsimp simp add: valid_ptr_in_cur_domain_def)|clarsimp simp add: check_cap_ref_def valid_ptr_in_cur_domain_def)+
qed

lemma transfer_caps_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (\<lambda>s. (\<forall>(cap, o_ref, _)\<in>(set caps).
      check_cap_ref cap (colour_oracle (cur_domain s)) \<and> valid_ptr_in_cur_domain o_ref s)) and
     (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb receiver s)) (colour_oracle (cur_domain s))) and
     invs\<rbrace>
 transfer_caps info caps endpoint receiver recv_buffer
\<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: transfer_caps_def wp: transfer_caps_loop_colour_maintained)
   apply (wpsimp wp: hoare_vcg_op_lift weak_if_wp')
     apply (wpsimp simp: lookup_slot_for_cnode_op_def)
     apply safe
      apply wpsimp
       apply (wpsimp wp: resolve_address_bits_ret_valid)+
    apply (wpsimp simp: lookup_cap_def)
     apply (wpsimp wp: get_cap_wp)
    apply (wpsimp simp: lookup_slot_for_thread_def)
     apply (wp add: hoare_vcg_all_liftE_R)
     apply (rule_tac Q'="\<lambda>rv s. colour_invariant s \<and> invs s \<and>
              ((\<exists>x. rv = ((a, b), x)) \<longrightarrow>
              (\<forall>cap. cte_wp_at ((=) cap)
                      (a, b) s \<longrightarrow>
                     check_cap_ref cap
                      (colour_oracle
   (cur_domain s)) \<and> valid_ptr_in_cur_domain a s))" in hoare_strengthen_postE_R)
  oops
  by (wpsimp simp: valid_ptr_in_cur_domain_def wp: resolve_address_bits_ret_colour)+

(* XXX
crunch do_normal_transfer, do_ipc_transfer
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps)
*)

lemma copy_mrs_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     copy_mrs  sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
    apply (rule conjI)
     apply (rule impI)
  by (wpsimp wp: mapM_wp[where S="UNIV"] store_word_offs_colour_maintained load_word_offs_P as_user_colour_maintained)+

lemma do_normal_transfer_colour_maintained: (* broken by invs *)
  "\<lbrace>colour_invariant and
    (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb sender s)) (colour_oracle (cur_domain s))) and
    (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb receiver s)) (colour_oracle (cur_domain s)))\<rbrace>
     do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: do_normal_transfer_def)
        apply (wp add: as_user_colour_maintained
                       set_message_info_colour_maintained
                       transfer_caps_colour_maintained)+
     apply (wp add: copy_mrs_colour_maintained)
     apply (wpsimp simp: valid_ptr_in_cur_domain_def wp: hoare_vcg_op_lift copy_mrs_cur_domain)
     apply (wpsimp simp: copy_mrs_def)
      apply (rule conjI)
       apply (rule impI)
       apply (wpsimp simp: store_word_offs_def as_user_def do_machine_op_def load_word_offs_def wp: mapM_wp[where S="UNIV"] load_word_offs_P)+
        apply (simp add: get_tcb_def)
        apply simp
        apply (wpsimp simp: store_word_offs_def do_machine_op_def load_word_offs_def wp: mapM_wp[where S="UNIV"])
        apply (simp add: get_tcb_def)
        apply simp
        apply (wpsimp simp: store_word_offs_def as_user_def do_machine_op_def load_word_offs_def wp: mapM_wp[where S="UNIV"] set_object_wp)
        apply (simp add: get_tcb_def)
        defer
        apply wpsimp+
       apply (simp add: lookup_extra_caps_def
                        lookup_cap_and_slot_def
                        lookup_slot_for_thread_def)
       apply wpsimp
       apply (wp add: mapME_set)
       apply wpsimp
       apply (wp add: get_cap_wp)
       apply wpsimp
       apply (wp add: hoare_vcg_all_liftE_R)
       apply (wpsimp wp: resolve_address_bits_ret_colour[unfolded valid_ptr_in_cur_domain_def])+
       apply (wpsimp wp: mapME_wp')
       apply wpsimp+
  oops
  by (cases "receiver = sender"; clarsimp)
oops

lemma set_mrs_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     set_mrs thread buf msgs
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: set_mrs_def colour_invariant_def wp: zipWithM_x_inv' store_word_offs_colour_maintained set_object_wp)
  apply (simp add: obj_at_update obj_at_def)
  apply (drule get_tcb_SomeD)
  apply (case_tac "ptr=thread")
   apply clarsimp
  using check_kernel_object_ref.simps(2) apply blast
  by fastforce

lemma make_fault_msg_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
    make_fault_msg fault thread
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (cases fault; wpsimp)
       apply (rule conjI)
        apply (rule impI)
  by (wpsimp wp: as_user_colour_maintained RISCV64.make_arch_fault_msg_inv)+

lemma handle_double_fault_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain tptr s)\<rbrace>
   handle_double_fault tptr ex1 ex2
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: handle_double_fault_def wp: set_thread_state_colour_maintained)

lemma retype_region_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
    retype_region ptr numObjects o_bits type dev
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp only: retype_region_def)
  apply wp
  apply (simp del: fun_upd_apply)
  apply (clarsimp simp: colour_invariant_def obj_at_def)
  apply (drule foldr_kh_eq)
  apply (case_tac "ptra \<in> (\<lambda>x. ptr_add ptr (x * 2 ^ obj_bits_api type o_bits)) ` {0..<numObjects}")
   apply (case_tac type)
        apply (
          simp
            split:
              RISCV64_A.aobject_type.splits
            add:
              colour_oracle_no_zero
              default_object_def
              default_tcb_def
              check_cap_ref_def
              default_ep_def
              default_notification_def default_ntfn_def
              empty_cnode_def
              RISCV64_A.default_arch_object_def
              RISCV64_A.arch_kernel_obj.case
              RISCV64_A.pte.case
        )+
  by fastforce

lemma delete_objects_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
  delete_objects ptr bits
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: delete_objects_def do_machine_op_def colour_invariant_def)
  apply (clarsimp simp add: detype_def)
  by fastforce

lemma reset_untyped_cap_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s)\<rbrace>
  reset_untyped_cap src_slot
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: reset_untyped_cap_def wp: set_cap_colour_maintained)
      apply (rule hoare_post_impE[where Q'="\<lambda>_. colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s)" and E'="\<lambda>_. colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s)"])
        apply simp+
      apply (wpsimp wp: mapME_x_wp[where S=UNIV] preemption_point_inv)
           apply (simp add: colour_invariant_def valid_ptr_in_cur_domain_def, simp add: colour_invariant_def valid_ptr_in_cur_domain_def)
         apply (wpsimp simp: irq_state_independent_A_def wp: preemption_point_inv)
          apply (simp add: colour_invariant_def valid_ptr_in_cur_domain_def, simp add: colour_invariant_def valid_ptr_in_cur_domain_def)
        apply (wpsimp wp: set_cap_colour_maintained set_cap_valid_ptr_in_cur_domain)
       apply wp
        apply (simp add: check_cap_ref_def)
        apply (wpsimp simp: valid_ptr_in_cur_domain_def wp: do_machine_op_colour_maintained)+
    apply (rule impI|rule conjI)+
     apply (wp add: delete_objects_colour_maintained)
     apply (wp add: hoare_vcg_imp_lift)
    apply (wpsimp simp: check_cap_ref_def)
   apply (wpsimp wp: hoare_vcg_imp_lift get_cap_wp)
  apply (clarsimp simp: check_cap_ref_def)
  apply(clarsimp simp add: valid_ptr_in_cur_domain_def cte_wp_at_def)
  by blast

lemma syscall_colour_maintained:
  "\<lbrakk>\<lbrace>colour_invariant\<rbrace> param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace>, \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
   \<forall>x. \<lbrace>colour_invariant\<rbrace> param_b x \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
   \<forall>x. \<lbrace>colour_invariant\<rbrace> param_c x \<lbrace>\<lambda>_. colour_invariant\<rbrace>, \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
   \<forall>x. \<lbrace>colour_invariant\<rbrace> param_d x \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
   \<forall>x. \<lbrace>colour_invariant\<rbrace> param_e x \<lbrace>\<lambda>_. colour_invariant\<rbrace>, \<lbrace>\<lambda>_. colour_invariant\<rbrace>\<rbrakk> \<Longrightarrow>
   \<lbrace>colour_invariant\<rbrace>
    syscall param_a param_b param_c param_d param_e
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wp syscall_valid)
  by ((erule allE)+, simp)+

lemma next_domain_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
      next_domain
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: next_domain_def colour_invariant_def Let_def)

lemma colour_invariant_cur_thread[simp]:
  "colour_invariant (s\<lparr>cur_thread := thread\<rparr>) = colour_invariant s"
  by (simp add: colour_invariant_def)

lemma switch_to_idle_thread_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
      switch_to_idle_thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: switch_to_idle_thread_def RISCV64_A.arch_switch_to_idle_thread_def RISCV64_A.set_vm_root_def RISCV64_A.find_vspace_for_asid_def
    wp: do_machine_op_colour_maintained hoare_vcg_op_lift get_cap_cte_wp_at3)

lemma switch_to_thread_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
      switch_to_thread t
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: switch_to_thread_def RISCV64_A.arch_switch_to_thread_def RISCV64_A.set_vm_root_def RISCV64_A.find_vspace_for_asid_def
  wp: tcb_sched_action_colour_maintained do_machine_op_colour_maintained hoare_vcg_op_lift get_cap_cte_wp_at3)

lemma guarded_switch_to_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
      guarded_switch_to thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: guarded_switch_to_def
  wp: switch_to_thread_colour_maintained hoare_vcg_imp_lift[where P'=\<bottom>])

lemma colour_invariant_scheduler_action[simp]:
  "colour_invariant (s\<lparr>scheduler_action := action\<rparr>) = colour_invariant s"
  by (simp add: colour_invariant_def)

lemma colour_invariant_arch_state[simp]:
  "colour_invariant (s\<lparr>arch_state := x\<rparr>) = colour_invariant s"
  unfolding colour_invariant_def
  by simp

lemma colour_invariant_interrupt_states[simp]:
  "colour_invariant (s\<lparr>interrupt_states := x\<rparr>) = colour_invariant s"
  unfolding colour_invariant_def
  by simp

lemma colour_invariant_machine_state[simp]:
  "colour_invariant (s\<lparr>machine_state := x\<rparr>) = colour_invariant s"
  unfolding colour_invariant_def
  by clarsimp

context Arch begin

crunch schedule_choose_new_thread, schedule
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps)

lemma send_ipc_colour_maintained: (* unfinished before *)
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (cur_thread s) s) and invs and (\<lambda>s. valid_ptr_in_cur_domain thread s)\<rbrace>
  send_ipc block call badge can_grant can_grant_reply thread epptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: send_ipc_def wp: set_simple_ko_colour_maintained)
       apply (wpsimp simp: valid_ptr_in_cur_domain_def Let_def wp: set_thread_state_colour_maintained)
       apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def thread_get_def set_object_def get_object_def gets_the_def)
      apply wpsimp+
      apply (wpsimp simp: valid_ptr_in_cur_domain_def Let_def wp: set_thread_state_colour_maintained)
      apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def thread_get_def set_object_def get_object_def gets_the_def)
     apply wpsimp+
          apply (rule_tac Q'="\<lambda>_.
            colour_invariant and
            valid_ptr_in_cur_domain thread and invs and
            (\<lambda>s. call \<longrightarrow>
              (if (can_grant \<or> can_grant_reply) then (valid_ptr_in_cur_domain x21)
              else (\<lambda>s. check_tcb_state Inactive (colour_oracle (cur_domain s)))) s)" in hoare_post_imp)
           apply force
          apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
             apply safe
                 apply (rule_tac Q'="\<lambda>_ s. (x21 \<in> colour_oracle (cur_domain s) \<or> x21 = 0) \<and> (thread \<in> colour_oracle (cur_domain s) \<or> thread = 0)" in hoare_strengthen_post)
                  apply wpsimp
                 apply (clarsimp simp add: valid_ptr_in_cur_domain_def)
  oops

lemma handle_fault_colour_maintained: (* unfinished before *)
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain thread\<rbrace>
        handle_fault thread ex
      \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: handle_fault_def handle_double_fault_def send_fault_ipc_def wp: set_thread_state_colour_maintained)
      apply (case_tac "handler_cap")
                 apply wpsimp+
               defer
               apply (wpsimp simp: cap_fault_on_failure_def)+
  apply safe
     defer
     defer
     apply wpsimp
    apply wpsimp
   apply wpsimp
     apply (wpsimp simp: send_ipc_def wp: set_simple_ko_colour_maintained)
         apply (wpsimp simp: valid_ptr_in_cur_domain_def Let_def wp: set_thread_state_colour_maintained)
         apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def)
           apply (wpsimp simp: get_thread_state_def thread_get_def)
          apply (wpsimp simp: set_object_def get_object_def)
         apply (wpsimp simp: gets_the_def)
        apply wpsimp
       apply simp
       apply wpsimp
       apply (wpsimp simp: valid_ptr_in_cur_domain_def Let_def wp: set_thread_state_colour_maintained)
       apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def)
         apply (wpsimp simp: get_thread_state_def thread_get_def)
        apply (wpsimp simp: set_object_def get_object_def)
       apply (wpsimp simp: gets_the_def)
  oops

(* Arch-specific ones trivial for RISCV64 - move to appropriate place *)

crunch init_arch_objects, arch_post_cap_deletion, prepare_thread_delete,
  arch_post_modify_registers, arch_mask_irq_signal, handle_reserved_irq
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps)

(* Failed proofs found by crunch, in order of discovery (all arch ones first, then arch-agnostic).
   Don't forget to re-check crunch after proving each of these if it required new preconditions,
   using this crunch command:

crunch call_kernel for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update crunch_simps
     wp: crunch_wps RISCV64.arch_get_sanitise_register_info_inv
         RISCV64.handle_arch_fault_reply_inv) *)

(* Arch-specific *)

crunch set_pt
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps)

thm valid_ptr_in_cur_domain_def
lemma store_pte_colour_maintained[wp]:
  "\<lbrace>\<lambda>s. colour_invariant s \<and> invs s \<and>
        \<comment> \<open>let's see how usable this ends up if we assert p and pte are coloured and not bogus\<close>
        table_base p \<in> colour_oracle (cur_domain s) \<and>
        \<comment> \<open>we can't just assert it *is* PagePTE, because otherwise unmap_page ends up with a
           contradictory precondition where pte = InvalidPTE. so we have to handle that case\<close>
        (case pte of InvalidPTE \<Rightarrow> True |
           PagePTE ppn attr rights \<Rightarrow> valid_ptr_in_cur_domain (addr_from_ppn ppn) s |
           PageTablePTE ppn x \<Rightarrow> valid_ptr_in_cur_domain (addr_from_ppn ppn) s)\<rbrace>
     store_pte p pte
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding store_pte_def
  apply clarsimp
  apply wpsimp
  apply(frule invs_cur_domain_list)
  apply(clarsimp simp:valid_ptr_in_cur_domain_def cur_domain_list_def colour_invariant_def)
  apply(rename_tac s pt a x)
  apply(drule_tac x="table_base p" in spec)
  apply(drule_tac x="ArchObj (PageTable pt)" in spec)
  apply(drule_tac x="(cur_domain s, a)" in bspec)
   apply clarsimp
  using colour_oracle_no_zero
  by (fastforce simp:valid_ptr_in_cur_domain_def split:pte.splits)

lemma unmap_page_colour_maintained[wp]:
  "\<lbrace>\<lambda>s. colour_invariant s \<and> invs s \<and>
     (case vspace_for_asid asid s of Some pt \<Rightarrow>
       (case pt_lookup_slot pt vptr (ptes_of s) of
         Some (x, b) \<Rightarrow> table_base b \<in> colour_oracle (cur_domain s) |
         None \<Rightarrow> True) |
      None \<Rightarrow> True)\<rbrace>
     unmap_page pgsz asid vptr pptr
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding unmap_page_def
  by (wpsimp wp: crunch_wps simp: crunch_simps split:option.splits)

crunch set_vm_root, set_asid_pool
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps)

lemma delete_asid_colour_maintained[wp]:
  "\<lbrace>\<lambda>s. colour_invariant s \<and>
     (case asid_table s (asid_high_bits_of asid) of None \<Rightarrow> True |
       Some pool_ptr \<Rightarrow> pool_ptr \<in> colour_oracle (cur_domain s) \<and>
         (\<forall>pool x. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow>
           (case pool x of None \<Rightarrow> True |
             Some pt' \<Rightarrow> valid_ptr_in_cur_domain pt' s)))\<rbrace>
     delete_asid asid pt \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  unfolding delete_asid_def
  apply(wpsimp simp:valid_ptr_in_cur_domain_def split:option.splits)
  by blast

crunch delete_asid_pool
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps valid_ptr_in_cur_domain_def colour_invariant_def)

lemma unmap_page_table_colour_maintained[wp]:
  "\<lbrace>colour_invariant and invs\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding unmap_page_table_def
  apply wpsimp
  sorry (* FIXME: recursive function, come back to this one *)

lemma arch_finalise_cap_colour_maintained[wp]:
  "\<lbrace>colour_invariant and invs and
    (\<lambda>s. case cap of FrameCap obj rights fsize is_dev (Some (asid, ref)) \<Rightarrow>
      (case vspace_for_asid asid s of None \<Rightarrow> True |
        Some pt \<Rightarrow> (case pt_lookup_slot pt ref (ptes_of s) of None \<Rightarrow> True |
          Some (xa, b) \<Rightarrow> table_base b \<in> colour_oracle (cur_domain s))) |
      PageTableCap obj (Some (asid, ref)) \<Rightarrow> if x \<and> vspace_for_asid asid s = Some obj
        then (case asid_table s (asid_high_bits_of asid) of None \<Rightarrow> True |
          Some pool_ptr \<Rightarrow> pool_ptr \<in> colour_oracle (cur_domain s) \<and>
            (\<forall>pool y. ako_at (ASIDPool pool) pool_ptr s \<longrightarrow> (case pool y of  None \<Rightarrow> True |
              Some pt' \<Rightarrow> valid_ptr_in_cur_domain pt' s)))
        else True)\<rbrace> arch_finalise_cap cap x \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding arch_finalise_cap_def
  apply wpsimp
  by (force split:option.splits)

lemma arch_invoke_irq_control_colour_maintained[wp]:
  "\<lbrace>\<lambda>s. colour_invariant s \<and>
       (\<forall> x. ((), x) \<in> fst (setIRQTrigger irq trigger (machine_state s)) \<longrightarrow>
         invs (s\<lparr>machine_state := x, interrupt_states :=
           (\<lambda>y. if y = irq then IRQSignal else (interrupt_states (s\<lparr>machine_state := x\<rparr>) y))\<rparr>)) \<and>
       valid_ptr_in_cur_domain (fst control_slot) s \<and>
       valid_ptr_in_cur_domain (fst handler_slot) s \<and>
       check_cap_ref (IRQHandlerCap irq) (colour_oracle (cur_domain s))\<rbrace>
     arch_invoke_irq_control (RISCVIRQControlInvocation irq handler_slot control_slot trigger)
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply(wpsimp wp:crunch_wps maskInterrupt_invs
    simp:crunch_simps set_irq_state_def valid_ptr_in_cur_domain_def)
   apply(wpsimp simp:do_machine_op_def)
  by (clarsimp simp:valid_ptr_in_cur_domain_def)

crunch arch_invoke_irq_handler
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps valid_ptr_in_cur_domain_def colour_invariant_def)

crunch handle_vm_fault, handle_hypervisor_fault
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps valid_ptr_in_cur_domain_def colour_invariant_def)

lemma arch_perform_invocation_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace> arch_perform_invocation param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding RISCV64_A.arch_perform_invocation_def
  apply wpsimp
      apply(wpsimp simp:perform_page_table_invocation_def perform_pt_inv_map_def
        wp:arch_update_cap_invs_map set_cap_valid_ptr_in_cur_domain)
      apply(wpsimp wp:hoare_vcg_op_lift split:pte.splits)
     apply(wpsimp simp:perform_pt_inv_unmap_def
       update_map_data_def subset_eq check_cap_ref_in_cur_domain comp_def
       wp:get_cap_inv hoare_vcg_conj_lift split:arch_cap.splits)
     thm hoare_vcg_ball_lift
     sorry (* FIXME: don't get what's going on here. why won't ball_lift apply? *)

(* Arch-agnostic *)

lemma set_thread_state_valid_cur_dom[wp]:
  "set_thread_state ref ts \<lbrace>valid_ptr_in_cur_domain ref'\<rbrace>"
  unfolding set_thread_state_def valid_ptr_in_cur_domain_def
  by wpsimp

lemma setup_caller_cap_colour_maintained[wp]:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain sender and
     ((\<lambda>s. check_cap_ref
             (ReplyCap sender False
               (if grant then {AllowGrant, AllowWrite} else {AllowWrite}))
             (colour_oracle (cur_domain s)) \<and>
        sender \<noteq> idle_thread s \<and>
        st_tcb_at (\<lambda>st. \<not> halted st) sender s \<and>
        st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = {}) sender s \<and>
        ex_nonz_cap_to sender s) and
      valid_ptr_in_cur_domain (fst (receiver, tcb_cnode_index 3)) and invs)\<rbrace>
    setup_caller_cap sender receiver grant
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding setup_caller_cap_def
  apply wpsimp
   apply(wpsimp wp:sts_invs_minor)
  by clarsimp

(* DOWN TO HERE *)

crunch possible_switch_to
  for valid_ptr_in_cur_domain[wp]: "valid_ptr_in_cur_domain a"

lemma sts_Running_invs[wp]:
  "\<lbrace>st_tcb_at active t and invs and ex_nonz_cap_to t\<rbrace>
     set_thread_state t Running
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wp sts_invs_minor2)
  apply (auto elim!: pred_tcb_weakenE
           notE [rotated, OF _ idle_no_ex_cap]
           simp: invs_def valid_state_def valid_pspace_def)
  done

(* DOWN TO HERE but really it's do_ipc_transfer, do_normal_transfer, transfer_caps_loop etc *)
lemma send_ipc_colour_maintained:
  "\<lbrace>colour_invariant and
     (valid_ptr_in_cur_domain thread and
      (\<lambda>s. check_tcb_state
             (BlockedOnSend epptr
               \<lparr>sender_badge = badge, sender_can_grant = can_grant,
                  sender_can_grant_reply = can_grant_reply, sender_is_call = call\<rparr>)
             (colour_oracle (cur_domain s)))) and
     valid_ptr_in_cur_domain epptr and
     (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb thread s))
            (colour_oracle (cur_domain s))) and
     invs\<rbrace>
  send_ipc block call badge can_grant can_grant_reply thread epptr \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding send_ipc_def
  apply(wpsimp simp:Let_def wp:hoare_vcg_conj_lift)
        apply(wp hoare_drop_imp)
       apply(wp hoare_drop_imp)
      apply wpsimp
     apply(wpsimp simp:Let_def wp:hoare_drop_imp)
    apply(wpsimp wp:hoare_vcg_op_lift | rule conjI)+
         apply(wpsimp wp:hoare_vcg_conj_lift sts_st_tcb_at'')
        apply(wpsimp wp:hoare_vcg_conj_lift sts_st_tcb_at'' hoare_drop_imp)
       apply(wp hoare_drop_imp)
      apply(wpsimp wp:hoare_vcg_op_lift | rule conjI)+
      sorry

lemma handle_fault_colour_maintained:
"\<lbrace>colour_invariant and
 (valid_ptr_in_cur_domain param_a and
  (\<lambda>s. let tcb = TCB (tcb_fault_update (\<lambda>_. Some param_b) $ the (get_tcb param_a s))
        in check_kernel_object_ref tcb (colour_oracle (cur_domain s))) and
  invs)\<rbrace>
handle_fault param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding handle_fault_def
  apply wpsimp
    apply(wpsimp simp:send_fault_ipc_def Let_def)
    
  sorry

lemma create_cap_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace> create_cap param_a param_b param_c param_d param_e 
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma invoke_untyped_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace> invoke_untyped param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma blocked_cancel_ipc_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_b\<rbrace>
   blocked_cancel_ipc param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma cancel_all_ipc_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace> cancel_all_ipc param_a 
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma unbind_maybe_notification_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace> unbind_maybe_notification param_a 
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma cancel_all_signals_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace> cancel_all_signals param_a 
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma empty_slot_colour_maintained:
  "\<lbrace>colour_invariant and
 ((valid_ptr_in_cur_domain $ fst param_a) and
  (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s))))\<rbrace>
empty_slot param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma cap_delete_one_colour_maintained:
  "\<lbrace>colour_invariant and
 ((valid_ptr_in_cur_domain $ fst param_a) and
  (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s))))\<rbrace>
cap_delete_one param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma reply_cancel_ipc_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a and
 (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
reply_cancel_ipc param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma cancel_signal_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_b and
 valid_ptr_in_cur_domain param_a\<rbrace>
cancel_signal param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma cancel_ipc_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a and
 (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
cancel_ipc param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma update_waiting_ntfn_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace>
update_waiting_ntfn param_a param_b param_c param_d \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma send_signal_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a and
 (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
send_signal param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma suspend_colour_maintained:
  "\<lbrace>colour_invariant and
 (valid_ptr_in_cur_domain param_a and
  (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s))))\<rbrace>
suspend param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma setup_reply_master_colour_maintained:
  "\<lbrace>colour_invariant and
 ((valid_ptr_in_cur_domain $ fst (param_a, tcb_cnode_index 2)) and
  (\<lambda>s. check_cap_ref (ReplyCap param_a True {AllowGrant, AllowWrite})
         (colour_oracle (cur_domain s))))\<rbrace>
setup_reply_master param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma restart_colour_maintained:
  "\<lbrace>colour_invariant and
 (valid_ptr_in_cur_domain param_a and
  (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))) and
 (\<lambda>s. check_cap_ref (ReplyCap param_a True {AllowGrant, AllowWrite})
        (colour_oracle (cur_domain s)))\<rbrace>
restart param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma option_update_thread_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace>
option_update_thread param_a param_b param_c \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma cap_swap_for_delete_colour_maintained:
  "\<lbrace>colour_invariant and
 ((valid_ptr_in_cur_domain $ fst param_a) and (valid_ptr_in_cur_domain $ fst param_b))\<rbrace>
cap_swap_for_delete param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma deleting_irq_handler_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
deleting_irq_handler param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma rec_del_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
rec_del param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma check_cap_at_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace> check_cap_at param_a param_b param_c \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma bind_notification_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_b and
 valid_ptr_in_cur_domain param_a\<rbrace>
bind_notification param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma unbind_notification_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace> unbind_notification param_a 
\<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma set_domain_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace> set_domain param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma handle_fault_reply_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace> handle_fault_reply param_a param_b param_c param_d 
\<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma do_reply_transfer_colour_maintained:
  "\<lbrace>colour_invariant and
 ((\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb param_a s))
         (colour_oracle (cur_domain s))) and
  (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb param_b s))
         (colour_oracle (cur_domain s)))) and
 ((valid_ptr_in_cur_domain $ fst param_c) and
  (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))) and
 valid_ptr_in_cur_domain param_b and
 (\<lambda>s. let tcb = TCB (tcb_fault_update (\<lambda>_. None) $ the (get_tcb param_b s))
       in check_kernel_object_ref tcb (colour_oracle (cur_domain s)))\<rbrace>
do_reply_transfer param_a param_b param_c param_d \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma cap_move_colour_maintained:
  "\<lbrace>colour_invariant and
 ((valid_ptr_in_cur_domain $ fst param_c) and
  (\<lambda>s. check_cap_ref param_a (colour_oracle (cur_domain s)))) and
 ((valid_ptr_in_cur_domain $ fst param_b) and
  (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s))))\<rbrace>
cap_move param_a param_b param_c \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma cap_swap_colour_maintained:
  "\<lbrace>colour_invariant and
 ((valid_ptr_in_cur_domain $ fst param_b) and
  (\<lambda>s. check_cap_ref param_c (colour_oracle (cur_domain s)))) and
 ((valid_ptr_in_cur_domain $ fst param_d) and
  (\<lambda>s. check_cap_ref param_a (colour_oracle (cur_domain s))))\<rbrace>
cap_swap param_a param_b param_c param_d \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry
  
lemma cancel_badged_sends_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace>
cancel_badged_sends param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma invoke_irq_control_colour_maintained:
  "\<lbrace>colour_invariant and invs\<rbrace> invoke_irq_control param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma invoke_irq_handler_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s))) and
 invs\<rbrace>
invoke_irq_handler param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma invoke_cnode_colour_maintained:
  "\<lbrace>colour_invariant and invs and
 (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
invoke_cnode param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma handle_invocation_colour_maintained:
  "\<lbrace>colour_invariant and invs and
 (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
handle_invocation param_a param_b \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma handle_reply_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
handle_reply \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma complete_signal_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace> complete_signal param_a param_b 
\<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma timer_tick_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace> timer_tick \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma receive_ipc_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a and
 (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb param_a s))
        (colour_oracle (cur_domain s))) and
 invs\<rbrace>
receive_ipc param_a param_b param_c \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma receive_signal_colour_maintained:
  "\<lbrace>colour_invariant and valid_ptr_in_cur_domain param_a\<rbrace>
receive_signal param_a param_b param_c \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma handle_interrupt_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))\<rbrace>
handle_interrupt param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

lemma handle_recv_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s))) and
 invs\<rbrace>
handle_recv param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace> "
  sorry

lemma handle_event_colour_maintained:
  "\<lbrace>colour_invariant and
 (invs and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s))))\<rbrace>
handle_event param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  sorry

(* lemmas demanded by call_kernel itself *)

lemma schedule_cur_thread_valid_in_cur_domain:
  "\<lbrace>invs\<rbrace> schedule \<lbrace>\<lambda>rv s. valid_ptr_in_cur_domain (cur_thread s) s\<rbrace>"
  unfolding schedule_def
  sorry

lemma schedule_tcb_at_cur_thread:
  "\<lbrace>invs\<rbrace> schedule \<lbrace>\<lambda>rv s. tcb_at (cur_thread s) s\<rbrace>"
  apply(rule_tac P="invs" in hoare_strengthen_post)
   apply(rule schedule_invs)
  apply(drule (1) tcb_at_invs)
  done

lemma check_cap_ref_null[intro!]:
  "check_cap_ref NullCap oracle"
  unfolding check_cap_ref_def
  by force

crunch maybe_handle_interrupt for colour_maintained[wp]: "colour_invariant"
  (wp: crunch_wps simp: crunch_simps)

(* The crunch command used to discover all needed lemmas.
crunch call_kernel for colour_maintained: "colour_invariant"
  (simp: obj_at_update crunch_simps
     wp: crunch_wps RISCV64.arch_get_sanitise_register_info_inv
         RISCV64.handle_arch_fault_reply_inv
         schedule_cur_thread_valid_in_cur_domain
         schedule_tcb_at_cur_thread)
*)

(* Beyond what the crunch command tried to use, we also needed to add ct_active as a precondition *)
theorem call_kernel_colour_maintained:
  "\<lbrace>colour_invariant and
     (invs and ct_active and (\<lambda>s. check_cap_ref NullCap (colour_oracle (cur_domain s)))) and
     (\<lambda>s. valid_ptr_in_cur_domain (cur_thread s) s)\<rbrace>
    call_kernel ev \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding call_kernel_def
  apply(wpsimp simp:crunch_simps wp:crunch_wps
    activate_thread_colour_maintained schedule_colour_maintained
    schedule_cur_thread_valid_in_cur_domain schedule_tcb_at_cur_thread
    handle_interrupt_colour_maintained do_machine_op_colour_maintained)
   apply(wpsimp wp:handle_event_colour_maintained simp:check_cap_ref_null)
  apply wpsimp
  done

end
