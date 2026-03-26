(*
 * Copyright 2026, UNSW (ABN 57 195 873 179)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ColourInv_AI
  imports
    KernelInit_AI
    "$L4V_ARCH/ArchDetSchedSchedule_AI"
    MSpec_AI
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
          \<comment> \<open>the invs we specifically need\<close>
          cur_domain_list s;
          pspace_in_kernel_window s;
          RISCV64.valid_uses s\<rbrakk>
         \<Longrightarrow> check_cap_ref cap
               (colour_oracle (cur_domain s))"
  apply (simp add: cte_wp_at_cases2 valid_ptr_in_cur_domain_def)
  apply (safe; simp add: colour_invariant_def obj_at_def cur_domain_list_def)
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
    apply (simp add: RISCV64.pspace_in_kernel_window_def)
    apply (erule_tac x=0 in allE;
           erule_tac x="CNode sz fun" in allE)
    apply (simp add: RISCV64.kernel_window_def)
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
  apply (simp add: RISCV64.pspace_in_kernel_window_def)
  apply (erule_tac x=0 in allE)
  apply (erule_tac x="TCB tcb" in allE)
  apply (simp add: RISCV64.kernel_window_def)
  apply (simp add: RISCV64.valid_uses_def)
  apply (erule_tac x=0 in allE)
  apply (simp add: subset_eq)
  by (erule_tac x=0 in ballE; simp add: RISCV64_A.pptr_base_def RISCV64.pptrBase_def RISCV64.canonical_bit_def)

lemma cap_insert_colour_maintained[wp]:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s)))
    and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s)
    and (\<lambda>s. valid_ptr_in_cur_domain (fst dest_slot) s)
    \<comment> \<open>the invs we specifically need so we can use cte_wp_at_check_cap_ref\<close>
    and cur_domain_list and pspace_in_kernel_window and RISCV64.valid_uses\<rbrace>
    cap_insert new_cap src_slot dest_slot
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (cases src_slot)
  apply (wpsimp simp: cap_insert_def update_cdt_def colour_invariant_def)
            apply safe
             apply (fold colour_invariant_def)
             apply (wpsimp wp: set_cdt_colour_maintained)+
    apply(wpsimp wp:get_cap_wp)
   apply(wpsimp wp:get_cap_wp)
  apply(clarsimp simp:cte_wp_at_check_cap_ref)
  done

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

lemma derive_cap_not_in_objrefs:
  "\<lbrace>\<lambda>s. x \<notin> obj_refs cap\<rbrace> derive_cap (b, c) cap \<lbrace>\<lambda>r s. x \<notin> obj_refs r\<rbrace>, -"
  unfolding derive_cap_def RISCV64_A.arch_derive_cap_def
  apply wpsimp
  by (force simp add: RISCV64_A.aobj_ref.simps(3) RISCV64_A.arch_cap.sel(2))

lemma derive_cap_check_cap_ref[wp]:
  "\<lbrace>\<lambda>s. check_cap_ref cap (colour_oracle (cur_domain s))\<rbrace>
   derive_cap (b, c) cap
   \<lbrace>\<lambda>rv s. check_cap_ref rv (colour_oracle (cur_domain s))\<rbrace>, -"
  unfolding derive_cap_def RISCV64_A.arch_derive_cap_def
  apply wpsimp
  by (auto simp:check_cap_ref_def RISCV64_A.aobj_ref.simps RISCV64_A.arch_cap.sel)

lemma hoare_vcg_imp_conj_liftE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s\<rbrace>,-; \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q'' rv s) \<and> Q''' rv s\<rbrace>,-\<rbrakk> \<Longrightarrow>
   \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q' rv s \<and> Q'' rv s) \<and> Q''' rv s\<rbrace>,-"
  by (smt (verit, del_insts) case_prodE case_prodI2 inf_left_commute pred_conj_def(1)
    pred_top_right_neutral prod.sel(1,2) validE_R_valid_eq valid_def)

lemma hoare_vcg_imp_all_comm:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (\<forall>x. Q rv s \<longrightarrow> Q' rv x s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> (\<forall>x. Q' rv x s)\<rbrace>"
  by (smt (verit, del_insts) case_prodE case_prodI2 inf_left_commute pred_conj_def(1)
    pred_top_right_neutral prod.sel(1,2) validE_R_valid_eq valid_def)

lemma hoare_vcg_imp_all_commE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (\<forall>x. Q rv s \<longrightarrow> Q' rv x s)\<rbrace>,- \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> (\<forall>x. Q' rv x s)\<rbrace>,-"
  by (smt (verit, del_insts) case_prodE case_prodI2 inf_left_commute pred_conj_def(1)
    pred_top_right_neutral prod.sel(1,2) validE_R_valid_eq valid_def)

lemma hoare_vcg_double_imp_all_commE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. (\<forall>x. Q rv s \<longrightarrow> R rv s \<longrightarrow> Q' rv x s)\<rbrace>,- \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s \<longrightarrow> (\<forall>x. Q' rv x s)\<rbrace>,-"
  by (smt (verit, del_insts) case_prodE case_prodI2 inf_left_commute pred_conj_def(1)
    pred_top_right_neutral prod.sel(1,2) validE_R_valid_eq valid_def)

lemma hoare_vcg_imp_comm:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s \<longrightarrow> S rv s\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. R rv s \<longrightarrow> Q rv s \<longrightarrow> S rv s\<rbrace>"
  by (smt (verit, del_insts) case_prodE case_prodI2 inf_left_commute pred_conj_def(1)
    pred_top_right_neutral prod.sel(1,2) validE_R_valid_eq valid_def)

lemma hoare_vcg_imp_commE_R:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s \<longrightarrow> S rv s\<rbrace>,- \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. R rv s \<longrightarrow> Q rv s \<longrightarrow> S rv s\<rbrace>,-"
  by (smt (verit, del_insts) case_prodE case_prodI2 inf_left_commute pred_conj_def(1)
    pred_top_right_neutral prod.sel(1,2) validE_R_valid_eq valid_def)

lemma hoare_vcg_imp_all_liftE_R:
  "(\<And>x. \<lbrace>P x\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv x s\<rbrace>,-) \<Longrightarrow>
   \<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> (\<forall>x. Q' rv x s)\<rbrace>,-"
  apply(rule hoare_vcg_imp_all_commE_R)
  apply(rule hoare_vcg_all_liftE_R)
  by blast

lemmas hoare_vcg_imp_conj_liftE_R' = hoare_vcg_imp_conj_liftE_R[where Q'''="\<top>\<top>", simplified]

thm transfer_caps_loop_valid_objs
thm transfer_caps_loop_invs

definition no_refs_zombies
where
  "no_refs_zombies c s \<equiv> (\<forall>r\<in>obj_refs c.
     \<forall>a b. cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') (a, b) s \<longrightarrow>
           cte_wp_at (Not \<circ> is_zombie) (a, b) s \<and> \<not> is_zombie c)"

definition no_refs_to
where
  "no_refs_to c slot s \<equiv> (\<forall>r\<in>obj_refs c.
     \<forall>a b. cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') (a, b) s \<longrightarrow> (a, b) \<noteq> slot)"

(* the form used by this helper looks a lot less clunky *)
thm get_cap_zombies_helper
definition no_refs_zombies_weaker
where
  "no_refs_zombies_weaker cap s \<equiv> \<not> is_zombie cap \<longrightarrow>
   (\<forall>r\<in>obj_refs cap.
      \<forall>slot. cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') slot s \<longrightarrow>
             cte_wp_at (Not \<circ> is_zombie) slot s)"

(* but actually it's weaker... *)
lemma no_refs_zombies_weaker:
  "no_refs_zombies c s \<Longrightarrow> no_refs_zombies_weaker c s"
  unfolding no_refs_zombies_def no_refs_zombies_weaker_def
  by fast

lemma no_refs_zombies_stronger:
  "no_refs_zombies_weaker c s \<Longrightarrow> \<not> is_zombie c \<Longrightarrow> no_refs_zombies c s"
  unfolding no_refs_zombies_def no_refs_zombies_weaker_def
  by blast

crunch set_extra_badge, update_cdt
  for no_refs_zombies[wp]: "no_refs_zombies c"
  and no_refs_to[wp]: "no_refs_to c slot"
  (wp: crunch_wps simp: crunch_simps no_refs_zombies_def no_refs_to_def)

lemma no_refs_zombies_trans_state[simp]:
  "no_refs_zombies c (trans_state f s) = no_refs_zombies c s"
  unfolding no_refs_zombies_def
  by auto

lemma no_refs_to_trans_state[simp]:
  "no_refs_to c slot (trans_state f s) = no_refs_to c slot s"
  unfolding no_refs_to_def
  by auto

lemma no_refs_zombies_is_original_cap[simp]:
  "no_refs_zombies c (s\<lparr>is_original_cap := x\<rparr>) = no_refs_zombies c s"
  unfolding no_refs_zombies_def
  by blast

lemma no_refs_to_is_original_cap[simp]:
  "no_refs_to c slot (s\<lparr>is_original_cap := x\<rparr>) = no_refs_to c slot s"
  unfolding no_refs_to_def
  by blast

lemma get_cap_zombies_helper'[wp]:
  "\<lbrace>zombies_final\<rbrace> get_cap slot \<lbrace>no_refs_zombies_weaker\<rbrace>"
  unfolding no_refs_zombies_weaker_def
  by (wp get_cap_zombies_helper)

lemma get_cap_zombies_helper''[wp]:
  "\<lbrace>zombies_final and cte_wp_at (\<lambda>c. \<not> is_zombie c) slot\<rbrace> get_cap slot \<lbrace>no_refs_zombies\<rbrace>"
  apply(strengthen no_refs_zombies_stronger)
  apply wpsimp
   apply(wpsimp wp:get_cap_wp)
  by (clarsimp simp:cte_wp_at_def)

(* note: we prove a better lemma below *)
lemma set_cap_no_refs_zombies_old:
  "\<lbrace>no_refs_zombies c and no_refs_zombies c' and zombies_final
    and cte_wp_at ((=) c') slot and K (\<not> is_zombie c) and K (\<not> is_zombie c')\<rbrace>
     set_cap c slot \<lbrace>\<lambda>_. no_refs_zombies c\<rbrace>"
  (* unfolding no_refs_zombies_def *)
  apply(rule_tac Q'="\<lambda>_ s. cte_wp_at (\<lambda>c'. c' = c) slot s \<and> zombies_final s \<and> \<not> is_zombie c"
    in hoare_strengthen_post)
   apply(wp set_cap_sets)
   (* new_cap_zombies is more promising than set_cap_zombies when
      we can rely on the slots initially to be empty, but
      set_untyped_cap_as_full will actually be taking a non-empty src_slot
   apply(wp new_cap_zombies)
   apply(clarsimp simp:no_refs_zombies_def) *)
    (* set_cap_zombies should be usable when we know slot's cap isn't a zombie too *)
    apply(wp set_cap_zombies)
   apply clarsimp
   apply(clarsimp simp:ex_zombie_refs_def2 no_refs_zombies_def)
   apply(fastforce simp:cte_wp_at_def)
  apply(clarsimp simp:cte_wp_at_def)
  apply(rule use_valid[OF _ get_cap_zombies_helper''])
   apply blast
  apply(clarsimp simp:cte_wp_at_def)
  done

lemma no_refs_zombies_def2:
  "no_refs_zombies c s \<equiv> \<forall>r\<in>obj_refs c.
   \<forall>a b. (\<exists>cap. Some cap = caps_of_state s (a, b) \<and> r \<in> obj_refs cap) \<longrightarrow>
         (\<exists>cap. Some cap = caps_of_state s (a, b) \<and> \<not> is_zombie cap) \<and> \<not> is_zombie c"
  unfolding no_refs_zombies_def cte_wp_at_def
  by (clarsimp simp:get_cap_caps_of_state)

(* this is much more general than the earlier one we proved above,
   and it doesn't need as many preconditions *)
lemma set_cap_no_refs_zombies_other[wp]:
  "\<lbrace>no_refs_zombies c and K (\<not> is_zombie c) and K (\<not> is_zombie c')\<rbrace>
   set_cap c' slot \<lbrace>\<lambda>_. no_refs_zombies c\<rbrace>"
  unfolding no_refs_zombies_def2
  apply(wpsimp wp:set_cap_caps_of_state)
  by blast

lemma no_refs_to_def2:
  "no_refs_to c slot s \<equiv> \<forall>r\<in>obj_refs c.
   \<forall>a b. (\<exists>cap. Some cap = caps_of_state s (a, b) \<and> r \<in> obj_refs cap) \<longrightarrow> (a, b) \<noteq> slot"
  unfolding no_refs_to_def cte_wp_at_def
  by (clarsimp simp:get_cap_caps_of_state)

lemma set_cap_no_refs_to[wp]:
  "\<lbrace>no_refs_to c slot and K (slot' \<noteq> slot)\<rbrace>
   set_cap c' slot' \<lbrace>\<lambda>_. no_refs_to c slot\<rbrace>"
  unfolding no_refs_to_def2
  apply(wpsimp wp:set_cap_caps_of_state)
  by blast

lemma no_refs_zombies_max_free_index_update[simp]:
  "no_refs_zombies (max_free_index_update cap) = no_refs_zombies cap"
  unfolding no_refs_zombies_def
  by simp

lemma set_untyped_cap_as_full_no_refs_zombies_src:
  "\<lbrace>no_refs_zombies src_cap and K (\<not> is_zombie src_cap)\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>_. no_refs_zombies src_cap\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  by wpsimp

(* obj_ref_of isn't exhaustive enough to give us that the obj_refs are the same :( *)
lemma
  "obj_ref_of c = obj_ref_of c' \<Longrightarrow> no_refs_zombies c = no_refs_zombies c'"
  unfolding no_refs_zombies_def
  apply(case_tac c, simp_all)
  apply(case_tac c', simp_all)
  oops

(* it is if they're both untyped, though *)
lemma untyped_no_refs_zombies_eq:
  "is_untyped_cap c \<Longrightarrow> is_untyped_cap c' \<Longrightarrow> obj_ref_of c = obj_ref_of c' \<Longrightarrow>
   no_refs_zombies c = no_refs_zombies c'"
  unfolding no_refs_zombies_def
  apply(case_tac c, simp_all)
  apply(case_tac c', simp_all)
  done

lemma set_untyped_cap_as_full_no_refs_zombies_new:
  "\<lbrace>no_refs_zombies src_cap and no_refs_zombies new_cap
    and K (\<not> is_zombie src_cap) and K (\<not> is_zombie new_cap)\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>_. no_refs_zombies new_cap\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  by wpsimp

(* this is the most general one *)
lemma set_untyped_cap_as_full_no_refs_zombies[wp]:
  "\<lbrace>no_refs_zombies c and K (\<not> is_zombie c) and K (\<not> is_zombie src_cap)\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>_. no_refs_zombies c\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  by wpsimp

lemma set_untyped_cap_as_full_no_refs_to[wp]:
  "\<lbrace>no_refs_to c slot and K (src_slot \<noteq> slot)\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
   \<lbrace>\<lambda>_. no_refs_to c slot\<rbrace>"
  unfolding set_untyped_cap_as_full_def
  by wpsimp

crunch cap_insert
  for no_refs_to[wp]: "no_refs_to c slot"
  (wp: crunch_wps set_cap_no_refs_to simp: crunch_simps)

(*
-- lemma no_refs_zombies_NullCap[intro]:
  "no_refs_zombies NullCap s"
  unfolding no_refs_zombies_def
  by simp
*)

lemma cap_insert_no_refs_zombies[wp]:
  "\<lbrace>no_refs_zombies c and K (\<not> is_zombie c) and K (\<not> is_zombie c'') and
    (\<lambda>s. \<exists>c'. cte_wp_at ((=) c') src_slot s \<and> \<not> is_zombie c')\<rbrace>
   cap_insert c'' src_slot dest_slot
   \<lbrace>\<lambda>_. no_refs_zombies c\<rbrace>"
  unfolding cap_insert_def
  apply wpsimp
     apply(wpsimp wp:get_cap_wp)
    apply wpsimp
   apply(wpsimp wp:get_cap_wp)
  apply clarsimp
  apply(prop_tac "cap = c'")
   using cte_wp_at_eqD2 apply blast
  apply simp
  done

(*
-- crunch cap_insert
  for no_refs_zombies[wp]: "no_refs_zombies c slot"
  (wp: crunch_wps simp: crunch_simps)
*)

lemmas hoare_post_impE_R = hoare_post_impE[where E="\<top>\<top>" and E'="\<top>\<top>",
  simplified validE_R_def[symmetric], simplified]

lemma hoare_absorb_impE_R:
  "\<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>,- \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s\<rbrace>,-"
  by (metis (mono_tags, lifting) hoare_post_impE_R)

(* very ad-hoc but whatever *)
lemma hoare_absorb_double_impE_R:
  "\<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q' rv s) \<and> (Q rv s \<longrightarrow> R rv s)\<rbrace>,- \<Longrightarrow>
   \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s \<longrightarrow> R rv s\<rbrace>,-"
  using hoare_strengthen_postE_R by fastforce

lemma hoare_absorb_double_keep_impE_R:
  "\<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. (Q rv s \<longrightarrow> Q' rv s) \<and> (Q rv s \<longrightarrow> Q' rv s \<longrightarrow> R rv s)\<rbrace>,- \<Longrightarrow>
   \<lbrace> P \<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> Q' rv s \<longrightarrow> R rv s\<rbrace>,-"
  using hoare_strengthen_postE_R by fastforce

crunch store_word_offs
  for valid_cap[wp]: "\<lambda>s. s \<turnstile> c"

lemma transfer_caps_loop_colour_maintained:
  "\<lbrace>colour_invariant and
    cur_domain_list and pspace_in_kernel_window and RISCV64.valid_uses and
        (\<lambda>s.
            (
              distinct (map snd caps) \<and> 
              distinct slots \<and>
              (\<forall>(cap, o_ref, cni)\<in>(set caps).
                s \<turnstile> cap \<and>
                cte_wp_at ((=) cap) (o_ref, cni) s \<and>
                cap \<noteq> NullCap \<and>
                no_refs_zombies cap s \<and> \<not> is_zombie cap \<and>
                no_refs_to cap (o_ref, cni) s \<and>
                real_cte_at (o_ref, cni) s \<and>
                check_cap_ref cap (colour_oracle (cur_domain s)) \<and>
                valid_ptr_in_cur_domain o_ref s)) \<and>
              (\<forall>slot\<in>set slots. valid_ptr_in_cur_domain (fst slot) s \<and>
                ex_cte_cap_wp_to is_cnode_cap slot s \<and>
                cte_wp_at ((=) NullCap) slot s \<and>
                real_cte_at slot s)
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
         (* case 1 of 6 *)
         apply (wpsimp wp: set_extra_badge_colour_maintained)
          apply(wpsimp wp:hoare_vcg_conj_lift)
           apply(wpsimp simp:set_extra_badge_def wp:hoare_vcg_op_lift)
          apply(wpsimp wp:hoare_vcg_const_Ball_lift)
         apply fastforce
        (* case 2 of 6 *)
        (* I think the problem is when cap_insert uses its wp rule for invs,
           it introduces all these extra obligations that are hard to deal with.
           This is what Sai meant by the proof being "broken by invs".
           FIXME: Can we get away with relying on something weaker than invs here?
        apply(wpsimp wp_del:cap_insert_invs) *)
        (* note: cap_insert_colour_maintained was the culprit
        apply(wpsimp wp_del:cap_insert_colour_maintained) *)
        apply(wpsimp wp:hoare_vcg_op_lift cap_insert_weak_cte_wp_at)
         apply(wpsimp wp: hoare_vcg_if_lift_ER)
         apply(wpsimp wp: hoare_vcg_op_lift)
           apply(wpsimp wp:derive_cap_non_NullCap)
          apply wpsimp
           (*apply (wpsimp simp: derive_cap_def RISCV64_A.arch_derive_cap_def)
          apply (wpsimp wp: derive_cap_inv)*) (* <- stuff below seems to increase cases... may want to delete from line below till safe (exclusive) *)
         (* not longer needed if we're not propagating inv
         apply(strengthen cap_irqs_appropriate_strengthen)
         apply(strengthen real_cte_tcb_valid)
         *)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply(wp derive_cap_objrefs_iszombie)
         (* XXX can we delete?
         (* NB: no longer demanded since we stopped asking for all the invs
         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')
          apply(wpsimp wp:derive_cap_valid_cap) *)
         (* use this when not needing to reason specifically at the cap at hd slots
         apply(wp derive_cap_objrefs_iszombie)  *)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
         (* XXX: might need the below working if we ever need to strengthen the
            cte_wp_at predicate for the caps set again:
         (* see if we can get away without rv \<noteq> NullCap for a sec?
         apply(wpsimp wp:hoare_drop_impE_R) *) *)
          apply(wp derive_cap_objrefs_iszombie)

         apply (wpsimp wp:hoare_vcg_imp_conj_liftE_R')

          apply(clarsimp simp:Ball_def)
          apply(rule hoare_vcg_imp_all_liftE_R)+
          apply(rule hoare_vcg_imp_commE_R)
          apply(rule hoare_vcg_imp_liftE_R)
           apply wpsimp

          apply(wpsimp wp:hoare_vcg_imp_conj_liftE_R')
           apply(wpsimp wp:hoare_vcg_imp_liftE_R derive_cap_NullCap)
          apply(rule hoare_vcg_imp_commE_R)
          apply(rule hoare_vcg_imp_liftE_R)
           apply wpsimp

          apply(wpsimp wp:hoare_vcg_imp_conj_liftE_R')
           apply(wpsimp wp:hoare_vcg_imp_liftE_R derive_cap_NullCap)
(*
          apply(wpsimp wp:hoare_vcg_imp_conj_liftE_R')
            (* this produces noise but I don't see an easier way *)
            apply(wpsimp simp: derive_cap_def RISCV64_A.arch_derive_cap_def)
*)
           apply(wp derive_cap_objrefs_iszombie)
          apply(wp derive_cap_objrefs_iszombie)
         apply(wp derive_cap_objrefs_iszombie) *)
        apply clarsimp
        apply(clarsimp simp:check_cap_ref_in_cur_domain split_beta no_refs_to_def)
        apply(rule conjI)
         apply(meson distinct_tl)
        (* old, when we were assuming caps and slots were disjoint sets
        apply(rule conjI)
         apply(meson disjoint_iff list.set_sel(2))
        *)
        apply(rule conjI)
         apply clarsimp
         apply(rule conjI)
          apply clarsimp
          apply (metis (mono_tags, opaque_lifting) cte_wp_at_eqD2 hd_in_set prod_injects(2))
          (* old, when we were assuming caps and slots disjoint
          apply (metis (no_types, lifting) list.set_sel(1) map_set_in orthD1 prod.sel(2))
          *)
         apply clarsimp
         apply(drule (1) bspec)
         apply clarsimp
         apply(rename_tac aa b c s aaa ab ba)
         (* cap aaa is in `caps` at slot (ab, ba) *)
         (* cap aa is at slot (b, c) and it came from `caps`. *)
         (* We are being asked to show that slot (ab, ba) \<noteq> (b, c).
            I think we should have this if all slots in `caps` are distinct. *)
         apply(rule context_conjI)
          apply(metis image_eqI prod.sel(2))
         apply(rule conjI)
          apply(meson list.set_sel(2))
         apply blast
        apply clarsimp
        apply(rename_tac aa b c s ab ba)
        apply(drule_tac x="(ab, ba)" in bspec)
         apply(meson list.set_sel(2))
        apply clarsimp
        apply (metis (full_types, opaque_lifting) cte_wp_at_eqD2 distinct.simps(2) list.collapse)
       (* case 3 of 6 *)
       apply(wpsimp wp:hoare_vcg_op_lift cap_insert_weak_cte_wp_at)
        apply(wpsimp wp: hoare_vcg_if_lift_ER)
        apply(wpsimp wp: hoare_vcg_op_lift)
          apply(wpsimp wp:derive_cap_non_NullCap)
         apply wpsimp
        (* NB: this proof is identical to the last case. try to deduplicate? *)
        apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
        apply (wp hoare_vcg_imp_conj_liftE_R', wp hoare_drop_impE_R)
        apply(wp derive_cap_objrefs_iszombie)
       apply clarsimp
       apply(clarsimp simp:check_cap_ref_in_cur_domain split_beta)
       apply(rule conjI)
        apply(meson distinct_tl)
       (* old, when we were assuming caps and slots disjoint
       apply(rule conjI)
        apply(meson disjoint_iff list.set_sel(2))
       *)
       apply(rule conjI)
        apply(prop_tac "(\<exists>c'. cte_wp_at ((=) c') (b, c) s \<and> \<not> is_zombie c')")
         using cte_wp_at_norm
         apply blast
        apply clarsimp
        apply(rule conjI)
         apply clarsimp
         apply (metis (mono_tags, opaque_lifting) cte_wp_at_eqD2 hd_in_set prod_injects(2))
         (* old, when we were assuming caps and slots disjoint
         apply (metis (no_types, lifting) list.set_sel(1) map_set_in orthD1 prod.sel(2))
         *)
        apply clarsimp
        apply(drule (1) bspec)
        apply clarsimp
        apply(rule context_conjI)
         apply(metis image_eqI prod.sel(2))
        apply(meson list.set_sel(2))
       apply clarsimp
       apply(drule_tac x="(ab, ba)" in bspec)
        apply(meson list.set_sel(2))
       apply clarsimp
       apply (metis (full_types, opaque_lifting) cte_wp_at_eqD2 distinct.simps(2) list.collapse)
      (* case 4 of 6 *)
      (* this one's just like case 1 *)
      apply (wpsimp wp: set_extra_badge_colour_maintained)
       apply(wpsimp simp: set_extra_badge_def wp:hoare_vcg_op_lift)
      apply(wpsimp wp:hoare_vcg_const_Ball_lift)
      apply fastforce
     (* the 5th and 6th cases are free! *)
     apply wpsimp
    apply wpsimp
    done
qed

lemma resolve_address_bits_ret_colour:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref (fst args) (colour_oracle (cur_domain s)))
    and cur_domain_list and pspace_in_kernel_window and RISCV64.valid_uses\<rbrace>
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
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref (fst args) (colour_oracle (cur_domain s)))
    and cur_domain_list and pspace_in_kernel_window and RISCV64.valid_uses\<rbrace>
     resolve_address_bits args
   \<lbrace>\<lambda>rv s. valid_ptr_in_cur_domain (fst (fst rv)) s\<rbrace>,-"
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

lemma hoare_strengthen_post_impE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> R rv s\<rbrace>,-; \<And>rv s. Q rv s \<Longrightarrow> Q' rv s \<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s\<rbrace>,-"
  unfolding validE_R_def
  by (simp add: hoare_strengthen_postE)

lemma hoare_strengthen_imp_postE_R:
  "\<lbrakk> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R' rv s \<and> R rv s\<rbrace>,-\<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<longrightarrow> R rv s\<rbrace>,-"
  unfolding validE_R_def
  by (simp add: hoare_strengthen_postE)

(* duplicate from MSpec_AI, for tweaking. turns out it's the same cn_ref *)
lemma resolve_address_bits'_cte_wp_at_succeed:
  "\<lbrace>\<lambda>s. (\<exists>sz_bits. fst args = CNodeCap cn_ref sz_bits guard \<and>
       length (snd args) = sz_bits + size guard \<and>
       \<comment> \<open>the guard is a prefix of the raw 64-bit list given via the args\<close>
       guard \<le> snd args \<and>
       cte_wp_at ((=) mycap) (cn_ref, drop (size guard) (snd args)) s)\<rbrace>
     resolve_address_bits' z args
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) mycap) (cn_ref, drop (size guard) (snd args)) s\<rbrace>,
   \<lbrace>\<lambda>rv s. False\<rbrace>"
proof (induct args rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]
    apply (simp only: cap.simps)
    apply(rule conjI)
     apply (clarsimp simp add: in_monad Let_def)
     apply(force simp:fail_def in_returnOk split:if_splits)
    apply(rename_tac obj_ref nat list)
    apply (case_tac "nat + length list = 0")
     apply (simp add: fail_def)
    apply (simp only: if_False)
    apply clarify
    apply (simp only: K_bind_def in_bindE_R)
    apply (elim conjE exE)
    apply (simp only: split: if_split_asm)
     (* case: rest = [], so returnOk ((obj_ref, offset), []) happens *)
     apply (clarsimp simp add: in_monad Let_def)
    (* for microkit caps, we don't hit the other cases *)
    apply(clarsimp simp:in_monad)
    done
qed

thm resolve_address_bits'_specific
lemma resolve_address_bits'_cte_wp_at:
  "\<lbrace>cte_wp_at ((=) mycap) (cn_ref, drop (size guard) (snd args)) and
      K (fst args = CNodeCap cn_ref sz_bits guard \<and>
         length (snd args) = sz_bits + size guard \<and>
         guard \<le> snd args)\<rbrace>
     resolve_address_bits' z args
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) mycap) (fst rv) s\<rbrace>,-"
proof (induct args rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]
    apply(force simp:fail_def in_returnOk split:if_splits)
    done
qed

lemma resolve_address_bits_cte_wp_at:
  "\<lbrace>cte_wp_at ((=) mycap) (cn_ref, drop (size guard) (snd args)) and
      K (fst args = CNodeCap cn_ref sz_bits guard \<and>
         length (snd args) = sz_bits + size guard \<and>
         guard \<le> snd args)\<rbrace>
     resolve_address_bits args
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) mycap) (fst rv) s\<rbrace>,-"
  unfolding resolve_address_bits_def
  by (wp resolve_address_bits'_cte_wp_at)

lemma resolve_address_bits'_cte_wp_at':
  "\<lbrace>cte_wp_at ((=) mycap) (cn_ref, cni) and
      K (\<exists> guard sz_bits. cap = CNodeCap cn_ref sz_bits guard \<and>
         length cref = sz_bits + size guard)\<rbrace>
     resolve_address_bits' z (cap, cref)
   \<lbrace>\<lambda>rv s. fst rv = (cn_ref, cni) \<longrightarrow> cte_wp_at ((=) mycap) (cn_ref, cni) s\<rbrace>,-"
proof (induct "(cap, cref)" rule: resolve_address_bits'.induct)
  case (1 z)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]    
    apply(clarsimp simp:fail_def in_returnOk split:if_splits)
    by (metis in_monad(7,8) whenE_bindE_throwError_to_if)
qed

lemma resolve_address_bits_cte_wp_at':
  "\<lbrace>cte_wp_at ((=) mycap) (cn_ref, cni) and
      K (\<exists>guard sz_bits. cap = CNodeCap cn_ref sz_bits guard \<and>
         length cref = sz_bits + size guard)\<rbrace>
     resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. fst rv = (cn_ref, cni) \<longrightarrow> cte_wp_at ((=) mycap) (cn_ref, cni) s\<rbrace>,-"
  unfolding resolve_address_bits_def
  by (wp resolve_address_bits'_cte_wp_at')

lemma resolve_address_bits'_P_rv:
  "\<lbrace>\<lambda>s. P cn_ref cni s \<and> cap = CNodeCap cn_ref sz_bits guard \<and>
       length cref = sz_bits + size guard \<and> cref = cni\<rbrace>
     resolve_address_bits' z (cap, cref)
   \<lbrace>\<lambda>rv s. fst rv = (cn_ref, cni) \<longrightarrow> P cn_ref cni s\<rbrace>,-"
proof (induct "(cap, cref)" rule: resolve_address_bits'.induct)
  case (1 z)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]    
    apply(clarsimp simp:fail_def in_returnOk split:if_splits)
    by (metis in_monad(7,8) whenE_bindE_throwError_to_if)
qed

lemma resolve_address_bits_P_rv:
  "\<lbrace>\<lambda>s. P cn_ref cni s \<and> cap = CNodeCap cn_ref sz_bits guard \<and>
       length cref = sz_bits + size guard \<and> cref = cni\<rbrace>
     resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. fst rv = (cn_ref, cni) \<longrightarrow> P cn_ref cni s\<rbrace>,-"
  unfolding resolve_address_bits_def
  by (wp resolve_address_bits'_P_rv)

lemma resolve_address_bits'_P_rv_concise:
  "\<lbrace>\<lambda>s. P (cn_ref, drop (length guard) cref) s \<and> cap = CNodeCap cn_ref sz_bits guard \<and>
       length cref = sz_bits + size guard\<rbrace>
     resolve_address_bits' z (cap, cref)
   \<lbrace>\<lambda>rv s. P (fst rv) s\<rbrace>,-"
proof (induct "(cap, cref)" rule: resolve_address_bits'.induct)
  case (1 z)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]    
    apply(clarsimp simp:fail_def in_returnOk whenE_def split:if_splits)
    apply(simp add: in_monad(8))
    done
qed

lemma resolve_address_bits_P_rv_concise:
  "\<lbrace>\<lambda>s. P (cn_ref, drop (length guard) cref) s \<and> cap = CNodeCap cn_ref sz_bits guard \<and>
       length cref = sz_bits + size guard\<rbrace>
     resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. P (fst rv) s\<rbrace>,-"
  unfolding resolve_address_bits_def
  by (wp resolve_address_bits'_P_rv_concise)

lemma resolve_address_bits'_P_refonly:
  "\<lbrace>\<lambda>s. P cn_ref s \<and>
         cap = CNodeCap cn_ref sz_bits guard \<and>
         length cref = sz_bits + size guard\<rbrace>
     resolve_address_bits' z (cap, cref)
   \<lbrace>\<lambda>rv s. (\<exists> cni. fst rv = (cn_ref, cni)) \<longrightarrow> P cn_ref s\<rbrace>,-"
proof (induct "(cap, cref)" rule: resolve_address_bits'.induct)
  case (1 z)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]    
    apply(clarsimp simp:fail_def in_returnOk split:if_splits)
    by (smt (z3) fst_conv in_monad(6,7,8) sum.simps(2) throwError_def whenE_def)
    (* old:
    by (metis (full_types) in_monad(7,8) whenE_bindE_throwError_to_if) *)
qed

lemma resolve_address_bits_P_refonly:
  "\<lbrace>\<lambda>s. P cn_ref s \<and>
         cap = CNodeCap cn_ref sz_bits guard \<and>
         length cref = sz_bits + size guard\<rbrace>
     resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. (\<exists> cni. fst rv = (cn_ref, cni)) \<longrightarrow> P cn_ref s\<rbrace>,-"
  unfolding resolve_address_bits_def
  by (wp resolve_address_bits'_P_refonly)

lemma resolve_address_bits'_P_refonly_concise:
  "\<lbrace>\<lambda>s. P cn_ref s \<and>
      cap = CNodeCap cn_ref sz_bits guard \<and>
      length cref = sz_bits + size guard\<rbrace>
     resolve_address_bits' z (cap, cref)
   \<lbrace>\<lambda>rv s. P (fst (fst rv)) s\<rbrace>,-"
proof (induct "(cap, cref)" rule: resolve_address_bits'.induct)
  case (1 z)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]    
    apply(clarsimp simp:fail_def in_returnOk split:if_splits)
    by (smt (z3) fst_conv in_monad(6,7,8) sum.simps(2) throwError_def whenE_def)
qed

lemma resolve_address_bits_P_refonly_concise:
  "\<lbrace>\<lambda>s. P cn_ref s \<and>
         cap = CNodeCap cn_ref sz_bits guard \<and>
         length cref = sz_bits + size guard\<rbrace>
     resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. P (fst (fst rv)) s\<rbrace>,-"
  unfolding resolve_address_bits_def
  by (wp resolve_address_bits'_P_refonly_concise)

lemma resolve_address_bits'_cte_wp_at_P_rv:
  "\<lbrace>(\<lambda>s. cte_wp_at ((=) mycap) (cn_ref, cni) s \<longrightarrow> P cn_ref cni s) and
      K (\<exists> guard sz_bits. cap = CNodeCap cn_ref sz_bits guard \<and>
         length cref = sz_bits + size guard)\<rbrace>
     resolve_address_bits' z (cap, cref)
   \<lbrace>\<lambda>rv s. fst rv = (cn_ref, cni) \<longrightarrow> cte_wp_at ((=) mycap) (cn_ref, cni) s \<longrightarrow> P cn_ref cni s\<rbrace>,-"
proof (induct "(cap, cref)" rule: resolve_address_bits'.induct)
  case (1 z)
  show ?case
    apply (clarsimp simp add: validE_R_def validE_def valid_def split: sum.split)
    apply (subst (asm) resolve_address_bits'.simps)
    apply (cases cap)
              defer 6 (* cnode *)
          apply (auto simp: in_monad)[11]    
    apply(clarsimp simp:fail_def in_returnOk split:if_splits)
    by (metis in_monad(7,8) whenE_bindE_throwError_to_if)
qed

lemma resolve_address_bits_cte_wp_at_P_rv:
  "\<lbrace>(\<lambda>s. cte_wp_at ((=) mycap) (cn_ref, cni) s \<longrightarrow> P cn_ref cni s) and
      K (\<exists>guard sz_bits. cap = CNodeCap cn_ref sz_bits guard \<and>
         length cref = sz_bits + size guard)\<rbrace>
     resolve_address_bits (cap, cref)
   \<lbrace>\<lambda>rv s. fst rv = (cn_ref, cni) \<longrightarrow> cte_wp_at ((=) mycap) (cn_ref, cni) s \<longrightarrow> P cn_ref cni s\<rbrace>,-"
  unfolding resolve_address_bits_def
  by (wp resolve_address_bits'_cte_wp_at_P_rv)

term obj_at
lemma lookup_slot_for_cnode_op_valid_ptr_in_cur_domain:
  "\<lbrace>\<lambda>s. croot = CNodeCap cn_ref sz_bits guard \<and> 
      obj_at ((=) (CNode sz_bits contents)) cn_ref s \<and>
      length ptr = sz_bits + length guard \<and>
      length ptr \<le> depth \<and>
      valid_ptr_in_cur_domain cn_ref s\<rbrace>
   lookup_slot_for_cnode_op is_source croot ptr depth
  \<lbrace>\<lambda>rv s. valid_ptr_in_cur_domain (fst rv) s\<rbrace>,-"
  unfolding lookup_slot_for_cnode_op_def
  apply wp
     (* NB: wpsimp here introduces a forall, so avoid it *)
     apply clarsimp
     apply wp
      (* NB: wpsimp here introduces a forall, so avoid it
      apply wpsimp *)
      apply clarsimp
      apply wpsimp
     apply clarsimp
     apply wpsimp
     apply(rule hoare_drop_impE_R)
     apply(wp resolve_address_bits_P_refonly_concise)
    apply wp
   apply wp
  by auto

definition load_cap_transfer_preconds :: "64 word \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> cap_ref \<Rightarrow> cap_ref \<Rightarrow>
  'a state \<Rightarrow> bool"
where
  "load_cap_transfer_preconds buffer sz_bits guard root_cr index_cr s \<equiv>
   \<forall>x\<in>fst (loadWord
           (buffer + word_of_nat (msg_max_length + msg_max_extra_caps + 2) * word_size)
           (machine_state s)).
    \<forall>xa xb.
       x = (xa, xb) \<longrightarrow>
       data_to_cptr xa = root_cr \<and>
       (\<forall>x\<in>fst (loadWord
                  (buffer +
                   word_of_nat (msg_max_length + msg_max_extra_caps + 2) * word_size +
                   word_size)
                  (machine_state (s\<lparr>machine_state := xb\<rparr>))).
           \<forall>xa xb.
              x = (xa, xb) \<longrightarrow>
              buffer + word_of_nat (msg_max_length + msg_max_extra_caps + 2) * word_size +
              2 * word_size &&
              mask 3 =
              0 \<longrightarrow>
              (unat::64 word \<Rightarrow> nat)
               (word_rcat
                 (map (\<lambda>i. underlying_memory xb
                             (buffer +
                              word_of_nat (msg_max_length + msg_max_extra_caps + 2) *
                              word_size +
                              2 * word_size +
                              (7 - word_of_int i)))
                   [0..7])) =
              sz_bits + length guard \<and>
              data_to_cptr xa = index_cr \<and>
              sz_bits + length guard = 64)"

definition ct_receive_conds
where
  "ct_receive_conds cts root_cr index_cr depth \<equiv>
     unat (ct_receive_depth cts) = depth \<and>
     ct_receive_root cts = root_cr \<and>
     length (ct_receive_root cts) = depth \<and>
     \<comment> \<open>ct_receive_index cts = index_cr \<and>\<close>
     length (ct_receive_index cts) = depth"

lemma load_cap_transfer_receive_conds:
  "\<lbrace>\<lambda>s. load_cap_transfer_preconds buffer sz_bits guard root_cr index_cr s\<rbrace>
   load_cap_transfer buffer
   \<lbrace>\<lambda>rv s. ct_receive_conds rv root_cr index_cr (sz_bits + length guard)\<rbrace>"
  unfolding load_cap_transfer_def captransfer_from_words_def
  apply wpsimp
      apply(wpsimp simp:RISCV64.loadWord_def)
     apply wpsimp
     apply(wpsimp simp:do_machine_op_def)
    apply(wpsimp simp:do_machine_op_def)
   apply wpsimp
  apply(clarsimp simp:load_cap_transfer_preconds_def ct_receive_conds_def)
  by fastforce

lemma get_cap_specific:
  "\<lbrace>\<lambda>s.(kheap s (fst c) = Some (CNode sz contents) \<and> well_formed_cnode_n sz contents
       \<and> contents (snd c) = Some cap) \<or>
     (kheap s (fst c) = Some (TCB tcb) \<and> tcb_cnode_map tcb (snd c) = Some cap)\<rbrace>
   get_cap c
   \<lbrace>\<lambda>rv s. rv = cap\<rbrace>"
  unfolding get_cap_def get_object_def
  apply wpsimp
  by fastforce

lemma get_cap_tcb:
  "\<lbrace>\<lambda>s. kheap s (fst c) = Some (TCB tcb) \<and> tcb_cnode_map tcb (snd c) = Some cap\<rbrace>
     get_cap c
   \<lbrace>\<lambda>rv s. rv = cap\<rbrace>"
  unfolding get_cap_def get_object_def
  by wpsimp

term do_ipc_transfer
  (* the recv_buffer comes from `lookup_ipc_buffer True receiver` *)
  term lookup_ipc_buffer (* this consults a ArchObjectCap FrameCap of the receiver's *)
  term aobj_ref
term do_normal_transfer
term get_receive_slots
term transfer_caps
term load_cap_transfer
term captransfer_from_words
lemma get_receive_slots_valid_ptr_in_cur_domain_Some[wp]:
  "\<lbrace>\<lambda>s. invs s \<and> colour_invariant s \<and>
     valid_ptr_in_cur_domain receiver s \<and>
     valid_ptr_in_cur_domain cn_ref s \<and>
     get_tcb receiver s = Some tcb \<and>
     \<comment> \<open>This is the cnode that lookup_slot_for_thread (called by get_receive_slots
       via lookup_cap) receives to call resolve_address_bits on\<close>
     tcb_ctable tcb = CNodeCap cn_ref sz_bits guard \<and>
     obj_at ((=) (CNode sz_bits contents)) cn_ref s \<and>
     contents (drop (length guard) root_cr) = Some (CNodeCap cn_ref sz_bits guard) \<and>
     well_formed_cnode_n sz_bits contents \<and>
     load_cap_transfer_preconds buffer sz_bits guard root_cr index_cr s \<and>
     sz_bits + length guard = 64\<rbrace>
   get_receive_slots receiver (Some buffer)
   \<lbrace>\<lambda>rv s. \<forall>slot \<in> set rv. valid_ptr_in_cur_domain (fst slot) s\<rbrace>"
  apply (simp add: split_def whenE_def split del: if_split)
  apply wpsimp
      (* perhaps avoid get_cap_wp because it introduces forall-quantified cte_wp_at.
         furthermore we can just drop the rv precond and use get_cap_inv.
      apply(wpsimp wp:get_cap_wp) *)
      apply(wp hoare_drop_imp)
     apply wp
     apply(wp lookup_slot_for_cnode_op_valid_ptr_in_cur_domain[where
       sz_bits=sz_bits and guard=guard and cn_ref=cn_ref and contents=contents])
    (* NB: lookup_cap called by get_receive_slots *)
    apply(clarsimp simp:lookup_cap_def)
    (* note, there's a lot of avoiding wpsimp at certain points from here
       to prevent introducing unwanted forall-quantifiers *)
    apply wp
     apply clarsimp
     apply wpsimp
     apply(rule hoare_vcg_conj_lift)
      apply(rule get_cap_specific[where sz=sz_bits and contents=contents and tcb=tcb])
     apply wp
    apply clarsimp
    apply wp
    (* NB: lookup_slot_for_thread called by get_receive_slots via lookup_cap *)
    apply(clarsimp simp:lookup_slot_for_thread_def)
    apply wpsimp
     apply(wp resolve_address_bits_P_rv_concise[where sz_bits=sz_bits and guard=guard and cn_ref=cn_ref])
    apply wpsimp
   apply wpsimp
   apply(rule hoare_vcg_imp_lift)
    apply wp
   apply(rule_tac Q'="\<lambda>rv s. ct_receive_conds rv root_cr index_cr (sz_bits + length guard) \<and>
     valid_ptr_in_cur_domain cn_ref s \<and>
     tcb_ctable (the (get_tcb receiver s)) = CNodeCap cn_ref sz_bits guard \<and>
     obj_at ((=) (CNode sz_bits contents)) cn_ref s \<and>
     kheap s receiver = Some (TCB tcb) \<and>
     contents (drop (length guard) root_cr) = Some (CNodeCap cn_ref sz_bits guard) \<and>
     well_formed_cnode_n sz_bits contents"
     in hoare_strengthen_post)
    apply(wp hoare_vcg_conj_lift)
     apply(wp load_cap_transfer_receive_conds)
    apply wpsimp
   apply(clarsimp simp:ct_receive_conds_def)
   apply(clarsimp simp:obj_at_def)
  apply clarsimp
  apply(clarsimp simp:get_tcb_def split:option.splits kernel_object.splits)
  done

lemma get_receive_slots_valid_ptr_in_cur_domain_None[wp]:
  "\<lbrace>\<top>\<rbrace> get_receive_slots receiver None
   \<lbrace>\<lambda>rv s. \<forall>slot \<in> set rv. valid_ptr_in_cur_domain (fst slot) s\<rbrace>"
  apply wpsimp
  done

declare get_receive_slots.simps[simp del]

lemma get_receive_slots_valid_ptr_in_cur_domain[wp]:
  "\<lbrace>\<lambda>s. case rbuf of Some buffer \<Rightarrow>
     (invs s \<and> colour_invariant s \<and>
     valid_ptr_in_cur_domain receiver s \<and>
     valid_ptr_in_cur_domain cn_ref s \<and>
     get_tcb receiver s = Some tcb \<and>
     \<comment> \<open>This is the cnode that lookup_slot_for_thread (called by get_receive_slots
       via lookup_cap) receives to call resolve_address_bits on\<close>
     tcb_ctable tcb = CNodeCap cn_ref sz_bits guard \<and>
     obj_at ((=) (CNode sz_bits contents)) cn_ref s \<and>
     contents (drop (length guard) root_cr) = Some (CNodeCap cn_ref sz_bits guard) \<and>
     well_formed_cnode_n sz_bits contents \<and>
     load_cap_transfer_preconds buffer sz_bits guard root_cr index_cr s \<and>
     sz_bits + length guard = 64) | None \<Rightarrow> True\<rbrace>
   get_receive_slots receiver rbuf
   \<lbrace>\<lambda>rv s. \<forall>slot \<in> set rv. valid_ptr_in_cur_domain (fst slot) s\<rbrace>"
  apply(case_tac rbuf)
   prefer 2
   apply clarsimp
   apply wpsimp
  apply wpsimp
  done

lemma hoare_vcg_rv_Ball_conj_lift:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>r\<in>set rv. Q r s\<rbrace> \<Longrightarrow> \<lbrace>P'\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>r\<in>set rv. Q' r s\<rbrace> \<Longrightarrow>
   \<lbrace>P and P'\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>r\<in>set rv. Q r s \<and> Q' r s\<rbrace>"
  unfolding valid_def
  by fast

thm get_receive_slots.simps
term "c::captransfer"

lemma transfer_caps_colour_maintained[wp]:
  "\<lbrace>case rbuf of Some buffer \<Rightarrow> colour_invariant and
     (\<lambda>s. distinct (map snd caps) \<and>
        (\<forall>(cap, o_ref, cni)\<in>(set caps).
        \<comment> \<open>Also asked for by transfer_caps_loop_colour_maintained:\<close>
        s \<turnstile> cap \<and>
        cte_wp_at ((=) cap) (o_ref, cni) s \<and>
        cap \<noteq> NullCap \<and>
        no_refs_zombies cap s \<and> \<not> is_zombie cap \<and>
        no_refs_to cap (o_ref, cni) s \<and>
        real_cte_at (o_ref, cni) s \<and>
        \<comment> \<open>Here originally:\<close>
        check_cap_ref cap (colour_oracle (cur_domain s)) \<and>
        valid_ptr_in_cur_domain o_ref s)) and
     (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb receiver s)) (colour_oracle (cur_domain s)) \<and>
        \<comment> \<open>Stuff now asked for by get_receive_slots_valid_ptr_in_cur_domain\<close>
        valid_ptr_in_cur_domain receiver s \<and>
        valid_ptr_in_cur_domain cn_ref s \<and>
        get_tcb receiver s = Some tcb \<and>
        tcb_ctable tcb = CNodeCap cn_ref sz_bits guard \<and>
        obj_at ((=) (CNode sz_bits contents)) cn_ref s \<and>
        contents (drop (length guard) root_cr) = Some (CNodeCap cn_ref sz_bits guard) \<and>
        well_formed_cnode_n sz_bits contents \<and>
        load_cap_transfer_preconds buffer sz_bits guard root_cr index_cr s \<and>
        sz_bits + length guard = 64)
     and invs
     | None \<Rightarrow> colour_invariant\<rbrace>
   transfer_caps info caps endpoint receiver rbuf
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding transfer_caps_def
  apply(case_tac rbuf)
   (* FIXME: the only reason this is not an issue is its preconds aren't conditional on rbuf,
      but this is sort of a flaky way to go about things *)
   apply (wpsimp wp: transfer_caps_loop_colour_maintained)
  apply (wpsimp wp: transfer_caps_loop_colour_maintained)
   (* This was needed when we didn't case split on whether rbuf = (Some buffer)
   apply (wpsimp wp: hoare_vcg_op_lift weak_if_wp') *)
   apply(rule hoare_vcg_rv_Ball_conj_lift)
    apply(rule get_receive_slots_valid_ptr_in_cur_domain[where
      cn_ref=cn_ref and tcb=tcb and sz_bits=sz_bits and guard=guard and contents=contents and
      root_cr=root_cr and index_cr=index_cr])
   apply(wp hoare_vcg_rv_Ball_conj_lift)
  apply clarsimp
  apply(frule invs_valid_objs)
  apply(frule RISCV64.invs_valid_uses)
  apply(clarsimp simp:invs_def valid_state_def)
  done

lemma transfer_caps_colour_maintained_None[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     transfer_caps info caps endpoint receiver None
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  unfolding transfer_caps_def
  by wpsimp

lemma copy_mrs_colour_maintained[wp]:
  "\<lbrace>colour_invariant\<rbrace>
     copy_mrs  sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
    apply (rule conjI)
     apply (rule impI)
  by (wpsimp wp: mapM_wp[where S="UNIV"] store_word_offs_colour_maintained load_word_offs_P as_user_colour_maintained)+

(* XXX briefly considered this, but not sure about it. might still be a reasonable idea
lemma copy_mrs_receiver_tcb:
  "\<lbrace>\<lambda>s. check_cap_ref (tcb_ctable (the (get_tcb receiver s))) (colour_oracle (cur_domain s))\<rbrace>
     copy_mrs sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_ s. check_cap_ref (tcb_ctable (the (get_tcb receiver s))) (colour_oracle (cur_domain s))\<rbrace>"
  unfolding copy_mrs_def
  apply wpsimp
  oops

lemma copy_mrs_sender_tcb:
  "\<lbrace>\<lambda>s. P (get_tcb sender s) (cur_domain s)\<rbrace>
     copy_mrs sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_ s. P (get_tcb sender s) (cur_domain s)\<rbrace>"
  unfolding copy_mrs_def
  apply wpsimp
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
  apply (cases "receiver = sender"; clarsimp)
   apply(fastforce simp:RISCV64.pspace_in_kernel_window_def RISCV64.kernel_window_2_def
     split:option.splits kernel_object.splits)
  apply(fastforce simp:RISCV64.pspace_in_kernel_window_def RISCV64.kernel_window_2_def
    split:option.splits kernel_object.splits)
  try0
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
*)

lemma do_normal_transfer_colour_maintained:
  "\<lbrace>colour_invariant and invs and
    (case rbuf of Some rbuffer \<Rightarrow>
     \<lambda>s. check_cap_ref (tcb_ctable (the (get_tcb receiver s))) (colour_oracle (cur_domain s))
      | None \<Rightarrow> \<top>) and
    (case sbuf of Some sbuffer \<Rightarrow>
     \<lambda>s. check_cap_ref (tcb_ctable (the (get_tcb sender s))) (colour_oracle (cur_domain s))
      | None \<Rightarrow> \<top>)\<rbrace>
     do_normal_transfer sender sbuf endpoint badge grant receiver rbuf
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply(case_tac "rbuf = None")
   prefer 2 (* Important to do the Some case first as the None cases have trivial preconds *)
   apply (wpsimp simp: do_normal_transfer_def)
      apply(rule hoare_vcg_conj_lift)
       apply(wpsimp wp:hoare_vcg_op_lift copy_mrs_cur_domain)
       defer (* FIXME: new preconditions demanded by transfer_caps_loop_colour_maintained *)
      apply(wpsimp wp:hoare_vcg_conj_lift)
       apply (wpsimp simp: copy_mrs_def)
        apply (rule conjI)
         apply (rule impI)
         apply (wpsimp simp: store_word_offs_def as_user_def do_machine_op_def load_word_offs_def
           wp: mapM_wp[where S="UNIV"] load_word_offs_P)+
          apply (simp add: get_tcb_def)
         apply simp
        apply (wpsimp simp: store_word_offs_def do_machine_op_def load_word_offs_def
           wp: mapM_wp[where S="UNIV"])
         apply (simp add: get_tcb_def)
        apply simp
       apply (wpsimp simp: store_word_offs_def as_user_def do_machine_op_def load_word_offs_def
         wp: mapM_wp[where S="UNIV"] set_object_wp)
        apply (simp add: get_tcb_def)
        apply (cases "receiver = sender"; clarsimp)
       apply simp
      (* FIXME: new preconditions demanded by get_receive_slots_valid_ptr_in_cur_domain *)
      defer
     apply wpsimp
      apply(rule hoare_vcg_conj_liftE_R)
       defer (* FIXME: distinctness req is new *)
      apply (simp add: lookup_extra_caps_def
                       lookup_cap_and_slot_def
                       lookup_slot_for_thread_def)
      apply wpsimp
       apply (wp add: mapME_set)
           (* again, avoid some wpsimps and get_cap_wp to avoid introduced forall quantifiers? *)
           apply clarsimp
           apply wp
           apply wpsimp
           apply (wp add: get_cap_wp)
          apply wpsimp
           apply (wp add: hoare_vcg_all_liftE_R)
           apply(wp resolve_address_bits_P_rv_concise)
          apply wpsimp
          defer (* FIXME: new reqs *)
         apply wpsimp+
       apply (wpsimp wp: mapME_wp')
      apply (wpsimp simp: store_word_offs_def do_machine_op_def load_word_offs_def wp: mapM_wp[where S="UNIV"])
     apply wpsimp+
  (* trivial case where rbuf = None *)
  apply(wpsimp simp: do_normal_transfer_def)
  (* XXX: old final steps by Sai, not sure what these were targeted at
  apply (cases "receiver = sender"; clarsimp)
   apply(fastforce simp:RISCV64.pspace_in_kernel_window_def RISCV64.kernel_window_2_def
     split:option.splits kernel_object.splits)
  apply(fastforce simp:RISCV64.pspace_in_kernel_window_def RISCV64.kernel_window_2_def
    split:option.splits kernel_object.splits) *)
  sorry

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

(* FIXME: broken now that do_normal_transfer_colour_maintained has new reqs *)
crunch make_fault_msg, do_ipc_transfer
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps)

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

-- crunch call_kernel for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update crunch_simps
     wp: crunch_wps RISCV64.arch_get_sanitise_register_info_inv
         RISCV64.handle_arch_fault_reply_inv) *)

(* Arch-specific *)

crunch set_pt
  for colour_maintained[wp]: colour_invariant
  (wp: crunch_wps simp: crunch_simps)

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
  "\<lbrace>\<lambda>s. colour_invariant s \<and> cur_domain_list s \<and> pspace_in_kernel_window s \<and> valid_uses s \<and>
       (\<forall> x. ((), x) \<in> fst (setIRQTrigger irq trigger (machine_state s)) \<longrightarrow>
         invs (s\<lparr>machine_state := x, interrupt_states :=
           (\<lambda>y. if y = irq then IRQSignal else (interrupt_states (s\<lparr>machine_state := x\<rparr>) y))\<rparr>)) \<and>
       valid_ptr_in_cur_domain (fst control_slot) s \<and>
       valid_ptr_in_cur_domain (fst handler_slot) s \<and>
       check_cap_ref (IRQHandlerCap irq) (colour_oracle (cur_domain s))\<rbrace>
     arch_invoke_irq_control (RISCVIRQControlInvocation irq handler_slot control_slot trigger)
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp wp:crunch_wps maskInterrupt_invs
    simp:crunch_simps set_irq_state_def valid_ptr_in_cur_domain_def)

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
  "\<lbrace>colour_invariant and cur_domain_list and pspace_in_kernel_window and valid_uses
    and valid_ptr_in_cur_domain sender and
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
  by wpsimp

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
         apply(wpsimp simp:get_thread_state_def wp:thread_get_wp)
        apply wpsimp
       apply wpsimp
       apply(wpsimp simp:get_thread_state_def wp:thread_get_wp)
      apply wpsimp
      apply(wpsimp simp:get_thread_state_def wp:thread_get_wp)
     apply wpsimp
     apply(wpsimp simp:get_thread_state_def wp:thread_get_wp)
    apply(wpsimp wp:hoare_vcg_op_lift | rule conjI)+
      apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
     apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
    apply(wpsimp simp:set_simple_ko_def wp:set_object_wp get_object_wp)
   apply(wpsimp simp:get_simple_ko_def wp:get_object_wp)
  apply clarsimp
  (* FIXME - a bit horrendous due to use of low-level wp rules above *)
  apply(clarsimp simp:valid_ptr_in_cur_domain_def obj_at_def check_cap_ref_def)
  apply safe
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
-- crunch call_kernel for colour_maintained: "colour_invariant"
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
