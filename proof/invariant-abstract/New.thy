theory New
  imports
    KernelInit_AI
    "$L4V_ARCH/ArchDetSchedSchedule_AI"
begin
section "Initialisation"
axiomatization
  colour_oracle :: "domain \<Rightarrow> obj_ref set"
  \<comment>\<open>where
    colour_oracle_no_overlap: "x \<noteq> y \<Longrightarrow> (colour_oracle x \<inter> colour_oracle y = {})" and
    colour_oracle_cur_thread: "\<forall>s. cur_thread s \<in> (colour_oracle (cur_domain s))"\<close>

definition
  check_cap_ref :: "cap \<Rightarrow> obj_ref set \<Rightarrow> bool"
  where
    "check_cap_ref cap obj_set \<equiv> obj_refs cap \<subseteq> obj_set"

term "ArchInvariants_AI.RISCV64.obj_addrs" (* should be used everywhere? *)

fun
  check_tcb_state :: "thread_state \<Rightarrow> obj_ref set \<Rightarrow> bool"
where
  "check_tcb_state (BlockedOnReceive obj_ref _) obj_dom = (obj_ref \<in> obj_dom)"
 |"check_tcb_state (BlockedOnSend obj_ref _) obj_dom = (obj_ref \<in> obj_dom)"
 |"check_tcb_state (BlockedOnNotification obj_ref) obj_dom = (obj_ref \<in> obj_dom)"
 |"check_tcb_state _ _ = True"

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
    tcb_ipc_buffer t \<in> obj_dom \<and>
    set_option (tcb_bound_notification t) \<subseteq> obj_dom)"
  | "check_kernel_object_ref (Endpoint ep) obj_dom = (case ep of IdleEP \<Rightarrow> True
                                                             | SendEP s \<Rightarrow> (set s \<subseteq> obj_dom)
                                                             | RecvEP r \<Rightarrow>  (set r \<subseteq> obj_dom))"
  | "check_kernel_object_ref (Notification ntfn) obj_dom =
    ((case (ntfn_obj ntfn) of WaitingNtfn l \<Rightarrow> set l \<subseteq> obj_dom
                            | _ \<Rightarrow> True)
    \<and> (case (ntfn_bound_tcb ntfn) of Some tcb \<Rightarrow> tcb \<in> obj_dom
                                   | None \<Rightarrow> True))"
  | "check_kernel_object_ref (ArchObj ao) obj_dom = (case ao of RISCV64_A.DataPage _ _ \<Rightarrow> True
                                                            | RISCV64_A.ASIDPool ap \<Rightarrow> (\<forall>x.
                                                                case (ap x) of Some obj_ref \<Rightarrow> obj_ref \<in> obj_dom
                                                                             | None \<Rightarrow> True)
                                                            | RISCV64_A.PageTable pt \<Rightarrow> (\<forall>x.
                                                                case (pt x) of RISCV64_A.InvalidPTE \<Rightarrow> True
                                                                             | RISCV64_A.PagePTE ppn _ _ \<Rightarrow> RISCV64_A.addr_from_ppn ppn \<in> obj_dom
                                                                             | RISCV64_A.PageTablePTE ppn _  \<Rightarrow> RISCV64_A.addr_from_ppn ppn \<in> obj_dom))"

definition colour_invariant
  where
    "colour_invariant s \<equiv> \<forall>ptr kobj.
    (ko_at kobj ptr s \<and> ptr \<in> colour_oracle (cur_domain s)) \<longrightarrow>
    check_kernel_object_ref kobj (colour_oracle (cur_domain s))"

crunch set_thread_state for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

section "KHeap_A Colour Invariant"
lemma set_object_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_kernel_object_ref kobj (colour_oracle (cur_domain s)))\<rbrace>
   set_object ptr kobj
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: colour_invariant_def obj_at_update wp: set_object_wp)

lemma thread_set_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. let tcb = TCB (f $ the (get_tcb ptr s)) in check_kernel_object_ref tcb (colour_oracle (cur_domain s)))\<rbrace>
   thread_set f ptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: colour_invariant_def obj_at_update wp: thread_set_wp)

lemma thread_set_priority_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_priority ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: thread_set_priority_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma thread_set_time_slice_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_time_slice ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: thread_set_time_slice_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma thread_set_domain_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_domain ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: thread_set_domain_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma set_mcpriority_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     set_mcpriority ref mcp
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: set_mcpriority_def colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma arch_thread_set_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
        let tcb = the $ get_tcb ptr s in
        let arch_tcb = f $ tcb_arch tcb in
        let new_tcb = TCB $ tcb \<lparr> tcb_arch := arch_tcb \<rparr> in
        check_kernel_object_ref new_tcb (colour_oracle (cur_domain s)))\<rbrace>
     arch_thread_set f ptr
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: colour_invariant_def obj_at_update wp: arch_thread_set_wp)

lemma set_bound_notification_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. (set_option ntfn) \<subseteq> colour_oracle (cur_domain s))\<rbrace>
   set_bound_notification ptr ntfn
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: set_bound_notification_thread_set colour_invariant_def obj_at_update wp: thread_set_wp, fastforce)

lemma set_simple_ko_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
        let kobj = the $ kheap s ptr in
          is_simple_type kobj \<longrightarrow>
          partial_inv f kobj \<noteq> None \<longrightarrow>
          check_kernel_object_ref (f ep) (colour_oracle (cur_domain s)))\<rbrace>
     set_simple_ko f ptr ep
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: set_simple_ko_def obj_at_update colour_invariant_def obj_at_def wp: get_object_wp set_object_wp)

lemma throw_on_false_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
      f
    \<lbrace>\<lambda>_ . colour_invariant\<rbrace>
   \<Longrightarrow>
   \<lbrace>colour_invariant\<rbrace>
      throw_on_false ex f
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (simp add: hoare_wp_splits(12) throw_on_false_wp)

lemma set_thread_state_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_tcb_state ts (colour_oracle (cur_domain s)))\<rbrace>
       set_thread_state ref ts
      \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold set_thread_state_def Let_def)
  apply wp
     apply wpsimp
     apply (unfold set_thread_state_act_def set_scheduler_action_def get_thread_state_def)
     apply wpsimp
     apply (wp add: thread_get_wp)
    apply (wp add: set_object_wp)
   apply (wp add: gets_the_wp)
  unfolding colour_invariant_def
  apply (simp add: obj_at_update obj_at_def del: check_kernel_object_ref.simps)
  apply clarsimp
  apply (drule get_tcb_SomeD)
  apply (rule conjI|rule impI)+
  using get_tcb_rev by fastforce+

lemma as_user_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     as_user ptr f
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold as_user_def)
  apply wpsimp
       apply (wp add: set_object_wp)+
  apply clarsimp
  unfolding colour_invariant_def
  apply (simp add: obj_at_update)
  apply clarsimp
  apply (case_tac "ptr\<noteq>ptra")
   apply (simp add: obj_at_def)+
  using get_tcb_SomeD by fastforce

\<comment>\<open>I suspect that a lot of the above can effectively be turned into crunches - might try that at some point\<close>
crunch reschedule_required,
  possible_switch_to,
  set_thread_state_act,
  set_priority,
  set_scheduler_action,
  tcb_sched_action,
  set_tcb_queue,
  set_irq_state for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)

section "Top-Down Colour Invariant Work"
crunch store_word_offs,
  set_extra_badge,
  set_cdt,
  update_cdt,
  set_message_info,
  activate_thread for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update RISCV64_A.arch_activate_idle_thread_def)

lemma set_cap_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref cap (colour_oracle (cur_domain s)))\<rbrace>
   set_cap cap cs_ptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold set_cap_def)
  apply wpsimp
     apply (wp add: set_object_wp)
    apply wpsimp
   apply (wp add: get_object_wp)
  apply (simp add: colour_invariant_def obj_at_update obj_at_def)
  using check_kernel_object_ref.simps(1,2) by blast

lemma set_untyped_cap_as_full_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref src_cap (colour_oracle (cur_domain s)))\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold set_untyped_cap_as_full_def)
  apply wpsimp
    apply (wp add: set_cap_colour_maintained)
  apply wpsimp
   apply clarsimp
  by (simp add: check_cap_ref_def)

lemma cte_wp_at_check_cap_ref:
  "\<And>s cap.
         \<lbrakk>cte_wp_at ((=) cap) (a, b) s;
          colour_invariant s;
          a \<in> colour_oracle (cur_domain s)\<rbrakk>
         \<Longrightarrow> check_cap_ref cap
               (colour_oracle (cur_domain s))"
  apply (simp add: cte_wp_at_cases2)
  apply (erule disjE|erule exE|erule conjE)+
   apply (simp_all add: colour_invariant_def obj_at_def)
   apply (erule_tac x=a in allE)
   apply (erule_tac x="CNode sz fun" in allE)
   apply (erule impE)
    apply simp
   apply (simp add: check_kernel_object_ref_def)
   apply (erule_tac x=b in allE)
   apply simp
  apply (erule disjE|erule exE|erule conjE)+
  apply (erule_tac x=a in allE)
  apply (erule_tac x="TCB tcb" in allE)
  apply (erule impE)
   apply simp
  using ranI ran_tcb_cnode_map
  by force

lemma cap_insert_colour_maintained':
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s))) and (\<lambda>s. a\<in>colour_oracle (cur_domain s))\<rbrace>
   cap_insert new_cap (a, b) dest_slot
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold cap_insert_def colour_invariant_def)
  apply wpsimp
             apply (unfold update_cdt_def)
             apply wpsimp
              apply (rule conjI)
               apply (rule impI)
               apply (fold colour_invariant_def)
               apply (wp add: set_cdt_colour_maintained)
              apply (rule impI)
              apply (wp add: set_cdt_colour_maintained)
             apply wpsimp+
        apply (wp add: set_cap_colour_maintained)
       apply (wp add: set_untyped_cap_as_full_colour_maintained)
      apply wpsimp
     apply (rule get_cap_wp)
    apply wpsimp
   apply (rule get_cap_wp)
  apply simp
  apply (rule allI|rule impI|erule conjE)+
  by (simp add: cte_wp_at_check_cap_ref)

lemma cap_insert_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s))) and (\<lambda>s. fst (src_slot) \<in>colour_oracle (cur_domain s))\<rbrace>
   cap_insert new_cap src_slot dest_slot
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (cases src_slot; simp add: cap_insert_colour_maintained')

lemma hoare_weird_if:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,-; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<not>(cond rv) \<longrightarrow> R rv s\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. if cond rv then (\<lambda>s. Q s \<and> True) else (\<lambda>s. Q s \<and> R rv s)\<rbrace>,-"
      apply (wp add: hoare_vcg_if_lift_ER[where P=P])
      apply (wp add: hoare_vcg_conj_liftE_R'[where P=P and P'=P])
  apply (wp add: hoare_vcg_imp_liftE_R'[where P'="(\<lambda>s. False)" and Q'=P])
  apply (wp add: hoare_FalseE)
  apply wpsimp+
  apply (rule hoare_strengthen_postE_R[where Q'="\<lambda>rv s. (\<not> cond rv \<longrightarrow> R rv s) \<and> Q s"])
  apply (wp add: hoare_vcg_conj_liftE_R'[where P=P and P'=P])
  by wpsimp+


lemma transfer_caps_loop_colour_maintained:
  "\<lbrace>colour_invariant and
        (\<lambda>s. \<forall>(cap, o_ref, _)\<in>(set caps). check_cap_ref cap (colour_oracle (cur_domain s)) \<and> o_ref \<in> colour_oracle (cur_domain s))\<rbrace>
     transfer_caps_loop ep rcv_buffer n caps slots mi
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
proof (induct caps arbitrary: ep rcv_buffer n slots mi)
  case Nil
  then show ?case by simp
next
  case (Cons a caps)
  note Cons.hyps[wp]
  show ?case
    apply (cases a)
    apply wpsimp
    apply (rule conjI; rule impI)+
      apply wpsimp
       apply (wp add: set_extra_badge_colour_maintained)
       apply (simp add: set_extra_badge_def)
       apply wpsimp
      apply simp
     apply wpsimp
        apply (wp add: cap_insert_colour_maintained)
       apply simp
       apply wpsimp
      apply wp
      apply (wp add: hoare_weird_if[where P=
        "colour_invariant and
        (\<lambda>s. \<forall>(cap, o_ref, _)\<in>(set (a # caps)).
           check_cap_ref cap (colour_oracle (cur_domain s)) \<and> o_ref \<in> colour_oracle (cur_domain s))"
      ])
       apply simp
       apply (wp add: derive_cap_inv)
       apply simp
      apply (simp add: check_cap_ref_def)
      apply (wp add: derive_cap_objrefs_iszombie)
      apply simp+
    apply (rule conjI; rule impI)+
     apply wpsimp
      apply (wp add: set_extra_badge_colour_maintained)
      apply (simp add: set_extra_badge_def)
      apply wpsimp
     apply simp
    by wpsimp
qed

lemma transfer_caps_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. \<forall>(cap, o_ref, _)\<in>(set caps). check_cap_ref cap (colour_oracle (cur_domain s)) \<and> o_ref \<in> colour_oracle (cur_domain s))\<rbrace>
 transfer_caps info caps endpoint receiver recv_buffer
\<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold transfer_caps_def)
  apply wpsimp
     apply (wp add: transfer_caps_loop_colour_maintained)
  by wpsimp+

lemma copy_mrs_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     copy_mrs  sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold copy_mrs_def)
  apply wpsimp
     apply (rule conjI)
      apply (rule impI)
      apply (wp add: mapM_wp[where S="UNIV"])
        apply (wp add: store_word_offs_colour_maintained)
       apply (wp add: load_word_offs_P)
      apply simp
     apply (rule impI)
     apply (wp add: mapM_wp)
       apply (wp add: store_word_offs_colour_maintained)
      apply (wp add: load_word_offs_P)
     apply simp
    apply (wp add: mapM_wp[where S="UNIV"])
  by (simp; wp add: as_user_colour_maintained)+

lemma do_normal_transfer_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     do_normal_transfer  sender sbuf endpoint badge grant receiver rbuf
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold do_normal_transfer_def)
  apply wpsimp
        apply (wp add: as_user_colour_maintained
                       set_message_info_colour_maintained
                       transfer_caps_colour_maintained)+
     apply (wp add: copy_mrs_colour_maintained)
     apply (simp add: copy_mrs_def; wpsimp)
      apply (rule conjI)
       apply (rule impI)
       apply (wp add: mapM_wp[where S="UNIV"])
       apply simp
      apply (rule impI)
      apply (wp add: mapM_wp[where S="UNIV"])
      apply simp
     apply (wp add: mapM_wp[where S="UNIV"])
     apply simp
    apply wpsimp
  apply (simp add: lookup_extra_caps_def
                   lookup_cap_and_slot_def
                   lookup_slot_for_thread_def)
  apply wpsimp
    apply (wp add: mapME_set)
  apply wpsimp
  apply (wp add: get_cap_wp)
  apply wpsimp
  apply (wp add: hoare_vcg_all_liftE_R)
  oops

term "resolve_address_bits'"
term "real_cte_at"
find_theorems name: hoare_vcg name: "if"
find_theorems "resolve_address_bits"
find_theorems "lookup_slot_for_thread"

lemma set_mrs_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     set_mrs thread buf msgs
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: set_mrs_def)
  apply wpsimp
  apply (rule conjI)
  apply (rule impI)
  apply (wp add: zipWithM_x_inv' store_word_offs_colour_maintained)
  apply (rule impI)
  apply (wp add: zipWithM_x_inv' store_word_offs_colour_maintained)
  apply (wp add: set_object_wp)
  apply wpsimp
  apply (simp add: colour_invariant_def)
  apply clarsimp
  apply (simp add: obj_at_update obj_at_def)
  apply (drule get_tcb_SomeD)
  apply (case_tac "ptr=thread")
  apply clarsimp
  using check_kernel_object_ref.simps(2) apply blast
  by simp

lemma make_fault_msg_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
    make_fault_msg fault thread
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (cases fault; wpsimp)
  apply (rule conjI)
  apply (rule impI)
  apply wpsimp
  apply (wp add: as_user_colour_maintained)
  apply simp
  apply (rule impI)
  apply wpsimp
  apply (wp add: as_user_colour_maintained)
  apply simp
     apply (wp add: as_user_colour_maintained)
  apply simp
     apply (wp add: as_user_colour_maintained)
  apply simp
     by (wp add: RISCV64.make_arch_fault_msg_inv)

lemma setup_caller_cap_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. sender \<in> colour_oracle (cur_domain s))\<rbrace>
  setup_caller_cap sender receiver grant
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: setup_caller_cap_def)
  apply (rule conjI)
  apply (rule impI)
  apply wpsimp
  apply (wp add: cap_insert_colour_maintained)
  apply (wp add: set_thread_state_colour_maintained)
  apply wpsimp
  apply (simp add: colour_invariant_def obj_at_def check_cap_ref_def)
  apply (rule impI)
  apply wpsimp
  apply (wp add: cap_insert_colour_maintained)
  apply (wp add: set_thread_state_colour_maintained)
  apply wpsimp
  by (simp add: colour_invariant_def obj_at_def check_cap_ref_def)

lemma handle_double_fault_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
  handle_double_fault tptr ex1 ex2
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: handle_double_fault_def)
  apply (wp add: set_thread_state_colour_maintained)
  by simp

lemma send_ipc_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
  send_ipc block call badge can_grant can_grant_reply thread epptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: send_ipc_def)
  apply wpsimp
  apply (wp add: set_simple_ko_colour_maintained)
  apply (wp add: set_thread_state_colour_maintained)
  apply wpsimp
  apply (simp add: Let_def)
  apply (simp add: set_thread_state_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def)
  apply wpsimp
     apply (wp add: thread_get_wp)
    apply (wp add: set_object_wp)
   apply (wp add: gets_the_wp)
  apply wpsimp+
    apply (wp add: set_simple_ko_colour_maintained)
  apply (wp add: set_thread_state_colour_maintained)
  apply wpsimp
  apply (simp add: Let_def)
  apply (simp add: set_thread_state_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def)
  apply wpsimp
     apply (wp add: thread_get_wp)
    apply (wp add: set_object_wp)
   apply (wp add: gets_the_wp)
  apply wpsimp+
  apply (wp add: setup_caller_cap_colour_maintained)
  apply (wp add: set_thread_state_colour_maintained)
  apply wpsimp
  apply (simp add: possible_switch_to_def)
  apply (rule conjI|rule impI)+
  apply wpsimp
  apply (simp add: tcb_sched_action_def)
  apply wpsimp+
  apply (simp add: tcb_sched_action_def)
  apply wpsimp+
oops
find_theorems name: hoare_vcg

lemma send_fault_ipc_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
  send_fault_ipc tptr fault
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: send_fault_ipc_def)
  apply wpsimp
  apply (case_tac handler_cap)
  apply wpsimp+
  apply (rule conjI|rule impI)+
  apply wpsimp
oops

(* side condition here is *very odd*. Comes from default_tcb, in particular tcb_ipc_buffer.
   Might need to modify my guessed overlap property to make it so NULL is common to all *)
lemma retype_region_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. 0 \<in> colour_oracle (cur_domain s))\<rbrace>
  retype_region ptr numObjects o_bits type dev
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp only: retype_region_def)
  apply wp
  apply (simp del: fun_upd_apply)
  apply (clarsimp simp: colour_invariant_def obj_at_def)
  apply (drule foldr_kh_eq)
  apply (case_tac "ptra \<in> (\<lambda>x. ptr_add ptr (x * 2 ^ obj_bits_api type o_bits)) ` {0..<numObjects}")
  apply (case_tac type)
  by (
    simp
      split:
        RISCV64_A.aobject_type.splits
      add:
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

lemma delete_objects_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
  delete_objects ptr bits
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: delete_objects_def do_machine_op_def colour_invariant_def)
  by (clarsimp simp add: detype_def)

lemma reset_untyped_cap_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
  reset_untyped_cap src_slot
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: reset_untyped_cap_def)
  apply (wp add: set_cap_colour_maintained)
  apply wpsimp
  apply (wp add: do_machine_op_colour_maintained)
  apply wpsimp
  apply (wp add: mapME_x_wp[where S=UNIV])
  apply (wp add: preemption_point_inv)
  apply (simp add: irq_state_independent_A_def, clarsimp)
  apply (simp add: colour_invariant_def)
          apply (simp add: colour_invariant_def)
  apply (wp add: preemption_point_inv)
  apply (simp add: irq_state_independent_A_def, clarsimp)
  apply (simp add: colour_invariant_def)
         apply (simp add: colour_invariant_def)
  apply wpsimp
        apply (wp add: set_cap_colour_maintained)
  apply wpsimp
  apply (wp add: do_machine_op_colour_maintained)
  apply (simp add: check_cap_ref_def)
  apply simp
  apply wpsimp+
  apply (rule impI|rule conjI)+
  apply (wp add: delete_objects_colour_maintained)
  apply (wp add: hoare_vcg_imp_lift)
  apply (simp add: check_cap_ref_def)
    apply (wp add: delete_objects_colour_maintained)
  apply wpsimp
apply (wp add: hoare_vcg_imp_lift)
  apply (simp add: check_cap_ref_def)
    apply (wp add: delete_objects_colour_maintained)
apply (wp add: hoare_vcg_imp_lift)
    apply (wp add: delete_objects_colour_maintained)
  apply wpsimp
   apply (wp add: hoare_vcg_imp_lift)
  apply (wp add: get_cap_cte_wp_at3)
  apply (wp add: get_cap_inv)
   apply (wp add: hoare_vcg_imp_lift)
  apply (wp add: get_cap_cte_wp_at3)
   apply (wp add: hoare_vcg_conj_lift)
     apply (wp add: hoare_vcg_imp_lift)
     apply (wp add: get_cap_cte_wp_at3)
  apply (wp add: get_cap_inv)
   apply (wp add: hoare_vcg_conj_lift)
    apply (wp add: hoare_vcg_disj_lift)
     apply (wp add: get_cap_cte_wp_at3)
  apply (wp add: get_cap_inv)
   apply (wp add: hoare_vcg_conj_lift)
  apply (wpsimp simp: check_cap_ref_def)
  apply (wp add: hoare_vcg_imp_lift)
    apply (wp add: get_cap_cte_wp_at3)
  apply (wp add: get_cap_inv)
  by clarsimp

lemma syscall_colour_maintained:
  "\<lbrakk>\<forall>x. \<lbrace>colour_invariant\<rbrace> param_b x \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
      \<forall>x. \<lbrace>colour_invariant\<rbrace> param_d x \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
      \<forall>x. \<lbrace>colour_invariant\<rbrace> param_e x \<lbrace>\<lambda>_. colour_invariant\<rbrace>\<rbrakk> \<Longrightarrow>
    \<lbrace>colour_invariant\<rbrace>
     syscall param_a param_b param_c param_d param_e
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: syscall_def)
  apply wpsimp
     apply (erule allE)+
     apply assumption
    apply wpsimp
      apply (erule allE)+
      apply assumption
     apply (erule allE)+
     apply wpsimp
  oops

lemma next_domain_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
     let domain_index' = Suc (domain_index s) mod length (domain_list s);
     next_dom = domain_list s ! domain_index';
     new_dom = fst next_dom in
     \<forall>ptr kobj.
      (ko_at kobj ptr s \<and> ptr \<in> colour_oracle new_dom) \<longrightarrow>
      check_kernel_object_ref kobj (colour_oracle new_dom))\<rbrace>
      next_domain
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: next_domain_def)
  apply wpsimp
  apply (simp add: colour_invariant_def)
   apply wpsimp+
  apply (thin_tac "colour_invariant s")
  by (simp add: colour_invariant_def Let_def)

lemma arch_switch_to_idle_thread_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
      arch_switch_to_idle_thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: RISCV64_A.arch_switch_to_idle_thread_def RISCV64_A.set_vm_root_def)
  apply wpsimp
oops

crunch schedule for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update RISCV64_A.arch_switch_to_idle_thread_def)

crunch call_kernel for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)
end
