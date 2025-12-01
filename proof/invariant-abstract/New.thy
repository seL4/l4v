theory New
  imports
    KernelInit_AI
    "$L4V_ARCH/ArchDetSchedSchedule_AI"
begin
section "Initialisation"
axiomatization
  colour_oracle :: "domain \<Rightarrow> obj_ref set"
  where
    colour_oracle_no_overlap: "x \<noteq> y \<Longrightarrow> (colour_oracle x \<inter> colour_oracle y = {0})" \<comment>\<open>and
    colour_oracle_cur_thread: "\<forall>s. cur_thread s \<in> (colour_oracle (cur_domain s))"\<close>

lemma colour_oracle_zero: "0 \<in> colour_oracle x"
by (metis (full_types, lifting) IntD2
    colour_oracle_no_overlap
    semiring_norm(160)
    singletonI)

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
    "colour_invariant s \<equiv> \<forall>ptr kobj. \<forall>(dom, _)\<in>(set (domain_list s)).
    (ko_at kobj ptr s \<and> ptr \<in> colour_oracle dom) \<longrightarrow>
    check_kernel_object_ref kobj (colour_oracle dom)"

definition valid_ptr_in_cur_domain
  where
    "valid_ptr_in_cur_domain ptr s \<equiv> ptr \<in> colour_oracle (cur_domain s) \<and> ptr \<noteq> 0"

crunch set_thread_state, reschedule_required for cur_domain[wp]: "\<lambda>s. P (cur_domain s)"

lemma ptr_no_domain_overlap:
  "\<lbrakk>valid_ptr_in_cur_domain ptr s; ptr \<in> colour_oracle a\<rbrakk> \<Longrightarrow> a = cur_domain s"
  apply (simp add: valid_ptr_in_cur_domain_def)
  using colour_oracle_no_overlap by fastforce

crunch as_user, set_cap, set_untyped_cap_as_full for valid_ptr_in_cur_domain: "\<lambda>s. valid_ptr_in_cur_domain a s"
  (simp: valid_ptr_in_cur_domain_def)

section "KHeap_A Colour Invariant"
lemma set_object_colour_maintained:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s. check_kernel_object_ref kobj (colour_oracle (cur_domain s)))\<rbrace>
   set_object ptr kobj
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: colour_invariant_def obj_at_update wp: set_object_wp)
  by (drule ptr_no_domain_overlap, simp+)

lemma thread_set_colour_maintained:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s. let tcb = TCB (f $ the (get_tcb ptr s)) in check_kernel_object_ref tcb (colour_oracle (cur_domain s)))\<rbrace>
   thread_set f ptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: colour_invariant_def obj_at_update wp: thread_set_wp)
  by (drule ptr_no_domain_overlap, simp+)

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
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s.
        let tcb = the $ get_tcb ptr s in
        let arch_tcb = f $ tcb_arch tcb in
        let new_tcb = TCB $ tcb \<lparr> tcb_arch := arch_tcb \<rparr> in
        check_kernel_object_ref new_tcb (colour_oracle (cur_domain s)))\<rbrace>
     arch_thread_set f ptr
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: colour_invariant_def obj_at_update wp: arch_thread_set_wp)
  by (drule ptr_no_domain_overlap, simp+)

lemma set_bound_notification_colour_maintained:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain ptr) and (\<lambda>s. (set_option ntfn) \<subseteq> colour_oracle (cur_domain s))\<rbrace>
   set_bound_notification ptr ntfn
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: set_bound_notification_thread_set colour_invariant_def obj_at_update wp: thread_set_wp)
  apply (drule ptr_no_domain_overlap)
  apply simp
  by fastforce

lemma set_simple_ko_colour_maintained:
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

lemma throw_on_false_colour_maintained:
  "\<lbrace>colour_invariant and P\<rbrace>
      f
    \<lbrace>\<lambda>_ . colour_invariant\<rbrace>
   \<Longrightarrow>
   \<lbrace>colour_invariant and P\<rbrace>
      throw_on_false ex f
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (simp add: hoare_wp_splits(12) throw_on_false_wp)

lemma set_thread_state_colour_maintained:
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

lemma as_user_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     as_user ptr f
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: as_user_def colour_invariant_def obj_at_update obj_at_def wp: set_object_wp, fastforce dest: get_tcb_SomeD)

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
  set_message_info for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)

lemma activate_thread_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (cur_thread s) s) and (\<lambda>s. tcb_at (cur_thread s) s)\<rbrace> \<comment>\<open>(*yikes*)\<close>
     activate_thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: activate_thread_def wp: set_thread_state_colour_maintained as_user_colour_maintained as_user_valid_ptr_in_cur_domain)
  apply (wpsimp simp: RISCV64_A.arch_activate_idle_thread_def)
  apply (wpsimp simp: get_thread_state_def)
  apply (wpsimp wp: thread_get_wp)+
  apply (simp add: tcb_at_def get_tcb_def obj_at_def is_tcb_def)
using is_obj_defs(3) is_tcb_def
  by presburger


lemma set_cap_colour_maintained:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain $ fst cs_ptr) and (\<lambda>s. check_cap_ref cap (colour_oracle (cur_domain s)))\<rbrace>
   set_cap cap cs_ptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: set_cap_def colour_invariant_def obj_at_update obj_at_def wp: set_object_wp get_object_wp)
  apply safe
  using ptr_no_domain_overlap by fastforce+

lemma set_untyped_cap_as_full_colour_maintained:
  "\<lbrace>colour_invariant and (valid_ptr_in_cur_domain $ fst src_slot) and (\<lambda>s. check_cap_ref src_cap (colour_oracle (cur_domain s)))\<rbrace>
     set_untyped_cap_as_full src_cap new_cap src_slot
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold set_untyped_cap_as_full_def)
  apply wpsimp
    apply (wp add: set_cap_colour_maintained)
   apply wpsimp
  by (simp add: check_cap_ref_def)

lemma cte_wp_at_check_cap_ref:
  "\<And>s cap.
         \<lbrakk>cte_wp_at ((=) cap) (a, b) s;
          colour_invariant s;
          valid_ptr_in_cur_domain a s\<rbrakk>
         \<Longrightarrow> check_cap_ref cap
               (colour_oracle (cur_domain s))"
  apply (simp add: cte_wp_at_cases2)
  apply (erule disjE|erule exE|erule conjE)+
   apply (simp_all add: colour_invariant_def valid_ptr_in_cur_domain_def obj_at_def)
   apply (erule_tac x=a in allE)
   apply (erule_tac x="CNode sz fun" in allE)
  apply (erule_tac x="(cur_domain s, _)" in ballE)
  apply clarsimp
  apply (erule_tac x=b in allE)
    apply (simp add: check_kernel_object_ref_def)
  apply (erule_tac allE)
   apply (erule_tac x=b in allE)
   apply simp
defer
  apply (erule disjE|erule exE|erule conjE)+
  apply (erule_tac x=a in allE)
  apply (erule_tac x="TCB tcb" in allE)
  apply (erule impE)
   apply simp
  using ranI ran_tcb_cnode_map by force
sorry

lemma cap_insert_colour_maintained':
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s))) and (\<lambda>s. a\<in>colour_oracle (cur_domain s)) and (\<lambda>s. valid_ptr_in_cur_domain a s) and (\<lambda>s. valid_ptr_in_cur_domain (fst dest_slot) s)\<rbrace>
   cap_insert new_cap (a, b) dest_slot
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: cap_insert_def update_cdt_def colour_invariant_def)
            apply safe
             apply (fold colour_invariant_def)
             apply (wpsimp wp: set_cdt_colour_maintained)+
  by (wpsimp simp: cte_wp_at_check_cap_ref wp: set_cdt_colour_maintained set_cap_colour_maintained set_untyped_cap_as_full_colour_maintained get_cap_wp set_untyped_cap_as_full_valid_ptr_in_cur_domain)+

lemma cap_insert_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s))) and (\<lambda>s. fst (src_slot) \<in>colour_oracle (cur_domain s)) and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s) and (\<lambda>s. valid_ptr_in_cur_domain (fst dest_slot) s)\<rbrace>
cap_insert new_cap src_slot dest_slot
\<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (cases src_slot; simp add: cap_insert_colour_maintained')

lemma hoare_weird_if:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,-; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<not>(cond rv) \<longrightarrow> R rv s\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. if cond rv then (\<lambda>s. Q s \<and> True) else (\<lambda>s. Q s \<and> R rv s)\<rbrace>,-"
  apply (wpsimp wp: hoare_vcg_if_lift_ER hoare_vcg_conj_liftE_R' hoare_vcg_imp_liftE_R'[where Q'=P])
     apply (wpsimp wp: hoare_FalseE)
    apply wpsimp+
   apply (rule hoare_strengthen_postE_R[where Q'="\<lambda>rv s. (\<not> cond rv \<longrightarrow> R rv s) \<and> Q s"])
  by (wpsimp wp: hoare_vcg_conj_liftE_R')+

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
      apply (wpsimp wp: set_extra_badge_colour_maintained)
       apply (simp add: set_extra_badge_def)
       apply wpsimp
      apply simp
     apply wpsimp
        apply (wp add: cap_insert_colour_maintained)
       apply simp
       apply wpsimp+
      apply (wp add: hoare_weird_if[where P=
        "colour_invariant and
        (\<lambda>s. \<forall>(cap, o_ref, _)\<in>(set (a # caps)).
           check_cap_ref cap (colour_oracle (cur_domain s)) \<and> o_ref \<in> colour_oracle (cur_domain s))"
      ])
       apply (wpsimp simp: check_cap_ref_def wp: derive_cap_inv)+
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
  by (wpsimp simp: transfer_caps_def wp: transfer_caps_loop_colour_maintained)

lemma copy_mrs_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     copy_mrs  sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
    apply (rule conjI)
     apply (rule impI)
  by (wpsimp wp: mapM_wp[where S="UNIV"] store_word_offs_colour_maintained load_word_offs_P as_user_colour_maintained)+

lemma do_normal_transfer_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
 do_normal_transfer  sender sbuf endpoint badge grant receiver rbuf
\<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: do_normal_transfer_def)
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
  apply (wpsimp simp: set_mrs_def colour_invariant_def wp: zipWithM_x_inv' store_word_offs_colour_maintained set_object_wp)
  apply (simp add: obj_at_update obj_at_def)
  apply (drule get_tcb_SomeD)
  apply (case_tac "ptr=thread")
   apply clarsimp
  using check_kernel_object_ref.simps(2) apply blast
  by fastforce

lemma make_fault_msg_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
    make_fault_msg fault thread
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (cases fault; wpsimp)
       apply (rule conjI)
        apply (rule impI)
  by (wpsimp wp: as_user_colour_maintained RISCV64.make_arch_fault_msg_inv)+

lemma setup_caller_cap_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain sender s) and (\<lambda>s. valid_ptr_in_cur_domain receiver s)\<rbrace>
  setup_caller_cap sender receiver grant
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: setup_caller_cap_def)
  apply (rule conjI)
   apply (rule impI)
  by (wpsimp simp: colour_invariant_def obj_at_def check_cap_ref_def wp: cap_insert_colour_maintained set_thread_state_colour_maintained;
        simp add: valid_ptr_in_cur_domain_def)+

lemma handle_double_fault_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain tptr s)\<rbrace>
  handle_double_fault tptr ex1 ex2
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: handle_double_fault_def wp: set_thread_state_colour_maintained)

lemma send_ipc_colour_maintained':
  "\<lbrace>colour_invariant and (\<lambda>s. thread \<in> colour_oracle (cur_domain s)) and (\<lambda>s. epptr \<in> colour_oracle (cur_domain s))\<rbrace>
  send_ipc block call badge can_grant can_grant_reply thread epptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
thm send_ipc_valid_sched
thm si_blk_makes_simple
thm si_invs'
  apply (simp add: send_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_inv])
  apply (case_tac ep, simp_all)
    apply (cases block, simp_all)[1]
defer
   apply (rename_tac list)
   apply (cases block, simp_all)[1]
defer
   apply (rename_tac list)
  apply (case_tac list, simp_all add: invs_def valid_state_def valid_pspace_def split del:if_split)
  apply (rename_tac dest queue)
defer
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
  apply ((rule conjI|rule impI)+, simp add: obj_at_def)+
defer
apply (rule conjI|rule impI)+
defer
apply (rule conjI|rule impI)+
  apply (simp add: obj_at_def)
apply (rule conjI|rule impI)+
defer
  apply clarsimp
apply (simp add: obj_at_def)
apply (rule conjI|rule impI)+
defer
apply (rule conjI|rule impI)+
defer
apply (rule conjI|rule impI)+
defer
apply (rule conjI|rule impI)+
defer
       apply (wp add: set_simple_ko_colour_maintained)
      apply (wp add: set_thread_state_colour_maintained)
      apply wpsimp
oops

lemma send_ipc_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
  send_ipc block call badge can_grant can_grant_reply thread epptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: send_ipc_def)
\<comment>\<open>apply (rule bind_wp [OF _ get_simple_ko_inv])
  apply (case_tac ep, simp_all)\<close>
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
  apply (wpsimp simp: colour_invariant_def wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_conj_lift)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_conj_lift set_scheduler_action_colour_maintained tcb_sched_action_colour_maintained reschedule_required_colour_maintained)+
  apply (wpsimp
    simp: set_thread_state_def Let_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def colour_invariant_def
    wp: thread_get_wp set_object_wp gets_the_wp
  )+
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_conj_lift)+
  apply (wpsimp simp: get_tcb_None_tcb_at wp: do_ipc_transfer_tcb_at)+
           apply (wpsimp simp: obj_at_def wp: hoare_vcg_all_lift hoare_vcg_imp_lift hoare_vcg_conj_lift hoare_vcg_disj_lift hoare_exI)+
  apply (rule do_ipc_transfer_scheduler_act[where P="\<lambda>s. s \<noteq> resume_cur_thread"])
    oops
  find_theorems do_ipc_transfer tcb_at
  find_theorems do_ipc_transfer "\<lbrace>_\<rbrace>_\<lbrace>\<lambda>_ _. obj_at _ _ _\<rbrace>"
  find_theorems do_ipc_transfer scheduler_action
thm do_ipc_transfer_scheduler_act[where P="\<lambda>s. s \<noteq> resume_cur_thread"]

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

lemma retype_region_colour_maintained:
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
        colour_oracle_zero
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

lemma delete_objects_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
  delete_objects ptr bits
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: delete_objects_def do_machine_op_def colour_invariant_def)
  apply (clarsimp simp add: detype_def)
  by fastforce

lemma reset_untyped_cap_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s)\<rbrace>
  reset_untyped_cap src_slot
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: reset_untyped_cap_def wp: set_cap_colour_maintained)
       apply (wpsimp simp: valid_ptr_in_cur_domain_def wp: do_machine_op_colour_maintained)
  apply (rule hoare_post_impE[where Q'="\<lambda>_. colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s)" and E'="\<lambda>_. colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s)"])
  apply simp+
      apply (wpsimp wp: mapME_x_wp[where S=UNIV] preemption_point_inv)
           apply (simp add: colour_invariant_def valid_ptr_in_cur_domain_def, simp add: colour_invariant_def valid_ptr_in_cur_domain_def)
         apply (wpsimp simp: irq_state_independent_A_def wp: preemption_point_inv)
          apply (simp add: colour_invariant_def valid_ptr_in_cur_domain_def, simp add: colour_invariant_def valid_ptr_in_cur_domain_def)
        apply (wpsimp wp: set_cap_colour_maintained set_cap_valid_ptr_in_cur_domain)
  apply wp
       apply (wp add: do_machine_op_colour_maintained)
       apply (simp add: check_cap_ref_def)
      apply (wpsimp simp: valid_ptr_in_cur_domain_def wp: do_machine_op_colour_maintained)+
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
   apply (wp add: hoare_vcg_imp_lift get_cap_cte_wp_at3 hoare_vcg_conj_lift hoare_vcg_disj_lift)
    apply (wpsimp simp: check_cap_ref_def)
   apply (wp add: hoare_vcg_imp_lift get_cap_cte_wp_at3)
   by (clarsimp simp add: valid_ptr_in_cur_domain_def cte_wp_at_def)

lemma syscall_colour_maintained:
  "\<lbrakk>\<forall>x. \<lbrace>colour_invariant\<rbrace> param_a \<lbrace>\<lambda>_. colour_invariant\<rbrace>, \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
    \<forall>x. \<lbrace>colour_invariant\<rbrace> param_b x \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
    \<forall>x. \<lbrace>colour_invariant\<rbrace> param_c x \<lbrace>\<lambda>_. colour_invariant\<rbrace>, \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
    \<forall>x. \<lbrace>colour_invariant\<rbrace> param_d x \<lbrace>\<lambda>_. colour_invariant\<rbrace>;
    \<forall>x. \<lbrace>colour_invariant\<rbrace> param_e x \<lbrace>\<lambda>_. colour_invariant\<rbrace>, \<lbrace>\<lambda>_. colour_invariant\<rbrace>\<rbrakk> \<Longrightarrow>
    \<lbrace>colour_invariant\<rbrace>
     syscall param_a param_b param_c param_d param_e
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wp syscall_valid)
  by ((erule allE)+, simp)+

lemma next_domain_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
     let domain_index' = Suc (domain_index s) mod length (domain_list s);
     next_dom = domain_list s ! domain_index';
     new_dom = fst next_dom in
     colour_invariant (s\<lparr>cur_domain := new_dom\<rparr>))\<rbrace>
      next_domain
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: next_domain_def colour_invariant_def Let_def)

lemma temp: "colour_invariant s = colour_invariant (s\<lparr>cur_thread := thread\<rparr>)"
  by (simp add: colour_invariant_def)

lemma switch_to_idle_thread_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
      switch_to_idle_thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: switch_to_idle_thread_def RISCV64_A.arch_switch_to_idle_thread_def RISCV64_A.set_vm_root_def temp[symmetric] RISCV64_A.find_vspace_for_asid_def
    wp: do_machine_op_colour_maintained hoare_vcg_op_lift get_cap_cte_wp_at3)

lemma switch_to_thread_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
      switch_to_thread t
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: switch_to_thread_def temp[symmetric] RISCV64_A.arch_switch_to_thread_def RISCV64_A.set_vm_root_def RISCV64_A.find_vspace_for_asid_def
  wp: tcb_sched_action_colour_maintained do_machine_op_colour_maintained hoare_vcg_op_lift get_cap_cte_wp_at3)

lemma guarded_switch_to_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
      guarded_switch_to thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  by (wpsimp simp: guarded_switch_to_def
  wp: switch_to_thread_colour_maintained hoare_vcg_imp_lift[where P'=\<bottom>])

lemma schedule_choose_new_thread_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
     let domain_index' = Suc (domain_index s) mod length (domain_list s);
     next_dom = domain_list s ! domain_index';
     new_dom = fst next_dom in
     colour_invariant (s\<lparr>cur_domain := new_dom\<rparr>))\<rbrace>
      schedule_choose_new_thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: schedule_choose_new_thread_def choose_thread_def next_domain_def colour_invariant_def
  wp: switch_to_idle_thread_colour_maintained set_scheduler_action_colour_maintained guarded_switch_to_colour_maintained hoare_vcg_op_lift)
  by ((rule impI|rule conjI)+, clarsimp simp: Let_def)+

lemma temp2: "colour_invariant s = colour_invariant (s\<lparr>scheduler_action := action\<rparr>)"
  by (simp add: colour_invariant_def)

lemma schedule_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
     let domain_index' = Suc (domain_index s) mod length (domain_list s);
     next_dom = domain_list s ! domain_index';
     new_dom = fst next_dom in
      colour_invariant (s\<lparr>cur_domain := new_dom\<rparr>))\<rbrace>
      schedule
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: schedule_def temp2[symmetric] tcb_sched_action_def
  wp: schedule_choose_new_thread_colour_maintained set_scheduler_action_wp tcb_sched_action_colour_maintained guarded_switch_to_colour_maintained schedule_switch_thread_fastfail_inv hoare_vcg_op_lift)
  apply (wpsimp wp: hoare_pre_cont)
  apply (wpsimp wp: schedule_switch_thread_fastfail_inv)+
  apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
  apply (wpsimp wp: hoare_pre_cont)
  apply (wpsimp wp: schedule_switch_thread_fastfail_inv)+
  apply (wpsimp wp: schedule_choose_new_thread_colour_maintained)+
  apply (wpsimp wp: gts_drop_imp)
  apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
  by (clarsimp simp add: colour_invariant_def)

crunch call_kernel for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)
end
