theory New
  imports
    KernelInit_AI
    "$L4V_ARCH/ArchDetSchedSchedule_AI"
begin
section "Initialisation"
axiomatization
  colour_oracle :: "domain \<Rightarrow> obj_ref set"
  where
    colour_oracle_no_overlap: "x \<noteq> y \<longrightarrow> (colour_oracle x \<inter> colour_oracle y = {})"

term "obj_refs"
term "obj_ref_of"

definition
  check_cap_ref :: "cap \<Rightarrow> obj_ref set \<Rightarrow> bool"
  where
    "check_cap_ref cap obj_set \<equiv> obj_refs cap \<subseteq> obj_set"


term "ArchInvariants_AI.RISCV64.obj_addrs" (* should be used everywhere? *)
term "ArchInvariants_AI.RISCV64.global_refs"
term "ArchInvariants_AI.RISCV64.device_region"
term "obj_addrs"

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
    (case (tcb_state t) of BlockedOnReceive obj_ref _ \<Rightarrow> obj_ref \<in> obj_dom
                         | BlockedOnSend obj_ref _ \<Rightarrow> obj_ref \<in> obj_dom
                         | BlockedOnNotification obj_ref \<Rightarrow> obj_ref \<in> obj_dom
                         | _ \<Rightarrow> True) \<and>
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

section "KHeap_A Colour Invariant"
lemma set_object_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_kernel_object_ref kobj (colour_oracle (cur_domain s)))\<rbrace>
   set_object ptr kobj
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wp add: set_object_wp)
  apply (simp add: colour_invariant_def)
  apply wpsimp
  apply (simp add: obj_at_update)
  by presburger

lemma thread_set_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. let tcb = TCB (f $ the (get_tcb ptr s)) in check_kernel_object_ref tcb (colour_oracle (cur_domain s)))\<rbrace>
   thread_set f ptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wp add: thread_set_wp)
  apply (simp add: colour_invariant_def)
  apply (simp add: obj_at_update)
  by fastforce

lemma thread_set_priority_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_priority ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: thread_set_priority_def)
  apply (wp add: thread_set_wp)
  apply (simp add: colour_invariant_def obj_at_update)
  by fastforce+

lemma thread_set_time_slice_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_time_slice ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: thread_set_time_slice_def)
  apply (wp add: thread_set_wp)
  apply (simp add: colour_invariant_def obj_at_update)
  by fastforce+

lemma thread_set_domain_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     thread_set_domain ptr prio
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: thread_set_domain_def)
  apply (wp add: thread_set_wp)
  apply (simp add: colour_invariant_def obj_at_update)
  by fastforce+

lemma set_mcpriority_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     set_mcpriority ref mcp
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: set_mcpriority_def)
  apply (wp add: thread_set_wp)
  apply (simp add: colour_invariant_def obj_at_update)
  by fastforce+

lemma arch_thread_set_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
        let tcb = the $ get_tcb ptr s in
        let arch_tcb = f $ tcb_arch tcb in
        let new_tcb = TCB $ tcb \<lparr> tcb_arch := arch_tcb \<rparr> in
        check_kernel_object_ref new_tcb (colour_oracle (cur_domain s)))\<rbrace>
     arch_thread_set f ptr
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wp add: arch_thread_set_wp)
  apply (simp add: colour_invariant_def)
  apply (simp add: obj_at_update)
  by fastforce

lemma set_bound_notification_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. (set_option ntfn) \<subseteq> colour_oracle (cur_domain s))\<rbrace>
   set_bound_notification ptr ntfn
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (simp add: set_bound_notification_thread_set)
  apply (wp add: thread_set_wp)
  apply (simp add: colour_invariant_def obj_at_update)
  by fastforce+

lemma set_simple_ko_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
        let kobj = the $ kheap s ptr in
          is_simple_type kobj \<longrightarrow>
          partial_inv f kobj \<noteq> None \<longrightarrow>
          check_kernel_object_ref (f ep) (colour_oracle (cur_domain s)))\<rbrace>
     set_simple_ko f ptr ep
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold set_simple_ko_def)
  apply wpsimp
      apply (wp add: get_object_wp set_object_wp)+
  apply (simp add: obj_at_update colour_invariant_def obj_at_def)
  by auto

lemma throw_on_false_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
      f
    \<lbrace>\<lambda>_ . colour_invariant\<rbrace>
   \<Longrightarrow>
   \<lbrace>colour_invariant\<rbrace>
      throw_on_false ex f
   \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
by (simp add: hoare_wp_splits(12)
    throw_on_false_wp)

lemma set_thread_state_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s.
        let new_tcb = TCB (tcb \<lparr> tcb_state := ts \<rparr>) in
        check_kernel_object_ref new_tcb (colour_oracle (cur_domain s)))\<rbrace>
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
  apply (simp add: obj_at_update obj_at_def)
  unfolding colour_invariant_def
  apply (simp add: obj_at_update obj_at_def)
  by (smt (verit, best) RISCV64.ko_at_kheap
      check_kernel_object_ref.simps(2)
      get_tcb_obj_atE option.sel)

lemma as_user_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     as_user ptr f
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (unfold as_user_def)
  apply wpsimp
       apply (wp add: set_object_wp)+
  apply auto
  unfolding colour_invariant_def
  apply (simp add: obj_at_update)
  apply auto
  apply (case_tac "ptr\<noteq>ptra")
  apply (simp add: obj_at_def)+
  using get_tcb_SomeD by fastforce

crunch reschedule_required,
  possible_switch_to,
  set_thread_state_act,
  set_priority,
  set_scheduler_action,
  tcb_sched_action,
  set_tcb_queue,
  set_irq_state for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)

(*crunch thread_set_domain, thread_set_time_slice, thread_set_priority for colour_maintained: "colour_invariant"
  (wp: thread_set_wp
   simp: thread_set_domain_def thread_set_time_slice_def thread_set_priority_def colour_invariant_def obj_at_update)*)

section "Top-Down Colour Invariant Work"
term "call_kernel" (* what does schedule do? otherwise, it's basically handle_event and <handle> *)

crunch store_word_offs,
  set_extra_badge,
  set_cdt,
  update_cdt,
  set_message_info for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)

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
apply auto
by (simp add: check_cap_ref_def)

lemma tmp:
  "\<lbrakk>\<forall>ptr kobj.
           ko_at kobj ptr s \<and>
           ptr \<in> colour_oracle (cur_domain s) \<longrightarrow>
           check_kernel_object_ref kobj
            (colour_oracle (cur_domain s));
        fst (get_cap (a, b) s) = {(capa, s)} \<and>
        cap = capa\<rbrakk>
       \<Longrightarrow> check_cap_ref cap
            (colour_oracle (cur_domain s))"
sorry

lemma cap_insert_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s)))\<rbrace>
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
apply auto
apply (unfold colour_invariant_def)
apply (unfold cte_wp_at_def)
apply (erule exE)+
apply (thin_tac "fst (get_cap dest_slot s) = {(capb, s)} \<and> NullCap = capb")
apply (thin_tac "check_cap_ref new_cap (colour_oracle (cur_domain s))")
apply (erule allE[where x=a])
apply (erule allE[where x=kobj])
apply (subgoal_tac "kobj\<in>fst (get_object a s)")
apply (case_tac A)
apply simp
sorry

find_theorems "cte_wp_at ((=) _) _ _"
find_theorems "fst (get_cap _ _)"

lemma temp:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,-; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<not>(cond rv) \<longrightarrow> R rv s\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. if cond rv then (\<lambda>s. Q s \<and> True) else (\<lambda>s. Q s \<and> R rv s)\<rbrace>,-"
by (smt (verit) packed_validRE
    packed_validRI)

thm temp[where Q="\<lambda>s. colour_invariant s" and R="\<lambda>rv s. check_cap_ref rv (colour_oracle (cur_domain s))" and cond="\<lambda>rv. rv = NullCap"]

lemma transfer_caps_loop_colour_maintained: (* TODO - add precond saying all caps satisfy check (breaks a bunch of stuff) *)
  "\<lbrace>colour_invariant\<rbrace>
   transfer_caps_loop  ep rcv_buffer n caps slots mi
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (induction caps arbitrary: mi n slots ep rcv_buffer)
    apply simp
apply wpsimp
apply (rule conjI; rule impI)+
apply wpsimp
apply assumption
apply wpsimp
apply (wp add: set_extra_badge_colour_maintained)
apply simp
apply wpsimp
apply assumption
apply wpsimp
apply (wp add: cap_insert_colour_maintained)
apply simp
apply wpsimp
defer
defer
apply (rule conjI; rule impI)+
apply wpsimp
apply assumption
apply wpsimp
apply (wp add: set_extra_badge_colour_maintained)
apply simp
apply wpsimp
apply wp
apply (wp add: temp)
apply simp
apply (simp add: check_cap_ref_def)
sorry


find_theorems "derive_cap"
find_theorems "transfer_caps_loop"
find_theorems "\<lambda>rv. if _ then _ else _"
find_theorems "_ = NullCap \<longrightarrow> _"
thm "derive_cap_objrefs"
thm "hoare_post_imp"
thm "hoare_if_r_and"

lemma transfer_caps_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
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
               transfer_caps_colour_maintained)+ (* TODO - come back to this once transfer caps is done *)
sorry

lemma syscall_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
   syscall param_a param_b param_c param_d param_e
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
sorry

crunch call_kernel for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)
end
