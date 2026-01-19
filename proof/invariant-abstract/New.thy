theory New
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

term "ArchInvariants_AI.RISCV64.obj_addrs" (* should be used everywhere? *)
term obj_ref_of

fun
  check_tcb_state :: "thread_state \<Rightarrow> obj_ref set \<Rightarrow> bool"
  where
    "check_tcb_state (BlockedOnReceive obj_ref _) obj_dom = (obj_ref \<in> obj_dom \<union> {0})"
  |"check_tcb_state (BlockedOnSend obj_ref _) obj_dom = (obj_ref \<in> obj_dom \<union> {0})"
  |"check_tcb_state (BlockedOnNotification obj_ref) obj_dom = (obj_ref \<in> obj_dom \<union> {0})"
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

definition colour_invariant
  where
    "colour_invariant s \<equiv> \<forall>ptr kobj. \<forall>(dom, _)\<in>(set (domain_list s)).
    (ko_at kobj ptr s \<and> ptr \<in> colour_oracle dom) \<longrightarrow>
    (check_kernel_object_ref kobj (colour_oracle dom) \<or> ptr = 0)"

definition valid_ptr_in_cur_domain
  where
    "valid_ptr_in_cur_domain ptr s \<equiv> ptr \<in> colour_oracle (cur_domain s) \<or> ptr = 0"

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

lemma ptr_no_domain_overlap:
  "\<lbrakk>valid_ptr_in_cur_domain ptr s; ptr \<in> colour_oracle a\<rbrakk> \<Longrightarrow> a = cur_domain s"
  apply (simp add: valid_ptr_in_cur_domain_def)
  apply safe
  using colour_oracle_no_overlap colour_oracle_no_zero by fastforce+

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
  "\<lbrace>colour_invariant\<rbrace>
      f
    \<lbrace>\<lambda>_ . colour_invariant\<rbrace>
   \<Longrightarrow>
   \<lbrace>colour_invariant\<rbrace>
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
          valid_ptr_in_cur_domain a s;
          invs s\<rbrakk>
         \<Longrightarrow> check_cap_ref cap
               (colour_oracle (cur_domain s))"
  apply (simp add: cte_wp_at_cases2 valid_ptr_in_cur_domain_def)
  apply safe
   apply (simp_all add: colour_invariant_def obj_at_def)
  apply (frule invs_cur_domain_list)
  apply (erule exE)
   apply (erule_tac x=a in allE)
   apply (erule_tac x="CNode sz fun" in allE)
  apply (erule_tac x="(cur_domain s, aa)" in ballE)
  apply clarsimp
  apply safe
  apply (erule_tac x=b in allE)
    apply (simp add: check_kernel_object_ref_def)
  apply (simp add: colour_oracle_no_zero)
     apply (erule_tac x=a in allE)
   apply (erule_tac x="CNode sz fun" in allE)
      apply clarsimp
  apply (frule invs_pspace_in_kernel_window)
  apply (simp add: RISCV64.pspace_in_kernel_window_def)
  apply (erule_tac x=0 in allE)
      apply (erule_tac x="CNode sz fun" in allE)
  apply clarsimp
  apply (simp add: RISCV64.kernel_window_def)
  apply (frule RISCV64.invs_valid_uses)
  apply (simp add: RISCV64.valid_uses_def)
  apply (erule_tac x=0 in allE)
  apply clarsimp
  apply (simp add: subset_eq)
  apply clarsimp
  apply (erule_tac x=0 in ballE)
  apply (simp add: RISCV64_A.pptr_base_def RISCV64.pptrBase_def RISCV64.canonical_bit_def)
  apply simp
  apply (frule invs_cur_domain_list)
  apply (erule exE)
  apply (erule_tac x=a in allE)
  apply (erule_tac x="TCB tcb" in allE)
   apply (erule_tac x="(cur_domain s, aa)" in ballE)
  apply (frule_tac a=b and b=cap in ranI)
    apply (fastforce simp add: ran_tcb_cnode_map colour_oracle_no_zero)
  apply simp
  apply (frule invs_cur_domain_list)
  apply (erule exE)
     apply (erule_tac x=a in allE)
   apply (erule_tac x="TCB tcb" in allE)
  apply (erule_tac x="(cur_domain s, aa)" in ballE)
      apply clarsimp
  apply (frule invs_pspace_in_kernel_window)
  apply (simp add: RISCV64.pspace_in_kernel_window_def)
  apply (erule_tac x=0 in allE)
      apply (erule_tac x="TCB tcb" in allE)
  apply clarsimp
  apply (simp add: RISCV64.kernel_window_def)
  apply (frule RISCV64.invs_valid_uses)
  apply (simp add: RISCV64.valid_uses_def)
  apply (erule_tac x=0 in allE)
  apply clarsimp
  apply (simp add: subset_eq)
  apply clarsimp
  apply (erule_tac x=0 in ballE)
  apply (simp add: RISCV64_A.pptr_base_def RISCV64.pptrBase_def RISCV64.canonical_bit_def)
  apply simp
  by simp

lemma cap_insert_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref new_cap (colour_oracle (cur_domain s))) and (\<lambda>s. valid_ptr_in_cur_domain (fst src_slot) s) and (\<lambda>s. valid_ptr_in_cur_domain (fst dest_slot) s)\<rbrace>
cap_insert new_cap src_slot dest_slot
\<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (cases src_slot)
  apply (wpsimp simp: cap_insert_def update_cdt_def colour_invariant_def)
            apply safe
             apply (fold colour_invariant_def)
             apply (wpsimp wp: set_cdt_colour_maintained)+
  by (wpsimp simp: cte_wp_at_check_cap_ref wp: set_cdt_colour_maintained set_cap_colour_maintained set_untyped_cap_as_full_colour_maintained get_cap_wp set_untyped_cap_as_full_valid_ptr_in_cur_domain)+

lemma hoare_weird_if:
  "\<lbrakk>\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. Q\<rbrace>,-; \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<not>(cond rv) \<longrightarrow> R rv s\<rbrace>,-\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv. if cond rv then (\<lambda>s. Q s \<and> True) else (\<lambda>s. Q s \<and> R rv s)\<rbrace>,-"
  apply (wpsimp wp: hoare_vcg_if_lift_ER hoare_vcg_conj_liftE_R' hoare_vcg_imp_liftE_R'[where Q'=P])
     apply (wpsimp wp: hoare_FalseE)
    apply wpsimp+
   apply (rule hoare_strengthen_postE_R[where Q'="\<lambda>rv s. (\<not> cond rv \<longrightarrow> R rv s) \<and> Q s"])
  by (wpsimp wp: hoare_vcg_conj_liftE_R')+

lemma transfer_caps_loop_colour_maintained:
  "\<lbrace>colour_invariant and
        (\<lambda>s.
            (
              (\<forall>(cap, o_ref, _)\<in>(set caps).
                check_cap_ref cap (colour_oracle (cur_domain s)) \<and>
                valid_ptr_in_cur_domain o_ref s)) \<and>
              (\<forall>(slot, _)\<in>(set slots). valid_ptr_in_cur_domain slot s)
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
    apply (rule conjI; rule impI)+
      apply (wpsimp wp: set_extra_badge_colour_maintained)
       apply (simp add: set_extra_badge_def valid_ptr_in_cur_domain_def)
       apply wpsimp
      apply (simp add: valid_ptr_in_cur_domain_def)
     apply wpsimp
        apply (wpsimp simp: valid_ptr_in_cur_domain_def wp: cap_insert_colour_maintained)
       apply simp
       apply wpsimp+
      apply (wp add: hoare_weird_if[where P=
        "colour_invariant and
        (\<lambda>s. (\<forall>(cap, o_ref, _)\<in>(set (a # caps)).
           check_cap_ref cap (colour_oracle (cur_domain s)) \<and> valid_ptr_in_cur_domain o_ref s) \<and>
              (\<forall>(slot, _)\<in>(set slots). valid_ptr_in_cur_domain slot s))"
      ])
       apply (wpsimp simp: check_cap_ref_def wp: derive_cap_inv)+
      apply (wp add: derive_cap_objrefs_iszombie)
      apply simp+
    apply (rule conjI|rule impI)+
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

lemma transfer_caps_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. (\<forall>(cap, o_ref, _)\<in>(set caps). check_cap_ref cap (colour_oracle (cur_domain s)) \<and> valid_ptr_in_cur_domain o_ref s)) and (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb receiver s)) (colour_oracle (cur_domain s)))\<rbrace>
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
  apply (rule_tac Q'="\<lambda>rv s. colour_invariant s \<and>
           ((\<exists>x. rv = ((a, b), x)) \<longrightarrow>
           (\<forall>cap. cte_wp_at ((=) cap)
                   (a, b) s \<longrightarrow>
                  check_cap_ref cap
                   (colour_oracle
(cur_domain s)) \<and> valid_ptr_in_cur_domain a s))" in hoare_strengthen_postE_R)
  by (wpsimp simp: valid_ptr_in_cur_domain_def wp: resolve_address_bits_ret_colour)+

lemma copy_mrs_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
     copy_mrs  sender sbuf receiver rbuf n
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: copy_mrs_def)
    apply (rule conjI)
     apply (rule impI)
  by (wpsimp wp: mapM_wp[where S="UNIV"] store_word_offs_colour_maintained load_word_offs_P as_user_colour_maintained)+

lemma do_normal_transfer_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb sender s)) (colour_oracle (cur_domain s))) and (\<lambda>s. check_cap_ref (tcb_ctable (the $ get_tcb receiver s)) (colour_oracle (cur_domain s)))\<rbrace>
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
  by (cases "receiver = sender"; clarsimp)

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

lemma next_domain_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
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
  "\<lbrace>colour_invariant\<rbrace>
      schedule_choose_new_thread
    \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
  apply (wpsimp simp: schedule_choose_new_thread_def choose_thread_def next_domain_def colour_invariant_def
  wp: switch_to_idle_thread_colour_maintained set_scheduler_action_colour_maintained guarded_switch_to_colour_maintained hoare_vcg_op_lift)
  by ((rule impI|rule conjI)+, clarsimp simp: Let_def)+

lemma temp2: "colour_invariant s = colour_invariant (s\<lparr>scheduler_action := action\<rparr>)"
  by (simp add: colour_invariant_def)

lemma schedule_colour_maintained:
  "\<lbrace>colour_invariant\<rbrace>
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

\<comment>\<open>apply (rule bind_wp [OF _ get_simple_ko_inv])
  apply (case_tac ep, simp_all)\<close>
  find_theorems do_ipc_transfer tcb_at
  find_theorems do_ipc_transfer "\<lbrace>_\<rbrace>_\<lbrace>\<lambda>_ _. obj_at _ _ _\<rbrace>"
  find_theorems do_ipc_transfer scheduler_action
thm do_ipc_transfer_scheduler_act[where P="\<lambda>s. s \<noteq> resume_cur_thread"]

lemma send_ipc_colour_maintained:
  "\<lbrace>colour_invariant and (\<lambda>s. valid_ptr_in_cur_domain (cur_thread s) s) and invs and (\<lambda>s. valid_ptr_in_cur_domain thread s)\<rbrace>
  send_ipc block call badge can_grant can_grant_reply thread epptr
  \<lbrace>\<lambda>_. colour_invariant\<rbrace>"
                  apply (wpsimp simp: send_ipc_def wp: set_simple_ko_colour_maintained)
                       apply (wpsimp simp: valid_ptr_in_cur_domain_def Let_def wp: set_thread_state_colour_maintained)
           apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def thread_get_def set_object_def get_object_def gets_the_def)
apply wpsimp+
apply (wpsimp wp: set_simple_ko_colour_maintained)
                       apply (wpsimp simp: valid_ptr_in_cur_domain_def Let_def wp: set_thread_state_colour_maintained)
apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def get_thread_state_def thread_get_def set_object_def get_object_def gets_the_def)
  apply wpsimp+
apply (wpsimp wp: setup_caller_cap_colour_maintained)
                       apply (wpsimp wp: set_thread_state_colour_maintained)
apply (rule_tac Q'="\<lambda>_.
  colour_invariant and
  valid_ptr_in_cur_domain thread and
  (\<lambda>s. call \<longrightarrow>
    (if (can_grant \<or> can_grant_reply) then (valid_ptr_in_cur_domain x21)
    else (\<lambda>s. check_tcb_state Inactive (colour_oracle (cur_domain s)))) s)" in hoare_post_imp)
  apply force
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: possible_switch_to_colour_maintained)
apply (wpsimp simp: valid_ptr_in_cur_domain_def)
apply wpsimp
apply safe
apply (wpsimp simp: valid_ptr_in_cur_domain_def)+
apply (wpsimp wp: set_thread_state_colour_maintained)
apply wpsimp
prefer 2
apply wpsimp
prefer 2
apply wpsimp
prefer 2
apply wpsimp
prefer 2
apply wpsimp
apply (wpsimp simp: do_ipc_transfer_def)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
  apply (wpsimp wp: do_normal_transfer_colour_maintained)
  apply (rule_tac Q'="\<lambda>_ s. (x21 \<in> colour_oracle (cur_domain s) \<or> x21 = 0) \<and> (thread \<in> colour_oracle (cur_domain s) \<or> thread = 0)" in hoare_strengthen_post)
  apply wpsimp
        apply (clarsimp simp add: valid_ptr_in_cur_domain_def)
  apply wpsimp
  apply (wpsimp simp: do_fault_transfer_def)
  apply (wpsimp wp: as_user_colour_maintained)
  apply (rule_tac Q'="\<lambda>_ s. (x21 \<in> colour_oracle (cur_domain s) \<or> x21 = 0) \<and> (thread \<in> colour_oracle (cur_domain s) \<or> thread = 0)" in hoare_strengthen_post)
  apply wpsimp
        apply (clarsimp simp add: valid_ptr_in_cur_domain_def)
  apply (wpsimp wp: set_message_info_colour_maintained set_mrs_colour_maintained make_fault_msg_colour_maintained thread_get_wp gts_wp)+
  apply (wpsimp simp: set_simple_ko_def wp: set_object_wp get_object_wp get_simple_ko_wp)
  apply clarsimp
apply (wpsimp wp: get_simple_ko_wp)
  apply clarsimp
  apply (safe; clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
  apply (clarsimp simp add: obj_at_def)
  apply (case_tac "xa = cur_thread s"; clarsimp simp add: st_tcb_at_def obj_at_def)
  apply (frule tcb_at_invs)
apply (clarsimp simp add: obj_at_def is_tcb_def)
  apply (clarsimp simp add: obj_at_def)
  apply (case_tac "xa = cur_thread s"; clarsimp simp add: st_tcb_at_def obj_at_def)
  apply (frule tcb_at_invs)
apply (clarsimp simp add: obj_at_def is_tcb_def)
apply (clarsimp simp add: obj_at_def)
  apply (case_tac "xa = cur_thread s"; clarsimp simp add: st_tcb_at_def obj_at_def)
  apply (frule tcb_at_invs)
apply (clarsimp simp add: obj_at_def is_tcb_def)
apply (meson kernel_object.distinct(10)
    ko_at_obj_congD tcb_at_invs
    tcb_at_ko_at)
apply (clarsimp simp add: obj_at_def)
apply safe
  find_theorems st_tcb_at -valid "st_tcb_at ((=) _) _ _"
find_theorems -valid cur_thread
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
  apply (wpsimp wp: get_simple_ko_wp)
apply (rule_tac Q'="\<lambda>_ s. colour_invariant s \<and> (block \<longrightarrow> valid_ptr_in_cur_domain thread s)" in hoare_strengthen_post)
        apply (wpsimp wp: get_simple_ko_wp)
  apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
        apply (wpsimp wp: get_simple_ko_wp)
apply (rule_tac Q'="\<lambda>_ s. colour_invariant s \<and> (block \<longrightarrow> valid_ptr_in_cur_domain thread s)" in hoare_strengthen_post)
        apply (wpsimp wp: get_simple_ko_wp)
  apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
        apply (wpsimp wp: get_simple_ko_wp)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (rule_tac Q'="\<lambda>_ s. colour_invariant s \<and> (block \<longrightarrow> valid_ptr_in_cur_domain thread s)" in hoare_strengthen_post)
        apply (wpsimp wp: get_simple_ko_wp)
  apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (rule_tac Q'="\<lambda>_ s. colour_invariant s \<and> (block \<longrightarrow> valid_ptr_in_cur_domain thread s)" in hoare_strengthen_post)
        apply (wpsimp wp: get_simple_ko_wp)
       apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
      apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (rule_tac Q'="\<lambda>_ s. colour_invariant s \<and> (block \<longrightarrow> valid_ptr_in_cur_domain thread s)" in hoare_strengthen_post)
        apply (wpsimp wp: get_simple_ko_wp)
       apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (rule_tac Q'="\<lambda>_ s. colour_invariant s \<and> (block \<longrightarrow> valid_ptr_in_cur_domain (cur_thread s) s)" in hoare_strengthen_post)
        apply (wpsimp wp: get_simple_ko_wp)
       apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: get_simple_ko_wp)
apply (rule_tac Q'="\<lambda>_ s. colour_invariant s \<and> (block \<longrightarrow> valid_ptr_in_cur_domain (cur_thread s) s)" in hoare_strengthen_post)
        apply (wpsimp wp: get_simple_ko_wp)
       apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
  apply safe
apply (clarsimp simp add: colour_oracle_no_zero valid_ptr_in_cur_domain_def)+
apply safe
  apply (simp add: obj_at_def)
  apply clarsimp
oops

lemma handle_fault_colour_maintained:
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
apply (wpsimp wp: set_simple_ko_colour_maintained)
                       apply (wpsimp simp: valid_ptr_in_cur_domain_def Let_def wp: set_thread_state_colour_maintained)
           apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def)
apply (wpsimp simp: get_thread_state_def thread_get_def)
apply (wpsimp simp: set_object_def get_object_def)
apply (wpsimp simp: gets_the_def)
apply (wpsimp wp: setup_caller_cap_colour_maintained)
apply (wpsimp wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp wp: possible_switch_to_colour_maintained)
apply (wpsimp simp: valid_ptr_in_cur_domain_def wp: hoare_vcg_op_lift hoare_vcg_conj_lift)
apply (wpsimp simp: possible_switch_to_def)
apply (wpsimp simp: possible_switch_to_def)
apply (wpsimp simp: possible_switch_to_def valid_ptr_in_cur_domain_def)
apply (wpsimp wp: set_thread_state_colour_maintained)
apply (wpsimp simp: set_thread_state_def set_thread_state_act_def set_scheduler_action_def)
apply (wpsimp simp: get_thread_state_def thread_get_def)
apply (wpsimp simp: set_object_def get_object_def)
apply (wpsimp simp: gets_the_def)
apply wpsimp
                         apply (rule_tac Q'="\<lambda>_ s.(\<exists>ko. kheap s x31 = Some ko \<and> a_type ko \<noteq> AEndpoint)" in hoare_post_imp)
                          apply fastforce
  apply (wpsimp wp: sts_obj_at_impossible)
                         apply (rule_tac p=x31 and T=AEndpoint and P="\<lambda>x. \<not>x" in set_thread_state_typ_at[unfolded obj_at_def])
defer
  apply (wpsimp wp: hoare_vcg_op_lift)
thm sts_typ_at[unfolded obj_at_def, where p=x31 and T=AEndpoint]
thm sts_obj_at_impossible[unfolded obj_at_def, where P="\<lambda>k. a_type k \<noteq> AEndpoint"]
  find_theorems set_thread_state obj_at
thm sts_typ_ats
defer
oops

crunch call_kernel for colour_maintained: "colour_invariant"
  (simp: colour_invariant_def obj_at_update)
end
