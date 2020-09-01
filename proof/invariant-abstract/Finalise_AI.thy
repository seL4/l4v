(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_AI
imports
  "./$L4V_ARCH/ArchIpcCancel_AI"
  "./$L4V_ARCH/ArchInterruptAcc_AI"
  "./$L4V_ARCH/ArchRetype_AI"
begin

definition
  fst_cte_ptrs :: "cap \<Rightarrow> cslot_ptr set"
where
 "fst_cte_ptrs cap \<equiv> (case cap of
    cap.CNodeCap r bits guard \<Rightarrow> {(r, replicate bits False)}
  | cap.ThreadCap r           \<Rightarrow> {(r, tcb_cnode_index 0)}
  | cap.Zombie r zb n         \<Rightarrow> {(r, replicate (zombie_cte_bits zb) False)}
  | _                         \<Rightarrow> {})"

context begin interpretation Arch .

requalify_consts
  vs_cap_ref
  unmap_page
  clearMemory
  arch_post_cap_delete_pre

requalify_facts
  final_cap_lift
  no_irq_clearMemory
  valid_global_refsD
  valid_global_refsD2
  arch_post_cap_deletion_valid_objs
  arch_post_cap_deletion_cte_wp_at
  arch_post_cap_deletion_caps_of_state
  arch_post_cap_deletion_irq_node
  arch_post_cap_deletion_invs
  valid_arch_arch_tcb_set_registers

end

definition
  "post_cap_delete_pre cap cs \<equiv> case cap of
     IRQHandlerCap irq \<Rightarrow> cap \<notin> ran cs
   | ArchObjectCap acap \<Rightarrow> arch_post_cap_delete_pre cap cs
   | _ \<Rightarrow> False"

lemma update_restart_pc_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> update_restart_pc t \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (simp add: update_restart_pc_def as_user_caps_of_state)

locale Finalise_AI_1 =
  fixes state_ext_type1 :: "('a :: state_ext) itself"
  fixes state_ext_type2 :: "('b :: state_ext) itself"
  assumes replaceable_cdt_update[simp]:
    "\<And>f (s :: 'a state). replaceable (cdt_update f s) = replaceable s"
  assumes replaceable_revokable_update[simp]:
    "\<And> f (s :: 'a state).replaceable (is_original_cap_update f s) = replaceable s"
  assumes replaceable_more_update[simp]:
    "\<And> (f :: 'a \<Rightarrow> 'b) (s :: 'a state) sl cap cap'. replaceable (trans_state f s) sl cap cap'
      = replaceable s sl cap cap'"
  assumes obj_ref_ofI: "\<And> cap x. obj_refs cap = {x} \<Longrightarrow> obj_ref_of cap = x"
  assumes empty_slot_invs:
    "\<And>sl info. \<lbrace>\<lambda> (s :: 'a state). invs s \<and> cte_wp_at (replaceable s sl cap.NullCap) sl s \<and>
          (info \<noteq> NullCap \<longrightarrow> post_cap_delete_pre info ((caps_of_state s) (sl \<mapsto> NullCap)))\<rbrace>
     empty_slot sl info
     \<lbrace>\<lambda>rv. invs\<rbrace>"
  assumes dom_tcb_cap_cases_lt:
    "dom tcb_cap_cases = {xs. length xs = 3 \<and> unat (of_bl xs :: machine_word) < 5}"
  assumes unbind_notification_final[wp]:
    "\<And> cap t.\<lbrace>is_final_cap' cap :: 'a state \<Rightarrow> bool\<rbrace>
       unbind_notification t
     \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
   assumes finalise_cap_cases1:
  "\<And> cap final slot. \<lbrace>\<lambda>(s :: 'a state). final \<longrightarrow> is_final_cap' cap s
         \<and> cte_wp_at ((=) cap) slot s\<rbrace>
     finalise_cap cap final
   \<lbrace>\<lambda>rv (s :: 'a state). fst rv = cap.NullCap
         \<and> snd rv = (if final then cap_cleanup_opt cap else NullCap)
         \<and> (snd rv \<noteq> NullCap \<longrightarrow> is_final_cap' cap s)
     \<or>
       is_zombie (fst rv) \<and> is_final_cap' cap s
        \<and> snd rv = NullCap
        \<and> appropriate_cte_cap (fst rv) = appropriate_cte_cap cap
        \<and> cte_refs (fst rv) = cte_refs cap
        \<and> gen_obj_refs (fst rv) = gen_obj_refs cap
        \<and> obj_size (fst rv) = obj_size cap
        \<and> fst_cte_ptrs (fst rv) = fst_cte_ptrs cap
        \<and> vs_cap_ref cap = None\<rbrace>"
  assumes arch_finalise_cap_typ_at[wp]:
    "\<And> P T p a b.
      \<lbrace>\<lambda>(s :: 'a state). P (typ_at T p s)\<rbrace> arch_finalise_cap a b \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  assumes prepare_thread_delete_typ_at[wp]:
    "\<And> P T p a.
      \<lbrace>\<lambda>(s :: 'a state). P (typ_at T p s)\<rbrace> prepare_thread_delete a \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  assumes prepare_thread_delete_cur_thread[wp]:
    "\<And> P a. prepare_thread_delete a \<lbrace>\<lambda>s :: 'a state. P (cur_thread s)\<rbrace>"
  assumes finalise_cap_new_valid_cap[wp]:
    "\<And> cap x. \<lbrace>valid_cap cap :: 'a state \<Rightarrow> bool\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. valid_cap (fst rv)\<rbrace>"
  assumes arch_finalise_cap_invs[wp]:
  "\<And> cap final.\<lbrace>invs and (valid_cap (ArchObjectCap cap) :: 'a state \<Rightarrow> bool)\<rbrace>
     arch_finalise_cap cap final
   \<lbrace>\<lambda>rv. invs\<rbrace>"
(*  assumes obj_at_not_live_valid_arch_cap_strg:
    "\<And>(s :: 'a state) cap r. (s \<turnstile> ArchObjectCap cap \<and> aobj_ref cap = Some r)
          \<longrightarrow> obj_at (\<lambda>ko. \<not> live ko) r s"*)
  assumes deleting_irq_handler_slot_not_irq_node:
    "\<And> irq sl.
    \<lbrace>if_unsafe_then_cap and valid_global_refs
                        and cte_wp_at (\<lambda>cp. cap_irqs cp \<noteq> {}) sl\<rbrace>
      deleting_irq_handler irq
    \<lbrace>\<lambda>rv (s :: 'a state). (interrupt_irq_node s irq, []) \<noteq> sl\<rbrace>"
  assumes no_cap_to_obj_with_diff_ref_finalI:
    "\<And>p (s :: 'a state) cap cap'. \<lbrakk> cte_wp_at ((=) cap) p s; is_final_cap' cap s;
              obj_refs cap' = obj_refs cap \<rbrakk>
        \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  assumes suspend_no_cap_to_obj_ref[wp]:
    "\<And> S t cap.
    \<lbrace>no_cap_to_obj_with_diff_ref cap S :: 'a state \<Rightarrow> bool\<rbrace>
       suspend t
     \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  assumes finalise_cap_replaceable:
    "\<And> cap x sl.
    \<lbrace>\<lambda>(s :: 'a state). s \<turnstile> cap \<and> x = is_final_cap' cap s
          \<and> cte_wp_at ((=) cap) sl s \<and> invs s
          \<and> (cap_irqs cap \<noteq> {} \<longrightarrow> if_unsafe_then_cap s \<and> valid_global_refs s)
          \<and> (is_arch_cap cap \<longrightarrow> pspace_aligned s \<and>
                                 valid_vspace_objs s \<and>
                                 valid_arch_state s \<and>
                                 valid_arch_caps s)\<rbrace>
       finalise_cap cap x
     \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) cap\<rbrace>"
  assumes deleting_irq_handler_cte_preserved:
  "\<And> P p irq.\<lbrakk> \<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap \<rbrakk>
    \<Longrightarrow> \<lbrace>cte_wp_at P p\<rbrace>
          deleting_irq_handler irq :: 'a state \<Rightarrow> (unit \<times> 'a state) set \<times> bool
        \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  assumes arch_finalise_cap_cur_thread[wp]:
    "\<And> P a b. arch_finalise_cap a b \<lbrace>\<lambda>s :: 'a state. P (cur_thread s)\<rbrace>"
  assumes arch_finalise_cap_cte_wp_at[wp]:
    "\<And> P P' p a b.
    \<lbrace>\<lambda>(s :: 'a state). P (cte_wp_at P' p s)\<rbrace> arch_finalise_cap a b \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  assumes prepare_thread_delete_cte_wp_at[wp]:
    "\<And> P p a.
      \<lbrace>\<lambda>(s :: 'a state). P (cte_wp_at P' p s)\<rbrace> prepare_thread_delete a \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  assumes prepare_thread_delete_caps_of_state:
    "\<And>P t. \<lbrace>\<lambda>(s :: 'a state). P (caps_of_state s)\<rbrace> prepare_thread_delete t \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"


text \<open>Properties about empty_slot\<close>

definition
 "halted_if_tcb \<equiv> \<lambda>t s. tcb_at t s \<longrightarrow> st_tcb_at halted t s"

lemma tcb_cap_valid_NullCapD:
  "tcb_cap_valid cap sl s \<Longrightarrow> tcb_cap_valid NullCap sl s"
  apply (clarsimp simp: tcb_cap_valid_def valid_ipc_buffer_cap_def
                 elim!: pred_tcb_weakenE split: option.splits)
  apply (rename_tac get set restr)
  apply (subgoal_tac "(get, set, restr) \<in> ran tcb_cap_cases")
   apply (fastforce simp: ran_tcb_cap_cases is_cap_simps
                    split: Structures_A.thread_state.split)
  apply (simp add: ranI)
  done


lemma valid_NullCapD:
  "valid_objs s \<Longrightarrow> tcb_cap_valid NullCap sl s"
  apply (clarsimp simp: tcb_cap_valid_def
                        valid_ipc_buffer_cap_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb split: option.split)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def tcb_cap_cases_def
                 split: Structures_A.thread_state.split)
  done


lemma valid_NullCap_strg:
  " valid_objs s \<longrightarrow> tcb_cap_valid NullCap sl s"
  by (simp add: valid_NullCapD)


lemma tcb_cap_valid_pspaceI[intro]:
  "\<lbrakk> tcb_cap_valid cap sl s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> tcb_cap_valid cap sl s'"
  by (clarsimp simp: tcb_cap_valid_def obj_at_def pred_tcb_at_def)


crunch valid_objs[wp]: deleted_irq_handler "valid_objs"


lemma tcb_cp_valid_trans_state_update[simp]: "tcb_cap_valid cap sl
         (trans_state f s) = tcb_cap_valid cap sl s"
  apply (simp add: tcb_cap_valid_def)
  done

crunches post_cap_deletion
  for valid_objs[wp]: "valid_objs"

lemma empty_slot_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> empty_slot sl irqopt \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (rule hoare_pre)
   apply (wp set_cap_valid_objs set_cdt_valid_objs set_cdt_valid_cap
                 | simp add: trans_state_update[symmetric] del: trans_state_update| wpcw
                 | strengthen valid_NullCap_strg
                 | wp (once) hoare_drop_imps)+
  done

crunch typ_at[wp]: empty_slot "\<lambda>s. P (typ_at T p s)"

lemmas empty_slot_valid_cap[wp] = valid_cap_typ [OF empty_slot_typ_at]

locale mdb_empty_abs = vmdb_abs +
  fixes slot
  fixes n::cdt
  defines "n \<equiv> (\<lambda>p. (if m p = Some slot then m slot else m p)) (slot := None)"


lemma (in mdb_empty_abs) parency:
  "n \<Turnstile> p \<rightarrow> p' = (p \<noteq> slot \<and> p' \<noteq> slot \<and> m \<Turnstile> p \<rightarrow> p')"
proof
  assume n: "n \<Turnstile> p \<rightarrow> p'"

  from n
  have "p \<noteq> slot"
    by (clarsimp dest!: tranclD simp: n_def cdt_parent_of_def
                 split: if_split_asm)
  moreover
  from n
  have "p' \<noteq> slot"
    by (clarsimp dest!: tranclD2 simp: n_def cdt_parent_of_def )
  moreover
  from n
  have "m \<Turnstile> p \<rightarrow> p'"
  proof induct
    case (base x)
    thus ?case
      apply (clarsimp simp: cdt_parent_of_def n_def split: if_split_asm)
       apply (rule trancl_trans)
        apply (fastforce simp: cdt_parent_of_def)+
      done
  next
    case (step y z)
    thus ?case
      apply (clarsimp simp: cdt_parent_of_def n_def split: if_split_asm)
       apply (erule trancl_trans)
       apply (rule trancl_trans)
        apply (fastforce simp: cdt_parent_of_def)
       apply (fastforce simp: cdt_parent_of_def)
      apply (erule trancl_trans)
      apply (fastforce simp: cdt_parent_of_def)
      done
  qed
  ultimately
  show "p \<noteq> slot \<and> p' \<noteq> slot \<and> m \<Turnstile> p \<rightarrow> p'" by simp
next
  assume asm: "p \<noteq> slot \<and> p' \<noteq> slot \<and> m \<Turnstile> p \<rightarrow> p'"

  from asm have p: "p \<noteq> slot" ..
  from asm have p': "p' \<noteq> slot" by simp

  from asm
  have m: "m \<Turnstile> p \<rightarrow> p'" by simp
  hence neq: "p \<noteq> p'" by clarsimp
  from m
  have "if p' = slot then
          \<exists>p''. (p, p'') \<in> (cdt_parent_rel m)^* \<and> m \<Turnstile> p'' \<leadsto> p' \<and> (p, p'') \<in> (cdt_parent_rel n)^*
        else
          n \<Turnstile> p \<rightarrow> p'"
  proof induct
    case (base y)
    thus ?case
      apply (clarsimp simp: cdt_parent_of_def simp del: split_paired_Ex)
      apply (fastforce simp: cdt_parent_of_def n_def p)
      done
  next
    case (step y z)
    thus ?case
      apply (clarsimp simp: cdt_parent_of_def simp del: split_paired_Ex)
      apply (rule conjI)
       apply (clarsimp simp del: split_paired_Ex)
       apply (cases "y = slot", simp)
       apply fastforce
      apply (clarsimp simp del: split_paired_Ex)
      apply (cases "y = slot")
       apply (simp del: split_paired_Ex)
       apply (elim exE conjE)
       apply (drule rtranclD [where R="cdt_parent_rel n"])
       apply (erule disjE)
        apply simp
        apply (rule r_into_trancl)
        apply (clarsimp simp: cdt_parent_of_def n_def)
       apply clarsimp
       apply (erule trancl_trans)
       apply (fastforce simp: cdt_parent_of_def n_def)
      apply simp
      apply (erule trancl_trans)
      apply (fastforce simp: cdt_parent_of_def n_def)
      done
  qed
  with p'
  show "n \<Turnstile> p \<rightarrow> p'" by simp
qed


lemma (in mdb_empty_abs) descendants:
  "descendants_of p n =
  (if p = slot then {} else descendants_of p m - {slot})"
  by (auto simp add: descendants_of_def parency)


lemma (in mdb_empty_abs) no_mloop_n:
  "no_mloop n"
  by (simp add: no_mloop_def parency)


lemma final_mdb_update[simp]:
  "is_final_cap' cap (cdt_update f s) = is_final_cap' cap s"
  by (clarsimp simp: is_final_cap'_def2)


lemma no_cap_to_obj_with_diff_cdt_update[simp]:
  "no_cap_to_obj_with_diff_ref cap S (cdt_update f s)
        = no_cap_to_obj_with_diff_ref cap S s"
  by (simp add: no_cap_to_obj_with_diff_ref_def)


lemma no_cap_to_obj_with_diff_rvk_update[simp]:
  "no_cap_to_obj_with_diff_ref cap S (is_original_cap_update f s)
        = no_cap_to_obj_with_diff_ref cap S s"
  by (simp add: no_cap_to_obj_with_diff_ref_def)

lemma zombies_final_cdt_update[simp]:
  "zombies_final (cdt_update f s) = zombies_final s"
  by (fastforce elim!: zombies_final_pspaceI)


lemma post_cap_deletion_invs:
  "\<lbrace>\<lambda>s. invs s \<and> (info \<noteq> NullCap \<longrightarrow> post_cap_delete_pre info (caps_of_state s))\<rbrace>
     post_cap_deletion info
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding post_cap_deletion_def deleted_irq_handler_def
  apply (rule hoare_pre)
   apply (wp arch_post_cap_deletion_invs | wpc)+
  apply (clarsimp simp: post_cap_delete_pre_def split: cap.splits)
  done

lemmas (in Finalise_AI_1) obj_ref_ofI' = obj_ref_ofI[OF obj_ref_elemD]

crunches post_cap_deletion
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"

lemma empty_slot_deletes[wp]:
  "\<lbrace>\<top>\<rbrace> empty_slot sl opt \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) sl\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (wp set_cap_sets get_cap_wp opt_return_pres_lift|simp)+
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done

crunch caps_of_state[wp]: post_cap_deletion "\<lambda>s. P (caps_of_state s)"

lemma empty_slot_final_cap_at:
  "\<lbrace>(\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s) and K (p \<noteq> p')\<rbrace>
      empty_slot p' opt \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: empty_slot_def final_cap_at_eq cte_wp_at_conj cte_wp_at_caps_of_state)
  apply (wpsimp wp: opt_return_pres_lift get_cap_wp)
  apply (fastforce simp: )?
  done

lemma set_cap_revokable_update:
  "((),s') \<in> fst (set_cap c p s) \<Longrightarrow>
  ((),is_original_cap_update f s') \<in> fst (set_cap c p (is_original_cap_update f s))"
  apply (cases p)
  apply (clarsimp simp add: set_cap_def in_monad get_object_def)
  apply (case_tac y)
  apply (auto simp add: in_monad set_object_def get_object_def split: if_split_asm)
  done


lemma set_cap_cdt_update:
  "((),s') \<in> fst (set_cap c p s) \<Longrightarrow> ((),cdt_update f s') \<in> fst (set_cap c p (cdt_update f s))"
  apply (cases p)
  apply (clarsimp simp add: set_cap_def in_monad get_object_def)
  apply (case_tac y)
  apply (auto simp add: in_monad set_object_def get_object_def split: if_split_asm)
  done

lemma tcb_cap_cases_lt:
  "n < 5 \<Longrightarrow> tcb_cap_cases (nat_to_cref 3 n) \<noteq> None"
  unfolding tcb_cnode_index_def2[symmetric]
  by (simp add: tcb_cap_cases_def
         | erule less_handy_casesE)+

lemma cte_refs_CNode_Zombie_helper[simp]:
  "{xs. length xs = n \<and> unat (of_bl xs :: word32) < 2 ^ n}
     = {xs. length xs = n}"
  apply safe
  apply (rule unat_of_bl_length)
  done


lemma empty_slot_caps_of_state:
  "\<lbrace>\<lambda>s. P ((caps_of_state s) (slot \<mapsto> cap.NullCap))\<rbrace>
     empty_slot slot opt
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: empty_slot_def set_cdt_def)
  apply (wp get_cap_wp opt_return_pres_lift | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        fun_upd_def[symmetric]
                        fun_upd_idem)
  done

crunch caps_of_state[wp]: cancel_all_ipc, cancel_all_signals "\<lambda>s. P (caps_of_state s)"
  (wp: mapM_x_wp' crunch_wps)

crunch caps_of_state[wp]: reply_unlink_tcb, reply_unlink_sc "\<lambda>s. P (caps_of_state s)"
  (wp: maybeM_inv mapM_x_wp' crunch_wps)

crunch caps_of_state[wp]: tcb_release_remove "\<lambda>s. P (caps_of_state s)"

crunch caps_of_state[wp]:
  unbind_notification, sched_context_unbind_ntfn, sched_context_maybe_unbind_ntfn,
  unbind_maybe_notification, unbind_from_sc, sched_context_unbind_tcb,
  sched_context_unbind_yield_from, update_sk_obj_ref "\<lambda>s. P (caps_of_state s)"
  (wp: ARM.set_object_caps_of_state crunch_wps maybeM_inv
   ignore: set_object set_tcb_obj_ref tcb_release_remove)

lemma sched_context_unbind_all_tcbs_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> sched_context_unbind_all_tcbs scref \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_all_tcbs_def)

crunch caps_of_state[wp]: fast_finalise "\<lambda>s. P (caps_of_state s)"
  (wp: maybeM_inv mapM_x_wp thread_set_caps_of_state_trivial get_simple_ko_inv assert_inv hoare_drop_imps
   simp: tcb_cap_cases_def crunch_simps get_blocking_object_def)

lemma cap_delete_one_caps_of_state:
  "\<lbrace>\<lambda>s. cte_wp_at can_fast_finalise p s
           \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap))\<rbrace>
     cap_delete_one p
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def
                   is_final_cap_def)
  apply (rule hoare_seq_ext [OF _ get_cap_sp])
  apply (case_tac "can_fast_finalise cap")
   apply (wp empty_slot_caps_of_state get_cap_wp)
   apply (clarsimp simp: cte_wp_at_caps_of_state
                         fun_upd_def[symmetric]
                         fun_upd_idem)
  apply (simp add: fast_finalise_def2)
  apply wp
  apply (clarsimp simp: can_fast_finalise_def)
  done

lemma suspend_caps_of_state:
  "\<lbrace>\<lambda>s. (\<forall>p. cte_wp_at can_fast_finalise p s
           \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap)))
           \<and> P (caps_of_state s)\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp wp: cancel_ipc_caps_of_state hoare_drop_imps simp: suspend_def fun_upd_def[symmetric])+

lemma suspend_final_cap:
  "\<lbrace>\<lambda>s. is_final_cap' cap s \<and> \<not> can_fast_finalise cap
            \<and> cte_wp_at ((=) cap) sl s\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv s. is_final_cap' cap s\<rbrace>"
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state
              del: split_paired_Ex split_paired_All)
  apply (wp suspend_caps_of_state)
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
  apply (rule_tac x=sl in exI)
  apply (intro allI impI conjI)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (subgoal_tac "(aa, ba) = sl")
   apply clarsimp
  apply (frule_tac x="(aa, ba)" in spec)
  apply (drule_tac x=sl in spec)
  apply clarsimp
  done

lemma cap_delete_one_final_cap:
  "\<lbrace>\<lambda>s. cte_wp_at ((=) cap) slot s
        \<and> \<not> can_fast_finalise cap
        \<and> is_final_cap' cap s\<rbrace>
     cap_delete_one slot'
   \<lbrace>\<lambda>rv s. is_final_cap' cap s\<rbrace>"
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state
              del: split_paired_All split_paired_Ex)
  apply (wp cap_delete_one_caps_of_state)
  apply (clarsimp simp: cte_wp_at_caps_of_state
              simp del: split_paired_Ex split_paired_All)
  apply (subgoal_tac "slot = (a, b)")
   apply (rule_tac x=slot in exI)
   apply clarsimp
  apply (frule_tac x=slot in spec)
  apply (drule_tac x="(a, b)" in spec)
  apply clarsimp
  done

lemma deleting_irq_handler_final:
  "\<lbrace>is_final_cap' cap and cte_wp_at ((=) cap) slot
          and K (\<not> can_fast_finalise cap)\<rbrace>
      deleting_irq_handler irq
   \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  apply  (rule hoare_gen_asm)
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_final_cap[where slot=slot])
  apply simp
  done

crunch cte_wp_at[wp]: update_sk_obj_ref "cte_wp_at P p"

crunch cte_wp_at[wp]: unbind_notification "cte_wp_at P p"
  (wp: maybeM_inv ignore: set_tcb_obj_ref)


crunch cte_wp_at[wp]: sched_context_maybe_unbind_ntfn "cte_wp_at P p"
  (wp: maybeM_inv ignore: set_tcb_obj_ref update_sched_context)

lemma sched_context_update_consumed_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> sched_context_update_consumed p \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wpsimp simp: sched_context_update_consumed_def wp: thread_set_cte_wp_at_trivial
         ball_tcb_cap_casesI | simp)

crunch cte_wp_at[wp]: complete_yield_to "cte_wp_at P p"
  (wp: maybeM_inv hoare_drop_imp ignore: set_tcb_obj_ref get_sched_context)

lemma sched_context_unbind_tcb_cte_wp_at[wp]:
  "\<lbrace>cte_wp_at P p\<rbrace> sched_context_unbind_tcb param_a \<lbrace>\<lambda>_. cte_wp_at P p\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp
         ball_tcb_cap_casesI | simp)

lemma (in Finalise_AI_1) finalise_cap_cases:
  "\<lbrace>\<lambda>(s :: 'a state). final \<longrightarrow> is_final_cap' cap s
         \<and> cte_wp_at ((=) cap) slot s\<rbrace>
     finalise_cap cap final
   \<lbrace>\<lambda>rv (s :: 'a state). fst rv = cap.NullCap
            \<and> snd rv = (if final then cap_cleanup_opt cap else NullCap)
            \<and> (snd rv \<noteq> NullCap \<longrightarrow> is_final_cap' cap s)
     \<or>
       is_zombie (fst rv) \<and> is_final_cap' cap s
        \<and> is_final_cap' (fst rv) s
        \<and> snd rv = NullCap
        \<and> appropriate_cte_cap (fst rv) = appropriate_cte_cap cap
        \<and> cte_refs (fst rv) = cte_refs cap
        \<and> gen_obj_refs (fst rv) = gen_obj_refs cap
        \<and> obj_size (fst rv) = obj_size cap
        \<and> fst_cte_ptrs (fst rv) = fst_cte_ptrs cap
        \<and> vs_cap_ref cap = None\<rbrace>"
  apply (rule hoare_strengthen_post,
         rule finalise_cap_cases1)
  apply (erule disjEI)
   apply (auto simp: is_final_cap'_def)
  done


lemma is_final_cap'_objrefsE:
  "\<lbrakk> is_final_cap' cap s; gen_obj_refs cap = gen_obj_refs cap' \<rbrakk>
     \<Longrightarrow> is_final_cap' cap' s"
  by (simp add: is_final_cap'_def)

crunch typ_at[wp]: update_sk_obj_ref, get_sk_obj_ref "\<lambda>s. P (typ_at T p s)"

crunch typ_at[wp]: fast_finalise "\<lambda>s. P (typ_at T p s)"
  (wp: maybeM_inv crunch_wps simp: crunch_simps)

crunch typ_at[wp]: deleting_irq_handler "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp:crunch_simps unless_def assertE_def)

context Finalise_AI_1 begin
context notes if_cong[cong] begin
  crunch typ_at[wp]: finalise_cap "\<lambda>(s :: 'a state). P (typ_at T p s)"
  (wp: maybeM_inv get_simple_ko_wp simp: crunch_simps)
end
end

lemma valid_cap_Null_ext:
  "valid_cap cap.NullCap = \<top>"
  by (rule ext) simp

lemma unbind_notification_valid_cap[wp]:
  "\<lbrace>valid_cap cap\<rbrace> unbind_notification t \<lbrace>\<lambda>rv. valid_cap cap\<rbrace>"
  unfolding unbind_notification_def
  by (wp abs_typ_at_lifts hoare_drop_imps | wpc | clarsimp)+

lemma refs_in_ntfn_q_refs:
  "(x, ref) \<in> ntfn_q_refs_of ntfn \<Longrightarrow> ref = NTFNSignal"
  by (clarsimp simp: ntfn_q_refs_of_def split: ntfn.splits)

lemma ntfn_q_refs_no_TCBSignal:
  "(x, TCBSignal) \<notin> ntfn_q_refs_of ntfn"
  by (clarsimp simp: ntfn_q_refs_of_def split: ntfn.splits)

lemma tcb_st_refs_no_TCBBound:
  "(x, TCBBound) \<notin> tcb_st_refs_of ts"
  by (clarsimp simp: tcb_st_refs_of_def split: thread_state.splits)

lemma (in Finalise_AI_1) unbind_maybe_notification_invs:
  "\<lbrace>invs\<rbrace> unbind_maybe_notification ntfnptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  supply if_cong[cong]
  apply (simp add: unbind_maybe_notification_def invs_def valid_state_def valid_pspace_def
                   get_sk_obj_ref_def update_sk_obj_ref_def maybeM_def)
  apply (rule hoare_seq_ext [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wpsimp wp: valid_irq_node_typ set_simple_ko_valid_objs hoare_drop_imp get_simple_ko_wp valid_ioports_lift)
  apply simp
  apply safe
       defer 3 defer 6
       prefer 2 prefer 4
       apply (auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                   simp: live_def live_ntfn_def)[2]
     apply (auto elim!: obj_at_valid_objsE simp: is_ntfn valid_obj_def,
            auto simp: valid_ntfn_def valid_bound_obj_def split: ntfn.splits)[2]
   apply (frule obj_at_state_refs_ofD)
   apply (frule (1) sym_refs_ko_atD)
   apply (clarsimp simp: obj_at_def)
   apply (erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)
   apply (clarsimp split: if_split_asm split del: if_split)
     apply (case_tac ko;
       clarsimp simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def
                      ep_q_refs_of_def ntfn_q_refs_of_def
                  split: thread_state.splits if_splits endpoint.splits ntfn.splits)
    apply (clarsimp simp: get_refs_def2 ntfn_q_refs_of_def split: ntfn.splits)
   apply (case_tac ko;
       clarsimp simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def
                      ep_q_refs_of_def ntfn_q_refs_of_def
                split: thread_state.splits if_splits endpoint.splits ntfn.splits)

  apply (frule obj_at_state_refs_ofD)
  apply (frule (1) sym_refs_ko_atD)
  apply (clarsimp simp: obj_at_def get_refs_def2 ntfn_q_refs_of_def split: ntfn.splits)
  done

lemma schedule_tcb_invs[wp]: "\<lbrace>invs\<rbrace> schedule_tcb param_a \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: schedule_tcb_def)

lemma symreftype_neq:
    "(x,tp) \<in> state_refs_of s ptr \<Longrightarrow> (x, symreftype tp) \<notin> state_refs_of s ptr"
  apply (drule state_refs_of_elemD)
  apply (clarsimp simp: obj_at_def)
  by (case_tac ko; fastforce simp: state_refs_of_def get_refs_def2
       tcb_st_refs_of_def ep_q_refs_of_def ntfn_q_refs_of_def
      split: ntfn.splits endpoint.splits thread_state.splits if_split_asm option.splits
      dest!: symreftype_inverse')
(*
lemma reply_unlink_tcb_invs:
  "\<lbrace>invs and (\<lambda>s. reply_tcb_reply_at (\<lambda>t. \<exists>tp. t = (Some tp)
          \<and> st_tcb_at (\<lambda>st. st = BlockedOnReply (Some rptr) \<or>
                            (st = BlockedOnReceive ep (Some rptr) \<and> ko_at (Endpoint IdleEP) ep s)) tp s) rptr s)\<rbrace>
      reply_unlink_tcb rptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: reply_unlink_tcb_def)
  apply (rule hoare_seq_ext[OF _ get_simple_ko_sp])
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def
      wp: sts_only_idle valid_irq_node_typ gts_inv hoare_drop_imp split_del: if_split)
  apply (frule ko_at_state_refs_ofD)
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_reply_def)
  apply (rule conjI, clarsimp)
   apply (drule (1) if_live_then_nonz_capD2)
    apply (clarsimp simp: live_def live_reply_def)
   apply simp
  apply (rule conjI)
   apply (erule delta_sym_refs)
    apply (clarsimp split: if_split_asm)
   apply (clarsimp split: if_split_asm split del: if_split simp: get_refs_def2)
       apply (erule (1) obj_at_valid_objsE)
       apply (clarsimp simp: valid_obj_def valid_reply_def valid_bound_obj_def tcb_at_def dest!: get_tcb_SomeD)
      apply (clarsimp dest!: symreftype_neq)
     apply (erule (1) obj_at_valid_objsE)
     apply (clarsimp simp: valid_obj_def valid_reply_def valid_bound_obj_def is_tcb is_sc_obj_def obj_at_def)
    apply (erule (1) obj_at_valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_reply_def valid_bound_obj_def is_tcb is_sc_obj_def obj_at_def)
    apply (clarsimp simp: state_refs_of_def obj_at_def get_refs_def2 tcb_st_refs_of_def reply_tcb_reply_at_def pred_tcb_at_def)
    apply (case_tac "tcb_state tcb"; simp)
   apply (erule (1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_reply_def valid_bound_obj_def is_tcb is_sc_obj_def obj_at_def
      split: option.splits)
   apply (fastforce simp: state_refs_of_def obj_at_def get_refs_def2 reply_tcb_reply_at_def pred_tcb_at_def)
  apply (erule (1) obj_at_valid_objsE)
  apply (simp add: valid_obj_def valid_reply_def valid_bound_obj_def obj_at_def is_tcb
      pred_tcb_at_def reply_tcb_reply_at_def split: kernel_object.splits)
  apply (case_tac "tcb_state tcb"; simp)
   apply (drule_tac p=y in if_live_then_nonz_capD2, simp)
    apply (simp add: live_def pred_tcb_at_def obj_at_def)
   apply (clarsimp dest!: idle_no_ex_cap)
  apply (drule_tac p=y in if_live_then_nonz_capD2, simp)
   apply (simp add: live_def pred_tcb_at_def obj_at_def)
  apply (clarsimp dest!: idle_no_ex_cap)
  done*)

lemma reply_tcb_state_refs:
  "\<lbrakk>reply_tcb reply = Some t; valid_objs s; sym_refs (state_refs_of s);
    kheap s rptr = Some (Reply reply)\<rbrakk>
  \<Longrightarrow> \<exists>tcb. kheap s t = Some (TCB tcb) \<and>
     st_tcb_at (\<lambda>st. st = BlockedOnReply rptr
                    \<or> (\<exists>ep pl. st = BlockedOnReceive ep (Some rptr) pl)) t s"
  apply (erule (1) valid_objsE)
  apply (drule sym_refs_ko_atD[rotated])
   apply (simp add: obj_at_def)
  apply (clarsimp simp: get_refs_def2 obj_at_def valid_obj_def valid_reply_def
                        valid_bound_obj_def pred_tcb_at_def is_tcb tcb_st_refs_of_def
                  split: thread_state.splits if_splits)
  done

lemma SCNtfn_in_state_refsD:
  "\<lbrakk>(y, SCNtfn) \<in> state_refs_of s x\<rbrakk>
    \<Longrightarrow> obj_at (\<lambda>ko. \<exists>np n. ko = SchedContext np n \<and> sc_ntfn np = Some y) x s"
  by (clarsimp simp: state_refs_of_def refs_of_rev obj_at_def split: option.splits)

lemma ntfn_sc_sym_refsD:
  "\<lbrakk>kheap s ptr = Some (Notification ntfn); ntfn_sc ntfn = Some sc;
    valid_objs s; sym_refs (state_refs_of s)\<rbrakk>
    \<Longrightarrow> obj_at (\<lambda>ko. \<exists>np n. ko = SchedContext np n \<and> sc_ntfn np = Some ptr) sc s"
  apply (rule valid_objsE, assumption+)
  apply (clarsimp simp: valid_obj_def valid_ntfn_def obj_at_def dest!: is_sc_objD)
  apply (rule_tac x=sc in valid_objsE, assumption+)
  apply (clarsimp simp: valid_obj_def valid_sched_context_def obj_at_def is_ntfn)
  apply (frule_tac p=sc in sym_refs_ko_atD[simplified obj_at_def, simplified], assumption)
  apply (frule_tac p=ptr in sym_refs_ko_atD[simplified obj_at_def, simplified], assumption)
  apply (clarsimp simp: split_def get_refs_def2)
  done

lemma not_in_own_refs[simp]:
  "valid_objs s \<Longrightarrow> (x, ref) \<notin> state_refs_of s x"
  apply (clarsimp simp: state_refs_of_def split: option.splits)
  apply (erule (1) valid_objsE)
  apply (rename_tac ko, case_tac ko; clarsimp simp: valid_obj_def)
      (* TCB *)
      apply (fastforce simp: tcb_st_refs_of_def valid_tcb_def get_refs_def2 obj_at_def is_ntfn
                             valid_tcb_state_def is_ep is_reply
                      dest!: is_sc_objD
                      split: thread_state.splits option.splits)
     (* EP *)
     apply (fastforce simp: ep_q_refs_of_def valid_ep_def get_refs_def2 obj_at_def is_tcb
                     split: endpoint.splits)
    (* NTFN *)
    apply (fastforce simp: ntfn_q_refs_of_def valid_ntfn_def get_refs_def2 obj_at_def is_tcb
                    dest!: is_sc_objD
                    split: ntfn.splits)
   (* SC *)
   apply (fastforce simp: valid_sched_context_def get_refs_def2 obj_at_def is_ntfn is_tcb is_reply
                          list_all_iff)
  (* Reply *)
  apply (fastforce simp: get_refs_def2 valid_reply_def obj_at_def is_tcb
                  dest!: is_sc_objD)
  done

lemma sched_context_maybe_unbind_ntfn_invs[wp]:
  "\<lbrace>invs\<rbrace> sched_context_maybe_unbind_ntfn nptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: invs_def valid_state_def valid_pspace_def update_sk_obj_ref_def
                      sched_context_maybe_unbind_ntfn_def maybeM_def get_sk_obj_ref_def
                  wp: valid_irq_node_typ set_simple_ko_valid_objs get_simple_ko_wp
                      get_sched_context_wp valid_ioports_lift update_sched_context_valid_idle)
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_objsE, assumption+, clarsimp simp: valid_obj_def)
  apply (clarsimp simp: valid_ntfn_def obj_at_def dest!: is_sc_objD)
  apply (rule_tac x=x in valid_objsE, assumption+, clarsimp simp: valid_obj_def valid_sched_context_def)
  apply (rule conjI, clarsimp simp: valid_obj_def valid_ntfn_def split: ntfn.splits)
  apply (rule conjI, clarsimp, erule (1) if_live_then_nonz_capD2, clarsimp simp: live_def live_ntfn_def)
  apply (rule conjI)
   apply (rule delta_sym_refs, assumption)
    apply (auto dest: refs_in_ntfn_q_refs refs_in_get_refs
                simp: state_refs_of_def valid_ntfn_def obj_at_def is_sc_obj_def
               split: if_split_asm option.split_asm ntfn.splits kernel_object.split_asm)[1]
   apply (clarsimp split: if_splits)
    apply ((solves \<open>clarsimp simp: state_refs_of_def\<close>
            | fastforce simp: obj_at_def
                       dest!: refs_in_get_refs SCNtfn_in_state_refsD ntfn_sc_sym_refsD)+)[2]
  apply (clarsimp simp: sym_refs_def)
  apply (erule_tac x = nptr in allE)
  apply (auto simp: state_refs_of_def valid_idle_def obj_at_def)
  done

lemma (in Finalise_AI_1) sched_context_unbind_yield_from_invs:
  "\<lbrace>invs \<comment> \<open>and (\<lambda>s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = (Some tp) \<and> st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) scptr s)\<close>\<rbrace>
      sched_context_unbind_yield_from scptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_yield_from_def maybeM_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  by (wpsimp simp: sched_context_unbind_yield_from_def wp: complete_yield_to_invs)

lemma list_all_remove1: "list_all P ls \<Longrightarrow> list_all P (remove1 x ls)"
  apply (induction ls arbitrary: x, simp)
  apply (case_tac ls, simp)
  by auto

declare reply_unlink_sc_invs[wp]

lemma  sched_context_clear_ntfn_sc_yf_helper[wp]:
  "\<lbrace>\<lambda>s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>
      sched_context_unbind_ntfn scptr \<lbrace>\<lambda>rv s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_ntfn_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp wp: hoare_drop_imp get_object_wp get_simple_ko_wp
              simp: update_sk_obj_ref_def set_simple_ko_def
                    update_sched_context_def set_object_def)
  apply (clarsimp simp: sc_yf_sc_at_def obj_at_def pred_tcb_at_def split: if_split_asm split del: if_split)
  by (case_tac "p=scptr"; fastforce)

lemma  tcb_sched_context_sc_yf_helper[wp]:
  "\<lbrace>\<lambda>s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update tptr new
   \<lbrace>\<lambda>rv s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def)
  apply (wpsimp wp: hoare_drop_imp get_object_wp get_simple_ko_wp
              simp: update_sk_obj_ref_def set_simple_ko_def update_sched_context_def set_object_def)
  apply (clarsimp simp: sc_yf_sc_at_def obj_at_def pred_tcb_at_def dest!: get_tcb_SomeD
                  split: if_split_asm split del: if_split)
  by (case_tac "p=tptr"; clarsimp simp: get_tcb_def)

lemma  sc_tcb_update_sc_yf_helper[wp]:
  "\<lbrace>\<lambda>s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>
   set_sc_obj_ref sc_tcb_update tptr new
   \<lbrace>\<lambda>rv s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>"
  apply (simp add: update_sched_context_def)
  apply (wpsimp wp: hoare_drop_imp get_object_wp get_simple_ko_wp set_object_wp
              simp: update_sk_obj_ref_def set_simple_ko_def)
  apply (clarsimp simp: sc_yf_sc_at_def obj_at_def pred_tcb_at_def dest!: get_tcb_SomeD
                  split: if_split_asm split del: if_split)
  by (case_tac "p=tptr"; clarsimp simp: get_tcb_def)

lemma sc_yf_sc_at_more_update[iff]:
  "sc_yf_sc_at P p (trans_state f s) = sc_yf_sc_at P p s"
  by (simp add: sc_yf_sc_at_def)

lemma sc_yf_sc_at_release_queue_update[simp]:
  "sc_yf_sc_at P p (release_queue_update f s) = sc_yf_sc_at P p s"
  by (simp add: sc_yf_sc_at_def)

lemma sc_yf_sc_at_ready_queues_update[simp]:
  "sc_yf_sc_at P p (ready_queues_update f s) = sc_yf_sc_at P p s"
  by (simp add: sc_yf_sc_at_def)

lemma sc_yf_sc_at_scheduler_action_update[simp]:
  "sc_yf_sc_at P p (scheduler_action_update f s) = sc_yf_sc_at P p s"
  by (simp add: sc_yf_sc_at_def)

lemma  sched_context_unbind_tcb_sc_yf_helper[wp]:
  "\<lbrace>\<lambda>s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>
      sched_context_unbind_tcb scptr \<lbrace>\<lambda>rv s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_tcb_def get_sc_obj_ref_def tcb_release_remove_def
                        tcb_sched_action_def set_tcb_queue_def get_tcb_queue_def
                        reschedule_required_def set_scheduler_action_def is_schedulable_def
                  cong: scheduler_action.case_cong)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  by (wpsimp wp: thread_get_wp')

lemma sched_context_unbind_all_tcbs_sc_yf_helper[wp]:
  "\<lbrace>\<lambda>s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>
      sched_context_unbind_all_tcbs scptr \<lbrace>\<lambda>rv s. sc_yf_sc_at (\<lambda>t. \<exists>tp. t = Some tp \<and>
                            st_tcb_at (\<lambda>st. tcb_st_refs_of st = {}) tp s) p s\<rbrace>"
  apply (clarsimp simp: sched_context_unbind_all_tcbs_def get_sc_obj_ref_def)
  apply (rule hoare_seq_ext[OF _ get_sched_context_sp])
  apply (wpsimp wp: hoare_drop_imp get_object_wp get_simple_ko_wp)
  done

lemma set_sc_rm_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
     set_sc_obj_ref sc_refill_max_update t tcb
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp simp: update_sched_context_def wp: get_object_wp)
  apply (clarsimp simp: if_live_then_nonz_cap_def, drule_tac x=t in spec)
  apply (fastforce simp: obj_at_def live_def live_sc_def)
  done

lemma set_sc_rm_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
   set_sc_obj_ref sc_refill_max_update t tcb
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_object_def update_sched_context_def
                wp: get_object_wp)
  by (fastforce elim!: rsubst[where P=P]
                 simp: state_refs_of_def obj_at_def Un_def split_def  Collect_eq get_refs_def2
                split: option.splits if_splits)

lemma sc_refill_max_update_cur_sc_tcb[wp]:
  "set_sc_obj_ref sc_refill_max_update b c \<lbrace>cur_sc_tcb\<rbrace>"
  unfolding cur_sc_tcb_def
  apply (wpsimp wp: update_sched_context_wp)
  apply (clarsimp simp: sc_at_pred_n_def obj_at_def)
  done

lemma reset_sc_refill_max_invs[wp]:
  "\<lbrace>invs and K (p \<noteq> idle_sc_ptr)\<rbrace> set_sc_obj_ref sc_refill_max_update p 0 \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp wp: set_sc_obj_ref_invs_no_change)

lemma (in Finalise_AI_1) fast_finalise_invs:
  "\<lbrace>invs and cte_wp_at ((=) cap) slot\<rbrace> fast_finalise cap final \<lbrace>\<lambda>_. invs\<rbrace>"
  by (cases cap;
      wpsimp wp: cancel_all_ipc_invs cancel_all_signals_invs
                   unbind_maybe_notification_invs sched_context_maybe_unbind_ntfn_invs
                   sched_context_unbind_yield_from_invs get_simple_ko_wp
                   reply_remove_invs gts_wp;
      fastforce dest: no_cap_to_idle_sc_ptr)

lemma cnode_at_unlive[elim!]:
  "s \<turnstile> cap.CNodeCap ptr bits gd \<Longrightarrow> obj_at (\<lambda>ko. \<not> live ko) ptr s"
  by (clarsimp simp: live_def valid_cap_def is_cap_table
              elim!: obj_at_weakenE)


lemma set_thread_state_final_cap[wp]:
  "\<lbrace>is_final_cap' cap\<rbrace> set_thread_state st t \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  by (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state, wp)


lemma tcb_cap_valid_imp':
  "((\<forall>(get, set, restr)\<in>ran tcb_cap_cases.
          \<forall>ptr st. restr ptr st cap \<longrightarrow> restr ptr st newcap)
            \<and> (\<forall>ptr. valid_ipc_buffer_cap cap ptr
                       \<longrightarrow> valid_ipc_buffer_cap newcap ptr))
     \<longrightarrow> (tcb_cap_valid cap sl s \<longrightarrow> tcb_cap_valid newcap sl s)"
  by (fastforce simp: tcb_cap_valid_def elim!: pred_tcb_weakenE
              split: option.split)


lemma tcb_cap_valid_imp_NullCap:
  "(tcb_cap_valid cap sl s \<longrightarrow> tcb_cap_valid NullCap sl s)"
  apply (strengthen tcb_cap_valid_imp')
  apply (clarsimp simp: ran_tcb_cap_cases valid_ipc_buffer_cap_def
                 split: Structures_A.thread_state.split_asm)
  done

lemma pred_tcb_at_def2:
  "pred_tcb_at proj P t \<equiv> \<lambda>s. \<exists>tcb. ko_at (TCB tcb) t s \<and> P (proj (tcb_to_itcb tcb))"
  by (rule eq_reflection, rule ext) (fastforce simp: pred_tcb_at_def obj_at_def)

(* sseefried: 'st_tcb_at_def2' only exists to make existing proofs go through. Can use 'pred_tcb_at_def2' instead *)
lemmas st_tcb_at_def2 = pred_tcb_at_def2[where proj=itcb_state,simplified]

lemma imp_and_strg: "Q \<and> C \<longrightarrow> (A \<longrightarrow> Q \<and> C) \<and> C" by blast
(* FIXME: move *)
lemma cases_conj_strg: "A \<and> B \<longrightarrow> (P \<and> A) \<or> (\<not> P \<and> B)"
  by simp
(* FIXME: move *)
lemma and_not_not_or_imp: "(~ A & ~ B | C) = ((A | B) \<longrightarrow> C)" by blast

lemmas tcb_cap_valid_imp = mp [OF mp [OF tcb_cap_valid_imp'], rotated]

crunch irq_node[wp]: cancel_all_ipc "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

lemma sched_context_unbind_tcb_irq_node[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
     sched_context_unbind_tcb param_a \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def wp: get_sched_context_wp)

crunch irq_node[wp]: cancel_all_signals, fast_finalise, unbind_from_sc,reply_unlink_sc
   "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps maybeM_inv simp: crunch_simps unless_def)

crunch irq_node[wp]: cap_delete_one "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps maybeM_inv simp: crunch_simps unless_def)

lemma deleting_irq_handler_empty:
  "\<lbrace>\<top>\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv s. cte_wp_at ((=) cap.NullCap) (interrupt_irq_node s irq, []) s\<rbrace>"
  apply (simp add: deleting_irq_handler_def cte_wp_at_caps_of_state
                   get_irq_slot_def)
  apply (wp hoare_use_eq_irq_node [OF cap_delete_one_irq_node cap_delete_one_caps_of_state])
  apply clarsimp
  done

lemmas gen_obj_refs_empty2 = trans [OF eq_commute gen_obj_refs_empty]

lemma cnode_zombie_thread_appropriate[simp]:
  "appropriate_cte_cap cp (cap.CNodeCap a b c)"
  "appropriate_cte_cap cp (cap.ThreadCap f)"
  "appropriate_cte_cap cp (cap.Zombie h i j)"
  by (simp add: appropriate_cte_cap_def split: cap.splits)+

lemma unbind_notification_not_bound:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = Some tcbptr) ntfnptr s
      \<and> valid_objs s \<and> sym_refs (state_refs_of s)\<rbrace>
     unbind_notification tcbptr
   \<lbrace>\<lambda>_. obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None) ntfnptr\<rbrace>"
  apply (simp add: unbind_notification_def maybeM_def)
  apply (rule hoare_pre)
   apply (rule hoare_seq_ext[OF _ gbn_wp[where P="\<lambda>ptr _. ptr = (Some ntfnptr)"]])
   apply (rule hoare_gen_asm[where P'=\<top>, simplified])
   apply (wp sbn_obj_at_impossible simple_obj_set_prop_at | wpc | simp add: update_sk_obj_ref_def)+
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_objsE, simp+)
  apply (drule_tac P="(=) (Some ntfnptr)" in ntfn_bound_tcb_at, simp+)
  apply (auto simp: obj_at_def valid_obj_def is_tcb valid_ntfn_def pred_tcb_at_def)
  done

 lemma unbind_maybe_notification_not_bound:
   "\<lbrace>\<lambda>s. ntfn_at ntfnptr s\<rbrace>
      unbind_maybe_notification ntfnptr
    \<lbrace>\<lambda>_. obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None) ntfnptr\<rbrace>"
  apply (simp add: unbind_maybe_notification_def maybeM_def get_sk_obj_ref_def)
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp sbn_obj_at_impossible simple_obj_set_prop_at | wpc | simp add: update_sk_obj_ref_def)+
  apply (clarsimp simp: obj_at_def)
  done

lemma unbind_notification_bound_tcb_at[wp]:
  "\<lbrace>\<top>\<rbrace> unbind_notification tcbptr \<lbrace>\<lambda>_. bound_tcb_at ((=) None) tcbptr\<rbrace>"
  apply (simp add: unbind_notification_def maybeM_def)
  apply (wpsimp wp: sbn_bound_tcb_at')
   apply (rule gbn_bound_tcb[THEN hoare_strengthen_post])
   apply clarsimp
  apply assumption
  done

crunch valid_mdb[wp]: unbind_notification "valid_mdb"
  (wp: maybeM_inv ignore: set_tcb_obj_ref)
crunch tcb_at[wp]: unbind_notification "tcb_at t"
  (wp: maybeM_inv)

lemma unbind_notification_no_cap_to_obj_ref[wp]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     unbind_notification tcbptr
   \<lbrace>\<lambda>_. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state)
  apply (wp unbind_notification_caps_of_state)
  done


lemma empty_slot_cte_wp_elsewhere:
  "\<lbrace>(\<lambda>s. cte_wp_at P p s) and K (p \<noteq> p')\<rbrace> empty_slot p' opt \<lbrace>\<lambda>rv s. cte_wp_at P p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: empty_slot_def cte_wp_at_caps_of_state)
  apply (wp opt_return_pres_lift | simp split del: if_split)+
  done


lemma fast_finalise_lift:
  assumes ep:"\<And>r. cancel_all_ipc r \<lbrace>P\<rbrace>"
  and ntfn:"\<And>r. cancel_all_signals r \<lbrace>P\<rbrace>"
  and reply:"\<And>r. cancel_ipc r \<lbrace>P\<rbrace>"
  and reply2: "\<And>sc re. reply_unlink_sc sc re \<lbrace>P\<rbrace>"
  and unbind:"\<And>r. unbind_notification r \<lbrace>P\<rbrace>"
  and unbind2: "\<And>r. unbind_maybe_notification r \<lbrace>P\<rbrace>"
  and unbind3:"\<And>r. sched_context_maybe_unbind_ntfn r \<lbrace>P\<rbrace>"
  and unbind4:"\<And>r. sched_context_unbind_all_tcbs r \<lbrace>P\<rbrace>"
  and unbind5:"\<And>t r. reply_remove t r \<lbrace>P\<rbrace>"
  and unbind6:"\<And>r. sched_context_unbind_ntfn r \<lbrace>P\<rbrace>"
  and unbind7:"\<And>r. sched_context_unbind_yield_from r \<lbrace>P\<rbrace>"
  and unbind8:"\<And>r. sched_context_unbind_reply r \<lbrace>P\<rbrace>"
  and unbind9:"\<And>sc. set_sc_obj_ref sc_refill_max_update sc 0 \<lbrace>P\<rbrace>"
  shows "fast_finalise cap final \<lbrace>P\<rbrace>"
  by (case_tac cap
      ; wpsimp wp: ep ntfn reply reply2 unbind unbind2 unbind3 unbind4 unbind5
                   unbind6 unbind7 unbind8 unbind9 hoare_drop_imps get_simple_ko_wp gts_wp)

lemma reply_unlink_sc_cte_wp_at:
  shows "\<lbrace>cte_wp_at P p\<rbrace> reply_unlink_sc ptr ptr' \<lbrace>\<lambda>rv s. cte_wp_at P p s\<rbrace>"
  unfolding reply_unlink_sc_def
  by (wpsimp wp: get_simple_ko_wp hoare_drop_imps)

crunch cte_wp_at[wp]: reply_unlink_tcb,unbind_from_sc "cte_wp_at P p"
  (wp: maybeM_inv hoare_drop_imp ignore: get_simple_ko)

lemma set_mrs_valid_objs[wp]:
  "set_mrs t a msgs \<lbrace>valid_objs\<rbrace>"
  supply if_split[split del]
  apply (cases a)
   apply (simp add: set_mrs_redux)
   apply (wpsimp wp: thread_set_valid_objs_triv)
           apply (fastforce simp: tcb_cap_cases_def)
          apply (simp add: valid_arch_arch_tcb_set_registers)+
  apply (simp add: set_mrs_redux zipWithM_x_mapM split_def
                   store_word_offs_def)
  apply (wpsimp wp: mapM_wp' thread_set_valid_objs_triv)
          apply (auto simp: tcb_cap_cases_def valid_arch_arch_tcb_set_registers)
  done

crunch valid_objs[wp]: set_consumed valid_objs
  (wp: crunch_wps simp: crunch_simps ignore: update_sched_context)

lemma complete_yield_to_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> complete_yield_to t \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: complete_yield_to_def | wp (once) hoare_drop_imps)+

lemma sched_context_unbind_tcb_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> sched_context_unbind_tcb t \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: sched_context_unbind_tcb_def | wp (once) hoare_drop_imps)+

lemma unbind_from_sc_valid_objs[wp]:
  "\<lbrace>valid_objs\<rbrace> unbind_from_sc t \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  by (wpsimp simp: unbind_from_sc_def wp: maybeM_inv)

lemma unbind_from_sc_invs[wp]:
  "\<lbrace>invs and K (t \<noteq> idle_thread_ptr)\<rbrace> unbind_from_sc t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: unbind_from_sc_def
                  wp: complete_yield_to_invs)
    apply (wpsimp wp: hoare_vcg_all_lift hoare_drop_imp)
   apply (wpsimp simp: get_tcb_obj_ref_def thread_get_def)
  apply clarsimp
  apply (fastforce dest!: get_tcb_SomeD thread_not_idle_implies_sc_not_idle)
  done

lemma cap_delete_one_cte_wp_at_preserved:
  assumes x: "\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap"
  shows "\<lbrace>cte_wp_at P p\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp cap_delete_one_caps_of_state)
  apply (clarsimp simp: cte_wp_at_caps_of_state x)
  done

interpretation delete_one_pre
  by (unfold_locales; wpsimp wp: cap_delete_one_cte_wp_at_preserved)

crunches sched_context_unbind_all_tcbs, sched_context_unbind_yield_from
  for cte_wp_at[wp]: "cte_wp_at P p"

crunch cte_wp_at[wp]: cancel_ipc "cte_wp_at P p"
  (wp: thread_set_cte_wp_at_trivial ball_tcb_cap_casesI)

crunch cte_wp_at[wp]: fast_finalise "cte_wp_at P p"
  (wp: crunch_wps ignore: set_tcb_obj_ref simp: crunch_simps)

lemma (in Finalise_AI_1) finalise_cap_equal_cap[wp]:
  "\<lbrace>cte_wp_at ((=) cap) sl\<rbrace>
     finalise_cap cap fin
   \<lbrace>\<lambda>rv. cte_wp_at ((=) cap) sl :: 'a state \<Rightarrow> bool\<rbrace>"
  supply if_cong[cong]
  apply (cases cap, simp_all split del: if_split)
    apply (wp suspend_cte_wp_at_preserved gts_wp get_simple_ko_wp
                 deleting_irq_handler_cte_preserved prepare_thread_delete_cte_wp_at
                 hoare_drop_imp thread_set_cte_wp_at_trivial reply_unlink_sc_cte_wp_at
               | clarsimp simp: can_fast_finalise_def unbind_maybe_notification_def
                                unbind_notification_def
                                tcb_cap_cases_def | wpc)+
  done

locale Finalise_AI_2 = Finalise_AI_1 a b
  for a :: "('a :: state_ext) itself"
  and b :: "('b :: state_ext) itself" +
  assumes cap_delete_one_invs[wp]:
    "\<And> ptr. \<lbrace>invs\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv. invs :: 'a state \<Rightarrow> bool\<rbrace>"

lemma cap_delete_one_deletes[wp]:
  "\<lbrace>\<top>\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) ptr\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def)
  apply (wp get_cap_wp)
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done


context Finalise_AI_2 begin

sublocale delete_one_abs a' for a' :: "('a :: state_ext) itself"
  by (unfold_locales; wp cap_delete_one_deletes cap_delete_one_caps_of_state)

end

crunch (in Finalise_AI_2) invs[wp]: deleting_irq_handler "invs :: 'a state \<Rightarrow> bool"
  (wp: maybeM_inv)

crunch tcb_at[wp]: unbind_notification "tcb_at t"


locale Finalise_AI_3 = Finalise_AI_2 a b
  for a :: "('a :: state_ext) itself"
  and b :: "('b :: state_ext) itself" +
  fixes replaceable_or_arch_update :: "'a state \<Rightarrow> machine_word \<times> bool list \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool"
  fixes c :: "'c itself"
  assumes finalise_cap_invs:
    "\<And> cap slot x.
    \<lbrace>invs and cte_wp_at ((=) cap) slot\<rbrace>
      finalise_cap cap x
    \<lbrace>\<lambda>rv. invs :: 'a state \<Rightarrow> bool\<rbrace>"
  assumes finalise_cap_irq_node:
    "\<And>P a b.
    \<lbrace>\<lambda>(s :: 'a state). P (interrupt_irq_node s)\<rbrace>
      finalise_cap a b
    \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  assumes arch_finalise_cte_irq_node[wp]:
    "\<And>P P' p a b.
    \<lbrace>\<lambda>(s :: 'a state). P (interrupt_irq_node s)
           (cte_wp_at (P' (interrupt_irq_node s)) (p (interrupt_irq_node s)) s)\<rbrace>
       arch_finalise_cap a b
    \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)
              (cte_wp_at (P' (interrupt_irq_node s)) (p (interrupt_irq_node s)) s)\<rbrace>"
  assumes irq_node_global_refs:
    "\<And>(s :: 'a state) irq. interrupt_irq_node s irq \<in> global_refs s"
  assumes get_irq_slot_fast_finalisable[wp]:
    "\<And> irq. \<lbrace>invs :: 'a state \<Rightarrow> bool\<rbrace> get_irq_slot irq \<lbrace>cte_wp_at can_fast_finalise\<rbrace>"
  assumes replaceable_or_arch_update_same:
    "\<And> s slot cap. replaceable_or_arch_update s slot cap cap"
  assumes replace_cap_invs_arch_update:
    "\<And> cap p. \<lbrace>\<lambda>s. cte_wp_at (replaceable_or_arch_update s p cap) p s
          \<and> invs s
          \<and> cap \<noteq> cap.NullCap
          \<and> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s
          \<and> s \<turnstile> cap\<rbrace>
       set_cap cap p
     \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  assumes dmo_tcb_cap_valid:
    "\<And>P cap ptr mop.
      \<lbrace>\<lambda>(s :: 'a state). P (tcb_cap_valid cap ptr s)\<rbrace>
        do_machine_op (mop :: 'c machine_monad)
      \<lbrace>\<lambda>_ s. P (tcb_cap_valid cap ptr s)\<rbrace>"
  assumes dmo_replaceable_or_arch_update [wp]:
    "\<And> slot cap cap' mo.
      \<lbrace>\<lambda>s. replaceable_or_arch_update s slot cap cap'\<rbrace>
        do_machine_op (mo :: 'c machine_monad)
      \<lbrace>\<lambda>r s. replaceable_or_arch_update s slot cap cap'\<rbrace>"
  assumes prepare_thread_delete_irq_node[wp]:
  "\<And>t. \<lbrace>\<lambda>(s :: 'a state). P (interrupt_irq_node s)\<rbrace>
     prepare_thread_delete t
       \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"

crunches suspend, unbind_maybe_notification, unbind_notification
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps select_wp maybeM_inv simp: crunch_simps)

crunch irq_node[wp]: deleting_irq_handler "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps select_wp simp: crunch_simps)

lemmas cancel_all_ipc_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF cancel_all_ipc_irq_node cancel_all_ipc_cte_wp_at]

lemmas cancel_all_signals_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF cancel_all_signals_irq_node cancel_all_signals_cte_wp_at]

lemmas suspend_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF suspend_irq_node suspend_cte_wp_at_preserved]

lemmas unbind_notification_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF unbind_notification_irq_node unbind_notification_cte_wp_at]

lemmas unbind_from_sc_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF unbind_from_sc_irq_node unbind_from_sc_cte_wp_at]

lemmas unbind_maybe_notification_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF unbind_maybe_notification_irq_node unbind_maybe_notification_cte_wp_at]

lemmas sched_context_maybe_unbind_ntfn_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF sched_context_maybe_unbind_ntfn_irq_node sched_context_maybe_unbind_ntfn_cte_wp_at]

lemmas sched_context_unbind_ntfn_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF sched_context_unbind_ntfn_irq_node sched_context_unbind_ntfn_cte_wp_at]

lemmas sched_context_unbind_yield_from_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF sched_context_unbind_yield_from_irq_node
                                sched_context_unbind_yield_from_cte_wp_at]

lemmas sched_context_unbind_reply_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF sched_context_unbind_reply_irq_node
                                sched_context_unbind_reply_cte_wp_at]

lemmas sched_context_unbind_all_tcbs_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF sched_context_unbind_all_tcbs_irq_node
                                sched_context_unbind_all_tcbs_cte_wp_at]

lemmas (in Finalise_AI_3) deleting_irq_handler_cte_preserved_irqn
  = hoare_use_eq_irq_node [OF deleting_irq_handler_irq_node
                              deleting_irq_handler_cte_preserved]

lemmas (in Finalise_AI_3) cancel_ipc_cte_preserved_irqn
  = hoare_use_eq_irq_node [OF cancel_ipc_irq_node
                              cancel_ipc_cte_wp_at_preserved]

lemmas (in Finalise_AI_3) reply_unlink_sc_cte_preserved_irqn
  = hoare_use_eq_irq_node [OF reply_unlink_sc_irq_node
                              reply_unlink_sc_cte_wp_at]

lemmas (in Finalise_AI_3) reply_remove_cte_preserved_irqn
  = hoare_use_eq_irq_node [OF reply_remove_irq_node
                              reply_remove_cte_wp_at]

lemmas (in Finalise_AI_3) prepare_thread_delete_cte_preserved_irqn
  = hoare_use_eq_irq_node [OF prepare_thread_delete_irq_node
                              prepare_thread_delete_cte_wp_at]

lemma unbind_notification_cte_cap_to[wp]:
"\<lbrace>ex_cte_cap_wp_to P sl\<rbrace> unbind_notification t \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P sl\<rbrace>"
  by (wp ex_cte_cap_to_pres)

lemma unbind_maybe_notification_cte_cap_to[wp]:
"\<lbrace>ex_cte_cap_wp_to P sl\<rbrace> unbind_maybe_notification t \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P sl\<rbrace>"
  by (wp ex_cte_cap_to_pres)

lemma (in Finalise_AI_3) finalise_cap_cte_cap_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P sl :: 'a state \<Rightarrow> bool\<rbrace> finalise_cap cap fin \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P sl\<rbrace>"
  supply if_cong[cong]
  apply (cases cap, simp_all add: ex_cte_cap_wp_to_def split del: if_split)
       apply (wp hoare_vcg_ex_lift hoare_drop_imps gts_wp hoare_vcg_all_lift
                 prepare_thread_delete_cte_preserved_irqn
                 deleting_irq_handler_cte_preserved_irqn
                 reply_unlink_sc_cte_preserved_irqn
                 cancel_ipc_cte_preserved_irqn
                 reply_remove_cte_preserved_irqn
                 | simp
                 | clarsimp simp: can_fast_finalise_def
                           split: cap.split_asm | wpc | wps)+
  done

lemma (in Finalise_AI_3) finalise_cap_zombie_cap[wp]:
  "\<lbrace>cte_wp_at (\<lambda>cp. is_zombie cp \<and> P cp) sl :: 'a state \<Rightarrow> bool\<rbrace>
     finalise_cap cap fin
   \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>cp. is_zombie cp \<and> P cp) sl\<rbrace>"
  apply (cases cap, simp_all split del: if_split)
       apply (wp deleting_irq_handler_cte_preserved cancel_ipc_cte_preserved_irqn
                 reply_unlink_sc_cte_wp_at hoare_drop_imps gts_wp get_simple_ko_wp
               | clarsimp simp: is_cap_simps can_fast_finalise_def | wpc)+
  done

lemma reply_remove_tcb_st_tcb_at_general:
  "\<lbrace>\<lambda>s. if t' = t then P (P' Inactive) else P (st_tcb_at P' t' s)\<rbrace>
    reply_remove_tcb t r
   \<lbrace>\<lambda>rv s. P (st_tcb_at P' t' s)\<rbrace>"
  apply (clarsimp simp: reply_remove_tcb_def)
  apply (rule hoare_seq_ext[OF _ gts_inv])
  apply (rule hoare_seq_ext[OF _ assert_inv])
  apply (rule hoare_seq_ext[OF _ gets_inv])
  apply (rule hoare_seq_ext[OF reply_unlink_tcb_st_tcb_at])
  by (wpsimp wp: get_sk_obj_ref_wp)

lemma cancel_ipc_st_tcb_at:
  "\<lbrace>\<lambda>s. if t' = t \<and> st_tcb_at (\<lambda>st. st \<notin> {Running, Restart, IdleThreadState}) t' s
        then P (P' Inactive)
        else P (st_tcb_at P' t' s)\<rbrace>
    cancel_ipc t
   \<lbrace>\<lambda>rv s. P (st_tcb_at P' t' s)\<rbrace>"
  apply (clarsimp simp: cancel_ipc_def)
  apply (rule hoare_seq_ext[OF _ gts_sp])
  apply (wpsimp wp: blocked_ipc_st_tcb_at_general reply_remove_tcb_st_tcb_at_general
                    cancel_signal_st_tcb_at_general thread_set_no_change_tcb_pred_gen
                    hoare_drop_imps)
  by (auto simp: pred_tcb_at_def obj_at_def)

lemma fast_finalise_st_tcb_at:
  "\<lbrace>st_tcb_at P t and K (fin \<longrightarrow> P Running \<and> P Restart \<and> P Inactive)\<rbrace>
     fast_finalise cap fin
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  by (rule hoare_gen_asm)
     (cases cap
      ; wpsimp wp: cancel_all_ipc_st_tcb_at cancel_all_signals_st_tcb_at
                   cancel_ipc_st_tcb_at get_simple_ko_wp gts_wp)

lemma cap_delete_one_st_tcb_at:
  "\<lbrace>st_tcb_at P t and K (P Running \<and> P Restart \<and> P Inactive)\<rbrace>
     cap_delete_one ptr
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (wpsimp wp: fast_finalise_st_tcb_at get_cap_wp simp: cte_wp_at_def)
  done

lemma deleting_irq_handler_st_tcb_at:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. \<not> ipc_queued_thread_state st \<longrightarrow> P st) and invs\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_st_tcb_at)
  apply simp
  done

lemma can_fast_finalise_Null:
  "can_fast_finalise cap.NullCap"
  by (simp add: can_fast_finalise_def)


lemmas (in Finalise_AI_3) finalise_cap_cte_at[wp] = valid_cte_at_typ [OF finalise_cap_typ_at]

lemma finalise_cap_fast_Null:
  "\<lbrace>\<lambda>s. can_fast_finalise cap\<rbrace> finalise_cap cap final \<lbrace>\<lambda>rv s. rv = (cap.NullCap, NullCap)\<rbrace>"
  apply (cases cap, simp_all add: can_fast_finalise_def)
     apply (wp | simp only: o_def simp_thms cases_simp if_cancel fst_conv)+
  done

lemmas cases_simp_option[simp] = cases_simp[where P="x = None" for x, simplified]

lemma replaceable_same:
  "replaceable s slot cap cap"
  by (simp add: replaceable_def)

lemma hoare_pre_disj':
  "\<lbrakk>\<lbrace>\<lambda>s. P s \<and> R s\<rbrace> f \<lbrace>T\<rbrace>;
   \<lbrace>\<lambda>s. Q s \<and> R s\<rbrace> f \<lbrace>T\<rbrace> \<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. (P s \<or> Q s) \<and> R s\<rbrace> f \<lbrace>T\<rbrace>"
  apply (rule hoare_pre)
  apply (erule (1) hoare_pre_disj)
  apply simp
  done

lemmas thread_set_final_cap =
    final_cap_lift [OF thread_set_caps_of_state_trivial]


schematic_goal no_cap_to_obj_with_diff_ref_lift:
  "\<lbrace>\<lambda>s. ?P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. ?P (caps_of_state s)\<rbrace>
   \<Longrightarrow> \<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
          f
      \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  by (simp add: no_cap_to_obj_with_diff_ref_def
                cte_wp_at_caps_of_state)


lemmas thread_set_no_cap_obj_ref_trivial
    = no_cap_to_obj_with_diff_ref_lift [OF thread_set_caps_of_state_trivial]


lemma cap_not_in_valid_global_refs:
  "\<lbrakk>invs s; caps_of_state s p = Some cap\<rbrakk> \<Longrightarrow>
   obj_refs cap \<inter> global_refs s = {}"
  apply (drule invs_valid_global_refs)
  apply (simp add: valid_global_refs_def valid_refs_def)
  apply (case_tac p, simp)
  apply (erule_tac x=a in allE, erule_tac x=b in allE)
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_def)
  apply blast
  done

lemma gbn_wp':
  "\<lbrace>\<lambda>s. \<forall>ntfn. bound_tcb_at ((=) ntfn) t s \<longrightarrow> P ntfn s\<rbrace> get_tcb_obj_ref tcb_bound_notification t \<lbrace>P\<rbrace>"
  unfolding get_tcb_obj_ref_def
  apply (wp thread_get_wp')
  apply (clarsimp)
  apply (drule spec, erule mp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

locale Finalise_AI_4 = Finalise_AI_3 a b _ c
  for a :: "('a :: state_ext) itself"
  and b :: "('b :: state_ext) itself"
  and c :: "'c itself"

locale Finalise_AI_5 = Finalise_AI_4 _ a b c
  for a :: "('a :: state_ext) itself"
  and b :: "('b :: state_ext) itself"
  and c :: "'c itself" +
  assumes clearMemory_invs[wp]:
    "\<And> w sz. \<lbrace>invs\<rbrace> do_machine_op (clearMemory w sz) \<lbrace>\<lambda>_. invs :: 'a state \<Rightarrow> bool\<rbrace>"
  assumes valid_idle_has_null_cap:
    "\<And> cap (s :: 'a state) v.
      \<lbrakk> if_unsafe_then_cap s; valid_global_refs s; valid_idle s; valid_irq_node s\<rbrakk>
      \<Longrightarrow> caps_of_state s (idle_thread s, v) = Some cap
      \<Longrightarrow> cap = NullCap"
  assumes zombie_cap_two_nonidles:
    "\<And> (s :: 'a state)  ptr ptr' zbits n.
      \<lbrakk> caps_of_state s ptr = Some (Zombie ptr' zbits n); invs s \<rbrakk>
         \<Longrightarrow> fst ptr \<noteq> idle_thread s \<and> ptr' \<noteq> idle_thread s"

lemma valid_irq_node_arch [iff]:
  "valid_irq_node (arch_state_update f s) = valid_irq_node s"
  by (simp add: valid_irq_node_def)

(* FIXME: move *)
lemma vms_arch_state_update[simp]:
  "valid_machine_state (arch_state_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

(* FIXME: move *)
lemma dmo_bind_return:
  "\<lbrace>P\<rbrace> do_machine_op f \<lbrace>\<lambda>_. Q\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> do_machine_op (do _ \<leftarrow> f; return x od) \<lbrace>\<lambda>_. Q\<rbrace>"
  by (simp add: do_machine_op_def bind_def return_def valid_def select_f_def
                     split_def)

lemma st_tcb_at_idle_thread:
  "\<lbrakk> st_tcb_at P (idle_thread s) s; valid_idle s \<rbrakk>
        \<Longrightarrow> P Structures_A.IdleThreadState"
  by (clarsimp simp: valid_idle_def st_tcb_def2 pred_tcb_def2)


lemma tcb_state_merge_tcb_state_default:
  "tcb_state (tcb_registers_caps_merge tcb tcb') = tcb_state tcb"
  "tcb_state (default_tcb dm) = Structures_A.Inactive"
  by (auto simp add: tcb_registers_caps_merge_def default_tcb_def)

lemma tcb_bound_notification_merge_tcb_state_default:
  "tcb_bound_notification (tcb_registers_caps_merge tcb tcb') = tcb_bound_notification tcb"
  "tcb_bound_notification (default_tcb dm) = None"
  by (auto simp add: tcb_registers_caps_merge_def default_tcb_def)

(*Lift hoare triples from an instantiation to the nondeterministic hoare triple version.
  Since bcorres states that f refines g with respect to the non_extended state,
  we can prove the hoare triple over the more abstract g and put undefined
  values into the extended_state*)

lemma use_bcorres: "bcorres f g \<Longrightarrow> (\<And>f f'.
        \<lbrace>P o (trans_state f)\<rbrace> g \<lbrace>\<lambda>r s. Q r (trans_state f' s)\<rbrace>)\<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  apply (clarsimp simp add: bcorres_underlying_def s_bcorres_underlying_def valid_def)
  apply (drule_tac x="\<lambda>_.exst s" in meta_spec)
  apply (drule_tac x="\<lambda>_.exst b" in meta_spec)
  apply (drule_tac x="truncate_state s" in spec)
  apply (simp add: trans_state_update')
  apply (drule_tac x="(a,truncate_state b)" in bspec)
  apply force
  apply (simp add:  trans_state_update')
  done

lemma dxo_noop: "do_extended_op f = (return () :: (unit,unit) s_monad)"
  apply (clarsimp simp add: do_extended_op_def bind_def gets_def get_def return_def
         select_f_def modify_def put_def mk_ef_def wrap_ext_op_unit_def)
  apply force
  done

(*FIXME: move *)
lemma corres_option_split:
  "\<lbrakk>v = v'; corres_underlying sr nf nf' r P P' a c; (\<And>x. v = Some x \<Longrightarrow> corres_underlying sr nf nf' r (Q x) (Q' x) (b x) (d x))\<rbrakk>
  \<Longrightarrow> corres_underlying sr nf nf' r (case_option P Q v) (case_option P' Q' v') (case_option a b v) (case_option c d v')"
  by (cases v', simp_all)


lemma hoare_post_case_option_ext:
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. case_option (P s) (\<lambda>rv'. Q rv' s) rv\<rbrace> \<Longrightarrow> \<lbrace>R\<rbrace> f \<lbrace>case_option P Q\<rbrace>"
  by (erule hoare_post_imp [rotated], simp split: option.splits)


lemma hoare_when_weak_wp:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> when G f \<lbrace>\<lambda>_. P\<rbrace>"
  by wp simp+


lemma zombie_not_ex_cap_to:
  "\<lbrakk> cte_wp_at ((=) (cap.Zombie ptr zbits n)) slot s;
         zombies_final s \<rbrakk>
      \<Longrightarrow> \<not> ex_nonz_cap_to ptr s"
  apply (clarsimp simp: ex_nonz_cap_to_def )
  apply (frule(1) zombies_finalD3[where P="(=) c" and P'="\<lambda>c. x \<in> S c" for c x S])
     apply (clarsimp simp: cte_wp_at_caps_of_state)
    apply assumption
   apply (rule notI, drule_tac a=ptr in equals0D)
   apply (clarsimp simp add: zobj_refs_to_obj_refs)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
  done

lemma is_cap_tableE:
  "\<lbrakk> is_cap_table sz ko; \<And>cs. \<lbrakk> ko = kernel_object.CNode sz cs; well_formed_cnode_n sz cs\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding is_cap_table_def
  by (auto split: Structures_A.kernel_object.split_asm)

lemma cap_table_at_length:
  "\<lbrakk> cap_table_at bits oref s; valid_objs s \<rbrakk>
     \<Longrightarrow> bits < (word_bits - cte_level_bits)"
  apply (erule(1) obj_at_valid_objsE)
  apply (case_tac ko, simp_all add: is_cap_table_def)
  apply (clarsimp simp: valid_obj_def valid_cs_def
                        valid_cs_size_def well_formed_cnode_n_def
                        length_set_helper)
  done


lemma unbind_notification_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s) \<and> valid_objs s \<and> tcb_at a s\<rbrace>
     unbind_notification a
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (rule hoare_seq_ext [OF _ gbn_sp])
  apply (case_tac ntfnptr; simp add: maybeM_def)
   apply (wpsimp)
  apply (wpsimp simp: update_sk_obj_ref_def wp: get_simple_ko_wp)

  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def pred_tcb_at_def ntfn_q_refs_of_def
                          state_refs_of_def
                    split: if_split_asm)
  by (auto simp: valid_obj_def obj_at_def symreftype_inverse'
                 ntfn_q_refs_of_def tcb_ntfn_is_bound_def state_refs_of_def
                 tcb_st_refs_of_def get_refs_def2
          split: ntfn.splits thread_state.splits if_split_asm
          dest!: sym_refs_bound_tcb_atD
          elim!: obj_at_valid_objsE
         intro!: ntfn_q_refs_no_NTFNBound)

crunches test_reschedule, tcb_release_remove
  for kheap[wp]: "\<lambda>s. P (kheap s)"
  and obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"
  (wp: crunch_wps simp: crunch_simps)

end
