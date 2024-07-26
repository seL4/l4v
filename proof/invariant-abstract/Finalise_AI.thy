(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Finalise_AI
imports
  ArchIpcCancel_AI
  ArchInterruptAcc_AI
  ArchRetype_AI
begin

definition
  fst_cte_ptrs :: "cap \<Rightarrow> cslot_ptr set"
where
 "fst_cte_ptrs cap \<equiv> (case cap of
    cap.CNodeCap r bits guard \<Rightarrow> {(r, replicate bits False)}
  | cap.ThreadCap r           \<Rightarrow> {(r, tcb_cnode_index 0)}
  | cap.Zombie r zb n         \<Rightarrow> {(r, replicate (zombie_cte_bits zb) False)}
  | _                         \<Rightarrow> {})"

arch_requalify_consts (A)
  unmap_page

arch_requalify_consts
  vs_cap_ref
  arch_post_cap_delete_pre

requalify_facts
  Arch.no_irq_clearMemory

arch_requalify_facts
  final_cap_lift
  valid_global_refsD
  arch_post_cap_deletion_valid_objs
  arch_post_cap_deletion_cte_wp_at
  arch_post_cap_deletion_caps_of_state
  arch_post_cap_deletion_irq_node
  arch_post_cap_deletion_invs

definition
  "post_cap_delete_pre cap cs \<equiv> case cap of
     IRQHandlerCap irq \<Rightarrow> cap \<notin> ran cs
   | ArchObjectCap acap \<Rightarrow> arch_post_cap_delete_pre cap cs
   | _ \<Rightarrow> False"

lemma update_restart_pc_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> update_restart_pc t \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  by (simp add: update_restart_pc_def as_user_caps)

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
          emptyable sl s \<and> (info \<noteq> NullCap \<longrightarrow> post_cap_delete_pre info ((caps_of_state s) (sl \<mapsto> NullCap)))\<rbrace>
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
  assumes deleting_irq_handler_cte_preserved:
  "\<And> P p irq.\<lbrakk> \<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap \<rbrakk>
    \<Longrightarrow> \<lbrace>cte_wp_at P p\<rbrace>
          deleting_irq_handler irq :: 'a state \<Rightarrow> (unit \<times> 'a state) set \<times> bool
        \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
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

lemma halted_emptyable:
  "\<And>ref. halted_if_tcb t s \<Longrightarrow> emptyable (t, ref) s"
  by (simp add: halted_if_tcb_def emptyable_def)


lemma tcb_cap_valid_NullCapD:
  "\<And>cap sl. \<lbrakk> tcb_cap_valid cap sl s; \<not> is_master_reply_cap cap \<rbrakk> \<Longrightarrow>
   tcb_cap_valid cap.NullCap sl s"
  apply (clarsimp simp: tcb_cap_valid_def valid_ipc_buffer_cap_def
                 elim!: pred_tcb_weakenE split: option.splits)
  apply (rename_tac get set restr)
  apply (subgoal_tac "(get, set, restr) \<in> ran tcb_cap_cases")
   apply (fastforce simp: ran_tcb_cap_cases is_cap_simps
                  split: Structures_A.thread_state.split)
  apply (simp add: ranI)
  done


lemma emptyable_valid_NullCapD:
  "\<lbrakk> emptyable sl s; valid_objs s \<rbrakk> \<Longrightarrow> tcb_cap_valid cap.NullCap sl s"
  apply (clarsimp simp: emptyable_def tcb_cap_valid_def
                        valid_ipc_buffer_cap_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_tcb split: option.split)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def tcb_cap_cases_def
                 split: Structures_A.thread_state.split)
  done


lemma emptyable_valid_NullCap_strg:
  "emptyable sl s \<and> valid_objs s \<longrightarrow> tcb_cap_valid cap.NullCap sl s"
  by (simp add: emptyable_valid_NullCapD)


lemma tcb_cap_valid_pspaceI[intro]:
  "\<lbrakk> tcb_cap_valid cap sl s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> tcb_cap_valid cap sl s'"
  by (clarsimp simp: tcb_cap_valid_def obj_at_def pred_tcb_at_def)


crunch deleted_irq_handler
  for valid_objs[wp]: "valid_objs"


lemma emptyable_rvk[simp]:
  "emptyable sl (is_original_cap_update f s) = emptyable sl s"
  by (simp add: emptyable_def)


lemma set_cdt_emptyable[wp]:
  "\<lbrace>emptyable sl\<rbrace> set_cdt m \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  by (simp add: set_cdt_def emptyable_def | wp)+

lemma emptyable_more_update[simp]:
  "emptyable sl (trans_state f s) = emptyable sl s"
  by (simp add: emptyable_def)

lemma tcb_cp_valid_trans_state_update[simp]: "tcb_cap_valid cap sl
         (trans_state f s) = tcb_cap_valid cap sl s"
  apply (simp add: tcb_cap_valid_def)
  done

crunch post_cap_deletion
  for valid_objs[wp]: "valid_objs"

lemma empty_slot_valid_objs[wp]:
  "\<lbrace>valid_objs and emptyable sl\<rbrace> empty_slot sl irqopt \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (rule hoare_pre)
   apply (wp set_cap_valid_objs set_cdt_valid_objs set_cdt_valid_cap
                 | simp add: trans_state_update[symmetric] del: trans_state_update| wpcw
                 | strengthen emptyable_valid_NullCap_strg
                 | wp (once) hoare_drop_imps)+
  done

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

lemma emptyable_no_reply_cap:
  assumes e: "emptyable sl s"
  and   mdb: "reply_caps_mdb (mdb s) (caps_of_state s)"
  and    vr: "valid_reply_caps s"
  and    vm: "valid_reply_masters s"
  and    vo: "valid_objs s"
  and    rc: "\<exists> R. caps_of_state s sl' = Some (cap.ReplyCap t False R)"
  and    rp: "mdb s sl' = Some sl"
  shows      "False"
proof -
  have rm:
    "\<exists> R. caps_of_state s sl = Some (cap.ReplyCap t True R)"
    using mdb rc rp unfolding reply_caps_mdb_def
    by fastforce
  have tcb_slot:
    "sl = (t, tcb_cnode_index 2)"
    using vm rm unfolding valid_reply_masters_def
    by (fastforce simp: cte_wp_at_caps_of_state is_master_reply_cap_to_def)
  have tcb_halted:
    "st_tcb_at halted t s"
    using vo rm tcb_slot e unfolding emptyable_def
    by (fastforce dest: caps_of_state_valid_cap simp: valid_cap_def)
  have tcb_not_halted:
    "st_tcb_at (Not \<circ> halted) t s"
    using vr rc unfolding valid_reply_caps_def
    by (fastforce simp add: has_reply_cap_def is_reply_cap_to_def cte_wp_at_caps_of_state
                 simp del: split_paired_Ex
                    elim!: pred_tcb_weakenE)
  show ?thesis
    using tcb_halted tcb_not_halted
    by (clarsimp simp: st_tcb_def2)
qed

lemmas (in Finalise_AI_1) obj_ref_ofI' = obj_ref_ofI[OF obj_ref_elemD]

crunch post_cap_deletion
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"

lemma empty_slot_deletes[wp]:
  "\<lbrace>\<top>\<rbrace> empty_slot sl opt \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>c. c = cap.NullCap) sl\<rbrace>"
  apply (simp add: empty_slot_def)
  apply (wp set_cap_sets get_cap_wp opt_return_pres_lift|simp)+
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done

crunch post_cap_deletion
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

lemma empty_slot_final_cap_at:
  "\<lbrace>(\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s) and K (p \<noteq> p')\<rbrace>
      empty_slot p' opt \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: empty_slot_def final_cap_at_eq cte_wp_at_conj cte_wp_at_caps_of_state)
  apply (wpsimp wp: opt_return_pres_lift get_cap_wp)
  apply (fastforce simp: )?
  done

crunch empty_slot
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"

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

crunch cancel_all_ipc
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: mapM_x_wp' crunch_wps)

crunch fast_finalise, unbind_notification
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: mapM_x_wp' crunch_wps thread_set_caps_of_state_trivial
   simp: tcb_cap_cases_def)


lemma cap_delete_one_caps_of_state:
  "\<lbrace>\<lambda>s. cte_wp_at can_fast_finalise p s
           \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap))\<rbrace>
     cap_delete_one p
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def
                   is_final_cap_def)
  apply (rule bind_wp [OF _ get_cap_sp])
  apply (case_tac "can_fast_finalise cap")
   apply (wp empty_slot_caps_of_state get_cap_wp)
   apply (clarsimp simp: cte_wp_at_caps_of_state
                         fun_upd_def[symmetric]
                         fun_upd_idem)
  apply (simp add: fast_finalise_def2)
  apply wp
  apply (clarsimp simp: can_fast_finalise_def)
  done

crunch blocked_cancel_ipc, cancel_signal
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

lemma cancel_ipc_caps_of_state:
  "\<lbrace>\<lambda>s. (\<forall>p. cte_wp_at can_fast_finalise p s
           \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap)))
           \<and> P (caps_of_state s)\<rbrace>
     cancel_ipc t
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: cancel_ipc_def reply_cancel_ipc_def
             cong: Structures_A.thread_state.case_cong)
  apply (wpsimp wp: cap_delete_one_caps_of_state)
     apply (rule_tac Q'="\<lambda>_ s. (\<forall>p. cte_wp_at can_fast_finalise p s
                                \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap)))
                                \<and> P (caps_of_state s)"
                  in hoare_post_imp)
      apply (clarsimp simp: fun_upd_def[symmetric] split_paired_Ball)
     apply (simp add: cte_wp_at_caps_of_state)
     apply (wpsimp wp: hoare_vcg_all_lift hoare_convert_imp thread_set_caps_of_state_trivial
                 simp: ran_tcb_cap_cases)+
   prefer 2
   apply assumption
  apply (rule hoare_strengthen_post [OF gts_sp])
  apply (clarsimp simp: fun_upd_def[symmetric] cte_wp_at_caps_of_state)
  done

lemma suspend_caps_of_state:
  "\<lbrace>\<lambda>s. (\<forall>p. cte_wp_at can_fast_finalise p s
           \<longrightarrow> P ((caps_of_state s) (p \<mapsto> cap.NullCap)))
           \<and> P (caps_of_state s)\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  by (wpsimp wp: cancel_ipc_caps_of_state simp: suspend_def fun_upd_def[symmetric])+

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

lemma unbind_notification_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. cte_wp_at P slot s\<rbrace> unbind_notification t \<lbrace>\<lambda>rv s. cte_wp_at P slot s\<rbrace>"
  by (wp thread_set_cte_wp_at_trivial hoare_drop_imp | wpc | simp add: unbind_notification_def tcb_cap_cases_def)+

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

crunch deleting_irq_handler
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp:crunch_wps simp:crunch_simps unless_def assertE_def)

context Finalise_AI_1 begin
context begin
  declare if_cong[cong]
  crunch finalise_cap
    for typ_at[wp]: "\<lambda>(s :: 'a state). P (typ_at T p s)"
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
  apply (simp add: unbind_maybe_notification_def invs_def valid_state_def valid_pspace_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
   apply (wpsimp wp: valid_irq_node_typ set_simple_ko_valid_objs valid_ioports_lift)
  apply simp
  apply safe
  defer 3 defer 6
       apply (auto elim!: obj_at_weakenE obj_at_valid_objsE if_live_then_nonz_capD2
                   simp: live_def valid_ntfn_set_bound_None is_ntfn valid_obj_def)[6]
  apply (rule delta_sym_refs, assumption)
   apply (fastforce simp: obj_at_def is_tcb
                   dest!: pred_tcb_at_tcb_at ko_at_state_refs_ofD
                   split: if_split_asm)
  apply (clarsimp split: if_split_asm)
   apply (subst (asm) ko_at_state_refs_ofD, assumption)
   apply (fastforce simp: ntfn_q_refs_no_NTFNBound symreftype_inverse'  is_tcb refs_of_rev
                  dest!: refs_in_ntfn_q_refs)
  apply (rule delta_sym_refs, assumption)
   apply (clarsimp split: if_split_asm)
   apply (subst (asm) ko_at_state_refs_ofD, assumption)
   apply (frule refs_in_ntfn_q_refs)
   apply (fastforce)
  apply (clarsimp split: if_split_asm)
   apply (frule_tac P="(=) (Some ntfnptr)" in ntfn_bound_tcb_at, simp_all add: obj_at_def)[1]
   apply (fastforce simp: ntfn_q_refs_no_NTFNBound tcb_at_no_ntfn_bound tcb_ntfn_is_bound_def
                          obj_at_def tcb_st_refs_no_TCBBound
                   dest!: pred_tcb_at_tcb_at bound_tcb_at_state_refs_ofD)
  apply (subst (asm) ko_at_state_refs_ofD, assumption)
  apply (fastforce simp: ntfn_q_refs_no_NTFNBound symreftype_inverse'  is_tcb refs_of_rev
                 dest!: refs_in_ntfn_q_refs)
  done

crunch (in Finalise_AI_1) fast_finalise
  for invs[wp]: "invs"

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
  "(\<not> is_master_reply_cap cap)
     \<longrightarrow> (tcb_cap_valid cap sl s \<longrightarrow> tcb_cap_valid cap.NullCap sl s)"
  apply (strengthen tcb_cap_valid_imp')
  apply (clarsimp simp: ran_tcb_cap_cases valid_ipc_buffer_cap_def
                 split: Structures_A.thread_state.split_asm)
  done

lemma pred_tcb_at_def2:
  "pred_tcb_at proj P t \<equiv> \<lambda>s. \<exists>tcb. ko_at (TCB tcb) t s \<and> P (proj (tcb_to_itcb tcb))"
  by (rule eq_reflection, rule ext) (fastforce simp: pred_tcb_at_def obj_at_def)

(* sseefried: 'st_tcb_at_def2' only exists to make existing proofs go through. Can use 'pred_tcb_at_def2' instead *)
lemmas st_tcb_at_def2 = pred_tcb_at_def2[where proj=itcb_state,simplified]

lemmas tcb_cap_valid_imp = mp [OF mp [OF tcb_cap_valid_imp'], rotated]

crunch cancel_all_ipc
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch cancel_all_signals, fast_finalise
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

crunch cap_delete_one
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps unless_def)

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
  apply (simp add: unbind_notification_def)
  apply (rule hoare_pre)
   apply (rule bind_wp[OF _ gbn_wp[where P="\<lambda>ptr _. ptr = (Some ntfnptr)"]])
   apply (rule hoare_gen_asm[where P'=\<top>, simplified])
   apply (wp sbn_obj_at_impossible simple_obj_set_prop_at | wpc | simp)+
  apply (clarsimp simp: obj_at_def)
  apply (rule valid_objsE, simp+)
  apply (drule_tac P="(=) (Some ntfnptr)" in ntfn_bound_tcb_at, simp+)
  apply (auto simp: obj_at_def valid_obj_def is_tcb valid_ntfn_def pred_tcb_at_def)
  done

 lemma unbind_maybe_notification_not_bound:
   "\<lbrace>\<lambda>s. ntfn_at ntfnptr s \<and> valid_objs s \<and> sym_refs (state_refs_of s)\<rbrace>
      unbind_maybe_notification ntfnptr
    \<lbrace>\<lambda>_. obj_at (\<lambda>ko. \<exists>ntfn. ko = Notification ntfn \<and> ntfn_bound_tcb ntfn = None) ntfnptr\<rbrace>"
  apply (simp add: unbind_maybe_notification_def)
  apply (rule hoare_pre)
   apply (wp get_simple_ko_wp sbn_obj_at_impossible simple_obj_set_prop_at | wpc | simp)+
  apply (clarsimp simp: obj_at_def)
  done

lemma unbind_notification_bound_tcb_at[wp]:
  "\<lbrace>\<top>\<rbrace> unbind_notification tcbptr \<lbrace>\<lambda>_. bound_tcb_at ((=) None) tcbptr\<rbrace>"
  apply (simp add: unbind_notification_def)
  apply (wpsimp wp: sbn_bound_tcb_at')
   apply (rule gbn_bound_tcb[THEN hoare_strengthen_post])
   apply clarsimp
  apply assumption
  done

crunch unbind_notification
  for valid_mdb[wp]: "valid_mdb"
crunch unbind_notification
  for tcb_at[wp]: "tcb_at t"

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
  assumes ep:"\<And>r. \<lbrace>P\<rbrace>cancel_all_ipc r \<lbrace>\<lambda>r s. P s\<rbrace>"
  and ntfn:"\<And>r. \<lbrace>P\<rbrace>cancel_all_signals r \<lbrace>\<lambda>r s. P s\<rbrace>"
  and unbind:"\<And>r. \<lbrace>P\<rbrace> unbind_notification r \<lbrace> \<lambda>r s. P s\<rbrace>"
  and unbind2: "\<And>r. \<lbrace>P\<rbrace> unbind_maybe_notification r \<lbrace> \<lambda>r s. P s\<rbrace>"
  shows "\<lbrace>P\<rbrace> fast_finalise cap final \<lbrace>\<lambda>r s. P s\<rbrace>"
  apply (case_tac cap,simp_all)
  apply (wp ep ntfn unbind unbind2 hoare_drop_imps | clarsimp | wpc)+
  done


crunch fast_finalise
  for cte_wp_at[wp]: "cte_wp_at P p"
  (rule: fast_finalise_lift)

lemma cap_delete_one_cte_wp_at_preserved:
  assumes x: "\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap"
  shows "\<lbrace>cte_wp_at P p\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp cap_delete_one_caps_of_state)
  apply (clarsimp simp: cte_wp_at_caps_of_state x)
  done

interpretation delete_one_pre
  by (unfold_locales; wpsimp wp: cap_delete_one_cte_wp_at_preserved)

lemma (in Finalise_AI_1) finalise_cap_equal_cap[wp]:
  "\<lbrace>cte_wp_at ((=) cap) sl\<rbrace>
     finalise_cap cap fin
   \<lbrace>\<lambda>rv. cte_wp_at ((=) cap) sl :: 'a state \<Rightarrow> bool\<rbrace>"
  apply (cases cap, simp_all split del: if_split)
    apply (wp suspend_cte_wp_at_preserved
                 deleting_irq_handler_cte_preserved prepare_thread_delete_cte_wp_at
                 hoare_drop_imp thread_set_cte_wp_at_trivial
               | clarsimp simp: can_fast_finalise_def unbind_maybe_notification_def
                                unbind_notification_def
                                tcb_cap_cases_def
               | wpc )+
  done

lemma emptyable_lift:
  assumes typ_at: "\<And>P T t. \<lbrace>\<lambda>s. P (typ_at T t s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at T t s)\<rbrace>"
  assumes st_tcb: "\<And>t. \<lbrace>st_tcb_at halted t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at halted t\<rbrace>"
  shows "\<lbrace>emptyable t\<rbrace> f \<lbrace>\<lambda>_. emptyable t\<rbrace>"
  unfolding emptyable_def
  apply (subst imp_conv_disj)+
  apply (rule hoare_vcg_disj_lift)
   apply (simp add: tcb_at_typ)
   apply (rule typ_at)
  apply (rule st_tcb)
  done


crunch set_simple_ko
  for emptyable[wp]: "emptyable sl"
  (rule: emptyable_lift)

lemma sts_emptyable:
  "\<lbrace>emptyable sl and st_tcb_at (\<lambda>st. \<not> halted st) t\<rbrace>
    set_thread_state t st
   \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  apply (simp add: emptyable_def)
  apply (subst imp_conv_disj)+
  apply (wp hoare_vcg_disj_lift sts_st_tcb_at_cases | simp add: tcb_at_typ)+
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done


lemma cancel_all_emptyable_helper:
  "\<lbrace>emptyable sl and (\<lambda>s. \<forall>t \<in> set q. st_tcb_at (\<lambda>st. \<not> halted st) t s)\<rbrace>
     mapM_x (\<lambda>t. do y \<leftarrow> set_thread_state t Structures_A.Restart;
                    do_extended_op (tcb_sched_enqueue_ext t) od) q
   \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp [where S="set q", simplified])
    apply (wp, simp, wp hoare_vcg_const_Ball_lift sts_emptyable sts_st_tcb_at_cases)
     apply simp+
  done

lemma unbind_notification_emptyable[wp]:
  "\<lbrace> emptyable sl \<rbrace> unbind_notification t \<lbrace> \<lambda>rv. emptyable sl\<rbrace>"
  unfolding unbind_notification_def
  apply (wp emptyable_lift hoare_drop_imps thread_set_no_change_tcb_state | wpc |simp)+
  done

lemma unbind_maybe_notification_emptyable[wp]:
  "\<lbrace> emptyable sl \<rbrace> unbind_maybe_notification r \<lbrace> \<lambda>rv. emptyable sl\<rbrace>"
  unfolding unbind_maybe_notification_def
  apply (wp emptyable_lift hoare_drop_imps thread_set_no_change_tcb_state | wpc |simp)+
  done

lemma cancel_all_signals_emptyable[wp]:
  "\<lbrace>invs and emptyable sl\<rbrace> cancel_all_signals ptr \<lbrace>\<lambda>_. emptyable sl\<rbrace>"
  unfolding cancel_all_signals_def unbind_maybe_notification_def
  apply (rule bind_wp[OF _ get_simple_ko_sp])
  apply (rule hoare_pre)
  apply (wp cancel_all_emptyable_helper
            hoare_vcg_const_Ball_lift
       | wpc
       | simp)+
  apply (auto elim: ntfn_queued_st_tcb_at)
  done

lemma cancel_all_ipc_emptyable[wp]:
  "\<lbrace>invs and emptyable sl\<rbrace> cancel_all_ipc ptr \<lbrace>\<lambda>_. emptyable sl\<rbrace>"
  apply (simp add: cancel_all_ipc_def)
  apply (rule bind_wp [OF _ get_simple_ko_sp])
  apply (case_tac ep, simp_all)
    apply (wp, simp)
   apply (wp cancel_all_emptyable_helper hoare_vcg_const_Ball_lift
        | simp add: get_ep_queue_def
        | clarsimp simp: invs_def valid_state_def valid_pspace_def
                         ep_queued_st_tcb_at)+
  done


lemma (in Finalise_AI_1) fast_finalise_emptyable[wp]:
  "\<lbrace>invs and emptyable sl\<rbrace> fast_finalise cap fin \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  apply (simp add: fast_finalise_def2)
  apply (case_tac cap, simp_all add: can_fast_finalise_def)
      apply (wp unbind_maybe_notification_invs hoare_drop_imps | simp add: o_def  | wpc)+
  done

locale Finalise_AI_2 = Finalise_AI_1 a b
  for a :: "('a :: state_ext) itself"
  and b :: "('b :: state_ext) itself" +
  assumes cap_delete_one_invs[wp]:
    "\<And> ptr. \<lbrace>invs and emptyable ptr\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv. invs :: 'a state \<Rightarrow> bool\<rbrace>"

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

lemma cap_delete_one_deletes_reply:
  "\<lbrace>cte_wp_at (is_reply_cap_to t) slot and valid_reply_caps\<rbrace>
    cap_delete_one slot
   \<lbrace>\<lambda>rv s. \<not> has_reply_cap t s\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply wp
     apply (rule_tac Q'="\<lambda>rv s. \<forall>sl' R. if (sl' = slot)
                               then cte_wp_at (\<lambda>c. c = cap.NullCap) sl' s
                               else caps_of_state s sl' \<noteq> Some (cap.ReplyCap t False R)"
                  in hoare_post_imp)
      apply (clarsimp simp add: has_reply_cap_def is_reply_cap_to_def cte_wp_at_caps_of_state
                      simp del: split_paired_All split_paired_Ex
                         split: if_split_asm elim!: allEI)
     apply (rule hoare_vcg_all_lift)
     apply simp
     apply (wp hoare_weak_lift_imp empty_slot_deletes empty_slot_caps_of_state get_cap_wp)+
  apply (fastforce simp: cte_wp_at_caps_of_state valid_reply_caps_def
                        is_cap_simps unique_reply_caps_def is_reply_cap_to_def
              simp del: split_paired_All)
  done

lemma cap_delete_one_reply_st_tcb_at:
  "\<lbrace>pred_tcb_at proj P t and cte_wp_at (is_reply_cap_to t') slot\<rbrace>
    cap_delete_one slot
   \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (rule bind_wp [OF _ get_cap_sp])
  apply (rule hoare_assume_pre)
  apply (clarsimp simp: cte_wp_at_caps_of_state when_def is_reply_cap_to_def)
  apply wpsimp
  done

lemma get_irq_slot_emptyable[wp]:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>emptyable\<rbrace>"
  apply (rule hoare_strengthen_post)
   apply (rule get_irq_slot_real_cte)
  apply (clarsimp simp: emptyable_def is_cap_table is_tcb elim!: obj_atE)
  done

crunch (in Finalise_AI_2) deleting_irq_handler
  for invs[wp]: "invs :: 'a state \<Rightarrow> bool"


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
  assumes deleting_irq_handler_st_tcb_at:
    "\<And>P t irq.\<lbrace>st_tcb_at P t and K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
       deleting_irq_handler irq
     \<lbrace>\<lambda>rv. st_tcb_at P t :: 'a state \<Rightarrow> bool\<rbrace>"
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

crunch suspend, unbind_maybe_notification, unbind_notification
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

crunch deleting_irq_handler
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas cancel_all_ipc_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF cancel_all_ipc_irq_node cancel_all_ipc_cte_wp_at]

lemmas cancel_all_signals_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF cancel_all_signals_irq_node cancel_all_signals_cte_wp_at]

lemmas suspend_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF suspend_irq_node suspend_cte_wp_at_preserved]

lemmas unbind_notification_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF unbind_notification_irq_node unbind_notification_cte_wp_at]

lemmas unbind_maybe_notification_cte_irq_node[wp]
    = hoare_use_eq_irq_node [OF unbind_maybe_notification_irq_node unbind_maybe_notification_cte_wp_at]

lemmas (in Finalise_AI_3) deleting_irq_handler_cte_preserved_irqn
  = hoare_use_eq_irq_node [OF deleting_irq_handler_irq_node
                              deleting_irq_handler_cte_preserved]

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
  apply (cases cap, simp_all add: ex_cte_cap_wp_to_def split del: if_split)
       apply (wp hoare_vcg_ex_lift hoare_drop_imps
                 prepare_thread_delete_cte_preserved_irqn
                 deleting_irq_handler_cte_preserved_irqn
                 prepare_thread_delete_cte_preserved_irqn
                 | simp
                 | clarsimp simp: can_fast_finalise_def
                           split: cap.split_asm | wpc)+
  done

lemma (in Finalise_AI_3) finalise_cap_zombie_cap[wp]:
  "\<lbrace>cte_wp_at (\<lambda>cp. is_zombie cp \<and> P cp) sl :: 'a state \<Rightarrow> bool\<rbrace>
     finalise_cap cap fin
   \<lbrace>\<lambda>rv. cte_wp_at (\<lambda>cp. is_zombie cp \<and> P cp) sl\<rbrace>"
  apply (cases cap, simp_all split del: if_split)
       apply (wp deleting_irq_handler_cte_preserved
               | clarsimp simp: is_cap_simps can_fast_finalise_def)+
  done

lemma fast_finalise_st_tcb_at:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. active st \<longrightarrow> P st)\<rbrace>
     fast_finalise cap fin
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (cases cap; wpsimp wp: cancel_all_ipc_st_tcb_at cancel_all_signals_st_tcb_at)
  done

lemma cap_delete_one_st_tcb_at:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. active st \<longrightarrow> P st)\<rbrace>
     cap_delete_one ptr
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (wpsimp wp: fast_finalise_st_tcb_at get_cap_wp)
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

(* FIXME: move *)
lemma invs_pspace_alignedI:
  "invs s \<Longrightarrow> pspace_aligned s"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  done

lemma cte_wp_at_disj:
  "cte_wp_at (\<lambda>c. P c \<or> P' c) sl s =
   (cte_wp_at (\<lambda>c. P c) sl s \<or> cte_wp_at (\<lambda>c. P' c) sl s)"
  unfolding cte_wp_at_def
  by fastforce

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

(* FIXME: move *)
lemma gts_wp:
  "\<lbrace>\<lambda>s. \<forall>st. st_tcb_at ((=) st) t s \<longrightarrow> P st s\<rbrace> get_thread_state t \<lbrace>P\<rbrace>"
  unfolding get_thread_state_def
  apply (wp thread_get_wp')
  apply clarsimp
  apply (drule spec, erule mp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma gbn_wp:
  "\<lbrace>\<lambda>s. \<forall>ntfn. bound_tcb_at ((=) ntfn) t s \<longrightarrow> P ntfn s\<rbrace> get_bound_notification t \<lbrace>P\<rbrace>"
  unfolding get_bound_notification_def
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
  "tcb_state default_tcb = Structures_A.Inactive"
  by (auto simp add: tcb_registers_caps_merge_def default_tcb_def)

lemma tcb_bound_notification_merge_tcb_state_default:
  "tcb_bound_notification (tcb_registers_caps_merge tcb tcb') = tcb_bound_notification tcb"
  "tcb_bound_notification default_tcb = None"
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

lemma emptyable_cte_wp_atD:   "\<lbrakk> cte_wp_at P sl s; valid_objs s;
     \<forall>cap. P cap \<longrightarrow> \<not> is_master_reply_cap cap \<rbrakk>
   \<Longrightarrow> emptyable sl s"
  apply (clarsimp simp: emptyable_def pred_tcb_at_def obj_at_def
                        is_tcb cte_wp_at_cases)
  apply (erule(1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def ran_tcb_cap_cases)
  done

lemma thread_set_emptyable:
  assumes z: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  shows      "\<lbrace>emptyable sl\<rbrace> thread_set f t \<lbrace>\<lambda>rv. emptyable sl\<rbrace>"
  by (wp emptyable_lift thread_set_no_change_tcb_state z)

end
