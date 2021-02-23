(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchAccess_AC
imports Access_AC
begin

section\<open>Arch-specific AC proofs\<close>

context Arch begin global_naming ARM_A

named_theorems Access_AC_assms

lemma acap_class_reply[Access_AC_assms]:
  "acap_class acap \<noteq> ReplyClass t"
  by (cases acap; simp)

lemma arch_troa_tro_alt[Access_AC_assms, elim!]:
  "arch_integrity_obj_atomic aag subjects l ko ko'
   \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko'"
  by (fastforce elim: arch_integrity_obj_atomic.cases intro: arch_integrity_obj_alt.intros)

lemma integrity_asids_refl[simp]: "integrity_asids aag subjects ptr s s"
  by (simp add: integrity_asids_def)

lemma clear_asidpool_trans[elim]:
  "\<lbrakk> asid_pool_integrity subjects aag pool pool';
     asid_pool_integrity subjects aag pool' pool'' \<rbrakk>
     \<Longrightarrow> asid_pool_integrity subjects aag pool pool''"
  unfolding asid_pool_integrity_def by metis

lemma cap_asid'_member[simp]:
  "asid \<in> cap_asid' cap = (\<exists>acap. cap = ArchObjectCap acap \<and> asid \<in> acap_asid' acap)"
  by (cases cap; clarsimp)

lemma clas_caps_of_state[Access_AC_assms]:
  "\<lbrakk> caps_of_state s slot = Some cap; pas_refined aag s \<rbrakk>
     \<Longrightarrow> cap_links_asid_slot aag (pasObjectAbs aag (fst slot)) cap"
  apply (clarsimp simp: cap_links_asid_slot_def label_owns_asid_slot_def pas_refined_def)
  apply (drule state_asids_to_policy_aux.intros)
   apply assumption
  apply (blast dest: state_asids_to_policy_aux.intros)
  done

lemma trasids_trans:
  "\<lbrakk> (\<forall>x. integrity_asids aag subjects x (asid_table s (asid_high_bits_of x))
                                         (asid_table s' (asid_high_bits_of x)));
     (\<forall>x. integrity_asids aag subjects x (asid_table s' (asid_high_bits_of x))
                                         (asid_table s'' (asid_high_bits_of x))) \<rbrakk>
     \<Longrightarrow> (\<forall>x. integrity_asids aag subjects x (asid_table s (asid_high_bits_of x))
                                             (asid_table s'' (asid_high_bits_of x)))"
  apply (clarsimp simp: integrity_asids_def)
  apply metis
  done

lemma arch_tro_alt_trans_spec[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_alt aag subjects l ko ko';
     arch_integrity_obj_alt aag subjects l ko' ko'' \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_alt aag subjects l ko ko''"
  by (fastforce simp: arch_integrity_obj_alt.simps)

lemmas arch_integrity_obj_simps [simp] =
  trm_orefl[OF refl]
  trd_orefl[OF refl]

lemma arch_integrity_update_autarch[Access_AC_assms]:
  "\<lbrakk> arch_integrity_subjects {pasSubject aag} aag (pasMayActivate aag) X st s; is_subject aag ptr \<rbrakk>
     \<Longrightarrow> arch_integrity_subjects {pasSubject aag} aag (pasMayActivate aag) X st
                                                  (s\<lparr>kheap := kheap s(ptr \<mapsto> obj)\<rparr>)"
  unfolding arch_integrity_subjects_def
  apply (intro conjI,simp_all)
   apply clarsimp
   apply (drule_tac x = x in spec, erule integrity_mem.cases)
   apply ((auto intro: integrity_mem.intros)+)[4]
   apply (erule trm_ipc, simp_all)
   apply (clarsimp simp: restrict_map_Some_iff tcb_states_of_state_def get_tcb_def)
  apply clarsimp
  apply (drule_tac x = x in spec, erule integrity_device.cases)
    apply (erule integrity_device.trd_lrefl)
   apply (erule integrity_device.trd_orefl)
  apply (erule integrity_device.trd_write)
  done

lemma as_user_state_vrefs[Access_AC_assms, wp]:
  "as_user t f \<lbrace>\<lambda>s. P (state_vrefs s)\<rbrace>"
  apply (simp add: as_user_def)
  apply (wpsimp wp: set_object_wp)
  apply (clarsimp simp: state_vrefs_def vs_refs_no_global_pts_def get_tcb_def
                 elim!: rsubst[where P=P, OF _ ext]
                 split: option.split_asm Structures_A.kernel_object.split)
  done

end


global_interpretation Access_AC_1?: Access_AC_1
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma arch_eintegrity_sa_update[Access_AC_assms]:
  "arch_integrity_subjects subjects aag activate X st (scheduler_action_update f s) =
   arch_integrity_subjects subjects aag activate X st s"
  by (simp add: arch_integrity_subjects_def trans_state_update'[symmetric])

lemma auth_ipc_buffers_tro:
  "\<lbrakk> integrity_obj_state aag activate subjects s s';
     x \<in> auth_ipc_buffers s' p; pasObjectAbs aag p \<notin> subjects \<rbrakk>
     \<Longrightarrow> x \<in> auth_ipc_buffers s p "
  by (drule_tac x = p in spec)
     (erule integrity_objE;
      fastforce simp: tcb_states_of_state_def get_tcb_def auth_ipc_buffers_def
               split: cap.split_asm arch_cap.split_asm if_split_asm bool.splits)

lemma arch_integrity_trans[Access_AC_assms]:
  assumes t1: "arch_integrity_subjects subjects aag activate X s s'"
  and     t2: "arch_integrity_subjects subjects aag activate X s' s''"
  and   tro1: "integrity_obj_state aag activate subjects s s'"
  and   tro2: "integrity_obj_state aag activate subjects s' s''"
  shows       "arch_integrity_subjects subjects aag activate X s s''"
proof -
  have intm: "\<forall>x. integrity_mem aag subjects x
                  (tcb_states_of_state s) (tcb_states_of_state s'') (auth_ipc_buffers s) X
                  (underlying_memory (machine_state s) x)
                  (underlying_memory (machine_state s'') x)" (is "\<forall>x. ?P x s s''")
  proof
    fix x
    from t1 t2 have m1: "?P x s s'" and m2: "?P x s' s''"
      unfolding integrity_subjects_def arch_integrity_subjects_def by auto

    from m1 show "?P x s s''"
    proof cases
      case trm_lrefl thus ?thesis by (rule integrity_mem.intros)
    next
      case trm_globals thus ?thesis by (rule integrity_mem.intros)
    next
      case trm_orefl
      from m2 show ?thesis
      proof cases
        case (trm_ipc p')

        show ?thesis
        proof (rule integrity_mem.trm_ipc)
          from trm_ipc show "case_option False can_receive_ipc (tcb_states_of_state s p')"
            by (fastforce split: option.splits dest: can_receive_ipc_backward [OF tro1])

          from trm_ipc show "x \<in> auth_ipc_buffers s p'"
            by (fastforce split: option.splits intro: auth_ipc_buffers_tro [OF tro1])
        qed (simp_all add: trm_ipc)
      qed (auto simp add: trm_orefl intro: integrity_mem.intros)
    next
      case trm_write thus ?thesis by (rule integrity_mem.intros)
    next
      case (trm_ipc p')
      note trm_ipc1 = trm_ipc

      from m2 show ?thesis
      proof cases
        case trm_orefl
        thus ?thesis using trm_ipc1
          by (auto intro!: integrity_mem.trm_ipc
                     simp: restrict_map_Some_iff
                     elim!: tsos_tro_running[OF tro2, rotated])
      next
        case (trm_ipc p'')
        show ?thesis
        proof (cases "p' = p''")
          case True thus ?thesis using trm_ipc trm_ipc1 by (simp add: restrict_map_Some_iff)
        next
          (* 2 tcbs sharing same IPC buffer, we can appeal to either t1 or t2 *)
          case False
          thus ?thesis using trm_ipc1
            by (auto intro!: integrity_mem.trm_ipc
                       simp: restrict_map_Some_iff
                      elim!: tsos_tro_running[OF tro2, rotated])
        qed
      qed (auto simp add: trm_ipc intro: integrity_mem.intros)
    qed
  qed

  moreover have "\<forall>x. integrity_device aag subjects x
                  (tcb_states_of_state s) (tcb_states_of_state s'')
                  (device_state (machine_state s) x)
                  (device_state (machine_state s'') x)" (is "\<forall>x. ?P x s s''")
  proof
    fix x
    from t1 t2 have m1: "?P x s s'" and m2: "?P x s' s''"
      unfolding integrity_subjects_def arch_integrity_subjects_def by auto

    from m1 show "?P x s s''"
    proof cases
      case trd_lrefl thus ?thesis by (rule integrity_device.intros)
    next
      case torel1: trd_orefl
      from m2 show ?thesis
      proof cases
        case (trd_lrefl) thus ?thesis by (rule integrity_device.trd_lrefl)
      next
        case trd_orefl thus ?thesis
          by (simp add:torel1)
      next
        case trd_write thus ?thesis by (rule integrity_device.trd_write)
      qed
    next
      case trd_write thus ?thesis by (rule integrity_device.intros)
    qed
  qed
  thus ?thesis using tro_trans[OF tro1 tro2] t1 t2 intm
    apply (clarsimp simp: integrity_subjects_def arch_integrity_subjects_def)
    apply (frule(1) trasids_trans[simplified])
    by blast
qed

lemma arch_integrity_refl[Access_AC_assms, simp]:
  "arch_integrity_subjects S aag activate X s s"
  unfolding arch_integrity_subjects_def
  by simp

end


global_interpretation Access_AC_2?: Access_AC_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma ipcframe_subset_page:
  "\<lbrakk> valid_objs s; get_tcb p s = Some tcb;
     tcb_ipcframe tcb = ArchObjectCap (PageCap d p' R vms xx);
     x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms))) msg_align_bits \<rbrakk>
     \<Longrightarrow> x \<in> ptr_range p' (pageBitsForSize vms)"
   apply (frule (1) valid_tcb_objs)
   apply (clarsimp simp add: valid_tcb_def ran_tcb_cap_cases)
   apply (erule set_mp[rotated])
   apply (rule ptr_range_subset)
     apply (simp add: valid_cap_def cap_aligned_def)
    apply (simp add: valid_tcb_def valid_ipc_buffer_cap_def is_aligned_andI1 split:bool.splits)
   apply (rule order_trans [OF _ pbfs_atleast_pageBits])
   apply (simp add: msg_align_bits pageBits_def)
  apply (rule and_mask_less')
  apply (simp add: pbfs_less_wb' [unfolded word_bits_conv])
  done

lemma auth_ipc_buffers_member_def:
  "x \<in> auth_ipc_buffers s p =
   (\<exists>tcb p' R vms xx. get_tcb p s = Some tcb
                   \<and> tcb_ipcframe tcb = (ArchObjectCap (PageCap False p' R vms xx))
                   \<and> caps_of_state s (p, tcb_cnode_index 4) =
                      Some (ArchObjectCap (PageCap False p' R vms xx))
                   \<and> AllowWrite \<in> R
                   \<and> x \<in> ptr_range (p' + (tcb_ipc_buffer tcb && mask (pageBitsForSize vms)))
                                    msg_align_bits)"
  unfolding auth_ipc_buffers_def
  by (clarsimp simp: caps_of_state_tcb' split: option.splits cap.splits arch_cap.splits bool.splits)

lemma trm_ipc':
  "\<lbrakk> pas_refined aag s; valid_objs s; case_option False can_receive_ipc (tcb_states_of_state s p');
     (tcb_states_of_state s' p') = Some Running; p \<in> auth_ipc_buffers s p' \<rbrakk>
     \<Longrightarrow> integrity_mem aag subjects p (tcb_states_of_state s) (tcb_states_of_state s')
                      (auth_ipc_buffers s) X
                      (underlying_memory (machine_state s) p)
                      (underlying_memory (machine_state s') p)"
  apply (cases "pasObjectAbs aag p' \<in> subjects")
   apply (rule trm_write)
   apply (clarsimp simp: auth_ipc_buffers_member_def)
   apply (frule pas_refined_mem[rotated])
    apply (erule sta_caps, simp)
     apply (erule(3) ipcframe_subset_page)
    apply (fastforce simp: cap_auth_conferred_def arch_cap_auth_conferred_def
                           vspace_cap_rights_to_auth_def is_page_cap_def)
   apply fastforce
  by (rule trm_ipc)

lemma asid_pool_integrity_mono:
  "\<lbrakk> asid_pool_integrity S aag cont cont' ; S \<subseteq> T \<rbrakk> \<Longrightarrow> asid_pool_integrity T aag cont cont'"
  unfolding asid_pool_integrity_def by fastforce

lemma arch_integrity_mono[Access_AC_assms]:
  "\<lbrakk> arch_integrity_subjects S aag activate X s s'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> arch_integrity_subjects T aag activate X s s'"
  apply (simp add: arch_integrity_subjects_def)
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_mem.cases;
           blast intro: integrity_mem.intros trm_ipc')
  apply (rule conjI)
   apply clarsimp
   apply (drule_tac x=x in spec, erule integrity_device.cases;
          blast intro: integrity_device.intros)
  apply (fastforce simp: integrity_asids_def)
  done

lemma arch_integrity_obj_atomic_mono[Access_AC_assms]:
  "\<lbrakk> arch_integrity_obj_atomic aag S l ao ao'; S \<subseteq> T; pas_refined aag s; valid_objs s \<rbrakk>
     \<Longrightarrow> arch_integrity_obj_atomic aag T l ao ao'"
  by (clarsimp simp: arch_integrity_obj_atomic.simps asid_pool_integrity_mono)

end


context Arch_pspace_update_eq begin

lemma state_vrefs[Access_AC_assms, iff]: "state_vrefs (f s) = state_vrefs s"
  by (simp add: state_vrefs_def pspace)

end


global_interpretation Access_AC_3?: Access_AC_3
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; fact Access_AC_assms)
qed


context Arch begin global_naming ARM_A

lemma pas_refined_irq_state_independent[intro!, simp]:
  "pas_refined x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>) =
   pas_refined x s"
  by (simp add: pas_refined_def)

end

end
