(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchTcbAcc_AI
imports TcbAcc_AI
begin

context Arch begin arch_global_naming

named_theorems TcbAcc_AI_assms

lemmas cap_master_cap_simps =
  cap_master_cap_def[simplified cap_master_arch_cap_def, split_simps cap.split arch_cap.split]

lemma cap_master_cap_arch_eqDs:
  "cap_master_cap cap = ArchObjectCap (FrameCap ref rghts sz dev mapdata)
     \<Longrightarrow> rghts = UNIV \<and> mapdata = None
          \<and> (\<exists>rghts mapdata. cap = cap.ArchObjectCap (FrameCap ref rghts sz dev mapdata))"
  "cap_master_cap cap = ArchObjectCap ASIDControlCap
     \<Longrightarrow> cap = ArchObjectCap ASIDControlCap"
  "cap_master_cap cap = ArchObjectCap (ASIDPoolCap pool asid)
     \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap = ArchObjectCap (ASIDPoolCap pool asid))"
  "cap_master_cap cap = ArchObjectCap (PageTableCap ptr pt_t data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = ArchObjectCap (PageTableCap ptr pt_t data))"
  by (clarsimp simp: cap_master_cap_def
              split: cap.split_asm arch_cap.split_asm)+

lemmas cap_master_cap_eqDs =
  cap_master_cap_eqDs1 cap_master_cap_arch_eqDs
  cap_master_cap_eqDs1 [OF sym] cap_master_cap_arch_eqDs[OF sym]


lemma vm_sets_diff[simp]:
  "vm_read_only \<noteq> vm_read_write"
  by (simp add: vm_read_write_def vm_read_only_def)


lemmas vm_sets_diff2[simp] = not_sym[OF vm_sets_diff]

lemma cap_master_cap_tcb_cap_valid_arch:
  "\<lbrakk> cap_master_cap c = cap_master_cap c'; is_arch_cap c' ;
     is_valid_vtable_root c \<Longrightarrow> is_valid_vtable_root c' ; tcb_cap_valid c p s \<rbrakk> \<Longrightarrow>
   tcb_cap_valid c' p s"
  (* slow: 5 to 10s *)
  by (auto simp: cap_master_cap_def tcb_cap_valid_def tcb_cap_cases_def
                 valid_ipc_buffer_cap_def  is_cap_simps
           elim: pred_tcb_weakenE
          split: option.splits cap.splits arch_cap.splits
                 Structures_A.thread_state.splits)

lemma storeWord_invs[wp, TcbAcc_AI_assms]:
  "\<lbrace>in_user_frame p and invs\<rbrace> do_machine_op (storeWord p w) \<lbrace>\<lambda>rv. invs\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l sz. l<8 \<Longrightarrow> p && mask 3 = 0 \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  proof -
    fix l sz
    assume al: "p && mask 3 = 0"
    assume "(l::machine_word) < 8" hence less: "l<2^3" by simp
    have le: "3 \<le> pageBitsForSize sz"
      by (case_tac sz, simp_all add: pageBits_def ptTranslationBits_def)
    show "?thesis l sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=3, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs)
    apply (clarsimp simp: storeWord_def invs_def valid_state_def upto0_7_def)
    apply (fastforce simp: valid_machine_state_def in_user_frame_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
             split: if_split_asm)
    done
qed

lemma valid_ipc_buffer_cap_0[simp, TcbAcc_AI_assms]:
  "valid_ipc_buffer_cap cap a \<Longrightarrow> valid_ipc_buffer_cap cap 0"
  by (auto simp add: valid_ipc_buffer_cap_def case_bool_If
    split: cap.split arch_cap.split)

lemma thread_set_hyp_refs_trivial [TcbAcc_AI_assms]:
  assumes x: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  assumes y: "\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb"
  shows      "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp elim!: rsubst[where P=P])
  apply (rule all_ext;
         clarsimp simp: state_hyp_refs_of_def hyp_refs_of_def tcb_hyp_refs_def get_tcb_def x y[simplified tcb_arch_ref_def])
  done

lemma mab_pb [simp]:
  "msg_align_bits \<le> pageBits"
  unfolding msg_align_bits pageBits_def by simp

lemma mab_wb [simp]:
  "msg_align_bits < word_bits"
  unfolding msg_align_bits word_bits_conv by simp


lemma get_cap_valid_ipc [TcbAcc_AI_assms]:
  "\<lbrace>valid_objs and obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_ipc_buffer tcb = v) t\<rbrace>
     get_cap (t, tcb_cnode_index 4)
   \<lbrace>\<lambda>rv s. valid_ipc_buffer_cap rv v\<rbrace>"
  apply (wp get_cap_wp)
  apply clarsimp
  apply (drule(1) cte_wp_tcb_cap_valid)
  apply (clarsimp simp add: tcb_cap_valid_def obj_at_def)
  apply (simp add: valid_ipc_buffer_cap_def mask_cap_def cap_rights_update_def
                   acap_rights_update_def is_tcb
            split: cap.split_asm arch_cap.split_asm)
  done



lemma pred_tcb_cap_wp_at [TcbAcc_AI_assms]:
  "\<lbrakk>pred_tcb_at proj P t s; valid_objs s;
    ref \<in> dom tcb_cap_cases;
    \<forall>cap. (pred_tcb_at proj P t s \<and> tcb_cap_valid cap (t, ref) s) \<longrightarrow> Q cap\<rbrakk> \<Longrightarrow>
   cte_wp_at Q (t, ref) s"
  apply (clarsimp simp: cte_wp_at_cases tcb_at_def dest!: get_tcb_SomeD)
  apply (rename_tac getF setF restr)
  apply (clarsimp simp: tcb_cap_valid_def pred_tcb_at_def obj_at_def)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp add: valid_obj_def valid_tcb_def)
  apply (erule_tac x="(getF, setF, restr)" in ballE)
   apply fastforce+
  done

lemma as_user_hyp_refs_of[wp, TcbAcc_AI_assms]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
     as_user t m
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wp as_user_wp_thread_set_helper
            thread_set_hyp_refs_trivial | simp)+
  done

lemmas sts_typ_ats = sts_typ_ats abs_atyp_at_lifts [OF set_thread_state_typ_at]

lemma arch_tcb_context_set_eq_AARCH64[TcbAcc_AI_assms]: "arch_tcb_context_set (arch_tcb_context_get t) t = t"
  unfolding arch_tcb_context_get_def arch_tcb_context_set_def
  by simp

lemma arch_tcb_context_get_eq_AARCH64[TcbAcc_AI_assms]: "arch_tcb_context_get (arch_tcb_context_set uc t) = uc"
  unfolding arch_tcb_context_get_def arch_tcb_context_set_def
  by simp

lemma tcb_context_update_aux: "arch_tcb_context_set (P (arch_tcb_context_get atcb)) atcb
                               = tcb_context_update (\<lambda>ctx. P ctx) atcb"
  by (simp add: arch_tcb_context_set_def arch_tcb_context_get_def)

lemma thread_set_valid_arch_state[TcbAcc_AI_assms]:
  "(\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb)
   \<Longrightarrow> thread_set f t \<lbrace> valid_arch_state \<rbrace>"
  by (wp valid_arch_state_lift_aobj_at_no_caps thread_set.aobj_at)

end

global_interpretation TcbAcc_AI?: TcbAcc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact TcbAcc_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma arch_thread_set_valid_idle[wp]:
  "\<lbrace>valid_idle and (\<lambda>s. t \<noteq> idle_thread s \<or> (\<forall>atcb. tcb_vcpu atcb = None \<longrightarrow> tcb_vcpu (f atcb) = None))\<rbrace>
   arch_thread_set f t
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wpsimp wp: arch_thread_set_valid_idle' simp: valid_arch_idle_def)

lemma arch_thread_set_if_live_then_nonz_cap_None[wp]:
  "arch_thread_set (tcb_vcpu_update Map.empty) t \<lbrace>if_live_then_nonz_cap\<rbrace>"
  by (wpsimp wp: arch_thread_set_if_live_then_nonz_cap' simp: hyp_live_def)

lemma arch_thread_set_if_live_then_nonz_cap_Some[wp]:
  "\<lbrace>(ex_nonz_cap_to t or obj_at live t) and if_live_then_nonz_cap\<rbrace>
   arch_thread_set (tcb_vcpu_update (\<lambda>_. Some vcp)) t
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_iflive)
  apply (clarsimp simp: ex_nonz_cap_to_def if_live_then_nonz_cap_def
                  dest!: get_tcb_SomeD)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (clarsimp simp: obj_at_def tcb_cap_cases_def)
  done

lemma arch_thread_set_valid_objs_vcpu_None[wp]:
  "arch_thread_set (tcb_vcpu_update Map.empty) t \<lbrace>valid_objs\<rbrace>"
  by (wpsimp wp: arch_thread_set_valid_objs' simp: valid_arch_tcb_def)

lemma arch_thread_set_valid_objs_vcpu_Some[wp]:
  "\<lbrace>valid_objs and vcpu_at vcpu\<rbrace> arch_thread_set (tcb_vcpu_update (\<lambda>_. Some vcpu)) t \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  by (wpsimp wp: arch_thread_set_valid_objs' simp: valid_arch_tcb_def)

lemma arch_thread_set_unlive_hyp[wp]:
  "\<lbrace>\<lambda>s. vr \<noteq> t \<longrightarrow> obj_at (Not \<circ> hyp_live) vr s\<rbrace>
   arch_thread_set (tcb_vcpu_update Map.empty) t
   \<lbrace>\<lambda>_. obj_at (Not \<circ> hyp_live) vr\<rbrace>"
  apply (wpsimp simp: arch_thread_set_def wp: set_object_wp)
  apply (clarsimp simp: obj_at_def hyp_live_def)
  done

lemma arch_thread_set_unlive0[wp]:
  "arch_thread_set (tcb_vcpu_update Map.empty) t \<lbrace>obj_at (Not \<circ> live0) vr\<rbrace>"
  apply (wpsimp simp: arch_thread_set_def wp: set_object_wp)
  apply (clarsimp simp: obj_at_def get_tcb_def split: kernel_object.splits)
  done

lemma arch_thread_set_unlive_other:
  "\<lbrace>\<lambda>s. vr \<noteq> t \<and> obj_at (Not \<circ> live) vr s\<rbrace>
   arch_thread_set (tcb_vcpu_update Map.empty) t
   \<lbrace>\<lambda>_. obj_at (Not \<circ> live) vr\<rbrace>"
  apply (wpsimp simp: arch_thread_set_def wp: set_object_wp)
  apply (clarsimp simp: obj_at_def)
  done

lemma arch_thread_set_vcpus_of[wp]:
  "arch_thread_set f t \<lbrace>\<lambda>s. P (vcpus_of s)\<rbrace>"
  apply (wp arch_thread_set_wp)
  apply (clarsimp simp: get_tcb_Some_ko_at)
  apply (erule rsubst[where P=P])
  apply (clarsimp simp: obj_at_def opt_map_def)
  done

end

end
