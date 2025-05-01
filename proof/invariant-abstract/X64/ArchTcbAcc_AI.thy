(*
 * Copyright 2014, General Dynamics C4 Systems
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
  "cap_master_cap cap = ArchObjectCap (ASIDPoolCap pool asid)
     \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap = ArchObjectCap (ASIDPoolCap pool asid))"
  "cap_master_cap cap = ArchObjectCap ASIDControlCap
     \<Longrightarrow> cap = ArchObjectCap ASIDControlCap"
  "cap_master_cap cap = ArchObjectCap (IOPortCap first_port last_port)
     \<Longrightarrow> cap = ArchObjectCap (IOPortCap first_port last_port)"
  "cap_master_cap cap = ArchObjectCap (PageCap dev ref rghts maptype sz mapdata)
     \<Longrightarrow> maptype = VMNoMap \<and> rghts = UNIV \<and> mapdata = None
          \<and> (\<exists>maptype rghts mapdata. cap = ArchObjectCap (PageCap dev ref rghts maptype sz mapdata))"
  "cap_master_cap cap = ArchObjectCap (PageTableCap ptr data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = ArchObjectCap (PageTableCap ptr data))"
  "cap_master_cap cap = ArchObjectCap (PageDirectoryCap ptr data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = ArchObjectCap (PageDirectoryCap ptr data))"
  "cap_master_cap cap = ArchObjectCap (PDPointerTableCap ptr data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = ArchObjectCap (PDPointerTableCap ptr data))"
  "cap_master_cap cap = ArchObjectCap (PML4Cap ptr data2)
     \<Longrightarrow> data2 = None \<and> (\<exists>data2. cap = ArchObjectCap (PML4Cap ptr data2))"
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
                 is_nondevice_page_cap_simps is_nondevice_page_cap_arch_def
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
  by (auto simp: valid_ipc_buffer_cap_def case_bool_If
          split: cap.split arch_cap.split)

lemma thread_set_hyp_refs_trivial [TcbAcc_AI_assms]:
  assumes x: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  assumes y: "\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb"
  shows      "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_wp)
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

lemma as_user_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
     as_user t m
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (wp as_user_wp_thread_set_helper
            thread_set_hyp_refs_trivial | simp)+
  done

lemmas sts_typ_ats = sts_typ_ats abs_atyp_at_lifts [OF set_thread_state_typ_at]

lemma arch_tcb_context_set_eq[TcbAcc_AI_assms]:
  "arch_tcb_context_set (arch_tcb_context_get t) t = t"
  unfolding arch_tcb_context_get_def arch_tcb_context_set_def
  by simp

lemma arch_tcb_context_get_eq[TcbAcc_AI_assms]:
  "arch_tcb_context_get (arch_tcb_context_set uc t) = uc"
  unfolding arch_tcb_context_get_def arch_tcb_context_set_def
  by simp

lemma tcb_context_update_aux: "arch_tcb_context_set (P (arch_tcb_context_get atcb)) atcb
                               = tcb_context_update (\<lambda>ctx. P ctx) atcb"
  by (simp add: arch_tcb_context_set_def arch_tcb_context_get_def)

crunch set_thread_state, set_bound_notification
  for valid_ioports[wp]: valid_ioports
  (wp: valid_ioports_lift)

lemma thread_set_ioports:
  assumes y: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows
  "\<lbrace>valid_ioports\<rbrace> thread_set f t \<lbrace>\<lambda>rv. valid_ioports\<rbrace>"
  by (wpsimp wp: valid_ioports_lift thread_set_caps_of_state_trivial y)

lemma thread_set_valid_arch_state[TcbAcc_AI_assms]:
  "(\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb)
   \<Longrightarrow> thread_set f t \<lbrace> valid_arch_state \<rbrace>"
  by (wp valid_arch_state_lift_ioports_aobj_at thread_set_ioports thread_set.aobj_at
         thread_set_caps_of_state_trivial
      | simp add: valid_arch_state_def)+

end

global_interpretation TcbAcc_AI?: TcbAcc_AI
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (unfold_locales; (fact TcbAcc_AI_assms)?)
  qed

context Arch begin arch_global_naming

lemma arch_thread_set_valid_idle[wp]:
  "arch_thread_set f t \<lbrace>valid_idle\<rbrace>"
  by (wpsimp wp: arch_thread_set_valid_idle' simp: valid_arch_idle_def)

lemma arch_thread_set_cur_fpu_False_if_live_then_nonz_cap[wp]:
  "arch_thread_set (tcb_cur_fpu_update \<bottom>) t \<lbrace>if_live_then_nonz_cap\<rbrace>"
  by (wpsimp wp: arch_thread_set_if_live_then_nonz_cap_unchanged simp: hyp_live_def arch_tcb_live_def)

lemmas arch_thread_set_cur_fpu_True_if_live_then_nonz_cap[wp]
  = arch_thread_set_if_live_then_nonz_cap'[where f="tcb_cur_fpu_update \<top>"]

lemma arch_thread_set_valid_objs_cur_fpu[wp]:
  "arch_thread_set (tcb_cur_fpu_update f) t \<lbrace>valid_objs\<rbrace>"
  by (wpsimp wp: arch_thread_set_valid_objs')

lemma arch_thread_set_cur_fpu_hyp_live[wp]:
  "arch_thread_set (tcb_cur_fpu_update f) t \<lbrace>obj_at (Not \<circ> hyp_live) vr\<rbrace>"
  apply (wpsimp wp: arch_thread_set_wp)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: get_tcb_def hyp_live_def split: kernel_object.splits)
  done

lemma arch_thread_set_unlive0[wp]:
  "arch_thread_set f t \<lbrace>obj_at (Not \<circ> live0) vr\<rbrace>"
  apply (wpsimp simp: arch_thread_set_def wp: set_object_wp)
  apply (clarsimp simp: obj_at_def get_tcb_def split: kernel_object.splits)
  done

lemma hyp_refs_update_some_tcb:
  "\<lbrakk>kheap s v = Some (TCB tcb); hyp_refs_of (TCB tcb) = hyp_refs_of (TCB (f tcb))\<rbrakk>
  \<Longrightarrow> P (state_hyp_refs_of (s\<lparr>kheap := (kheap s)(v \<mapsto> TCB (f tcb))\<rparr>)) = P (state_hyp_refs_of s)"
  apply (rule_tac f=P in arg_cong)
  apply (rule all_ext)
  apply (clarsimp simp: state_hyp_refs_of_def)
  done

lemma arch_thread_set_sym_refs_hyp':
  "\<lbrakk>\<And>tcb. hyp_refs_of (TCB tcb) = hyp_refs_of (TCB (tcb_arch_update f tcb))\<rbrakk>
   \<Longrightarrow> arch_thread_set f t \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply dest!: get_tcb_SomeD)
  apply (subst get_tcb_rev, assumption, subst option.sel)+
  apply (subst arch_tcb_update_aux3)
  apply (subst hyp_refs_update_some_tcb[where P=P and f="tcb_arch_update f"])
    apply assumption
   apply (clarsimp simp: refs_of_def)
  apply assumption
  done

lemma arch_thread_set_cur_fpu_sym_refs_hyp[wp]:
  "arch_thread_set (tcb_cur_fpu_update f) t \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  by (wpsimp wp: arch_thread_set_sym_refs_hyp')

end

end
