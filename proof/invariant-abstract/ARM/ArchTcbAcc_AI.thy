(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTcbAcc_AI
imports "../CSpace_AI"
begin
context Arch begin global_naming ARM

lemmas cap_master_cap_simps = 
  cap_master_cap_def[simplified cap_master_arch_cap_def, split_simps cap.split arch_cap.split]

lemma cap_master_cap_arch_eqDs:
  "cap_master_cap cap = cap.ArchObjectCap (arch_cap.PageCap ref rghts sz mapdata)
     \<Longrightarrow> rghts = UNIV \<and> mapdata = None
          \<and> (\<exists>rghts mapdata. cap = cap.ArchObjectCap (arch_cap.PageCap ref rghts sz mapdata))"
  "cap_master_cap cap = cap.ArchObjectCap arch_cap.ASIDControlCap
     \<Longrightarrow> cap = cap.ArchObjectCap arch_cap.ASIDControlCap"
  "cap_master_cap cap = cap.ArchObjectCap (arch_cap.ASIDPoolCap pool asid)
     \<Longrightarrow> asid = 0 \<and> (\<exists>asid. cap = cap.ArchObjectCap (arch_cap.ASIDPoolCap pool asid))"
  "cap_master_cap cap = cap.ArchObjectCap (arch_cap.PageTableCap ptr data)
     \<Longrightarrow> data = None \<and> (\<exists>data. cap = cap.ArchObjectCap (arch_cap.PageTableCap ptr data))"
  "cap_master_cap cap = cap.ArchObjectCap (arch_cap.PageDirectoryCap ptr data2)
     \<Longrightarrow> data2 = None \<and> (\<exists>data2. cap = cap.ArchObjectCap (arch_cap.PageDirectoryCap ptr data2))"
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
  "\<lbrakk> cap_master_cap c = cap_master_cap c'; is_arch_cap c \<rbrakk> \<Longrightarrow>
  tcb_cap_valid c p s = tcb_cap_valid c' p s"
  by (simp add: cap_master_cap_def tcb_cap_valid_def tcb_cap_cases_def
                   valid_ipc_buffer_cap_def  is_cap_simps
            split: option.splits cap.splits arch_cap.splits
                   Structures_A.thread_state.splits)

lemma storeWord_invs[wp]:
  "\<lbrace>in_user_frame p and invs\<rbrace> do_machine_op (storeWord p w) \<lbrace>\<lambda>rv. invs\<rbrace>"
proof -
  have aligned_offset_ignore:
    "\<And>l sz. l<4 \<Longrightarrow> p && mask 2 = 0 \<Longrightarrow>
       p+l && ~~ mask (pageBitsForSize sz) = p && ~~ mask (pageBitsForSize sz)"
  proof -
    fix l sz
    assume al: "p && mask 2 = 0"
    assume "(l::word32) < 4" hence less: "l<2^2" by simp
    have le: "2 \<le> pageBitsForSize sz" by (case_tac sz, simp_all)
    show "?thesis l sz"
      by (rule is_aligned_add_helper[simplified is_aligned_mask,
          THEN conjunct2, THEN mask_out_first_mask_some,
          where n=2, OF al less le])
  qed

  show ?thesis
    apply (wp dmo_invs)
    apply (clarsimp simp: storeWord_def invs_def valid_state_def)
    apply (fastforce simp: valid_machine_state_def in_user_frame_def
               assert_def simpler_modify_def fail_def bind_def return_def
               pageBits_def aligned_offset_ignore
             split: split_if_asm)
    done
qed

end
end