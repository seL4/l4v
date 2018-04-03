(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory PageTableDuplicates
imports Syscall_R
begin

context begin interpretation Arch . (*FIXME: arch_split*)


(* we need the following lemma in Syscall_R *)
crunch inv[wp]: getRegister "P"

lemma doMachineOp_ksPSpace_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksPSpace s)\<rbrace> doMachineOp f \<lbrace>\<lambda>ya s. P (ksPSpace s)\<rbrace>"
  by (simp add:doMachineOp_def split_def | wp)+

lemma getExtraCptrs_ksPSpace_inv[wp]:
  "\<lbrace>\<lambda>s. P (ksPSpace s)\<rbrace> getExtraCPtrs a i  \<lbrace>\<lambda>r s. P (ksPSpace s)\<rbrace>"
  apply (simp add:getExtraCPtrs_def)
  apply (rule hoare_pre)
  apply (wpc|simp|wp mapM_wp')+
  done

lemma koTypeOf_pte:
  "koTypeOf ko = ArchT PTET \<Longrightarrow> \<exists>pte. ko = KOArch (KOPTE pte)"
  "archTypeOf ako = PTET \<Longrightarrow> \<exists>pte. ako = KOPTE pte"
  apply (case_tac ko; simp)
  apply (rename_tac arch_kernel_object)
  apply (case_tac arch_kernel_object; simp)
  apply (case_tac ako; simp)
  done

lemma is_aligned_plus_bound:
  assumes al: "is_aligned p sz"
  assumes cmp: "sz \<le> lz"
  assumes b:  "b \<le> (2::machine_word) ^ sz - 1"
  assumes bound : "p < 2 ^ lz"
  assumes sz: "sz < word_bits"
  shows "p + b < 2 ^ lz"
  proof -
    have lower:"p + b \<le> p + (2 ^ sz - 1)"
      apply (rule word_plus_mono_right[OF b])
      apply (rule is_aligned_no_overflow'[OF al])
      done
    show ?thesis using bound sz
      apply -
      apply (rule le_less_trans[OF lower])
      apply (rule ccontr)
      apply (simp add:not_less)
      apply (drule neg_mask_mono_le[where n = sz])
      apply (subst (asm) is_aligned_neg_mask_eq)
       apply (rule is_aligned_weaken[OF is_aligned_triv cmp])
      apply (subst (asm) is_aligned_add_helper[THEN conjunct2,OF al])
       apply (simp add:word_bits_def)
      apply simp
    done
  qed

lemma page_table_at_pte_atD':
  "\<lbrakk>page_table_at' p s;is_aligned p' 3; p' && ~~ mask ptBits = p\<rbrakk> \<Longrightarrow> pte_at' p' s"
  apply (clarsimp simp:page_table_at'_def bit_simps)
  apply (drule_tac x = "p' && mask ptBits >> 3" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 9,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:ptBits_def mask_def pageBits_def bit_simps)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
   apply (simp add: is_aligned_andI1)
  apply (simp add:mask_out_sub_mask bit_simps)
  done

lemma page_directory_at_pde_atD':
  "\<lbrakk>page_directory_at' p s;is_aligned p' 3; p' && ~~ mask pdBits = p\<rbrakk> \<Longrightarrow> pde_at' p' s"
  apply (clarsimp simp:page_directory_at'_def bit_simps)
  apply (drule_tac x = "p' && mask pdBits >> 3" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 9,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:pdBits_def mask_def pageBits_def bit_simps)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
   apply (simp add: is_aligned_andI1)
  apply (simp add:mask_out_sub_mask bit_simps)
  done

lemma pd_pointer_table_at_pdpte_atD':
  "\<lbrakk>pd_pointer_table_at' p s;is_aligned p' 3; p' && ~~ mask pdptBits = p\<rbrakk> \<Longrightarrow> pdpte_at' p' s"
  apply (clarsimp simp:pd_pointer_table_at'_def bit_simps)
  apply (drule_tac x = "p' && mask pdBits >> 3" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 9,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:pdBits_def mask_def pageBits_def bit_simps)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
   apply (simp add: is_aligned_andI1)
  apply (simp add:mask_out_sub_mask bit_simps)
  done

lemma page_map_l4_at_pml4e_atD':
  "\<lbrakk>page_map_l4_at' p s;is_aligned p' 3; p' && ~~ mask pml4Bits = p\<rbrakk> \<Longrightarrow> pml4e_at' p' s"
  apply (clarsimp simp:page_map_l4_at'_def bit_simps)
  apply (drule_tac x = "p' && mask pdBits >> 3" in spec)
  apply (erule impE)
   apply (rule shiftr_less_t2n[where m = 9,simplified])
   apply (rule le_less_trans[OF word_and_le1])
   apply (simp add:pdBits_def mask_def pageBits_def bit_simps)
  apply (subst (asm) shiftr_shiftl1)
   apply simp
  apply simp
  apply (subst (asm) is_aligned_neg_mask_eq[where n = 3])
   apply (simp add: is_aligned_andI1)
  apply (simp add:mask_out_sub_mask bit_simps)
  done

lemma foldr_data_map_insert[simp]:
 "foldr (\<lambda>addr map a. if a = addr then Some b else map a)
 = foldr (\<lambda>addr. data_map_insert addr b)"
  apply (rule ext)+
  apply (simp add:data_map_insert_def[abs_def] fun_upd_def)
  done

lemma in_new_cap_addrs_aligned:
  "is_aligned ptr 3 \<Longrightarrow> p \<in> set (new_cap_addrs (2 ^ us) ptr ko) \<Longrightarrow> is_aligned p 3"
  apply (clarsimp simp:new_cap_addrs_def image_def)
  apply (erule aligned_add_aligned)
    apply (rule is_aligned_weaken[OF is_aligned_shiftl_self])
    apply (case_tac ko,simp_all add:objBits_simps' word_bits_def
       pageBits_def archObjSize_def split:arch_kernel_object.splits)
  done

lemma none_in_new_cap_addrs:
  "\<lbrakk>is_aligned ptr (objBitsKO obj + us); objBitsKO obj + us < word_bits;
  pspace_no_overlap' ptr (objBitsKO obj + us) s;
  pspace_aligned' s\<rbrakk>
  \<Longrightarrow> \<forall>x\<in>set (new_cap_addrs (2^us) ptr obj). ksPSpace s x = None"
  apply (rule ccontr,clarsimp)
  apply (drule not_in_new_cap_addrs[rotated - 1])
   apply simp+
  done

crunch arch_inv[wp]: createNewObjects "\<lambda>s. P (x64KSSKIMPML4 (ksArchState s))"
  (simp: crunch_simps zipWithM_x_mapM wp: crunch_wps hoare_unless_wp)

crunch arch_inv[wp]: resetUntypedCap "\<lambda>s. P (ksArchState s)"
  (simp: crunch_simps
     wp: hoare_drop_imps hoare_unless_wp mapME_x_inv_wp
         preemptionPoint_inv
    ignore:freeMemory forME_x)

lemma is_aligned_x64KSGlobalPD:
  "valid_arch_state' s
    \<Longrightarrow> is_aligned (x64KSSKIMPML4 (ksArchState s)) pml4Bits"
  by (clarsimp simp: valid_arch_state'_def page_map_l4_at'_def)

lemma new_CapTable_bound:
  "range_cover (ptr :: obj_ref) sz (APIType_capBits tp us) n
    \<Longrightarrow> tp = APIObjectType ArchTypes_H.apiobject_type.CapTableObject \<longrightarrow> us < 61"
  apply (frule range_cover.sz)
  apply (drule range_cover.sz(2))
  apply (clarsimp simp:APIType_capBits_def objBits_simps' word_bits_def)
  done

lemma mapM_x_mapM_valid:
  "\<lbrace> P \<rbrace> mapM_x f xs \<lbrace>\<lambda>r. Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace>mapM f xs \<lbrace>\<lambda>r. Q\<rbrace>"
  apply (simp add:NonDetMonadLemmaBucket.mapM_x_mapM)
  apply (clarsimp simp:valid_def return_def bind_def)
  apply (drule spec)
  apply (erule impE)
   apply simp
  apply (drule(1) bspec)
  apply fastforce
  done

crunch valid_arch_state'[wp]:
 flushTable valid_arch_state'
  (wp: crunch_wps  simp: crunch_simps unless_def
    ignore:getObject updateObject setObject)

declare withoutPreemption_lift [wp del]

crunch valid_cap'[wp]:
  isFinalCapability "\<lambda>s. valid_cap' cap s"
  (wp: crunch_wps filterM_preserved simp: crunch_simps unless_def
    ignore:getObject setObject)

lemma getObject_pte_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pte. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def)
  done

lemma getObject_pde_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pde. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def)
  done

lemma getObject_pdpte_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pdpte. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def)
  done

lemma getObject_pml4e_sp:
  "\<lbrace>P\<rbrace> getObject r \<lbrace>\<lambda>t::pml4e. P and ko_at' t r\<rbrace>"
  apply (wp getObject_ko_at)
  apply (auto simp: objBits_simps archObjSize_def)
  done

crunch inv [wp]: getThreadBufferSlot P
  (wp: crunch_wps)

end

end
