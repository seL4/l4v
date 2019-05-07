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

lemma foldr_data_map_insert[simp]:
 "foldr (\<lambda>addr map a. if a = addr then Some b else map a)
 = foldr (\<lambda>addr. data_map_insert addr b)"
  apply (rule ext)+
  apply (simp add:data_map_insert_def[abs_def] fun_upd_def)
  done

crunch arch_inv[wp]: createNewObjects "\<lambda>s. P (x64KSSKIMPML4 (ksArchState s))"
  (simp: crunch_simps zipWithM_x_mapM wp: crunch_wps hoare_unless_wp)

crunch arch_inv[wp]: resetUntypedCap "\<lambda>s. P (ksArchState s)"
  (simp: crunch_simps
     wp: hoare_drop_imps hoare_unless_wp mapME_x_inv_wp
         preemptionPoint_inv
    ignore:freeMemory forME_x)

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

crunch inv [wp]: getThreadBufferSlot P
  (wp: crunch_wps)

end

end
