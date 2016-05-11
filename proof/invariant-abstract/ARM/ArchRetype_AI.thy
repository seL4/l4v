(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(*
 Arch-specific retype invariants
*)

theory ArchRetype_AI
imports "../Retype_AI"
begin



context Arch begin

named_theorems Retype_AI_asms

lemma clearMemoryVM_return[simp, Retype_AI_asms]:
  "clearMemoryVM a b = return ()"
  by (simp add: clearMemoryVM_def)

end


interpretation Retype_AI?: Retype_AI 
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales, fact Retype_AI_asms)?)
  qed

context Arch begin global_naming ARM

lemma retype_region_plain_invs:
  "\<lbrace>invs and caps_no_overlap ptr sz and pspace_no_overlap ptr sz 
      and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
      and region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1}
      and K (ty = Structures_A.CapTableObject \<longrightarrow> 0 < us)
      and K (range_cover ptr sz (obj_bits_api ty us) n)
      and K (ty \<noteq> ArchObject PageDirectoryObj)\<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post[OF retype_region_post_retype_invs])
  apply (simp add: post_retype_invs_def)
  done

lemma storeWord_um_eq_0:
  "\<lbrace>\<lambda>m. underlying_memory m p = 0\<rbrace>
    storeWord x 0
   \<lbrace>\<lambda>_ m. underlying_memory m p = 0\<rbrace>"
  by (simp add: storeWord_def word_rsplit_0 | wp)+

lemma clearMemory_um_eq_0:
  "\<lbrace>\<lambda>m. underlying_memory m p = 0\<rbrace>
    clearMemory ptr bits
   \<lbrace>\<lambda>_ m. underlying_memory m p = 0\<rbrace>"
  apply (clarsimp simp: clearMemory_def)
  apply (wp mapM_x_wp_inv | simp)+
  apply (rule hoare_pre)
   apply (wp hoare_drop_imps storeWord_um_eq_0)
  apply (fastforce simp: ignore_failure_def split: split_if_asm)
  done

lemma cleanCacheRange_PoU_um_inv[wp]:
  "\<lbrace>\<lambda>m. P (underlying_memory m)\<rbrace>
    cleanCacheRange_PoU ptr w p
   \<lbrace>\<lambda>_ m. P (underlying_memory m)\<rbrace>"
  by (simp add: cleanCacheRange_PoU_def cleanByVA_PoU_def machine_op_lift_def machine_rest_lift_def
                split_def | wp)+
end

end