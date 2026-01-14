(*
 * Copyright 2014, General Dynamics C4 Systems
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Generic interface for lemmas on arch get/set object etc *)

theory ArchAcc_R
imports SubMonad_R
begin

arch_requalify_facts
  clearMemory_um_eq_0

unbundle l4v_word_context

declare in_set_zip_refl[simp]

lemmas [wp] = setObject_pspace_in_kernel_mappings'

lemma fun_all: "f = f' \<Longrightarrow> (\<forall>s. f s \<longrightarrow> f' s)"
 by simp

lemma distrib_imp:
  "P \<longrightarrow> Q \<and> Q' \<Longrightarrow> ((P \<longrightarrow> Q) \<Longrightarrow> (P \<longrightarrow> Q') \<Longrightarrow> R) \<Longrightarrow> R"
 by simp

method def_to_elim = (drule meta_eq_to_obj_eq, drule fun_all, elim allE, elim distrib_imp)
method simp_to_elim = (drule fun_all, elim allE impE)

crunch headM
  for inv[wp]: P
crunch tailM
  for inv[wp]: P

lemma cte_map_in_cnode1:
  "\<lbrakk> x \<le> x + 2 ^ (cte_level_bits + length y) - 1 \<rbrakk> \<Longrightarrow> x \<le> cte_map (x, y)"
  apply (simp add: cte_map_def)
  apply (rule word_plus_mono_right2[where b="mask (cte_level_bits + length y)"])
   apply (simp add: mask_def add_diff_eq)
  apply (rule leq_high_bits_shiftr_low_bits_leq_bits)
  apply (rule of_bl_max)
  done

crunch setIRQState
  for cte_wp_at'[wp]: "\<lambda>s. P (cte_wp_at' P' p s)"

crunch getIRQSlot
  for inv[wp]: "P"

lemma clearMemory_vms':
  "valid_machine_state' s \<Longrightarrow>
   \<forall>x\<in>fst (clearMemory ptr bits (ksMachineState s)).
      valid_machine_state' (s\<lparr>ksMachineState := snd x\<rparr>)"
  apply (clarsimp simp: valid_machine_state'_def
                        disj_commute[of "pointerInUserData p s" for p s])
  apply (drule_tac x=p in spec, simp)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = 0"
         in use_valid[where P=P and Q="\<lambda>_. P" for P], simp_all)
  apply (rule clearMemory_um_eq_0)
  done

lemma dmo_clearMemory_invs'[wp]:
  "\<lbrace>invs'\<rbrace> doMachineOp (clearMemory w sz) \<lbrace>\<lambda>_. invs'\<rbrace>"
  apply (simp add: doMachineOp_def split_def)
  apply wp
  apply (clarsimp simp: invs'_def dmo_clearMemory_invs')
  apply (rule conjI)
   apply (simp add: valid_irq_masks'_def, elim allEI, clarsimp)
   apply (drule use_valid)
     apply (rule no_irq_clearMemory[simplified no_irq_def, rule_format])
    apply simp_all
  apply (drule clearMemory_vms')
  apply fastforce
  done

locale ArchAcc_R =
  assumes arch_cap_rights_update:
    "\<And>c c' msk.
     acap_relation c c' \<Longrightarrow>
     cap_relation (cap.ArchObjectCap (acap_rights_update (acap_rights c \<inter> msk) c))
                  (Arch.maskCapRights (rights_mask_map msk) c')"

end
