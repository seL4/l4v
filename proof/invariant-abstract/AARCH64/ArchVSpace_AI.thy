(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
AARCH64-specific VSpace invariants
*)

theory ArchVSpace_AI
imports VSpacePre_AI
begin

context Arch begin global_naming AARCH64

sublocale
  set_vcpu: non_vspace_non_cap_non_mem_op "set_vcpu p vcpu" +
  get_vcpu: non_vspace_non_cap_non_mem_op "get_vcpu p"
  apply unfold_locales
  unfolding set_vcpu_def get_vcpu_def
  apply (wpsimp wp: set_object_non_pagetable[THEN hoare_set_object_weaken_pre] get_object_wp
                    set_object_caps_of_state[THEN hoare_set_object_weaken_pre] |
         clarsimp simp: is_tcb_def is_cap_table_def obj_at_def a_type_def
                 split: if_splits kernel_object.splits
                        arch_kernel_obj.splits)+
  done

crunch inv [wp]: get_vcpu "P"

lemma set_vcpu_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wpsimp wp: set_object_typ_at)
  done

lemma modify_obj_at : "\<lbrakk>\<forall>s. kheap s p = kheap (f s) p\<rbrakk> \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> modify f \<lbrace> \<lambda>rv s. P (obj_at P' p s)\<rbrace>"
  by (wpsimp simp: obj_at_def)

sublocale
  vcpu_disable: non_vspace_non_cap_op "vcpu_disable vcpu" +
  vcpu_enable: non_vspace_non_cap_op "vcpu_enable p" +
  vcpu_restore: non_vspace_non_cap_op "vcpu_restore p" +
  vcpu_save: non_vspace_non_cap_op "vcpu_save vcpu'"
  apply unfold_locales
  unfolding vcpu_disable_def vcpu_enable_def vcpu_restore_def vcpu_save_def
  by (wpsimp wp: set_vcpu.vsobj_at get_vcpu.vsobj_at mapM_wp mapM_x_wp
             simp: vcpu_update_def vgic_update_def vcpu_save_reg_def vcpu_restore_reg_def
                   vcpu_restore_reg_range_def vcpu_save_reg_range_def vgic_update_lr_def
                   save_virt_timer_def vcpu_write_reg_def restore_virt_timer_def
                   vcpu_read_reg_def is_irq_active_def get_irq_state_def
         | assumption)+

crunches
  vcpu_read_reg, vcpu_write_reg, vcpu_disable, vcpu_save, vcpu_enable, vcpu_restore,
  read_vcpu_register, write_vcpu_register, vcpu_switch
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: assertE_def crunch_simps wp: crunch_wps ignore: do_machine_op)

crunches vcpu_read_reg
  for inv[wp]: P

lemma pspace_in_kernel_window_set_vcpu[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_vcpu p vcpu \<lbrace>\<lambda>_.pspace_in_kernel_window\<rbrace>"
  by (rule pspace_in_kernel_window_atyp_lift, wp+)

crunch pspace_in_kernel_window[wp]: vcpu_switch "pspace_in_kernel_window"
  (simp: Metis.not_atomize crunch_simps a_type_def when_def
     wp: crunch_wps ignore: do_machine_op)

lemma find_vspace_for_asid_wp[wp]:
  "\<lbrace>\<lambda>s. (vspace_for_asid asid s = None \<longrightarrow> E InvalidRoot s) \<and>
        (\<forall>pt. vspace_for_asid asid s = Some pt \<longrightarrow> Q pt s) \<rbrace>
   find_vspace_for_asid asid \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding find_vspace_for_asid_def
  by wpsimp

crunch pspace_in_kernel_window[wp]: perform_page_invocation "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps)

lemma asid_word_bits [simp]: "asid_bits < word_bits"
  by (simp add: asid_bits_def word_bits_def)

lemma vspace_at_asid_vs_lookup:
  "vspace_at_asid asid pt s \<Longrightarrow>
   vs_lookup_table max_pt_level asid 0 s = Some (max_pt_level, pt)"
  by (fastforce simp: vs_lookup_table_def vspace_at_asid_def entry_for_asid_def
                      vspace_for_pool_def vspace_for_asid_def in_omonad)

lemma pt_at_asid_unique:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid' pt s;
     unique_table_refs s;
     valid_vs_lookup s; valid_vspace_objs s; valid_asid_table s;
     pspace_aligned s; valid_caps (caps_of_state s) s \<rbrakk>
       \<Longrightarrow> asid = asid'"
  by (drule vspace_at_asid_vs_lookup)+ (drule (1) unique_vs_lookup_table; simp)

lemma pt_at_asid_unique2:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid pt' s \<rbrakk> \<Longrightarrow> pt = pt'"
  by (clarsimp simp: vspace_at_asid_def)

lemmas ackInterrupt_irq_masks = no_irq[OF no_irq_ackInterrupt]

lemma ucast_ucast_low_bits:
  fixes x :: machine_word
  shows "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> ucast (ucast x:: asid_low_index) = x"
  apply (simp add: ucast_ucast_mask)
  apply (rule less_mask_eq)
  apply (subst (asm) word_less_sub_le)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_low_bits_def)
  done

lemma asid_high_bits_of_or:
  "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> asid_high_bits_of (base || x) = asid_high_bits_of base"
  apply (rule word_eqI)
  apply (drule le_2p_upper_bits)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_high_bits_of_def word_size nth_ucast nth_shiftr asid_low_bits_def word_bits_def)
  done

lemma vs_lookup_clear_asid_table:
  "vs_lookup_table bot_level asid vref (s\<lparr>arch_state := arch_state s \<lparr>arm_asid_table :=
                                            (asid_table s) (pptr := None)\<rparr>\<rparr>)
     = Some (level, p)
   \<Longrightarrow> vs_lookup_table bot_level asid vref s = Some (level, p)"
  by (fastforce simp: vs_lookup_table_def in_omonad pool_for_asid_def split: if_split_asm)

lemma vs_lookup_target_clear_asid_table:
  "vs_lookup_target bot_level asid vref (s\<lparr>arch_state := arch_state s \<lparr>arm_asid_table :=
                                            (asid_table s) (pptr := None)\<rparr>\<rparr>)
     = Some (level, p)
  \<Longrightarrow> vs_lookup_target bot_level asid vref s = Some (level, p)"
  apply (clarsimp simp: vs_lookup_target_def in_omonad vs_lookup_slot_def split: if_split_asm)
   apply (fastforce dest!: vs_lookup_clear_asid_table)
  apply (erule disjE, fastforce dest!: vs_lookup_clear_asid_table)
  apply clarify
  apply (drule vs_lookup_clear_asid_table)
  apply simp
  apply blast
  done

lemma vmid_for_asid_unmap_pool:
  "\<forall>asid_low. vmid_for_asid_2 (asid_of asid_high asid_low) table pools = None \<Longrightarrow>
   vmid_for_asid_2 asid (table(asid_high := None)) pools = vmid_for_asid_2 asid table pools"
  unfolding vmid_for_asid_2_def
  by (clarsimp simp: obind_def entry_for_pool_def split: option.splits)

lemma valid_arch_state_unmap_strg:
  "valid_arch_state s \<and> (\<forall>asid_low. vmid_for_asid s (asid_of asid_high asid_low) = None) \<longrightarrow>
   valid_arch_state(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (asid_table s)(asid_high := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def valid_global_arch_objs_def)
  apply (rule conjI)
   apply (clarsimp simp add: ran_def)
   apply blast
  apply (clarsimp simp: inj_on_def  vmid_inv_def is_inv_def vmid_for_asid_unmap_pool)
  done

lemma valid_vspace_objs_unmap_strg:
  "valid_vspace_objs s \<longrightarrow>
   valid_vspace_objs(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (asid_table s)(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vspace_objs_def)
  apply (blast dest: vs_lookup_clear_asid_table)
  done


lemma valid_vs_lookup_unmap_strg:
  "valid_vs_lookup s \<longrightarrow>
   valid_vs_lookup(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (asid_table s)(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vs_lookup_def)
  apply (blast dest: vs_lookup_target_clear_asid_table)
  done


lemma asid_high_bits_shl:
  "is_aligned base asid_low_bits \<Longrightarrow> ucast (asid_high_bits_of base) << asid_low_bits = base"
  unfolding asid_high_bits_of_def asid_low_bits_def is_aligned_mask
  by word_eqI_solve

lemma valid_asid_map_unmap:
  "valid_asid_map s \<and> is_aligned base asid_low_bits \<longrightarrow>
   valid_asid_map(s\<lparr>arch_state := arch_state s\<lparr>arm_asid_table := (asid_table s)(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  by (clarsimp simp: valid_asid_map_def)

lemma asid_low_bits_word_bits:
  "asid_low_bits < word_bits"
  by (simp add: asid_low_bits_def word_bits_def)

lemma valid_vs_lookup_arch_update:
  "arm_asid_table (f (arch_state s)) = asid_table s \<and>
   arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
     \<Longrightarrow> valid_vs_lookup (arch_state_update f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def)

lemma set_vcpu_pspace_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_aligned[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def get_object_def)
  done

crunches vcpu_save, vcpu_disable, set_vm_root
  for aligned [wp]: pspace_aligned
  (simp: crunch_simps wp: crunch_wps)

lemma set_vcpu_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_obj t (ArchObj (VCPU vcpu))\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_valid_objs)
  done

lemma get_vcpu_valid[wp]: "\<lbrace>valid_objs\<rbrace> get_vcpu t \<lbrace>\<lambda>r. valid_obj t (ArchObj (VCPU r))\<rbrace>"
  apply (wpsimp simp: get_vcpu_def)
  apply (erule valid_objsE; simp add: in_omonad)
  done

lemma get_vcpu_valid'[wp]:
  assumes "\<And>vcpu. valid_vcpu (P vcpu) = (valid_vcpu vcpu :: 'z::state_ext state \<Rightarrow> bool)"
  shows "\<lbrace>valid_objs::'z state \<Rightarrow> bool\<rbrace> get_vcpu t \<lbrace>\<lambda>r. valid_obj t (ArchObj (VCPU (P r)))\<rbrace>"
  apply (simp add: get_vcpu_def valid_obj_def[abs_def] assms)
  apply wpsimp
  apply (erule valid_objsE, simp add: in_omonad)
  apply (simp add: valid_obj_def)
  done

lemma valid_obj_valid_vcpu:
  "\<lbrace>valid_vcpu vcpu\<rbrace> F \<lbrace>\<lambda>r. valid_vcpu (P r vcpu)\<rbrace>
   \<Longrightarrow> \<lbrace>valid_obj t (ArchObj (VCPU vcpu))\<rbrace> F \<lbrace>\<lambda>r. valid_obj t (ArchObj (VCPU (P r vcpu)))\<rbrace>"
  by (simp add: valid_obj_def[abs_def])

lemma valid_vcpu_typ_at:
  "\<lbrakk>\<And>x. vcpu_tcb (P x vcpu) = vcpu_tcb vcpu;
    \<And>a. \<lbrace>typ_at ATCB a\<rbrace> F \<lbrace>\<lambda>r. typ_at ATCB a\<rbrace>\<rbrakk>
   \<Longrightarrow> \<lbrace>valid_vcpu vcpu\<rbrace> F \<lbrace>\<lambda>r. valid_vcpu (P r vcpu )\<rbrace>"
  by (wpsimp simp: valid_vcpu_def split: option.splits)

crunches vgic_update_lr, vcpu_write_reg, vcpu_save_reg, vcpu_disable, vcpu_restore,
          save_virt_timer, restore_virt_timer, vcpu_save, vcpu_switch, vcpu_save_reg_range
  for valid_objs[wp]: valid_objs
  (ignore: vcpu_update simp: vcpu_update_def valid_vcpu_def wp: crunch_wps)

lemma set_vcpu_wp:
  "\<lbrace>\<lambda>s. vcpu_at p s \<longrightarrow> Q (s\<lparr>kheap := kheap s(p \<mapsto> (ArchObj (VCPU vcpu))) \<rparr>) \<rbrace> set_vcpu p vcpu \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding set_vcpu_def
  apply (wp set_object_wp_strong)
  apply (clarsimp simp: obj_at_def split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma set_vcpu_vcpus_of[wp]:
  "\<lbrace>\<lambda>s. vcpus_of s p \<noteq> None \<longrightarrow> P (vcpus_of s (p \<mapsto> vcpu)) \<rbrace> set_vcpu p vcpu \<lbrace>\<lambda>_ s. P (vcpus_of s)\<rbrace>"
  by (wp set_vcpu_wp) (clarsimp simp: in_omonad obj_at_def)

lemma get_vcpu_wp:
  "\<lbrace>\<lambda>s. \<forall>v. vcpus_of s p = Some v \<longrightarrow> Q v s\<rbrace> get_vcpu p \<lbrace>Q\<rbrace>"
  by (wpsimp simp: get_vcpu_def)

lemma get_vcpu_wp_ko:
  "\<lbrace>\<lambda>s. \<forall>v. ko_at (ArchObj (VCPU v)) p s \<longrightarrow> Q v s\<rbrace> get_vcpu p \<lbrace>Q\<rbrace>"
  by (wpsimp wp: get_vcpu_wp simp: in_omonad obj_at_def)

lemma asid_pools_of_vcpu_None_upd_idem:
  "vcpu_at p s \<Longrightarrow> (asid_pools_of s)(p := None) = (asid_pools_of s)"
  by (clarsimp simp: opt_map_def obj_at_def)

lemma hyp_live_vcpu_tcb:
  "hyp_live (ArchObj (VCPU vcpu)) = (vcpu_tcb vcpu \<noteq> None)"
  by (clarsimp simp: hyp_live_def arch_live_def)

lemma pts_of_vcpu_None_upd_idem:
  "vcpu_at p s \<Longrightarrow> (pts_of s)(p := None) = pts_of s"
  by (clarsimp simp: opt_map_def obj_at_def)

lemma set_vcpu_valid_arch_state_hyp_live:
  "\<lbrace>valid_arch_state and K (hyp_live (ArchObj (VCPU vcpu)))\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (wpsimp wp: set_vcpu_wp simp: valid_arch_state_def)
  apply (clarsimp simp: asid_pools_of_vcpu_None_upd_idem vmid_inv_def)
  apply (rule conjI)
   apply (clarsimp simp: cur_vcpu_2_def hyp_live_vcpu_tcb in_opt_pred split: option.splits)
  apply (clarsimp simp: valid_global_arch_objs_def obj_at_def pts_of_vcpu_None_upd_idem)
  done

lemma set_vcpu_obj_at:
 "\<lbrace>\<lambda>s. obj_at P p s \<and> (p = t \<longrightarrow> P (ArchObj (VCPU vcpu)))\<rbrace>
    set_vcpu t vcpu \<lbrace>\<lambda>_. obj_at P p\<rbrace>"
 by (wpsimp wp: set_vcpu_wp simp: obj_at_def)

lemma vcpu_update_obj_at:
  "\<lbrace>\<lambda>s. obj_at P p s
        \<and> (p = vcpuptr \<longrightarrow> (\<forall>vcpu. vcpus_of s p = Some vcpu \<longrightarrow> P (ArchObj (VCPU (f vcpu))))) \<rbrace>
   vcpu_update vcpuptr f
   \<lbrace>\<lambda>_. obj_at P p\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_obj_at get_vcpu_wp)

lemma vcpu_update_vcpus_of[wp]:
  "\<lbrace>\<lambda>s. \<forall>vcpu. vcpus_of s vcpuptr = Some vcpu \<longrightarrow> P ((vcpus_of s) (vcpuptr \<mapsto> f vcpu)) \<rbrace>
   vcpu_update vcpuptr f
   \<lbrace>\<lambda>_ s. P (vcpus_of s)\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_vcpus_of get_vcpu_wp simp: fun_upd_def)

lemma hyp_live_vcpu_VGIC_update[simp]:
  "hyp_live (ArchObj (VCPU (vcpu_vgic_update f vcpu))) = hyp_live (ArchObj (VCPU vcpu))"
  by (simp add: hyp_live_def arch_live_def)

lemma hyp_live_vcpu_sctlr[simp]:
  "hyp_live (ArchObj (VCPU (vcpu_regs_update f vcpu))) = hyp_live (ArchObj (VCPU vcpu))"
  by (simp add: hyp_live_def arch_live_def)

lemmas vgic_update_obj_at =
  vcpu_update_obj_at[where f="\<lambda>vcpu. vcpu\<lparr>vcpu_vgic := f (vcpu_vgic vcpu)\<rparr>" for f,
                     folded vgic_update_def]

lemma vgic_update_hyp_live[wp]:
  "\<lbrace>obj_at hyp_live p\<rbrace> vgic_update vcpuptr f \<lbrace>\<lambda>_. obj_at hyp_live p\<rbrace>"
  by (wpsimp wp: vgic_update_obj_at simp: in_omonad obj_at_def)

lemma hyp_live_vcpu_vtimer_idem[simp]:
  "hyp_live (ArchObj (VCPU (vcpu_vtimer_update f vcpu))) = hyp_live (ArchObj (VCPU vcpu))"
  by (simp add: hyp_live_def arch_live_def)

lemma vcpu_update_vtimer_hyp_live[wp]:
  "vcpu_update vcpu_ptr (vcpu_vtimer_update f) \<lbrace> obj_at hyp_live p \<rbrace>"
  by (wpsimp wp: vcpu_update_obj_at simp: obj_at_def in_omonad)

crunches vcpu_save_reg, vcpu_write_reg
  for vcpu_hyp_live[wp]: "\<lambda>s. P (vcpu_hyp_live_of s)"
  (simp_del: fun_upd_apply simp: opt_map_upd_triv)

crunches vcpu_save_reg_range, vgic_update_lr, vcpu_disable, vcpu_save, vcpu_restore,
         save_virt_timer, restore_virt_timer
  for vcpu_hyp_live[wp]: "\<lambda>s. P (vcpu_hyp_live_of s)"
  (wp: vcpu_update_vtimer_hyp_live vcpu_update_obj_at crunch_wps
   simp_del: fun_upd_apply
   simp: opt_map_upd_triv)

(* FIXME: move *)
lemma obj_at_conj_distrib:
  "obj_at (P and Q) p = (obj_at P p and obj_at Q p)"
  by (rule ext) (auto simp: obj_at_def)

lemma set_vcpu_asid_pools_of[wp]:
  "set_vcpu p vcpu \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding set_vcpu_def set_object_def
  by (wpsimp wp: get_object_wp)
     (fastforce simp: obind_def opt_map_def obj_at_def split: option.split elim!: rsubst[where P=P])

lemma set_vcpu_pts_of[wp]:
  "set_vcpu p vcpu \<lbrace>\<lambda>s. P (pts_of s)\<rbrace>"
  unfolding set_vcpu_def set_object_def
  by (wpsimp wp: get_object_wp)
     (fastforce simp: obind_def opt_map_def obj_at_def split: option.split elim!: rsubst[where P=P])

crunches vgic_update, vcpu_restore_reg, save_virt_timer, vcpu_save_reg, save_virt_timer,
         restore_virt_timer
  for asid_pools_of[wp]: "\<lambda>s. P (asid_pools_of s)"
  and pts_of[wp]: "\<lambda>s. P (pts_of s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and valid_arch_state[wp]: valid_arch_state
  (wp: valid_arch_state_lift_arch)

crunches vcpu_disable, vcpu_restore, vcpu_save, vcpu_enable, vcpu_disable
  for valid_arch_state[wp]: valid_arch_state
  (wp: crunch_wps)

lemma get_vcpu_typ_at'[wp]:
  "\<lbrace>\<top>\<rbrace> get_vcpu vcpu \<lbrace>\<lambda>_. typ_at (AArch AVCPU) vcpu\<rbrace>"
  unfolding get_vcpu_def get_object_def
  by (wpsimp simp: obj_at_def in_omonad)

lemma vcpu_restore_typ_at'[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_restore vcpu \<lbrace>\<lambda>_. typ_at (AArch AVCPU) vcpu\<rbrace>"
  unfolding vcpu_restore_def by wp

lemma vcpu_enable_typ_at'[wp]:
  "\<lbrace>\<top>\<rbrace> vcpu_enable vcpu \<lbrace>\<lambda>_. typ_at (AArch AVCPU) vcpu\<rbrace>"
  unfolding vcpu_enable_def by wp

lemma valid_arch_state_update_vcpu:
  "\<lbrakk>valid_arch_state s ; typ_at (AArch AVCPU) t s; vcpu_hyp_live_of s t\<rbrakk>
   \<Longrightarrow> valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := Some (t, a)\<rparr>\<rparr>)"
  by (auto simp: valid_arch_state_def obj_at_def is_vcpu_def vmid_inv_def valid_global_arch_objs_def
                 cur_vcpu_2_def)

lemma vcpu_hyp_live_of_vcpu_at:
  "vcpu_hyp_live_of s p \<Longrightarrow> vcpu_at p s"
  by (clarsimp simp: in_omonad obj_at_def)

lemma vcpu_switch_valid_arch[wp]:
  "\<lbrace>valid_arch_state and (\<lambda>s. vcpu_opt \<noteq> None \<longrightarrow> vcpu_hyp_live_of s (the vcpu_opt))\<rbrace>
   vcpu_switch vcpu_opt
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding vcpu_switch_def
  apply (wpsimp | strengthen valid_arch_state_update_vcpu)+
  apply (auto simp: valid_arch_state_def cur_vcpu_def elim: vcpu_hyp_live_of_vcpu_at)
  done

lemma sym_refs_VCPU_hyp_live:
  assumes tcb: "ko_at (TCB tcb) t s"
  assumes vcpu: "tcb_vcpu (tcb_arch tcb) = Some v"
  assumes sym: "sym_refs (state_hyp_refs_of s)"
  shows "obj_at hyp_live v s"
proof -
  from tcb vcpu have "(v,TCBHypRef) \<in> state_hyp_refs_of s t"
    by (clarsimp simp: state_hyp_refs_of_def obj_at_def)
  with sym have "(t,HypTCBRef) \<in> state_hyp_refs_of s v"
    by (auto dest: sym_refsD)
  thus ?thesis
    by (clarsimp simp: state_hyp_refs_of_def obj_at_def hyp_live_def hyp_refs_of_def
                       tcb_vcpu_refs_def refs_of_ao_def arch_live_def vcpu_tcb_refs_def
                split: option.splits kernel_object.splits arch_kernel_obj.splits)
qed

definition valid_unmap :: "vmpage_size \<Rightarrow> asid * vspace_ref \<Rightarrow> bool" where
  "valid_unmap sz \<equiv> \<lambda>(asid, vptr). 0 < asid \<and> is_aligned vptr (pageBitsForSize sz)"

definition
  "parent_for_refs \<equiv> \<lambda>(_, slot, level) cap.
     \<exists>m. cap = ArchObjectCap (PageTableCap (table_base (level_type level) slot) level m) \<and> m \<noteq> None"

definition
  "same_ref \<equiv> \<lambda>(pte, slot, level) cap s.
     ((\<exists>p. pte_ref pte = Some p \<and> obj_refs cap = {p}) \<or> pte = InvalidPTE) \<and>
     (\<exists>asid vref. vs_cap_ref cap = Some (asid, vref_for_level vref level) \<and>
                  vs_lookup_slot level asid vref s = Some (level, slot) \<and>
                  vref \<in> user_region \<and> level \<le> max_pt_level)"

definition
  "valid_page_inv pg_inv \<equiv> case pg_inv of
    PageMap acap ptr m \<Rightarrow>
      cte_wp_at (is_arch_update (ArchObjectCap acap)) ptr
      and (cte_wp_at (\<lambda>c. vs_cap_ref c = None) ptr or (\<lambda>s. cte_wp_at (\<lambda>c. same_ref m c s) ptr s))
      and cte_wp_at is_frame_cap ptr
      and same_ref m (ArchObjectCap acap)
      and valid_slots m
      and valid_arch_cap acap
      and K (is_PagePTE (fst m) \<or> fst m = InvalidPTE)
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
      and K (valid_mapping_insert (level_type (snd (snd m))) (fst (snd m)) (fst m))
  | PageUnmap acap cslot \<Rightarrow>
     \<lambda>s. \<exists>dev r R sz m.
            acap = FrameCap r R sz dev m \<and>
            case_option True (valid_unmap sz) m \<and>
            cte_wp_at ((=) (ArchObjectCap acap)) cslot s \<and>
            valid_arch_cap acap s
  | PageGetAddr ptr \<Rightarrow> \<top>
  | PageFlush _ _ _ _ _ _ \<Rightarrow> \<top>"

definition
  "valid_pti pti \<equiv> case pti of
     PageTableMap acap cslot pte pt_slot level \<Rightarrow>
       pte_at level pt_slot and K (wellformed_pte pte \<and> is_PageTablePTE pte) and
       valid_arch_cap acap and
       cte_wp_at (\<lambda>c. is_arch_update (ArchObjectCap acap) c \<and> cap_asid c = None) cslot and
       invalid_pte_at level pt_slot and
       (\<lambda>s. \<exists>p' asid vref.
                vs_cap_ref_arch acap = Some (asid, vref_for_level vref level)
                \<and> vs_lookup_slot level asid vref s = Some (level, pt_slot)
                \<and> valid_pte level pte s
                \<and> pte_ref pte = Some p' \<and> obj_refs (ArchObjectCap acap) = {p'}
                \<and> (\<exists>ao. ko_at (ArchObj ao) p' s \<and> valid_vspace_obj (level-1) ao s)
                \<and> pts_of s p' = Some (empty_pt NormalPT_T)
                \<and> vref \<in> user_region) and
       K (is_PageTableCap acap \<and> cap_asid_arch acap \<noteq> None)
   | PageTableUnmap acap cslot \<Rightarrow>
       cte_wp_at ((=) (ArchObjectCap acap)) cslot
       and real_cte_at cslot
       and valid_arch_cap acap
       and is_final_cap' (ArchObjectCap acap)
       and K (is_PageTableCap acap \<and> acap_pt_type acap = NormalPT_T)
       and (\<lambda>s. \<forall>asid vref. vs_cap_ref_arch acap = Some (asid, vref) \<longrightarrow>
                            vspace_for_asid asid s \<noteq> aobj_ref acap)"

crunches unmap_page
  for aligned [wp]: pspace_aligned
  and "distinct" [wp]: pspace_distinct
  and valid_objs[wp]: valid_objs
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_cap_valid_slots[wp]:
  "set_cap cap p \<lbrace>valid_slots slots\<rbrace>"
  apply (cases slots, clarsimp simp: valid_slots_def)
  apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply fastforce
  done

lemma pt_lookup_from_level_inv[wp]:
  "\<lbrace>Q and E\<rbrace> pt_lookup_from_level level pt_ptr vptr target_pt_ptr \<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>_. E\<rbrace>"
proof (induct level arbitrary: pt_ptr)
  case 0
  then show ?case by (wpsimp simp: pt_lookup_from_level_simps)
next
  case (minus level)
  note IH = minus(1)
  from \<open>0 < level\<close>  show ?case by (subst pt_lookup_from_level_simps) (wpsimp wp: IH)
qed

crunches unmap_page_table
  for aligned[wp]: pspace_aligned
  and valid_objs[wp]: valid_objs
  and "distinct"[wp]: pspace_distinct
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)

definition
  "valid_apinv ap \<equiv> case ap of
    Assign asid p slot \<Rightarrow>
      (\<lambda>s. \<exists>pool. asid_pools_of s p = Some pool \<and> pool (ucast asid) = None)
      and cte_wp_at (\<lambda>cap. is_vsroot_cap cap \<and> cap_asid cap = None) slot
      and K (0 < asid)
      and (\<lambda>s. pool_for_asid asid s = Some p)"

lemmas setIRQTrigger_irq_masks = no_irq[OF no_irq_setIRQTrigger]

lemma dmo_setIRQTrigger_invs[wp]:
  "do_machine_op (setIRQTrigger irq b) \<lbrace>invs\<rbrace>"
  by (wp dmo_invs_lift)

lemma dmo_ackInterrupt[wp]: "do_machine_op (ackInterrupt irq) \<lbrace>invs\<rbrace>"
  by (wp dmo_invs_lift)

lemma dmo_setVMRoot[wp]:
  "do_machine_op (setVSpaceRoot pt asid) \<lbrace>invs\<rbrace>"
  by (wp dmo_invs_lift)

lemma find_vspace_for_asid_inv[wp]:
  "\<lbrace>P and Q\<rbrace> find_vspace_for_asid asid \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding find_vspace_for_asid_def by wpsimp

crunches get_vmid, invalidate_asid_entry, invalidate_tlb_by_asid, invalidate_tlb_by_asid_va
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and pts[wp]: "\<lambda>s. P (pts_of s)"
  and vcpus[wp]: "\<lambda>s. P (vcpus_of s)"
  and caps[wp]: "\<lambda>s. P (caps_of_state s)"
  and pred_tcb_at[wp]: "\<lambda>s. P (pred_tcb_at proj P t)"
  and asid_table[wp]: "\<lambda>s. P (asid_table s)"
  and aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and cur[wp]: cur_tcb
  and valid_objs[wp]: valid_objs

lemmas find_free_vmid_typ_ats[wp] = abs_typ_at_lifts [OF find_free_vmid_typ_at]
lemmas invalidate_asid_typ_ats[wp] = abs_typ_at_lifts [OF invalidate_asid_typ_at]
lemmas update_asid_pool_entry_typ_ats[wp] = abs_typ_at_lifts [OF update_asid_pool_entry_typ_at]
lemmas invalidate_vmid_entry_typ_ats[wp] = abs_typ_at_lifts [OF invalidate_vmid_entry_typ_at]
lemmas invalidate_asid_entry_typ_ats[wp] = abs_typ_at_lifts [OF invalidate_asid_entry_typ_at]
lemmas store_vmid_typ_ats[wp] = abs_typ_at_lifts [OF store_vmid_typ_at]
lemmas get_vmid_typ_ats[wp] = abs_typ_at_lifts [OF get_vmid_typ_at]
lemmas invalidate_tlb_by_asid_typ_ats[wp] = abs_typ_at_lifts [OF invalidate_tlb_by_asid_typ_at]
lemmas invalidate_tlb_by_asid_va_typ_ats[wp] = abs_typ_at_lifts [OF invalidate_tlb_by_asid_va_typ_at]

lemma valid_arch_state_arm_next_vmid[simp]:
  "valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>arm_next_vmid := next_vmid\<rparr>\<rparr>) =
   valid_arch_state s"
  unfolding valid_arch_state_def
  by (clarsimp simp: valid_global_arch_objs_def vmid_inv_def)

lemma update_asid_pool_entry_vspace_objs_of:
  "\<lbrace>\<lambda>s. \<forall>pool_ptr ap entry. pool_for_asid asid s = Some pool_ptr \<longrightarrow>
        asid_pools_of s pool_ptr = Some ap \<longrightarrow>
        ap (asid_low_bits_of asid) = Some entry \<longrightarrow>
        P ((vspace_objs_of s)(pool_ptr \<mapsto> ASIDPool (ap (asid_low_bits_of asid := f entry)))) \<rbrace>
   update_asid_pool_entry (\<lambda>entry. f entry) asid
   \<lbrace>\<lambda>_ s. P (vspace_objs_of s)\<rbrace>"
  unfolding update_asid_pool_entry_def set_asid_pool_def
  by (wpsimp wp: set_object_wp)
     (fastforce simp: in_omonad obj_at_def opt_map_def elim: rsubst[where P=P])

lemma vs_lookup_table_vspace_eq:
  "\<lbrakk> pts_of s' = pts_of s;
     \<forall>pool_ptr. vspace_for_pool pool_ptr asid (asid_pools_of s') =
                vspace_for_pool pool_ptr asid (asid_pools_of s);
     pool_for_asid asid s' = pool_for_asid asid s \<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref s' = vs_lookup_table level asid vref s"
  unfolding vs_lookup_table_def
  by (auto simp: obind_def split: option.splits)

lemma update_asid_pool_entry_valid_vs_lookup_table[wp]:
  "update_asid_pool_entry (\<lambda>entry. Some (ASIDPoolVSpace vmid (ap_vspace entry))) asid
   \<lbrace>\<lambda>s. P (vs_lookup_table level asid' vref s)\<rbrace>"
  unfolding update_asid_pool_entry_def set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst[where P=P])
  apply (rule vs_lookup_table_vspace_eq; clarsimp)
   apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def obind_def opt_map_def obj_at_def
                   split: option.splits)+
  done

lemma update_asid_pool_entry_valid_vspace_objs[wp]:
  "update_asid_pool_entry (\<lambda>entry. Some (ASIDPoolVSpace vmid (ap_vspace entry))) asid
   \<lbrace>valid_vspace_objs\<rbrace>"
  unfolding valid_vspace_objs_def
  by (wpsimp wp: hoare_vcg_imp_lift' hoare_vcg_all_lift update_asid_pool_entry_vspace_objs_of)
     (fastforce simp: in_omonad ran_def split: if_split_asm)

lemma vspace_for_asid_eq_lift:
  "\<lbrakk> asid_table s' = asid_table s;
     \<forall>pool_ptr. vspace_for_pool pool_ptr asid (asid_pools_of s') =
                vspace_for_pool pool_ptr asid (asid_pools_of s) \<rbrakk> \<Longrightarrow>
   vspace_for_asid asid s' = vspace_for_asid asid s"
  unfolding vspace_for_asid_def vspace_for_pool_def entry_for_asid_def pool_for_asid_def
  by (fastforce simp: obind_def split: option.splits)

lemma vspace_for_asid_lift:
  assumes table:  "\<And>P. f \<lbrace>\<lambda>s. P (asid_table s)\<rbrace>"
  assumes vspace: "\<And>P p. f \<lbrace>\<lambda>s. P (vspace_for_pool p asid (asid_pools_of s))\<rbrace>"
  shows "f \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  apply (clarsimp simp: valid_def)
  apply (erule rsubst[where P=P])
  apply (rule vspace_for_asid_eq_lift)
   apply (frule use_valid, rule table, rule refl, assumption)
  apply clarsimp
  apply (frule use_valid, rule vspace, rule refl, assumption)
  done

lemma update_asid_pool_entry_vspace_for_asid[wp]:
  "update_asid_pool_entry (\<lambda>entry. Some (ASIDPoolVSpace vmid (ap_vspace entry))) asid'
   \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  unfolding update_asid_pool_entry_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: vspace_for_asid_lift set_asid_pool_asid_pools_of; assumption?)
  apply (erule_tac P=P in rsubst)
  apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def obind_def fun_upd_apply
                  split: option.splits)
  done

lemma invalidate_asid_vspace_objs[wp]:
  "invalidate_asid asid \<lbrace>valid_vspace_objs\<rbrace>"
  unfolding invalidate_asid_def
  by wpsimp

lemma store_vmid_valid_vspace_objs[wp]:
  "store_vmid asid vmid \<lbrace>valid_vspace_objs\<rbrace>"
  unfolding store_vmid_def
  by wpsimp

lemma valid_global_arch_objs_upd_eq_lift:
  "(\<And>s. arm_us_global_vspace (f s) = arm_us_global_vspace s) \<Longrightarrow>
   valid_global_arch_objs (s\<lparr>arch_state := f (arch_state s)\<rparr>) = valid_global_arch_objs s"
  unfolding valid_global_arch_objs_def by simp

crunches get_vmid, invalidate_asid_entry, invalidate_tlb_by_asid, invalidate_tlb_by_asid_va,
         find_free_vmid
  for valid_vspace_objs[wp]: valid_vspace_objs
  and vspace_for_asid[wp]: "\<lambda>s. P (vspace_for_asid asid s)"
  and vspace_at_asid[wp]: "vspace_at_asid asid pt"
  (ignore: update_asid_pool_entry simp: vspace_at_asid_def)

lemma set_asid_pool_valid_global_arch_objs[wp]:
  "set_asid_pool p ap \<lbrace>valid_global_arch_objs\<rbrace>"
  unfolding valid_global_arch_objs_def
  by (wp_pre, wps, wpsimp)

crunches get_vmid, invalidate_asid_entry, invalidate_tlb_by_asid, invalidate_tlb_by_asid_va,
         find_free_vmid
  for valid_asid_table[wp]: valid_asid_table
  and valid_uses[wp]: valid_uses
  and cur_vcpu[wp]: cur_vcpu
  and valid_global_arch_objs[wp]: valid_global_arch_objs
  (ignore: set_asid_pool simp: valid_global_arch_objs_upd_eq_lift)

crunches do_machine_op
  for vmid_for_asid[wp]: "\<lambda>s. P (vmid_for_asid s)" (* FIXME: move to ArchAcc crunches *)

lemma vmid_for_asid_upd_eq:
  "\<lbrakk> pool_for_asid asid s = Some pool_ptr; asid_pools_of s pool_ptr = Some ap;
     ap (asid_low_bits_of asid) = Some entry; valid_asid_table s \<rbrakk>
   \<Longrightarrow> (\<lambda>asid'. vmid_for_asid_2
                  asid'
                  (asid_table s)
                  (asid_pools_of s(pool_ptr \<mapsto> ap(asid_low_bits_of asid \<mapsto>
                                                  ASIDPoolVSpace vmid vsp))))
       = (vmid_for_asid s) (asid := vmid)"
  apply (rule ext)
  apply (clarsimp simp: vmid_for_asid_2_def entry_for_pool_def pool_for_asid_def obind_def
                  split: option.splits)
  apply (rule conjI; clarsimp)
  apply (rule conjI; clarsimp simp: opt_map_def split: option.splits)
  apply (drule (1) valid_asid_table_inj, simp add: opt_map_def)
  apply (drule (1) asid_high_low_inj[OF _ sym, THEN sym])
  apply simp
  done

lemma find_free_vmid_vmid_inv[wp]:
  "\<lbrace>valid_asid_table and vmid_inv\<rbrace> find_free_vmid \<lbrace>\<lambda>_. vmid_inv\<rbrace>"
  unfolding find_free_vmid_def invalidate_vmid_entry_def invalidate_asid_def
            update_asid_pool_entry_def vmid_inv_def
  supply fun_upd_apply[simp del]
  apply (wpsimp|wps)+
  apply (frule is_inv_inj)
  apply (drule findNoneD)
  apply (rename_tac pool_ptr ap entry)
  apply (drule_tac x="arm_next_vmid (arch_state s)" in bspec, simp add: minBound_word)
  apply (fastforce simp: vmid_for_asid_upd_eq is_inv_def ran_upd[folded fun_upd_apply] dom_upd
                         fun_upd_apply
                   split: if_split_asm
                   dest: inj_on_domD)
  done

crunches find_free_vmid
  for valid_global_tables[wp]: "valid_global_tables"

lemma find_free_vmid_valid_arch [wp]:
  "find_free_vmid \<lbrace>valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def by wpsimp

lemma entry_for_asid_Some_vmidD:
  "entry_for_asid asid s = Some entry \<Longrightarrow> ap_vmid entry = vmid_for_asid s asid \<and> 0 < asid"
  unfolding entry_for_asid_def vmid_for_asid_def entry_for_pool_def pool_for_asid_def
  by (auto simp: obind_def opt_map_def split: option.splits)

lemma load_vmid_wp[wp]:
  "\<lbrace>\<lambda>s. P (asid_map s asid) s\<rbrace> load_vmid asid \<lbrace>P\<rbrace>"
  unfolding load_vmid_def
  by wpsimp (fastforce dest: entry_for_asid_Some_vmidD)

lemma valid_global_refs_vmid_table_upd[simp]:
  "valid_global_refs (s\<lparr>arch_state := arch_state s\<lparr>arm_vmid_table := x\<rparr>\<rparr>) = valid_global_refs s"
  unfolding valid_global_refs_def valid_refs_def global_refs_def
  by simp

lemma valid_global_refs_next_vmid_upd[simp]:
  "valid_global_refs (s\<lparr>arch_state := arch_state s\<lparr>arm_next_vmid := x\<rparr>\<rparr>) = valid_global_refs s"
  unfolding valid_global_refs_def valid_refs_def global_refs_def
  by simp

lemma valid_machine_state_arm_vmid_table_upd[simp]:
  "valid_machine_state (s\<lparr>arch_state := arch_state s\<lparr>arm_vmid_table := x\<rparr>\<rparr>) = valid_machine_state s"
  unfolding valid_machine_state_def
  by simp

lemma valid_machine_state_arm_next_vmid_upd[simp]:
  "valid_machine_state (s\<lparr>arch_state := arch_state s\<lparr>arm_next_vmid := x\<rparr>\<rparr>) = valid_machine_state s"
  unfolding valid_machine_state_def
  by simp

lemma vs_lookup_target_vspace_eq:
  "\<lbrakk> pts_of s' = pts_of s;
     \<forall>pool_ptr. vspace_for_pool pool_ptr asid (asid_pools_of s') =
                vspace_for_pool pool_ptr asid (asid_pools_of s);
     pool_for_asid asid s' = pool_for_asid asid s;
     \<forall>pt_t p. pte_refs_of pt_t p s' = pte_refs_of pt_t p s \<rbrakk>
   \<Longrightarrow> vs_lookup_target level asid vref s' = vs_lookup_target level asid vref s"
  for s :: "'z::state_ext state" and s' :: "'z::state_ext state"
  unfolding vs_lookup_target_def vs_lookup_slot_def
  by (frule (2) vs_lookup_table_vspace_eq[where level=level and vref=vref])
     (fastforce intro!: obind_eqI simp: obind_assoc)

lemma update_asid_pool_entry_valid_vs_lookup_target[wp]:
  "update_asid_pool_entry (\<lambda>entry. Some (ASIDPoolVSpace vmid (ap_vspace entry))) asid
   \<lbrace>\<lambda>s. P (vs_lookup_target level asid' vref s)\<rbrace>"
  unfolding update_asid_pool_entry_def set_asid_pool_def
  apply (wpsimp wp: set_object_wp)
  apply (erule rsubst[where P=P])
  apply (rule vs_lookup_target_vspace_eq; clarsimp)
   apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def obind_def opt_map_def obj_at_def
                   split: option.splits)+
  done

lemma vs_lookup_pages_target_lift:
  assumes "\<And>P level asid vref. f \<lbrace> \<lambda>s. P (vs_lookup_target level asid vref s) \<rbrace>"
  shows "f \<lbrace> \<lambda>s. P (vs_lookup_pages s) \<rbrace>"
  apply (rule_tac P=P in hoare_liftP_ext)+
  apply simp
  apply (rename_tac P asid)
  apply (rule_tac P=P in hoare_liftP_ext)
  apply (rule assms)
  done

lemma update_asid_pool_entry_vs_lookup_pages_vmid[wp]:
  "update_asid_pool_entry (\<lambda>entry. Some (ASIDPoolVSpace vmid (ap_vspace entry))) asid
   \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (wpsimp wp: vs_lookup_pages_target_lift[OF update_asid_pool_entry_valid_vs_lookup_target])

crunches update_asid_pool_entry, find_free_vmid, store_vmid
  for if_live[wp]: if_live_then_nonz_cap
  and zombies_final[wp]: zombies_final
  and state_refs[wp]: "\<lambda>s. P (state_refs_of s)"
  and hyp_refs[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and valid_mdb[wp]: valid_mdb
  and valid_ioc[wp]: valid_ioc
  and valid_idle[wp]: valid_idle
  and only_idle[wp]: only_idle
  and if_unsafe[wp]: if_unsafe_then_cap
  and valid_reply_caps[wp]: valid_reply_caps
  and valid_reply_masters[wp]: valid_reply_masters
  and valid_global_refs[wp]: valid_global_refs
  and irq_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and kernel_vspace[wp]: "\<lambda>s. P (arm_kernel_vspace (arch_state s))"
  and valid_global_objs[wp]: valid_global_objs
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  (simp: valid_global_objs_def)

crunches invalidate_asid, find_free_vmid, store_vmid
  for valid_machine_state[wp]: valid_machine_state
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and valid_irq_states[wp]: valid_irq_states
  (ignore: do_machine_op
   wp: pspace_respects_device_region_dmo cap_refs_respects_device_region_dmo
       dmo_valid_irq_states)

crunches invalidate_asid, find_free_vmid, store_vmid
  for vs_lookup_pages[wp]: "\<lambda>s. P (vs_lookup_pages s)"
  (ignore: update_asid_pool_entry)

crunches invalidate_asid
  for machine_state[wp]: "\<lambda>s. P (machine_state s)"

crunches update_asid_pool_entry
  for arch_state[wp]: "\<lambda>s. P (arch_state s)"

lemma update_asid_pool_entry_asid_pools[wp]:
  "\<lbrace>\<lambda>s. \<forall>pool_ptr ap entry.
          pool_for_asid asid s = Some pool_ptr \<longrightarrow> asid_pools_of s pool_ptr = Some ap \<longrightarrow>
          ap (asid_low_bits_of asid) = Some entry \<longrightarrow>
          P ((asid_pools_of s) (pool_ptr \<mapsto> ap(asid_low_bits_of asid := f entry))) \<rbrace>
   update_asid_pool_entry f asid
   \<lbrace>\<lambda>_ s. P (asid_pools_of s)\<rbrace>"
  unfolding update_asid_pool_entry_def
  supply fun_upd_apply[simp del]
  by wpsimp

lemma invalidate_asid_entry_invs[wp]:
  "invalidate_asid_entry asid \<lbrace>invs\<rbrace>"
  unfolding invalidate_asid_entry_def invalidate_asid_def invalidate_vmid_entry_def invs_def
            valid_state_def valid_pspace_def valid_arch_state_def vmid_inv_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: load_vmid_wp valid_irq_handlers_lift valid_irq_node_typ valid_irq_states_triv
                      valid_arch_caps_lift pspace_in_kernel_window_atyp_lift_strong
                simp: valid_kernel_mappings_def equal_kernel_mappings_def valid_asid_map_def
                      valid_global_vspace_mappings_def
         | wps)+
  apply (clarsimp simp: valid_irq_node_def valid_global_refs_def global_refs_def valid_arch_state_def
                        valid_global_objs_def valid_global_arch_objs_def valid_machine_state_def
                        valid_vspace_objs_def vmid_for_asid_upd_eq comp_upd_simp is_inv_None_upd)
  done

lemma find_free_vmid_invs[wp]:
  "find_free_vmid \<lbrace>invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: load_vmid_wp valid_irq_handlers_lift valid_irq_node_typ
                 valid_arch_caps_lift pspace_in_kernel_window_atyp_lift_strong
             simp: valid_kernel_mappings_def equal_kernel_mappings_def valid_asid_map_def
                   valid_global_vspace_mappings_def)

lemma store_hw_asid_valid_arch[wp]:
  "\<lbrace>valid_arch_state and (\<lambda>s. asid_map s asid = None \<and> arm_vmid_table (arch_state s) vmid = None)\<rbrace>
   store_vmid asid vmid
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding store_vmid_def valid_arch_state_def vmid_inv_def
  supply fun_upd_apply[simp del]
  apply (wpsimp simp: valid_global_arch_objs_upd_eq_lift | wps)+
  apply (fastforce simp: vmid_for_asid_upd_eq elim: is_inv_Some_upd)
  done

lemma store_vmid_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. asid_map s asid = None \<and> arm_vmid_table (arch_state s) vmid = None)\<rbrace>
   store_vmid asid vmid
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_irq_node_typ valid_irq_handlers_lift valid_arch_caps_lift
                 pspace_in_kernel_window_atyp_lift_strong
             simp: valid_kernel_mappings_def equal_kernel_mappings_def valid_asid_map_def
                   valid_global_vspace_mappings_def)

lemma invalidate_vmid_entry_None[wp]:
  "\<lbrace>\<top>\<rbrace> invalidate_vmid_entry vmid \<lbrace>\<lambda>_ s. arm_vmid_table (arch_state s) vmid = None\<rbrace>"
  unfolding invalidate_vmid_entry_def
  by wpsimp

lemma find_free_vmid_None[wp]:
  "\<lbrace>\<top>\<rbrace> find_free_vmid \<lbrace>\<lambda>vmid s. arm_vmid_table (arch_state s) vmid = None\<rbrace>"
  unfolding find_free_vmid_def
  by wpsimp (clarsimp dest!: findSomeD)

lemma invalidate_vmid_entry_vmid_for_asid_None[wp]:
  "invalidate_vmid_entry vmid \<lbrace>\<lambda>s. vmid_for_asid s asid = None\<rbrace>"
  unfolding invalidate_vmid_entry_def
  by wpsimp

lemma invalidate_asid_vmid_for_asid_None[wp]:
  "\<lbrace>\<lambda>s. asid' \<noteq> asid \<longrightarrow> vmid_for_asid s asid = None \<rbrace>
   invalidate_asid asid'
   \<lbrace>\<lambda>_ s. vmid_for_asid s asid = None\<rbrace>"
  unfolding invalidate_asid_def update_asid_pool_entry_def
  supply fun_upd_apply[simp del]
  apply (wpsimp|wps)+
  apply (auto simp: pool_for_asid_def vmid_for_asid_def entry_for_pool_def fun_upd_apply obind_def
                    in_opt_map_None_eq
              split: option.split)
  done

lemma find_free_vmid_None_asid_map[wp]:
  "find_free_vmid \<lbrace>\<lambda>s. asid_map s asid = None\<rbrace>"
  unfolding find_free_vmid_def
  by wpsimp

lemma get_hw_asid_valid_arch[wp]:
  "get_vmid asid \<lbrace>valid_arch_state\<rbrace>"
  unfolding get_vmid_def
  by wpsimp

lemma get_hw_asid_invs[wp]:
  "get_vmid asid \<lbrace>invs\<rbrace>"
  unfolding get_vmid_def
  by (wpsimp wp: store_vmid_invs load_vmid_wp simp: opt_map_def)

lemma dmo_invalidateTranslationASID_invs[wp]:
  "do_machine_op (invalidateTranslationASID asid) \<lbrace>invs\<rbrace>"
  by (wp dmo_invs_lift)

lemma dmo_invalidateTranslationSingle_invs[wp]:
  "do_machine_op (invalidateTranslationSingle asid) \<lbrace>invs\<rbrace>"
  by (wp dmo_invs_lift)

crunches invalidate_tlb_by_asid, invalidate_tlb_by_asid_va
  for invs: invs
  (ignore: do_machine_op)

lemma arm_context_switch_invs [wp]:
  "arm_context_switch pt asid \<lbrace>invs\<rbrace>"
  unfolding arm_context_switch_def by wpsimp

crunches set_vm_root
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: crunch_simps)

lemma set_global_user_vspace_invs[wp]:
  "set_global_user_vspace \<lbrace>invs\<rbrace>"
  unfolding set_global_user_vspace_def
  by wpsimp

lemma set_vm_root_invs[wp]:
  "set_vm_root t \<lbrace>invs\<rbrace>"
  unfolding set_vm_root_def
  by (wpsimp simp: if_distribR wp: get_cap_wp)

crunch pred_tcb_at[wp]: set_vm_root "pred_tcb_at proj P t"
  (simp: crunch_simps)

lemmas set_vm_root_typ_ats [wp] = abs_typ_at_lifts [OF set_vm_root_typ_at]

lemma valid_pte_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pte level pte s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pte level pte s)\<rbrace>"
  apply (insert bool_function_four_cases[where f=P])
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_const_imp_lift hoare_vcg_disj_lift x)+
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (simp | wp)+
  done


lemma set_cap_valid_pte_stronger:
  "set_cap cap p \<lbrace>\<lambda>s. P (valid_pte level pte s)\<rbrace>"
  by (wp valid_pte_lift3 set_cap_typ_at)


(* FIXME: move *)
lemma valid_cap_to_pt_cap:
  "\<lbrakk>valid_cap c s; obj_refs c = {p}; pt_at pt_t p s\<rbrakk> \<Longrightarrow> is_pt_cap c"
  by (clarsimp simp: valid_cap_def obj_at_def is_obj_defs is_pt_cap_def valid_arch_cap_ref_def
              split: cap.splits option.splits arch_cap.splits if_splits)

lemma set_cap_invalid_pte[wp]:
  "set_cap cap p' \<lbrace>invalid_pte_at pt_t p\<rbrace>"
  unfolding invalid_pte_at_def by wpsimp

lemma valid_cap_obj_ref_pt:
  "\<lbrakk> s \<turnstile> cap; s \<turnstile> cap'; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> is_pt_cap cap \<longrightarrow> is_pt_cap cap'"
  by (auto simp: is_cap_simps valid_cap_def valid_arch_cap_ref_def
                 obj_at_def is_ep is_ntfn is_cap_table is_tcb a_type_def
          split: cap.split_asm if_split_asm arch_cap.split_asm option.split_asm)

lemma is_pt_cap_asid_None_table_ref:
  "is_pt_cap cap \<Longrightarrow> (table_cap_ref cap = None) = (cap_asid cap = None)"
  by (auto simp: is_cap_simps table_cap_ref_def cap_asid_def
          split: option.split_asm)

lemma no_cap_to_obj_with_diff_ref_map:
  "\<lbrakk> caps_of_state s p = Some cap; is_pt_cap cap;
     table_cap_ref cap = None;
     unique_table_caps s;
     valid_objs s; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid_cap[where p=p])
  apply (frule(1) caps_of_state_valid_cap[where p="(a, b)" for a b])
  apply (drule(1) valid_cap_obj_ref_pt, simp)
  apply (drule(1) unique_table_capsD[rotated, where cps="caps_of_state s"]; simp?)
  apply (simp add: vs_cap_ref_table_cap_ref_eq)
  done

lemmas store_pte_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pte_caps_of_state]

lemma mdb_cte_at_store_pte[wp]:
  "store_pte pt_t y pte \<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wpsimp wp: hoare_vcg_disj_lift hoare_vcg_all_lift simp: store_pte_def set_pt_def)
  done

crunches store_pte
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"

(* FIXME: move *)
lemma vs_cap_ref_table_cap_ref_None:
  "vs_cap_ref x = None \<Longrightarrow> table_cap_ref x = None"
  by (simp add: vs_cap_ref_def arch_cap_fun_lift_def vs_cap_ref_arch_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_device_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> cap_is_device c = cap_is_device d"
  by (simp add: cap_master_cap_def
         split: cap.splits arch_cap.splits)

lemma vs_cap_ref_eq_imp_table_cap_ref_eq':
  "\<lbrakk> vs_cap_ref cap = vs_cap_ref cap'; cap_master_cap cap = cap_master_cap cap' \<rbrakk>
   \<Longrightarrow> table_cap_ref cap = table_cap_ref cap'"
  by (simp add: vs_cap_ref_def vs_cap_ref_arch_def arch_cap_fun_lift_def cap_master_cap_def
           split: cap.splits arch_cap.splits option.splits prod.splits)

lemma arch_update_cap_invs_map:
  "\<lbrace>cte_wp_at (is_arch_update cap and
               (\<lambda>c. \<forall>r. vs_cap_ref c = Some r \<longrightarrow> vs_cap_ref cap = Some r)) p
    and invs and valid_cap cap\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (clarsimp simp: cte_wp_at_caps_of_state
              simp del: imp_disjL)
  apply (frule(1) valid_global_refsD2)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (clarsimp simp: is_cap_simps is_arch_update_def
              simp del: imp_disjL)
  apply (frule master_cap_cap_range, simp del: imp_disjL)
  apply (thin_tac "cap_range a = cap_range b" for a b)
  apply (rule conjI)
   apply (clarsimp simp: is_valid_vtable_root_def vs_cap_ref_def vs_cap_ref_arch_def split: cap.splits)
   apply (simp split: arch_cap.splits option.splits pt_type.splits;
          clarsimp simp: cap_master_cap_simps vs_cap_ref_arch_def)
  apply (rule conjI)
   apply (rule ext)
   apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
  apply (rule context_conjI)
   apply (simp add: appropriate_cte_cap_irqs)
   apply (clarsimp simp: cap_irqs_def cap_irq_opt_def cap_master_cap_def
                  split: cap.split)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def cap_master_cap_def
                  split: cap.split_asm)
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply simp
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply (case_tac "table_cap_ref capa =
                    table_cap_ref (ArchObjectCap a)")
    apply (frule unique_table_refs_no_cap_asidE[where S="{p}"])
     apply (simp add: valid_arch_caps_def)
    apply (simp add: no_cap_to_obj_with_diff_ref_def Ball_def)
   apply (case_tac "table_cap_ref capa")
    apply clarsimp
    apply (erule no_cap_to_obj_with_diff_ref_map,
           simp_all)[1]
      apply (clarsimp simp: table_cap_ref_def cap_master_cap_simps
                            is_cap_simps table_cap_ref_arch_def
                     split: cap.split_asm arch_cap.split_asm
                     dest!: cap_master_cap_eqDs)
     apply (simp add: valid_arch_caps_def)
    apply (simp add: valid_pspace_def)
   apply (erule swap)
   apply (rule vs_cap_ref_eq_imp_table_cap_ref_eq')
    apply (frule table_cap_ref_vs_cap_ref_Some)
    apply fastforce
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp del: imp_disjL)
   apply (clarsimp simp: is_pt_cap_def cap_master_cap_simps
                         cap_asid_def vs_cap_ref_def
                  dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
   apply (drule valid_table_capsD[OF caps_of_state_cteD])
      apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
     apply (simp add: is_pt_cap_def)
    apply (simp add: cap_asid_def split: option.splits)
   apply simp
  apply (clarsimp simp: is_cap_simps is_pt_cap_def cap_master_cap_simps
                        cap_asid_def vs_cap_ref_def ranI
                 dest!: cap_master_cap_eqDs split: option.split_asm if_split_asm
                 elim!: ranE cong: master_cap_eq_is_device_cap_eq
             | rule conjI)+
  apply (clarsimp dest!: master_cap_eq_is_device_cap_eq)
  done

lemma pool_for_asid_ap_at:
  "\<lbrakk> pool_for_asid asid s = Some p; valid_arch_state s \<rbrakk> \<Longrightarrow> asid_pool_at p s"
  by (fastforce dest!: pool_for_asid_validD simp: valid_arch_state_def asid_pools_at_eq)

lemma arch_update_cap_invs_unmap_page:
  "\<lbrace>(\<lambda>s. \<exists>cap'.
             caps_of_state s p = Some cap' \<and>
             (\<forall>p'\<in>obj_refs cap'.
                 \<forall>asid vref.
                    vs_cap_ref cap' = Some (asid, vref) \<longrightarrow>
                    (\<forall>level. vs_lookup_target level asid vref s \<noteq> Some (level, p'))) \<and>
             is_arch_update cap cap')
             and invs and valid_cap cap
             and K (is_frame_cap cap)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps
                        fun_eq_iff appropriate_cte_cap_irqs
                        is_pt_cap_def is_valid_vtable_root_def
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   subgoal by (simp add: cap_range_def)
  apply (rule conjI)
   apply (clarsimp simp: reachable_target_def reachable_frame_cap_def)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: valid_cap_def obj_at_def split: if_split_asm)
  apply (rule conjI[rotated])
   apply (frule(1) cap_refs_in_kernel_windowD)
   apply (simp add: cap_range_def)
  apply (drule unique_table_refs_no_cap_asidE[where S="{p}"])
   apply (simp add: valid_arch_caps_def)
  apply (simp add: no_cap_to_obj_with_diff_ref_def table_cap_ref_def Ball_def)
  done

lemma mask_cap_PageTableCap[simp]:
  "mask_cap R (ArchObjectCap (PageTableCap p pt_t data)) = ArchObjectCap (PageTableCap p pt_t data)"
  by (clarsimp simp: mask_cap_def cap_rights_update_def acap_rights_update_def)

lemma arch_update_cap_pspace':
  "\<lbrace>cte_wp_at (is_arch_update cap) p and real_cte_at p and valid_pspace and valid_cap cap\<rbrace>
   set_cap cap p
   \<lbrace>\<lambda>_. valid_pspace\<rbrace>"
  apply (simp add: valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_cap_valid_objs update_cap_iflive arch_update_cap_zombies)
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def)
  apply (frule cap_master_cap_zobj_refs)
  apply clarsimp
  apply (drule caps_of_state_cteD)
  apply (drule (1) cte_wp_tcb_cap_valid)
  apply (erule real_cte_tcb_valid[rule_format])
  done

lemma arch_update_cap_invs_unmap_page_table:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and real_cte_at p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and (\<lambda>s. pts_of s (obj_ref_of cap) = Some (empty_pt (cap_pt_type cap)))
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>asid vref level. vs_cap_ref c = Some (asid, vref)
                                \<longrightarrow> vs_lookup_target level asid vref s \<noteq> Some (level, obj_ref_of cap)) p s)
             and K (is_pt_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace' arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (simp add: final_cap_at_eq)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps is_valid_vtable_root_def
                        appropriate_cte_cap_irqs is_pt_cap_def
                        fun_eq_iff[where f="cte_refs cap" for cap]
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   apply (simp add: cap_range_def)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (simp add: cap_range_def gen_obj_refs_def image_def)
  apply (rule conjI)
   apply (clarsimp simp: reachable_target_def reachable_frame_cap_def)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: valid_cap_def obj_at_def split: if_split_asm)
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def in_omonad)
  apply fastforce
  done

lemma global_refs_arch_update_eq:
  "arm_us_global_vspace (f (arch_state s)) = arm_us_global_vspace (arch_state s) \<Longrightarrow>
   global_refs (arch_state_update f s) = global_refs s"
  by (simp add: global_refs_def)

lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> (level,p)) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
            \<and> pt_at pt_t p s
        \<longrightarrow> p \<notin> global_refs s"
  apply clarsimp
  apply (cases "level = asid_pool_level"; simp)
   apply (simp add: vs_lookup_table_def in_omonad)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: obj_at_def)
  apply (drule (1) vs_lookup_table_target)
  apply (drule valid_vs_lookupD; clarsimp simp: vref_for_level_user_region)
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  done

lemma pt_lookup_from_level_wp:
  "\<lbrace>\<lambda>s. (\<forall>level pt' pte.
            pt_walk top_level level top_level_pt vref (ptes_of s) = Some (level, pt') \<longrightarrow>
            ptes_of s (level_type level) (pt_slot_offset level pt' vref) = Some pte \<longrightarrow>
            is_PageTablePTE pte \<longrightarrow>
            pte_ref pte = Some pt \<longrightarrow>
            Q (pt_slot_offset level pt' vref, level) s) \<and>
        ((\<forall>level < top_level.
            pt_walk top_level level top_level_pt vref (ptes_of s) \<noteq> Some (level, pt)) \<longrightarrow>
            E InvalidRoot s)\<rbrace>
  pt_lookup_from_level top_level top_level_pt vref pt
  \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
proof (induct top_level arbitrary: top_level_pt)
  case 0
  then show ?case
    by (wpsimp simp: pt_lookup_from_level_simps)
next
  case (minus top_level)
  note IH=minus(1)
  from \<open>0 < top_level\<close>
  show ?case
    apply (subst pt_lookup_from_level_simps)
    apply (wpsimp wp: IH)
    apply (rule conjI; clarsimp)
     prefer 2
     apply (subst (asm) (2) pt_walk.simps)
     apply (clarsimp)
    apply (rule conjI; clarsimp)
     apply (erule_tac x="top_level" in allE)
     apply (clarsimp simp: in_omonad is_PageTablePTE_def pptr_from_pte_def)
    apply (rule conjI; clarsimp)
     apply (rename_tac pt' pte)
     apply (frule pt_walk_max_level)
     apply (erule_tac x=level in allE)
     apply (erule_tac x=pt' in allE)
     apply simp
     apply (erule mp)
     apply (subst pt_walk.simps)
     apply (simp add: in_omonad vm_level.leq_minus1_less)
    apply (subst (asm) (3) pt_walk.simps)
    apply (case_tac "level = top_level - 1"; clarsimp)
    apply (subgoal_tac "level < top_level - 1", fastforce)
    apply (frule vm_level.zero_least)
    apply (subst (asm) vm_level.leq_minus1_less[symmetric], assumption)
    apply simp
    done
qed

lemmas pts_of_Some_alignedD = pspace_aligned_pts_ofD[rotated]

lemma vs_lookup_target_not_global:
  "\<lbrakk> vs_lookup_target level asid vref s = Some (level, pt); vref \<in> user_region; invs s \<rbrakk>
   \<Longrightarrow> pt \<notin> global_refs s"
  apply (drule (1) valid_vs_lookupD; clarsimp)
  apply (drule valid_global_refsD2; clarsimp)
  apply (simp add: cap_range_def)
  done

lemma reachable_page_table_not_global:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); level \<le> max_pt_level;
     vref \<in> user_region; invs s\<rbrakk>
   \<Longrightarrow> p \<notin> global_refs s"
  apply (drule (1) vs_lookup_table_target)
  apply (erule vs_lookup_target_not_global)
   apply (erule vref_for_level_user_region)
  apply assumption
  done

lemma user_region_invalid_mapping_slots:
  "vref \<in> user_region \<Longrightarrow> ucast (pt_index max_pt_level vref) \<notin> invalid_mapping_slots"
  unfolding user_region_def pt_index_def invalid_mapping_slots_def canonical_user_def
  apply (clarsimp split: if_split_asm)
  apply (rule ucast_le_maskI)
  apply (clarsimp simp: bit_simps word_and_le1 split: if_split_asm)
  apply (simp add: pt_bits_left_def bit_simps size_max_pt_level)
  apply (rule order_trans, rule word_and_le2)
  apply (rule leq_mask_shift)
  apply simp
  done

lemma unmap_page_table_invs[wp]:
  "\<lbrace>invs and K (vaddr \<in> user_region)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  unfolding unmap_page_table_def
  apply (wpsimp wp: invalidate_tlb_by_asid_invs dmo_invs_lift store_pte_invs_unmap
                    pt_lookup_from_level_wp)
  apply (frule pt_walk_max_level)
  apply (drule (2) pt_lookup_vs_lookupI)
  apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (frule pts_of_Some_alignedD; clarsimp)
  apply (rule conjI)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region, clarsimp)
   apply clarsimp
   apply (frule (1) cap_to_pt_is_pt_cap_and_type; clarsimp?)
     apply fastforce
    apply (fastforce intro: valid_objs_caps)
   apply (fastforce simp: is_cap_simps)
  apply (rule conjI; clarsimp?)
   apply (drule (3) vs_lookup_table_vspace)
   apply (simp add: user_region_invalid_mapping_slots)
  apply (drule (1) vs_lookup_table_target)
  apply (drule vs_lookup_target_not_global, erule vref_for_level_user_region; simp)
  done

lemma final_cap_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (is_final_cap' cap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_final_cap' cap s)\<rbrace>"
  by (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state, rule x)

lemmas dmo_final_cap[wp] = final_cap_lift [OF do_machine_op_caps_of_state]
lemmas store_pte_final_cap[wp] = final_cap_lift [OF store_pte_caps_of_state]
lemmas unmap_page_table_final_cap[wp] = final_cap_lift [OF unmap_page_table_caps_of_state]

lemma store_pte_vspace_for_asid[wp]:
  "store_pte pte_t p pte \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  by (wp vspace_for_asid_lift)

lemma mapM_swp_store_pte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots. table_base pt_t sl \<notin> global_refs s \<and>
                        (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base pt_t sl))) and
    K (pte = InvalidPTE)\<rbrace>
  mapM (swp (store_pte pt_t) pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (wp store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_all_lift)
   apply (clarsimp simp: wellformed_pte_def)
  apply simp
  done

lemma mapM_x_swp_store_pte_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl \<in> set slots. table_base pt_t sl \<notin> global_refs s \<and>
                                    (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base pt_t sl))) and
    K (pte = InvalidPTE)\<rbrace>
  mapM_x (swp (store_pte pt_t) pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pte_invs_unmap)+

lemma vs_lookup_table_step:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, pt'); level \<le> max_pt_level; 0 < level;
     ptes_of s level  (pt_slot_offset level pt' vref) = Some pte; is_PageTablePTE pte;
     pte_ref pte = Some pt \<rbrakk> \<Longrightarrow>
    vs_lookup_table (level-1) asid vref s = Some (level-1, pt)"
  apply (subst vs_lookup_split_Some[where level'=level]; assumption?)
   apply (simp add: order_less_imp_le)
  apply (subst pt_walk.simps)
  apply (clarsimp simp: in_omonad is_PageTablePTE_def pptr_from_pte_def)
  done

lemma pte_ref_Some_cases:
  "(pte_ref pte = Some ref) = ((is_PageTablePTE pte \<or> is_PagePTE pte) \<and> ref = pptr_from_pte pte)"
  by (cases pte) (auto simp: pptr_from_pte_def)

lemma store_pte_invalid_vs_lookup_target_unmap:
  "\<lbrace>\<lambda>s. vs_lookup_slot level' asid vref s = Some (level', slot) \<and>
        pte_refs_of level' slot s = Some p \<and>
        vref \<in> user_region \<and>
        pspace_aligned s \<and> pspace_distinct s \<and> valid_asid_table s \<and> valid_vspace_objs s \<rbrace>
   store_pte (level_type level') slot InvalidPTE
   \<lbrace>\<lambda>_ s. vs_lookup_target level asid vref s \<noteq> Some (level, p)\<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp simp: obj_at_def)
  apply (prop_tac "level' \<le> max_pt_level")
   apply (clarsimp simp flip: asid_pool_level_neq simp: in_omonad)
   apply (erule (4) vs_lookup_slot_no_asid)
  apply (frule (5) valid_vspace_objs_strong_slotD)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (clarsimp simp: in_omonad pte_ref_Some_cases)
  apply (rename_tac pt_ptr pte)
  apply (frule (5) vs_lookup_table_is_aligned)
  apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def pool_for_asid_vs_lookup
                  split: if_split_asm)
   apply (prop_tac "asid_pools_of s pt_ptr = None")
    apply (clarsimp simp: opt_map_def split: option.splits)
   apply simp
   apply (prop_tac "vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, p)")
    apply (clarsimp simp: vs_lookup_table_def in_omonad)
   apply (erule disjE)
    (* PageTablePTE: level' would have to be asid_pool_level, contradiction *)
    apply (drule (1) vs_lookup_table_step; simp?)
      apply (rule ccontr)
      apply (clarsimp simp flip: vm_level.neq_0_conv simp: is_PageTablePTE_def)
     apply (fastforce simp: pte_ref_Some_cases)
    apply (drule (1) no_loop_vs_lookup_table; simp?)
   (* PagePTE *)
   apply (prop_tac "\<exists>sz. data_at sz p s")
    apply (fastforce simp: is_PagePTE_def)
   apply clarsimp
   apply (drule (2) valid_vspace_objs_strongD[where level=max_pt_level]; clarsimp)
   apply (fastforce simp: data_at_def obj_at_def in_omonad)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pt_ptr' pte')
  apply (case_tac "level' \<le> level")
   apply (drule (7) vs_lookup_table_fun_upd_deep_idem)
   apply (frule (5) vs_lookup_table_is_aligned[where bot_level=level])
   apply (clarsimp simp: ptes_of_def fun_upd_apply in_omonad split: if_split_asm)
    apply (drule (1) no_loop_vs_lookup_table; simp)
   apply (rename_tac pt')
   apply (case_tac "level' = level", simp)
   apply (prop_tac "valid_pte level (pt_apply pt' (table_index level (pt_slot_offset level pt_ptr' vref))) s")
    apply (drule (2) valid_vspace_objsD[where bot_level=level])
     apply (simp add: in_omonad)
    apply simp
   apply (erule disjE)
    (* PageTablePTE *)
    apply (prop_tac "is_PageTablePTE (pt_apply pt' (table_index level (pt_slot_offset level pt_ptr' vref)))")
     apply (case_tac "pt_apply pt' (table_index level (pt_slot_offset level pt_ptr' vref))"; simp)
     apply (clarsimp simp: is_PageTablePTE_def obj_at_def data_at_def pptr_from_pte_def)
    apply (drule (1) vs_lookup_table_step; simp?)
      apply (rule ccontr)
      apply (clarsimp simp: is_PageTablePTE_def)
     apply (clarsimp simp: ptes_of_def in_omonad)
    apply (drule (1) vs_lookup_table_step)
        apply (rule ccontr)
        apply (clarsimp simp: is_PageTablePTE_def)
       apply (clarsimp simp: ptes_of_def in_omonad)
       apply (rule refl)
      apply simp
     apply (simp add: pte_ref_Some_cases)
    apply (simp add: pte_ref_Some_cases)
    apply (drule (1) no_loop_vs_lookup_table; simp)
   apply (prop_tac "\<not>is_PageTablePTE (pt_apply pt' (table_index level (pt_slot_offset level pt_ptr' vref)))")
     apply (case_tac "pt_apply pt' (table_index level (pt_slot_offset level pt_ptr' vref))"; simp)
     apply (clarsimp simp: is_PagePTE_def obj_at_def data_at_def pptr_from_pte_def pte_base_addr_def)
   apply (drule_tac level=level' and level'=level in vs_lookup_splitD; clarsimp)
   apply (subst (asm) pt_walk.simps)
   apply (clarsimp simp: in_omonad ptes_of_def split: if_split_asm)
  apply (simp add: not_le)
   apply (drule_tac level=level and level'=level' in vs_lookup_splitD; simp?)
  apply clarsimp
  apply (drule (1) vs_lookup_table_fun_upd_deep_idem; simp)
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: in_omonad)
  apply (subst (asm) (3) level_pte_of_def)
  apply (clarsimp simp: in_omonad fun_upd_apply split: if_split_asm)
  done

lemma pt_lookup_from_level_wrp:
  "\<lbrace>\<lambda>s. \<exists>asid. vspace_for_asid asid s = Some top_level_pt \<and>
               (\<forall>level slot pte.
                   vs_lookup_slot level asid vref s = Some (level, slot) \<longrightarrow>
                   ptes_of s level slot = Some pte \<longrightarrow>
                   is_PageTablePTE pte \<longrightarrow>
                   pte_ref pte = Some pt \<longrightarrow>
                   Q (slot, level) s) \<and>
               ((\<forall>level<max_pt_level. vs_lookup_table level asid vref s \<noteq> Some (level, pt)) \<longrightarrow>
                   E InvalidRoot s)\<rbrace>
   pt_lookup_from_level max_pt_level top_level_pt vref pt
   \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (wp pt_lookup_from_level_wp)
  apply (clarsimp simp: vspace_for_asid_def)
  apply (rule conjI; clarsimp)
   apply (frule pt_walk_max_level)
   apply (erule_tac x=level in allE)
   apply (erule allE, erule impE[where P="f = Some x" for f x])
    apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def entry_for_asid_def
                          vspace_for_pool_def in_omonad)
    apply fastforce
   apply simp
  apply (erule allE, erule (1) impE)
  apply (clarsimp simp: vs_lookup_table_def entry_for_asid_def vspace_for_pool_def
                  split: if_split_asm)
  done

crunches invalidate_tlb_by_asid
  for vs_lookup_target[wp]: "\<lambda>s. P (vs_lookup_target level asid vref s)"

lemma normal_pt_not_vspace_for_asid:
  "\<lbrakk> normal_pt_at pt s; pspace_aligned s; valid_asid_table s; valid_vspace_objs s \<rbrakk>
   \<Longrightarrow> vspace_for_asid asid s \<noteq> Some pt"
  apply clarsimp
  apply (drule vspace_for_asid_vs_lookup)
  apply (drule vs_lookup_table_pt_at; simp)
  apply (clarsimp simp: obj_at_def)
  done

lemma unmap_page_table_not_target:
  "\<lbrace>\<lambda>s. normal_pt_at pt s \<and> pspace_aligned s \<and> pspace_distinct s \<and>
        valid_asid_table s \<and> valid_vspace_objs s \<and>
        0 < asid \<and> vref \<in> user_region \<and>
        asid' = asid \<and> pt' = pt \<and> vref' = vref \<rbrace>
   unmap_page_table asid vref pt
   \<lbrace>\<lambda>_ s. vs_lookup_target level asid' vref' s \<noteq> Some (level, pt')\<rbrace>"
  unfolding unmap_page_table_def
  apply (wpsimp wp: store_pte_invalid_vs_lookup_target_unmap pt_lookup_from_level_wrp)
  apply (frule normal_pt_not_vspace_for_asid[where asid=asid]; assumption?)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def vs_lookup_table_def
                   split: if_split_asm;
          clarsimp simp: vspace_for_pool_def vspace_for_asid_def entry_for_asid_def obind_def
                   split: option.splits)
  apply (rule exI, rule conjI, assumption)
  apply (rule conjI; clarsimp)
   apply (fastforce simp: in_omonad)
  apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
   apply (clarsimp simp: pool_for_asid_vs_lookup vs_lookup_slot_def vspace_for_asid_def
                         entry_for_asid_def vspace_for_pool_def
                   split: if_split_asm)
  apply (rename_tac slot)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pte)
  apply (prop_tac "0 < level \<and> is_PageTablePTE pte")
   apply (drule (5) valid_vspace_objs_strong_slotD)
   apply clarsimp
   apply (case_tac pte; clarsimp simp: pte_ref_def)
   apply (clarsimp simp: data_at_def obj_at_def)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (drule (4) vs_lookup_table_step, simp)
  apply (prop_tac "level - 1 < max_pt_level", erule (1) vm_level.minus_one_leq_less)
  apply fastforce
  done

lemma is_final_cap_caps_of_state_2D:
  "\<lbrakk> caps_of_state s p = Some cap; caps_of_state s p' = Some cap';
     is_final_cap' cap'' s; gen_obj_refs cap \<inter> gen_obj_refs cap'' \<noteq> {};
     gen_obj_refs cap' \<inter> gen_obj_refs cap'' \<noteq> {} \<rbrakk>
       \<Longrightarrow> p = p'"
  apply (clarsimp simp: is_final_cap'_def3)
  apply (frule_tac x="fst p" in spec)
  apply (drule_tac x="snd p" in spec)
  apply (drule_tac x="fst p'" in spec)
  apply (drule_tac x="snd p'" in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state Int_commute
                        prod_eqI)
  done

crunches do_flush
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

crunches perform_page_invocation
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (simp: crunch_simps wp: crunch_wps set_object_pspace_respects_device_region
         pspace_respects_device_region_dmo)

lemma mapM_x_store_pte_caps_of_state[wp]:
  "mapM_x (swp (store_pte pt_t) InvalidPTE) slots \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma mapM_x_store_pte_valid_cap[wp]:
  "mapM_x (swp (store_pte pt_t) InvalidPTE) slots \<lbrace>valid_cap cap\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma mapM_x_store_pte_final_cap[wp]:
  "mapM_x (swp (store_pte pt_t) InvalidPTE) slots \<lbrace>is_final_cap' cap\<rbrace>"
  by (wpsimp wp: final_cap_lift)

lemma pt_ext[rule_format]:
  "\<lbrakk> \<forall>idx. idx \<le> mask (ptTranslationBits (pt_type pt)) \<longrightarrow> pt_apply pt idx = pt_apply pt' idx;
     pt_type pt = pt_type pt' \<rbrakk> \<Longrightarrow> pt = pt'"
  unfolding pt_apply_def
  apply (cases pt; cases pt'; clarsimp)
   apply (rule ext, rename_tac idx)
   apply (erule_tac x="ucast idx" in allE)
   apply (fastforce simp: ucast_up_ucast_id is_up bit_simps intro: ucast_leq_mask)
  apply (rule ext, rename_tac idx)
  apply (erule_tac x="ucast idx" in allE)
  apply (fastforce simp: ucast_up_ucast_id is_up bit_simps intro: ucast_leq_mask)
  done

lemma mapM_x_store_pte_empty[wp]:
  "\<lbrace> \<lambda>s. slots = [p , p + (1 << pte_bits) .e. p + (1 << pt_bits pt_t) - 1] \<and>
         is_aligned p (pt_bits pt_t) \<and> pt_at pt_t p s \<and> pt_t' = pt_t \<rbrace>
   mapM_x (swp (store_pte pt_t) InvalidPTE) slots
   \<lbrace> \<lambda>_ s. pts_of s p = Some (empty_pt pt_t') \<rbrace>"
  apply wp_pre
   apply (rule_tac I="\<lambda>s. slots = [p , p + (1 << pte_bits) .e. p + (1 << (pt_bits pt_t)) - 1] \<and>
                          is_aligned p (pt_bits pt_t) \<and> pt_at pt_t p s \<and> pt_t' = pt_t" and
                   V="\<lambda>xs s. \<forall>p' \<in> set slots - set xs. ptes_of s pt_t p' = Some InvalidPTE"
                   in mapM_x_inv_wp2)
    apply (clarsimp simp: obj_at_def in_omonad)
    apply (rule pt_ext[rotated], simp)
    apply (clarsimp simp: ptes_of_def in_omonad)
    apply (prop_tac "p + (idx << pte_bits) \<in> set slots")
     apply clarsimp
     apply (subst upto_enum_step_shift_red, simp)
       apply (simp add: bit_simps)
      apply (simp add: bit_simps)
     apply (clarsimp simp: image_iff)
     apply (rule_tac x="unat idx" in bexI)
      apply (clarsimp simp: ucast_nat_def shiftl_t2n)
     apply (clarsimp simp: bit_simps mask_def split: if_split_asm; solves unat_arith)
    apply (fastforce simp: table_index_plus table_base_plus)
   apply (wpsimp wp: store_pte_ptes_of)
  apply simp
  done

lemma vs_lookup_slot_pool_for_asid:
  "(vs_lookup_slot asid_pool_level asid vref s = Some (level, slot)) =
   (pool_for_asid asid s = Some slot \<and> level = asid_pool_level)"
  by (auto simp: vs_lookup_slot_def vs_lookup_table_def in_omonad)

lemma pt_walk_upd_Invalid:
  "pt_walk top_level level pt_ptr vref (ptes (pt_t, p \<mapsto> InvalidPTE)) = Some (level, p') \<Longrightarrow>
   pt_walk top_level level pt_ptr vref ptes = Some (level, p')"
  apply (induct top_level arbitrary: pt_ptr, simp)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad fun_upd2_def split: if_split_asm;
         fastforce simp: in_omonad pt_walk.simps)
  done

lemma store_pte_unreachable:
  "store_pte pt_t p InvalidPTE \<lbrace>\<lambda>s. vs_lookup_target level asid vref s \<noteq> Some (level, p')\<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del] vs_lookup_slot_pool_for_asid[simp]
  apply (wpsimp wp: set_object_wp simp: obj_at_def)
  apply (prop_tac "asid_pools_of s (table_base pt_t p) = None", clarsimp simp: opt_map_def)
  apply (erule notE)
  apply (cases "level = asid_pool_level"; clarsimp simp: vs_lookup_target_def in_omonad)
  apply (clarsimp simp: in_omonad vs_lookup_slot_def simp flip: asid_pool_level_neq
                  split: if_split_asm)
  apply (rename_tac pt_ptr)
  apply (clarsimp simp: in_omonad vs_lookup_table_def ptes_of_pts_of_upd split: if_split_asm)
  apply (drule pt_walk_upd_Invalid)
  apply (clarsimp cong: conj_cong)
  apply (rule conjI, clarsimp)
  apply (fastforce simp: ptes_of_def in_omonad fun_upd_apply split: if_split_asm)
  done

lemma mapM_x_store_pte_unreachable:
  "mapM_x (swp (store_pte pt_t) InvalidPTE) slots
   \<lbrace>\<lambda>s. vs_lookup_target level asid vref s \<noteq> Some (level, p)\<rbrace>"
  by (wpsimp wp: mapM_x_wp' store_pte_unreachable)

lemma mapM_x_typ_at[wp]:
  "mapM_x (swp (store_pte pt_t) InvalidPTE) slots \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

crunches unmap_page_table
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"
  and vspace_for_asid[wp]: "\<lambda>s. P (vspace_for_asid asid s)"
  and valid_cap[wp]: "valid_cap cap"

lemma vspace_for_asid_target:
  "vspace_for_asid asid s = Some pt \<Longrightarrow>
   vs_lookup_target asid_pool_level asid 0 s = Some (asid_pool_level, pt)"
  by (clarsimp simp: vs_lookup_target_def vs_lookup_slot_pool_for_asid vspace_for_asid_def
                     vspace_for_pool_def entry_for_asid_def in_omonad)

lemma perform_pt_inv_unmap_invs[wp]:
  "\<lbrace>invs and valid_pti (PageTableUnmap cap ct_slot)\<rbrace> perform_pt_inv_unmap cap ct_slot \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pt_inv_unmap_def
  apply (wpsimp wp: arch_update_cap_invs_unmap_page_table get_cap_wp hoare_vcg_ex_lift
                    hoare_vcg_all_lift hoare_vcg_imp_lift' mapM_x_swp_store_pte_invs_unmap
                    mapM_x_store_pte_unreachable hoare_vcg_ball_lift
                    unmap_page_table_not_target real_cte_at_typ_valid
                simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state)
  apply (clarsimp simp: is_arch_update_def is_cap_simps is_PageTableCap_def
                        update_map_data_def valid_cap_def valid_arch_cap_def cap_aligned_def)
  apply (frule caps_of_state_valid_cap, clarsimp)
  apply (rule conjI; clarsimp)
   apply (simp add: valid_cap_def cap_aligned_def)
   apply (erule valid_table_caps_pdD, fastforce)
  apply (rename_tac p pt_t asid vref)
  apply (clarsimp simp: wellformed_mapdata_def valid_cap_def cap_aligned_def cap_master_cap_simps)
  apply (simp flip: pt_bits_def)
  apply (rule conjI)
   apply clarsimp
   apply (subst (asm) mask_2pm1[where n="pt_bits _"], clarsimp simp: algebra_simps)
   apply (subst (asm) upto_enum_step_shift_red; simp?)
     apply (simp add: bit_simps)
    apply (simp add: bit_simps)
   apply clarsimp
   apply (subst table_base_plus[simplified shiftl_t2n mult_ac], assumption)
    apply (simp add: mask_def bit_simps)
    apply (unat_arith; subst (asm) unat_of_nat, simp)
   apply (subst table_base_plus[simplified shiftl_t2n mult_ac], assumption)
    apply (simp add: mask_def bit_simps)
    apply (unat_arith; subst (asm) unat_of_nat, simp)
   apply (rule conjI; clarsimp)
    apply (drule valid_global_refsD2, clarsimp)
    apply (simp add: cap_range_def)
   apply (frule vspace_for_asid_target)
   apply (drule valid_vs_lookupD; clarsimp)
   apply (clarsimp simp: obj_at_def)
   apply (frule (1) cap_to_pt_is_pt_cap_and_type, solves \<open>simp add: in_omonad\<close>)
    apply (fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)
  apply (fastforce simp add: mask_def algebra_simps)
  done

lemma set_cap_vspace_for_asid[wp]:
  "set_cap p cap \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  by (wpsimp wp: vspace_for_asid_lift)

lemma cap_asid_None_pt[simp]:
  "(cap_asid (ArchObjectCap (PageTableCap p pt_t m)) = None) = (m = None)"
  by (cases m; clarsimp simp: cap_asid_def)

lemma perform_pt_inv_map_invs[wp]:
  "\<lbrace>invs and valid_pti (PageTableMap cap ct_slot pte slot level)\<rbrace>
   perform_pt_inv_map cap ct_slot pte slot level
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pt_inv_map_def
  apply (wpsimp wp: store_pte_invs arch_update_cap_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift'
                    dmo_invs_lift)
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps
                        is_PageTableCap_def cap_master_cap_simps invalid_pte_at_def)
  apply (rename_tac cap' p' vref asid pt_t ao)
  apply (prop_tac "is_pt_cap cap'")
   apply (case_tac cap'; simp add: cap_master_cap_simps)
   apply (rename_tac acap, case_tac acap; simp add: cap_master_cap_simps)
  apply (clarsimp simp: is_cap_simps cap_master_cap_simps)
  apply (frule caps_of_state_valid_cap, fastforce)
  apply (clarsimp simp: vs_lookup_slot_def pool_for_asid_vs_lookup split: if_split_asm)
   apply (drule pool_for_asid_validD, clarsimp)
   apply (clarsimp simp: pte_at_def obj_at_def in_omonad)
  apply clarsimp
  apply (rename_tac pt_ptr)
  apply (prop_tac "is_aligned pt_ptr (pt_bits level)", fastforce dest!: vs_lookup_table_is_aligned)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: valid_cap_def cap_aligned_def valid_arch_cap_def)
  apply (rule conjI)
   apply (erule (3) reachable_page_table_not_global)
  apply (rule conjI)
   apply (clarsimp simp: valid_mapping_insert_def user_region_invalid_mapping_slots
                         pt_slot_offset_offset[where level=max_pt_level, simplified])
  apply (rule conjI, clarsimp)
   apply (rename_tac level' asid' vref')
   apply (prop_tac "level' \<le> max_pt_level")
    apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
    apply (clarsimp simp: vs_lookup_table_def simp flip: asid_pool_level_neq)
    apply (drule_tac p=pt_ptr in pool_for_asid_validD, clarsimp)
    apply (clarsimp simp: in_omonad)
   apply (drule (1) vs_lookup_table_unique_level; simp)
   apply clarsimp
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap_and_type, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: is_cap_simps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (rule conjI, clarsimp)
   apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap_and_type, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: is_cap_simps)
   apply (thin_tac "caps_of_state s ct_slot = Some cap" for cap)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply clarsimp
  apply (rename_tac level' asid' vref')
  apply (prop_tac "level' \<le> max_pt_level")
   apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
   apply (clarsimp simp: vs_lookup_table_def simp flip: asid_pool_level_neq)
   apply (drule_tac p=pt_ptr in pool_for_asid_validD, clarsimp)
   apply (clarsimp simp: in_omonad)
  apply (frule_tac level'=level' in vs_lookup_table_unique_level, assumption; clarsimp)
  apply (rule conjI, clarsimp) (* p \<noteq> pt_ptr *)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap_and_type, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: is_cap_simps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (frule pt_slot_offset_vref_for_level; simp)
  apply (cases ct_slot, fastforce)
  done

lemma perform_page_table_invocation_invs[wp]:
  "\<lbrace>invs and valid_pti pti\<rbrace> perform_page_table_invocation pti \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_page_table_invocation_def by (cases pti; wpsimp)

crunch cte_wp_at [wp]: unmap_page "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch typ_at [wp]: unmap_page "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas unmap_page_typ_ats [wp] = abs_typ_at_lifts [OF unmap_page_typ_at]

lemma pt_lookup_slot_cap_to:
  "\<lbrakk> invs s; \<exists>\<rhd>(max_pt_level, pt) s; is_aligned pt (pt_bits VSRootPT_T); vptr \<in> user_region;
     pt_lookup_slot pt vptr (ptes_of s) = Some (level, slot) \<rbrakk>
   \<Longrightarrow> \<exists>p cap. caps_of_state s p = Some cap \<and> is_pt_cap cap \<and> obj_refs cap = {table_base level slot} \<and>
               s \<turnstile> cap \<and> cap_asid cap \<noteq> None"
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (frule pt_walk_max_level)
  apply (rename_tac pt_ptr asid vref)
  apply (subgoal_tac "vs_lookup_table level asid vptr s = Some (level, pt_ptr)")
   prefer 2
   apply (drule pt_walk_level)
   apply (clarsimp simp: vs_lookup_table_def in_omonad)
  apply (frule_tac level=level in valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (drule vs_lookup_table_target[where level=level], simp)
  apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
  apply (frule (1) cap_to_pt_is_pt_cap_and_type, simp)
   apply (fastforce intro: valid_objs_caps)
  apply (frule pts_of_Some_alignedD, fastforce)
  apply (frule caps_of_state_valid, fastforce)
  apply (fastforce simp: cap_asid_def is_cap_simps)
  done

lemma find_vspace_for_asid_cap_to:
  "\<lbrace>invs\<rbrace>
   find_vspace_for_asid asid
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> obj_refs cap = {rv} \<and>
                      is_pt_cap cap \<and> s \<turnstile> cap \<and> is_aligned rv (pt_bits VSRootPT_T)\<rbrace>, -"
  apply wpsimp
  apply (drule vspace_for_asid_vs_lookup)
  apply (frule valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (frule pts_of_Some_alignedD, fastforce)
  apply simp
  apply (drule vs_lookup_table_target, simp)
  apply (drule valid_vs_lookupD; clarsimp simp: vref_for_level_def)
  apply (frule (1) cap_to_pt_is_pt_cap_and_type, simp)
   apply (fastforce intro: valid_objs_caps)
  apply (fastforce intro: caps_of_state_valid cap_to_pt_is_pt_cap_and_type)
  done

lemma ex_pt_cap_eq:
  "(\<exists>ref cap. caps_of_state s ref = Some cap \<and> obj_refs cap = {p} \<and> is_pt_cap cap) =
   (\<exists>ref pt_t asid. caps_of_state s ref = Some (ArchObjectCap (PageTableCap p pt_t asid)))"
  by (fastforce simp add: is_pt_cap_def obj_refs_def is_PageTableCap_def)

lemma pt_bits_left_not_asid_pool_size:
  "pt_bits_left asid_pool_level \<noteq> pageBitsForSize sz"
  by (cases sz; simp add: pt_bits_left_def bit_simps asid_pool_level_size size_max_pt_level)

lemma unmap_page_invs:
  "\<lbrace>invs and K (vptr \<in> user_region \<and> vmsz_aligned vptr sz)\<rbrace>
   unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding unmap_page_def
  apply (wpsimp wp: store_pte_invs_unmap invalidate_tlb_by_asid_va_invs dmo_invs_lift)
  apply (rule conjI; clarsimp)
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (rename_tac level pte pt_ptr)
  apply (drule vs_lookup_level)
  apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (frule vs_lookup_table_target, simp)
  apply (frule pts_of_Some_alignedD, clarsimp)
  apply (frule vref_for_level_user_region)
  apply (frule (2) vs_lookup_target_not_global)
  apply simp
  apply (frule (1) valid_vs_lookupD; clarsimp)
  apply (frule (1) cap_to_pt_is_pt_cap_and_type, fastforce, fastforce intro!: valid_objs_caps)
  apply (rule conjI, fastforce simp: is_cap_simps)
  apply clarsimp
  apply (drule (3) vs_lookup_table_vspace)
  apply (simp add: user_region_invalid_mapping_slots)
  done

lemma set_mi_invs[wp]:
  "set_message_info t a \<lbrace>invs\<rbrace>"
  by (simp add: set_message_info_def, wp)

lemma data_at_orth:
  "data_at a p s
   \<Longrightarrow> \<not> ep_at p s \<and> \<not> ntfn_at p s \<and> \<not> cap_table_at sz p s \<and> \<not> tcb_at p s \<and> \<not> asid_pool_at p s
         \<and> \<not> pt_at pt_t p s \<and> \<not> asid_pool_at p s \<and> \<not> vcpu_at p s"
  apply (clarsimp simp: data_at_def obj_at_def a_type_def)
  apply (case_tac "kheap s p",simp)
  subgoal for ko by (case_tac ko,auto simp add: is_ep_def is_ntfn_def is_cap_table_def is_tcb_def)
  done

lemma data_at_frame_cap:
  "\<lbrakk>data_at sz p s; valid_cap cap s; p \<in> obj_refs cap\<rbrakk> \<Longrightarrow> is_frame_cap cap"
  by (cases cap; clarsimp simp: is_frame_cap_def valid_cap_def valid_arch_cap_ref_def data_at_orth
                         split: option.splits arch_cap.splits)

lemma perform_pg_inv_get_addr[wp]:
  "\<lbrace>invs and valid_page_inv (PageGetAddr ptr)\<rbrace> perform_pg_inv_get_addr ptr \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pg_inv_get_addr_def by wpsimp

lemma unmap_page_pool_for_asid[wp]:
  "unmap_page pgsz asid vref pt \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  unfolding unmap_page_def by (wpsimp simp: pool_for_asid_def)

lemma data_at_level:
  "\<lbrakk> data_at pgsz p s; data_at (vmsize_of_level level) p s;
     pt_bits_left level' = pageBitsForSize pgsz; level \<le> max_page_level \<rbrakk> \<Longrightarrow>
   level = level'"
  by (fastforce simp: data_at_def obj_at_def)

lemma pt_lookup_slot_vs_lookup_slotI0:
  "\<lbrakk> vspace_for_asid asid s = Some pt_ptr;
     pt_lookup_slot pt_ptr vref (ptes_of s) = Some (level, slot) \<rbrakk>
   \<Longrightarrow> vs_lookup_slot 0 asid vref s = Some (level, slot)"
  unfolding pt_lookup_slot_def pt_lookup_slot_from_level_def vs_lookup_slot_def
  apply (clarsimp simp: in_omonad)
  apply (drule (1) pt_lookup_vs_lookupI, simp)
  apply (rule_tac x=level in exI)
  apply clarsimp
  apply (drule vs_lookup_level)
  apply (fastforce dest: pt_walk_max_level)
  done

crunches invalidate_tlb_by_asid_va
  for vs_lookup_target[wp]: "\<lambda>s. P (vs_lookup_target level asid' vref' s)"

lemma unmap_page_not_target:
  "\<lbrace> data_at pgsz pptr and valid_asid_table and valid_vspace_objs
     and pspace_aligned and pspace_distinct
     and unique_table_refs and valid_vs_lookup and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (0 < asid \<and> vref \<in> user_region \<and> pptr' = pptr \<and> asid' = asid \<and> vref' = vref) \<rbrace>
   unmap_page pgsz asid vref pptr
   \<lbrace>\<lambda>_ s. vs_lookup_target level asid' vref' s \<noteq> Some (level, pptr')\<rbrace>"
  unfolding unmap_page_def
  supply pt_bits_left_not_asid_pool_size[simp]
         vs_lookup_slot_pool_for_asid[simp]
         pool_for_asid_vs_lookup[simp]
  apply (wpsimp wp: store_pte_invalid_vs_lookup_target_unmap)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def vspace_for_asid_def obind_def vs_lookup_slot_def
                         vs_lookup_table_def entry_for_asid_def vspace_for_pool_def
                   split: if_split_asm option.splits)
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
  apply (rule conjI; clarsimp simp: in_omonad)
   apply (drule vs_lookup_slot_level)
   apply (rename_tac slot level' pte)
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: pte_ref_def is_PagePTE_def pptr_from_pte_def)
   apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
    apply (prop_tac "vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, pptr)")
     apply (clarsimp simp: vs_lookup_table_def in_omonad)
    apply (drule (2) valid_vspace_objs_strongD; clarsimp)
    apply (clarsimp simp: data_at_def in_omonad obj_at_def)
   apply (clarsimp simp: in_omonad)
   apply (rename_tac pte')
   apply (frule (5) valid_vspace_objs_strong_slotD[where level=level])
   apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
   apply (rename_tac pt_ptr pt_ptr')
   apply (prop_tac "is_PagePTE pte'")
    apply (case_tac pte'; clarsimp simp: obj_at_def data_at_def pptr_from_pte_def)
   apply (case_tac "level = level'", simp add: pte_ref_Some_cases)
   apply (clarsimp simp: is_PagePTE_def)
   apply (drule (3) data_at_level, simp)
  (* lookup has stopped at wrong level for pgsz *)
  apply (rename_tac level')
  apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
   apply (prop_tac "vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, pptr)")
    apply (clarsimp simp: vs_lookup_table_def in_omonad)
   apply (drule (2) valid_vspace_objs_strongD; clarsimp)
   apply (clarsimp simp: data_at_def in_omonad obj_at_def)
  apply (prop_tac "level' \<le> max_pt_level")
   apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def split: if_split_asm)
   apply (drule pt_walk_max_level, simp)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pte)
  apply (frule (5) valid_vspace_objs_strong_slotD[where level=level], clarsimp)
  apply (prop_tac "is_PagePTE pte \<and> pgsz = vmsize_of_level level")
   apply (case_tac pte; fastforce simp: data_at_def obj_at_def pptr_from_pte_def pte_base_addr_def)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (rename_tac pt_ptr' pt_ptr)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level)
   apply (drule_tac level'=level and level=level' in vs_lookup_splitD; assumption?)
   apply clarsimp
   apply (subst (asm) pt_walk.simps)
   apply (clarsimp simp: is_PagePTE_def split: if_split_asm)
  apply (simp add: not_le)
  apply (prop_tac "level' \<noteq> 0", clarsimp)
  apply (frule vs_lookup_table_stopped; clarsimp)
  apply (drule_tac level'=level' in vs_lookup_splitD; simp?)
  apply (drule vs_lookup_level)
  apply clarsimp
  apply (subst (asm) pt_walk.simps)
  apply clarsimp
  done

lemma perform_pg_inv_unmap[wp]:
  "\<lbrace>invs and valid_page_inv (PageUnmap cap ct_slot)\<rbrace> perform_pg_inv_unmap cap ct_slot \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pg_inv_unmap_def
  apply (wpsimp wp: arch_update_cap_invs_unmap_page hoare_vcg_ex_lift hoare_vcg_ball_lift
                    hoare_vcg_all_lift hoare_vcg_const_imp_lift get_cap_wp unmap_page_cte_wp_at
                    hoare_vcg_imp_lift'
                    unmap_page_not_target unmap_page_invs)
  apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state is_cap_simps is_arch_update_def
                        update_map_data_def cap_master_cap_simps)
  apply (frule caps_of_state_valid, clarsimp)
  apply (case_tac m; simp)
   apply (clarsimp simp: valid_cap_def valid_arch_cap_def cap_aligned_def cap_master_cap_simps)
  apply (clarsimp simp: valid_unmap_def cap_master_cap_simps valid_cap_def wellformed_mapdata_def
                        cap_aligned_def)
  apply (fastforce simp: data_at_def split: if_split_asm intro: valid_objs_caps)
  done

lemma if_pair_imp_strengthen:
  "\<And>s. Q s \<Longrightarrow> (if P then \<lambda>s. \<forall>x xa. R (x, xa) \<longrightarrow> T \<longrightarrow> Q s else Q) s"
  by auto

lemma perform_pg_inv_map_invs[wp]:
  "\<lbrace>invs and valid_page_inv (PageMap cap ct_slot (pte, slot, level))\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot level
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pg_inv_map_def
  supply if_split[split del]
  apply (wpsimp wp: store_pte_invs arch_update_cap_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift'
                    invalidate_tlb_by_asid_va_invs
         | strengthen if_pair_imp_strengthen)+
  apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps
                        cap_master_cap_simps parent_for_refs_def valid_slots_def same_ref_def)
  apply (rename_tac cref cidx asid vref)
  apply (frule caps_of_state_valid, clarsimp)
  apply (prop_tac "is_FrameCap cap")
   apply (cases cap; simp add: cap_master_cap_simps)
  apply (intro conjI)
        apply (blast dest: vs_lookup_slot_unique_level)
       apply (clarsimp simp: is_FrameCap_def cap_master_cap_simps valid_cap_def cap_aligned_def
                             valid_arch_cap_def)
      apply (simp add: vs_lookup_slot_table_unfold)
      apply (blast dest: reachable_page_table_not_global)
     apply clarsimp
     apply (clarsimp simp: is_PageTablePTE_def)
    apply (clarsimp simp: is_FrameCap_def split: if_splits)
    apply (drule (1) unique_table_refsD[rotated], solves \<open>simp\<close>; clarsimp)
  apply clarsimp
  apply (rename_tac level_x asid' vref' level'')
  apply (rule conjI, clarsimp simp: is_PagePTE_def)
  apply (rule conjI)
   apply (erule_tac x=level_x in allE, erule impE, fastforce)
   apply (clarsimp simp: is_PagePTE_def)
   apply (drule_tac p="(cref,cidx)" in caps_of_state_valid, clarsimp)
   apply (clarsimp simp: valid_cap_def obj_at_def data_at_def)
  apply (rename_tac level' asid' vref' p')
  apply (prop_tac "level' \<le> max_pt_level")
   apply (clarsimp simp flip: asid_pool_level_neq simp: pool_for_asid_vs_lookup)
   apply (drule pool_for_asid_validD, clarsimp)
   apply (drule_tac p="(cref,cidx)" in caps_of_state_valid, clarsimp)
   apply (clarsimp simp: valid_cap_def obj_at_def in_omonad)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (rename_tac pt_ptr)
  apply (frule_tac bot_level=level in vs_lookup_table_is_aligned; clarsimp)
  apply ((drule (1) vs_lookup_table_unique_level; assumption?), rule refl)
  apply (elim conjE)
  apply (drule pt_slot_offset_vref_for_level; blast?)
  apply (cases ct_slot)
  apply (fastforce split: if_split)
  done

crunches do_flush
  for mem[wp]: "\<lambda>ms. P (underlying_memory ms)"
  and irq_masks[wp]: "\<lambda>ms. P (irq_masks ms)"

crunches perform_flush
  for invs[wp]: invs
  (wp: dmo_invs_lift)

lemma perform_page_invs [wp]:
  "\<lbrace>invs and valid_page_inv pg_inv\<rbrace> perform_page_invocation pg_inv \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_page_invocation_def
  by (cases pg_inv; wpsimp)

end

locale asid_pool_map = Arch +
  fixes s ap pool asid ptp pt and s' :: "'a::state_ext state"
  defines "s' \<equiv> s\<lparr>kheap := kheap s(ap \<mapsto> ArchObj (ASIDPool (pool(asid_low_bits_of asid \<mapsto> ptp))))\<rparr>"
  assumes ap:  "asid_pools_of s ap = Some pool"
  assumes new: "pool (asid_low_bits_of asid) = None"
  assumes pt:  "pts_of s (ap_vspace ptp) = Some pt"
  assumes empty: "pt = empty_pt VSRootPT_T"
  assumes lookup: "pool_for_asid asid s = Some ap"
  assumes valid_vspace_objs: "valid_vspace_objs s"
  assumes valid_asids: "valid_asid_table s"
  assumes aligned: "is_aligned (ap_vspace ptp) (pt_bits VSRootPT_T)"
begin

lemma arch_state[simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)

lemma pool_for_asid[simp]:
  "pool_for_asid a s' = pool_for_asid a s"
  by (simp add: pool_for_asid_def)

lemma asid_pools_of[simp]:
  "asid_pools_of s' = (asid_pools_of s)(ap \<mapsto> pool(asid_low_bits_of asid \<mapsto> ptp))"
  by (simp add: s'_def)

lemma entry_for_pool[simp]:
  "entry_for_pool ap asid ((asid_pools_of s)(ap \<mapsto> pool(asid_low_bits_of asid \<mapsto> ptp))) = Some ptp"
  by (simp add: entry_for_pool_def in_omonad)

lemma pts_of[simp]:
  "pts_of s' = pts_of s"
proof -
  from ap
  have "pts_of s ap = None" by (simp add: opt_map_def split: option.splits)
  thus ?thesis by (simp add: s'_def)
qed

lemma empty_for_user:
  "vref \<in> user_region \<Longrightarrow>
   pt_apply pt (table_index VSRootPT_T (pt_slot_offset max_pt_level (ap_vspace ptp) vref)) = InvalidPTE"
  using empty aligned
  by clarsimp

lemma aligned_pte_bits[simp]:
  "is_aligned (pt_slot_offset max_pt_level (ap_vspace ptp) vref) pte_bits"
  by (rule is_aligned_pt_slot_offset_pte, rule aligned)

lemmas table_base_pt_slot_offset_VSRoot[simp] =
  table_base_pt_slot_offset[where level=max_pt_level, simplified]

lemma vs_lookup_table:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_table level asid' vref s' =
     (if asid' = asid \<and> level \<le> max_pt_level
      then Some (max_pt_level, (ap_vspace ptp))
      else vs_lookup_table level asid' vref s)"
  apply clarsimp
  apply (rule conjI; clarsimp)
   using lookup
   apply (clarsimp simp: vs_lookup_table_def vspace_for_pool_def in_omonad pool_for_asid_def)
   apply (subst pt_walk.simps)
   using pt aligned
   apply (clarsimp simp: obind_def ptes_of_def empty_for_user)
   apply (erule notE)
   using empty
   apply simp
  apply (clarsimp simp: vs_lookup_table_def)
  apply (rule obind_eqI, simp)
  apply clarsimp
  using ap lookup new
  apply (clarsimp simp: obind_def split: option.splits)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def obind_def split: option.splits if_split_asm)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def obind_def split: option.splits if_split_asm)
   apply (clarsimp simp: pool_for_asid_def)
   using valid_asids
   apply (clarsimp simp: valid_asid_table_def)
   apply (drule (2) inj_on_domD[rotated])
   apply (drule (1) asid_high_low_inj)
   apply clarsimp
  apply (clarsimp simp: vspace_for_pool_def entry_for_pool_def split: if_split_asm)
  done

lemma vs_lookup_slot:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_slot level asid' vref s' =
     (if asid' = asid \<and> level \<le> max_pt_level
      then Some (max_pt_level, pt_slot_offset max_pt_level (ap_vspace ptp) vref)
      else vs_lookup_slot level asid' vref s)"
  apply (simp add: vs_lookup_slot_def)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: in_omonad vs_lookup_table)
  apply (rule obind_eqI; clarsimp simp: vs_lookup_table)
  done

lemma pte_refs_of_None:
  "vref \<in> user_region \<Longrightarrow> pte_refs_of VSRootPT_T (pt_slot_offset max_pt_level (ap_vspace ptp) vref) s = None"
  using aligned pt
  by (clarsimp simp: ptes_of_def obind_def opt_map_def empty_for_user split: option.splits)

lemma vs_lookup_table_None:
  "level \<le> max_pt_level \<Longrightarrow> vs_lookup_table level asid vref s = None"
  using lookup new ap
  by (clarsimp simp: vs_lookup_table_def obind_def pool_for_asid_def
                     vspace_for_pool_def entry_for_pool_def
               split: option.splits)

lemma vs_lookup_slot_None:
  "level \<le> max_pt_level \<Longrightarrow> vs_lookup_slot level asid vref s = None"
  by (clarsimp simp: vs_lookup_slot_def obind_def vs_lookup_table_None)

lemma vs_lookup_target:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_target level asid' vref s' =
     (if asid' = asid \<and> level = asid_pool_level
      then Some (level, ap_vspace ptp)
      else vs_lookup_target level asid' vref s)"
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def in_omonad vs_lookup_slot)
   apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def in_omonad)
   using lookup
   apply (simp add: pool_for_asid_def vspace_for_pool_def in_omonad)
  apply (cases "asid' = asid")
   apply clarsimp
   apply (clarsimp simp: vs_lookup_target_def)
   apply (clarsimp simp: obind_def vs_lookup_slot_None vs_lookup_slot pte_refs_of_None)
  apply clarsimp
  apply (simp add: vs_lookup_target_def obind_def)
  apply (clarsimp simp: vs_lookup_slot)
  apply (cases "vs_lookup_slot level asid' vref s"; clarsimp)
  apply (rule conjI; clarsimp)
   prefer 2
   apply (simp split: option.splits)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (clarsimp simp: vs_lookup_table_def in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
   apply (drule pt_walk_max_level, simp)
  apply (rename_tac ap')
  apply (subgoal_tac "ap' \<noteq> ap \<or> asid_low_bits_of asid' \<noteq> asid_low_bits_of asid")
   using ap
   apply (simp add: vspace_for_pool_def entry_for_pool_def obind_def split: option.splits)
  using lookup valid_asids
  apply (clarsimp simp: valid_asid_table_def pool_for_asid_def)
  apply (drule (2) inj_on_domD[rotated])
  apply (drule (1) asid_high_low_inj)
  apply clarsimp
  done

lemma valid_pool:
  "valid_vspace_obj asid_pool_level (ASIDPool pool) s"
proof -
  from lookup
  have "vs_lookup_table asid_pool_level asid 0 s = Some (asid_pool_level, ap)"
    by (clarsimp simp: vs_lookup_table_def in_omonad)
  with valid_vspace_objs ap
  show ?thesis by (fastforce dest: valid_vspace_objsD simp: in_omonad)
qed

lemma valid_pte:
  "valid_pte level pte s \<Longrightarrow> valid_pte level pte s'"
  using ap
  apply (cases pte; simp add: pt_at_eq)
  apply (clarsimp simp: data_at_def obj_at_def s'_def in_omonad)
  done

lemma valid_vspace_obj:
  "valid_vspace_obj level ao s \<Longrightarrow> valid_vspace_obj level ao s'"
  by (cases ao; simp add: pt_at_eq valid_pte)

end

context Arch begin global_naming AARCH64

lemma set_asid_pool_arch_objs_map:
  "\<lbrace>valid_vspace_objs and valid_arch_state and valid_global_objs and
    valid_kernel_mappings and pspace_aligned and
    (\<lambda>s. asid_pools_of s ap = Some pool) and
    K (pool (asid_low_bits_of asid) = None) and
    (\<lambda>s. pool_for_asid asid s = Some ap) and
    (\<lambda>s. pts_of s (ap_vspace ape) = Some (empty_pt VSRootPT_T)) \<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> ape))
  \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  unfolding set_asid_pool_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (frule (2) asid_pool_map.intro, rule refl; assumption?)
    apply (clarsimp simp: valid_arch_state_def)
   apply (drule (1) pspace_aligned_pts_ofD, simp)
  apply (subst valid_vspace_objs_def)
  apply (clarsimp simp: asid_pool_map.vs_lookup_table split: if_split_asm)
   apply (clarsimp simp: in_omonad fun_upd_apply split: if_split_asm)
  apply (clarsimp simp: in_omonad fun_upd_apply split: if_split_asm)
   prefer 2
   apply (frule (2) valid_vspace_objsD)
    apply (simp add: in_omonad)
   apply (simp add: asid_pool_map.valid_vspace_obj)
  apply (clarsimp simp: obj_at_def fun_upd_apply)
  apply (rule conjI; clarsimp)
  apply (frule asid_pool_map.valid_pool)
  apply (fastforce simp: obj_at_def)
  done

lemma caps_of_state_fun_upd:
  "obj_at (same_caps val) p s \<Longrightarrow>
   (caps_of_state (s\<lparr>kheap := (kheap s) (p \<mapsto> val)\<rparr>)) = caps_of_state s"
  apply (drule caps_of_state_after_update)
  apply (simp add: fun_upd_def)
  done

lemma set_asid_pool_valid_arch_caps_map:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_global_objs and valid_objs
    and valid_vspace_objs and pspace_aligned and
    (\<lambda>s. asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
         (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {ap_vspace ape} \<and>
                    vs_cap_ref cap = Some (asid, 0)))
    and (\<lambda>s. pts_of s (ap_vspace ape) = Some (empty_pt VSRootPT_T))
    and K (pool (asid_low_bits_of asid) = None \<and> 0 < asid)\<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> ape))
  \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  unfolding set_asid_pool_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (frule (2) asid_pool_map.intro, rule refl; assumption?)
    apply (clarsimp simp: valid_arch_state_def)
   apply (drule (1) pspace_aligned_pts_ofD, simp)
  apply (clarsimp simp: valid_arch_caps_def)
  apply (simp add: caps_of_state_fun_upd obj_at_def in_omonad)
  apply (subgoal_tac "pts_of s ap = None")
   prefer 2
   apply (clarsimp simp: opt_map_def)
  apply simp
  apply (clarsimp simp: valid_vs_lookup_def caps_of_state_fun_upd obj_at_def)
  apply (clarsimp simp: asid_pool_map.vs_lookup_target split: if_split_asm)
  by (fastforce simp: vref_for_level_asid_pool user_region_def)

lemma vmid_for_asid_map_None:
  "\<lbrakk> asid_pools_of s ap = Some pool; pool_for_asid asid s = Some ap;
     pool (asid_low_bits_of asid) = None; ap_vmid ape = None \<rbrakk> \<Longrightarrow>
   (\<lambda>asid'. vmid_for_asid_2 asid' (asid_table s)
                                  (asid_pools_of s(ap \<mapsto> pool(asid_low_bits_of asid \<mapsto> ape)))) =
   vmid_for_asid s"
  unfolding vmid_for_asid_def
  apply (rule ext)
  apply (clarsimp simp: vmid_for_asid_2_def entry_for_pool_def pool_for_asid_def obind_def
                        opt_map_def
                  split: option.splits)
  done

lemma set_asid_pool_vmid_inv:
  "\<lbrace>\<lambda>s. vmid_inv s \<and> asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
        pool (asid_low_bits_of asid) = None \<and> ap_vmid ape = None \<rbrace>
   set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> ape))
   \<lbrace>\<lambda>_. vmid_inv\<rbrace>"
  unfolding vmid_inv_def
  apply (wp_pre, wps, wp)
  apply (simp add: vmid_for_asid_map_None del: fun_upd_apply)
  done

lemma set_asid_pool_valid_arch_state:
  "\<lbrace>valid_arch_state and
    (\<lambda>s. asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
         (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {ap_vspace ape} \<and>
                    vs_cap_ref cap = Some (asid, 0)))
    and (\<lambda>s. \<exists>pt. pts_of s (ap_vspace ape) = Some pt \<and> pt = empty_pt VSRootPT_T)
    and K (pool (asid_low_bits_of asid) = None \<and> 0 < asid  \<and> ap_vmid ape = None)\<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> ape))
  \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def
  by (wpsimp wp: set_asid_pool_vmid_inv|wps)+

lemma set_asid_pool_invs_map:
  "\<lbrace>invs and
    (\<lambda>s. asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
         (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {ap_vspace ape} \<and>
                    vs_cap_ref cap = Some (asid, 0)))
    and (\<lambda>s. \<exists>pt. pts_of s (ap_vspace ape) = Some pt \<and> pt = empty_pt VSRootPT_T)
    and K (pool (asid_low_bits_of asid) = None \<and> 0 < asid \<and> ap_vmid ape = None)\<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> ape))
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_asid_map_def)
  apply (wpsimp wp: valid_irq_node_typ set_asid_pool_typ_at set_asid_pool_arch_objs_map
                    valid_irq_handlers_lift set_asid_pool_valid_arch_caps_map
                    set_asid_pool_valid_arch_state)
  done

lemma ako_asid_pools_of:
  "ako_at (ASIDPool pool) ap s = (asid_pools_of s ap = Some pool)"
  by (clarsimp simp: obj_at_def in_omonad)

lemma store_pte_vs_lookup_target_unreachable:
  "\<lbrace>\<lambda>s. (\<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_t p) s) \<and>
        vref \<in> user_region \<and>
        vs_lookup_target bot_level asid vref s \<noteq> Some (level, p') \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>rv s. vs_lookup_target bot_level asid vref s \<noteq> Some (level, p')\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (subst (asm) vs_lookup_target_unreachable_upd_idem; clarsimp)
  done

lemma store_pte_vs_lookup_table_unreachable:
  "\<lbrace>\<lambda>s. (\<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_t p) s) \<and>
        vref \<in> user_region \<and>
        vs_lookup_table bot_level asid vref s \<noteq> Some (level, p') \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>rv s. vs_lookup_table bot_level asid vref s \<noteq> Some (level, p')\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (subst (asm) vs_lookup_table_unreachable_upd_idem'; clarsimp)
  done

lemma store_pte_valid_arch_state_unreachable:
  "\<lbrace>valid_arch_state and valid_global_vspace_mappings and (\<lambda>s. table_base pt_t p \<notin> global_refs s) \<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def
  by wpsimp

lemma store_pte_valid_vs_lookup_unreachable:
  "\<lbrace>valid_vs_lookup and pspace_aligned and valid_vspace_objs and valid_asid_table and
    (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_t p) s)\<rbrace>
   store_pte pt_t p pte
   \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_vs_lookup_target_unreachable)
  apply (erule disjE; clarsimp)
  done

lemma store_pte_valid_arch_caps_unreachable:
  "\<lbrace> invs and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_t p) s) and
     (\<lambda>s. \<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base pt_t p) pt_t asidopt))
                          \<longrightarrow> asidopt \<noteq> None) and
     (\<lambda>s. table_base pt_t p \<notin> global_refs s) \<rbrace>
   store_pte pt_t p pte
   \<lbrace> \<lambda>_. valid_arch_caps \<rbrace>"
  unfolding valid_arch_caps_def
  apply (wpsimp wp: store_pte_valid_vs_lookup_unreachable store_pte_valid_table_caps)
  by (fastforce simp: invs_def valid_state_def valid_arch_caps_def intro: valid_objs_caps)

lemma store_pte_invs_unreachable:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base pt_t p) s) and
    K (wellformed_pte pte \<and> valid_mapping_insert pt_t p pte) and
    (\<lambda>s. \<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base pt_t p) pt_t asidopt))
                         \<longrightarrow> asidopt \<noteq> None) and
    (\<lambda>s. table_base pt_t p \<notin> global_refs s) \<rbrace>
  store_pte pt_t p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  apply (wpsimp wp: store_pte_valid_arch_state_unreachable store_pte_valid_arch_caps_unreachable
                    store_pte_equal_kernel_mappings_no_kernel_slots
                    store_pte_valid_global_vspace_mappings
                    store_pte_valid_vspace_objs)
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_state_def
                   valid_arch_caps_def valid_objs_caps
              cong: conj_cong)
  done

lemma invs_valid_global_vspace_mappings[elim!]:
  "invs s \<Longrightarrow> valid_global_vspace_mappings s"
  by (clarsimp simp: invs_def valid_state_def)

lemma is_aligned_pte_offset:
  "is_aligned pt_ptr (pt_bits pt_t) \<Longrightarrow>
   is_aligned (pt_ptr + (i << pte_bits)) (pte_bits)"
  apply (rule is_aligned_add)
   apply (erule is_aligned_weaken, simp add: bit_simps)
  apply (simp add: is_aligned_shiftl)
  done

lemma ptes_of_from_pt:
  "\<lbrakk> pts pt_ptr = Some pt; is_aligned pt_ptr (pt_bits (pt_type pt));
     i \<le> mask (ptTranslationBits (pt_type pt)) \<rbrakk> \<Longrightarrow>
   level_pte_of (pt_type pt) (pt_ptr + (i << pte_bits)) pts = Some (pt_apply pt i)"
  by (clarsimp simp: level_pte_of_def in_omonad table_base_plus table_index_plus is_aligned_pte_offset)

lemma is_vsroot_cap_eq:
  "is_vsroot_cap cap = (\<exists>p m. cap = ArchObjectCap (PageTableCap p VSRootPT_T m))"
  unfolding is_vsroot_cap_def arch_cap_fun_lift_def
  by (auto simp: is_PageTableCap_def split: cap.splits)

lemma perform_asid_pool_invs[wp]:
  "\<lbrace>invs and valid_apinv api\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: perform_asid_pool_invocation_def store_asid_pool_entry_def
                  split: asid_pool_invocation.splits)
  apply (wpsimp wp: set_asid_pool_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift'
                    arch_update_cap_invs_map get_cap_wp set_cap_typ_at
                simp: ako_asid_pools_of
         | wp (once) hoare_vcg_ex_lift)+
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_apinv_def cong: conj_cong)
  apply (rename_tac asid pool_ptr slot_ptr slot_idx s pool cap)
  apply (clarsimp simp: is_cap_simps update_map_data_def is_arch_update_def is_arch_cap_def
                        cap_master_cap_simps asid_low_bits_of_def is_vsroot_cap_eq)
  apply (frule caps_of_state_valid, clarsimp)
  apply (rule conjI)
   apply (clarsimp simp: valid_cap_def cap_aligned_def wellformed_mapdata_def bit_simps)
  apply (frule valid_table_caps_pdD, fastforce)
  apply (frule valid_global_refsD2, fastforce)
  apply (clarsimp simp: cap_range_def)
  apply fastforce
  done

lemma invs_aligned_pdD:
  "\<lbrakk> pspace_aligned s; valid_arch_state s \<rbrakk> \<Longrightarrow> is_aligned (global_pt s) (pt_bits VSRootPT_T)"
  by (clarsimp simp: valid_arch_state_def)

lemma valid_vspace_obj_default:
  assumes "ty \<noteq> Structures_A.apiobject_type.Untyped"
  assumes "ty = ArchObject VSpaceObj \<Longrightarrow> level = max_pt_level"
  assumes "ty = ArchObject PageTableObj \<Longrightarrow> level \<noteq> max_pt_level"
  shows "ArchObj ao = default_object ty dev us \<Longrightarrow> valid_vspace_obj level ao s'"
  by (cases ty; simp add: default_object_def assms)


(* VCPU lemmas *)

crunches vcpu_switch
  for vs_lookup_table[wp]: "\<lambda>s. P (vs_lookup_table level asid vref s)"
  and vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"
  and vs_lookup_target[wp]: "\<lambda>s. P (vs_lookup_target level asid vref s)"
  and valid_vspace_objs[wp]: valid_vspace_objs
  and equal_mappings[wp]: equal_kernel_mappings
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

(* vcpu_switch can unfortunately not live in the non_vspace_non_cap_op locale, because it does not
  preserve arch_state *)
lemmas vcpu_switch_vs_lookup_pages[wp] = vs_lookup_pages_target_lift[OF vcpu_switch_vs_lookup_target]

crunches vcpu_update, vgic_update, vgic_update_lr, vcpu_disable, vcpu_restore, vcpu_save_reg_range,
         vcpu_save, vcpu_switch
  for distinct[wp]: pspace_distinct
  (wp: mapM_x_wp mapM_wp subset_refl)

(* lemmas for vcpu_switch invs *)
lemma dmo_isb_invs[wp]: "do_machine_op isb \<lbrace>invs\<rbrace>"
  and dmo_dsb_invs[wp]: "do_machine_op dsb \<lbrace>invs\<rbrace>"
  and dmo_setHCR_invs[wp]: "do_machine_op (setHCR w) \<lbrace>invs\<rbrace>"
  and dmo_setSCTLR_invs[wp]: "do_machine_op (setSCTLR x) \<lbrace>invs\<rbrace>"
  and dmo_getSCTLR_invs[wp]: "do_machine_op getSCTLR \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_vmcr_invs[wp]: "do_machine_op get_gic_vcpu_ctrl_vmcr \<lbrace>invs\<rbrace>"
  and dmo_set_gic_vcpu_ctrl_vmcr_invs[wp]: "\<And>x. do_machine_op (set_gic_vcpu_ctrl_vmcr x) \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_apr_invs[wp]: "do_machine_op get_gic_vcpu_ctrl_apr \<lbrace>invs\<rbrace>"
  and dmo_set_gic_vcpu_ctrl_apr_invs[wp]: "\<And>x. do_machine_op (set_gic_vcpu_ctrl_apr x) \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_lr_invs[wp]: "do_machine_op (get_gic_vcpu_ctrl_lr n) \<lbrace>invs\<rbrace>"
  and dmo_set_gic_vcpu_ctrl_lr_invs[wp]: "do_machine_op (set_gic_vcpu_ctrl_lr n x) \<lbrace>invs\<rbrace>"
  and dmo_get_gic_vcpu_ctrl_hcr_invs[wp]: "do_machine_op (get_gic_vcpu_ctrl_hcr) \<lbrace>invs\<rbrace>"
  and dmo_set_gic_vcpu_ctrl_hcr_invs[wp]: "\<And>x. do_machine_op (set_gic_vcpu_ctrl_hcr x) \<lbrace>invs\<rbrace>"
  and dmo_writeVCPUHardwareReg_invs[wp]: "do_machine_op (writeVCPUHardwareReg r v) \<lbrace>invs\<rbrace>"
  and dmo_readVCPUHardwareReg_invs[wp]: "do_machine_op (readVCPUHardwareReg r) \<lbrace>invs\<rbrace>"
  by (all \<open>wp dmo_invs_lift\<close>)

crunches set_vcpu
  for cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and tcb_at[wp]: "\<lambda>s. P (tcb_at p s)"
  (simp: tcb_at_typ)

(* set_vcpu invariants *)
lemma set_vcpu_cur_tcb[wp]:
  "set_vcpu p v \<lbrace>cur_tcb\<rbrace>"
  unfolding cur_tcb_def
  by (wp_pre, wps, wpsimp, assumption)

lemma set_vcpu_cap_refs_respects_device_region[wp]:
  "set_vcpu p vcpu \<lbrace>cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre])
  including unfold_objects_asm
  apply (clarsimp simp: a_type_def split: if_splits)
  done

lemma set_vcpu_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace>
     set_vcpu p vcpu
   \<lbrace>\<lambda>s. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre])
  including unfold_objects_asm
  apply (clarsimp simp: a_type_def split: if_splits)
  done

lemma set_vcpu_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_vcpu p v \<lbrace>\<lambda>_. cap_refs_in_kernel_window\<rbrace>"
  unfolding cap_refs_in_kernel_window_def[abs_def]
  apply (rule hoare_lift_Pf [where f="\<lambda>s. not_kernel_window s"])
  apply (rule valid_refs_cte_lift)
  apply wp+
  done

crunch valid_irq_states[wp]: set_vcpu valid_irq_states
  (wp: crunch_wps simp: crunch_simps)

crunch interrupt_state[wp]: set_vcpu "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas set_vcpu_valid_irq_handlers[wp] = valid_irq_handlers_lift[OF set_vcpu.caps set_vcpu_interrupt_state]

crunch interrupt_irq_node[wp]: set_vcpu "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas set_vcpu_valid_irq_node[wp] = valid_irq_node_typ[OF set_vcpu_typ_at set_vcpu_interrupt_irq_node]

crunch idle_thread[wp]: set_vcpu "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_vcpu_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp+

lemma set_vcpu_valid_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  by (rule valid_reply_masters_cte_lift) wp

lemma set_vcpu_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_vcpu_def set_object_def)
  including no_pre apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done

lemma set_vcpu_valid_reply_caps[wp]:
  "\<lbrace>valid_reply_caps\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  by (rule valid_reply_caps_st_cte_lift) wp+

lemma set_vcpu_if_unsafe_then_cap[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_ifunsafe[THEN hoare_set_object_weaken_pre])
  including unfold_objects
  apply (clarsimp simp: a_type_def)
  done

lemma set_vcpu_only_idle[wp]:
  "\<lbrace>only_idle\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)+

lemma set_vcpu_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wp valid_idle_lift)

lemma set_vcpu_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_ioc\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre] get_object_inv)
  including unfold_objects
  apply (clarsimp simp: valid_def get_object_def simpler_gets_def assert_def
          return_def fail_def bind_def
          a_type_simps is_tcb is_cap_table a_type_def)
  done

lemma set_vcpu_valid_mdb[wp]: "\<lbrace>valid_mdb\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift get_object_wp simp: set_vcpu_def set_object_def)

lemma set_vcpu_zombies_final[wp]: "\<lbrace>zombies_final\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_vcpu_def)
  including unfold_objects
  apply (wp set_object_zombies[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: a_type_def)
  done

lemma set_vcpu_if_live_then_nonz_cap_full:
  "\<lbrace>if_live_then_nonz_cap and (\<lambda>s. obj_at live p s \<or> (arch_live (VCPU v) \<longrightarrow> ex_nonz_cap_to p s))\<rbrace>
    set_vcpu p v \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  unfolding set_vcpu_def
  including unfold_objects
  apply (wp get_object_wp set_object_iflive[THEN hoare_set_object_weaken_pre])
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: live_def hyp_live_def arch_live_def a_type_def split: if_splits)
  apply (rule if_live_then_nonz_capD; simp add: live_def hyp_live_def arch_live_def)
  done

lemma set_vcpu_if_live_then_nonz_cap_None[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> set_vcpu p (vcpu\<lparr>vcpu_tcb := None\<rparr>) \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp wp: set_vcpu_if_live_then_nonz_cap_full simp: arch_live_def)

lemma set_vcpu_if_live_then_nonz_cap_Some[wp]:
  "\<lbrace>if_live_then_nonz_cap and ex_nonz_cap_to p\<rbrace> set_vcpu p (vcpu\<lparr>vcpu_tcb := Some tcb\<rparr>) \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  by (wpsimp wp: set_vcpu_if_live_then_nonz_cap_full simp: arch_live_def)

lemma state_refs_of_vcpu_simp: "typ_at (AArch AVCPU) p s \<Longrightarrow> state_refs_of s p = {}"
  apply (clarsimp simp: obj_at_def state_refs_of_def a_type_def aa_type_def)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  done

lemma set_object_vcpu_sym_refs:
  "\<lbrace>\<lambda>s. typ_at (AArch AVCPU) p s \<and> sym_refs (state_refs_of s)\<rbrace>
     set_object p (ArchObj (VCPU v))
   \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  including unfold_objects
  apply (wpsimp wp: set_object_wp
              simp: state_refs_of_def sym_refs_def)
  by force

lemma set_vcpu_sym_refs[wp]:
  "\<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace> set_vcpu p v \<lbrace>\<lambda>rv s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_vcpu_sym_refs[THEN hoare_set_object_weaken_pre])
  apply (simp add: get_object_def)
  apply (clarsimp simp: obj_at_def)
  done

lemma state_hyp_refs_of_simp_neq: "\<lbrakk> a \<noteq> p \<rbrakk> \<Longrightarrow> state_hyp_refs_of (s\<lparr>kheap := kheap s(p \<mapsto> v) \<rparr>) a = state_hyp_refs_of s a "
  by (simp add: state_hyp_refs_of_def)

lemma state_hyp_refs_of_simp_eq:
  "obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of v) p s
   \<Longrightarrow> state_hyp_refs_of (s\<lparr>kheap := kheap s(p \<mapsto> v) \<rparr>) p = state_hyp_refs_of s p"
  by (clarsimp simp: state_hyp_refs_of_def obj_at_def)

lemma set_object_vcpu_sym_refs_hyp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of ko) p s
      \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv s. sym_refs (state_hyp_refs_of s)\<rbrace>"
   apply (wpsimp wp: set_object_wp)
   apply (erule rsubst[where P = sym_refs])
   apply (rule ext)
   by (clarsimp simp: state_hyp_refs_of_def obj_at_def
                  split: option.splits if_splits)

lemma set_vcpu_sym_refs_refs_hyp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p s
      \<and> sym_refs (state_hyp_refs_of s)\<rbrace>
     set_vcpu p v
   \<lbrace>\<lambda>rv s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  apply (wp set_object_vcpu_sym_refs_hyp hoare_drop_imp)
  apply (clarsimp simp: hyp_refs_of_def)
  done


lemma set_vcpu_valid_pspace:
  "\<lbrace>valid_obj p (ArchObj (VCPU v))
    and valid_pspace
    and obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p\<rbrace>
     set_vcpu p v
   \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (wpsimp simp: valid_pspace_def pred_conj_def
                  wp: set_vcpu_if_live_then_nonz_cap_full set_vcpu_sym_refs_refs_hyp)
  apply (clarsimp simp: obj_at_def live_def)
  apply (auto simp: arch_live_def hyp_refs_of_def vcpu_tcb_refs_def hyp_live_def
              split: kernel_object.splits arch_kernel_obj.splits option.splits)
  done

lemma vmid_inv_set_vcpu:
  "vcpu_at p s \<Longrightarrow> vmid_inv (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (VCPU v))\<rparr>) = vmid_inv s"
  by (simp add: vmid_inv_def asid_pools_of_vcpu_None_upd_idem)

lemma pt_at_eq_set_vcpu:
  "vcpu_at p s \<Longrightarrow> pt_at pt_t p' (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (VCPU v))\<rparr>) = pt_at pt_t p' s"
  by (auto simp add: obj_at_def)

lemma set_vcpu_valid_arch_eq_hyp:
  "\<lbrace>valid_arch_state and obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p\<rbrace>
     set_vcpu p v
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def
  apply (wp set_vcpu_wp)
  apply (clarsimp simp: vmid_inv_set_vcpu asid_pools_of_vcpu_None_upd_idem pts_of_vcpu_None_upd_idem
                        valid_global_arch_objs_def pt_at_eq_set_vcpu)
  apply (clarsimp simp: cur_vcpu_def split: option.splits)
  by (auto simp: obj_at_def  vcpu_tcb_refs_def opt_map_def in_opt_pred split: option.splits)

lemma set_vcpu_invs_eq_hyp:
  "\<lbrace>obj_at (\<lambda>ko'. hyp_refs_of ko' = hyp_refs_of (ArchObj (VCPU v))) p
    and valid_obj p (ArchObj (VCPU v))
    and  invs \<rbrace>
     set_vcpu p v
   \<lbrace> \<lambda>_. invs \<rbrace>"
  unfolding invs_def valid_state_def
  by (wpsimp wp: set_vcpu_valid_pspace set_vcpu_valid_arch_eq_hyp)

(* FIXME: move both this and the original still in Retype_AI *)
lemmas do_machine_op_bind =
    submonad_bind [OF submonad_do_machine_op submonad_do_machine_op
                      submonad_do_machine_op]

lemma vcpu_restore_reg_invs[wp]:
  "vcpu_restore_reg v r \<lbrace>invs\<rbrace>"
  unfolding vcpu_restore_reg_def by wp

lemma valid_obj_vcpu_regs_simp[simp]:
  "valid_obj v (ArchObj (VCPU (vcpu\<lparr>vcpu_regs := regs\<rparr>))) = valid_obj v (ArchObj (VCPU (vcpu)))"
  unfolding valid_obj_def
  by (rule ext, clarsimp simp: valid_vcpu_def)

lemma valid_obj_vcpu_vgic_simp[simp]:
  "valid_obj v (ArchObj (VCPU (vcpu\<lparr>vcpu_vgic := vgic\<rparr>))) = valid_obj v (ArchObj (VCPU (vcpu)))"
  unfolding valid_obj_def
  by (rule ext, clarsimp simp: valid_vcpu_def)

lemma vcpu_save_reg_invs[wp]:
  "vcpu_save_reg v r \<lbrace>invs\<rbrace>"
  unfolding vcpu_save_reg_def vcpu_update_def
  apply (wpsimp wp: set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (fastforce simp: obj_at_def in_omonad dest: invs_valid_objs)
  done

lemma vcpu_update_trivial_invs:
  assumes tcb: "\<And>vcpu. vcpu_tcb (upd f vcpu) = vcpu_tcb vcpu"
  shows "vcpu_update vcpu_ptr (upd f) \<lbrace> invs \<rbrace>"
  unfolding vcpu_update_def
  apply (wpsimp wp: tcb set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (fastforce simp: obj_at_def valid_obj_def valid_vcpu_def tcb in_omonad
                   dest!: invs_valid_objs
                   split: option.splits)
  done

lemmas vcpu_update_invs[wp] =
  vcpu_update_trivial_invs[where upd="vcpu_vtimer_update", simplified]
  vcpu_update_trivial_invs[where upd="vcpu_regs_update", simplified]
  vcpu_update_trivial_invs[where upd="vcpu_vppi_masked_update", simplified]
  vcpu_update_trivial_invs[where upd="vcpu_vgic_update", simplified]
  vcpu_update_trivial_invs[where upd="\<lambda>f vcpu. vcpu\<lparr>vcpu_vgic := f (vcpu_vgic vcpu)\<rparr>"
                           , folded vgic_update_def, simplified]

crunches vcpu_restore_reg_range, vcpu_save_reg_range, vgic_update_lr, vcpu_read_reg
  for invs[wp]: invs
  (wp: mapM_x_wp)

lemma vcpu_write_reg_invs[wp]:
  "vcpu_write_reg vcpu_ptr reg val \<lbrace>invs\<rbrace>"
  unfolding vcpu_write_reg_def
  by (wpsimp cong: vcpu.fold_congs) (* crunch can't do cong yet *)

lemma save_virt_timer_invs[wp]:
  "save_virt_timer vcpu_ptr \<lbrace>invs\<rbrace>"
  unfolding save_virt_timer_def read_cntpct_def
  by (wpsimp wp: set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift' dmo_invs_lift)

(* migrated from ArchInterrupt_AI, which is not visible from here *)
lemma maskInterrupt_invs:
  "\<lbrace>invs and (\<lambda>s. \<not>b \<longrightarrow> interrupt_states s irq \<noteq> IRQInactive)\<rbrace>
   do_machine_op (maskInterrupt b irq)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
   by (wpsimp simp: do_machine_op_def split_def maskInterrupt_def)
      (clarsimp simp: in_monad invs_def valid_state_def valid_machine_state_def cur_tcb_def
                      valid_irq_states_def valid_irq_masks_def)

crunches vcpu_restore_reg
  for vcpus_of[wp]: "\<lambda>s. P (vcpus_of s)"

lemma restore_virt_timer_invs[wp]:
  "\<lbrace>\<lambda> s. invs s\<rbrace> restore_virt_timer vcpu_ptr \<lbrace>\<lambda>_ . invs\<rbrace>"
  unfolding restore_virt_timer_def read_cntpct_def
             is_irq_active_def get_irq_state_def
  by (wpsimp wp: set_vcpu_invs_eq_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift'
                 maskInterrupt_invs)

lemma vcpu_enable_invs[wp]:
  "vcpu_enable v \<lbrace>invs\<rbrace>"
  unfolding vcpu_enable_def
  by (wpsimp wp: dmo_invs_lift)

lemma vcpu_restore_invs[wp]:
  "vcpu_restore v \<lbrace>invs\<rbrace>"
  apply (simp add: vcpu_restore_def do_machine_op_bind dom_mapM empty_fail_cond)
  apply (wpsimp wp: mapM_wp_inv)
  done

lemma valid_obj_update:
  fixes val :: "'a::state_ext state"
  assumes valid_obj_f: "\<lbrace> valid_obj p v \<rbrace> f \<lbrace> \<lambda>rv (s :: 'a state). valid_obj p v s\<rbrace>"
  assumes eq : "\<And>r. valid_obj p (P v r) = ((valid_obj p v) :: 'a state \<Rightarrow> bool)"
  shows "\<lbrace>valid_obj p v\<rbrace> f \<lbrace>\<lambda>rv. valid_obj p (P v rv)\<rbrace>"
  by(simp add: eq valid_obj_f)

lemma modify_valid_lift_rv:
  "\<lbrakk> \<And>s rv. P x s = P (f x rv s) s ; \<lbrace>P x\<rbrace> f' \<lbrace> \<lambda>_ s. P x s\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P x\<rbrace> f' \<lbrace> \<lambda>rv s. P (f x rv s) s\<rbrace>"
  by simp

lemma valid_vcpu_regs_update[simp]:
  "valid_obj p (ArchObj (VCPU (vcpu_regs_update f vcpu))) s = valid_obj p (ArchObj (VCPU vcpu)) s"
  by (simp add: valid_vcpu_def valid_obj_def)

lemma valid_vcpu_vgic_update[simp]:
  "valid_obj p (ArchObj (VCPU (vcpu_vgic_update f vcpu))) s = valid_obj p (ArchObj (VCPU vcpu)) s"
  by (simp add: valid_vcpu_def valid_obj_def)

lemma vcpu_save_invs[wp]:
  "vcpu_save v \<lbrace>invs\<rbrace>"
  apply (clarsimp simp: vcpu_save_def dom_mapM split: option.splits)
  apply (wpsimp wp: mapM_wp_inv)
  done

lemma vcpu_disable_invs[wp]:
  "vcpu_disable v \<lbrace>invs\<rbrace>"
  apply (simp add: vcpu_disable_def)
  apply (wpsimp simp: do_machine_op_bind
                  wp: set_vcpu_invs_eq_hyp get_vcpu_wp maskInterrupt_invs dmo_invs_lift
                      hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
  done

lemma valid_machine_state_arch_state_update [simp]:
  "valid_machine_state (arch_state_update f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

lemma arm_asid_table_current_vcpu_update[simp]:
  "arm_asid_table ((arm_current_vcpu_update v) (arch_state s)) = arm_asid_table (arch_state s)"
  by clarsimp

lemma vmid_inv_current_vcpu_update[simp]:
  "vmid_inv (s\<lparr>arch_state := arm_current_vcpu_update Map.empty (arch_state s)\<rparr>) = vmid_inv s"
  by (clarsimp simp: vmid_inv_def)

lemma valid_irq_node_arch_state_update [simp]:
  "valid_irq_node (arch_state_update f s) = valid_irq_node s"
  by (simp add: valid_irq_node_def)

lemma valid_kernel_mappings_arch_state_update [simp]:
  "valid_kernel_mappings (arch_state_update f s) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def)


definition cur_vcpu_at where
  "cur_vcpu_at v s \<equiv> case v of None \<Rightarrow> True | Some (vp, _) \<Rightarrow> vcpu_at vp s \<and> obj_at hyp_live vp s"

lemma invs_current_vcpu_update:
  "\<lbrakk>cur_vcpu_at v s; valid_arch_state s\<rbrakk> \<Longrightarrow>
     invs (s\<lparr>arch_state := arch_state s \<lparr>arm_current_vcpu := v\<rparr>\<rparr>) = invs s"
  by (auto simp: invs_def valid_state_def cur_tcb_def cur_vcpu_at_def obj_at_conj_distrib
                 valid_global_refs_def valid_asid_map_def valid_arch_state_def
                 valid_global_objs_def valid_global_vspace_mappings_def cur_vcpu_def
                 global_refs_def vmid_inv_def valid_global_arch_objs_def in_omonad obj_at_def
                 hyp_live_def arch_live_def
          split: option.splits)

lemma invs_current_vcpu_update':
  "\<lbrakk> cur_vcpu_at v s; invs s \<rbrakk> \<Longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>arm_current_vcpu := v\<rparr>\<rparr>)"
  apply (prop_tac "valid_arch_state s", simp add: invs_def valid_state_def)
  apply (simp add: invs_current_vcpu_update)
  done

lemma vgic_update_sym_refs_hyp[wp]:
  "vgic_update vcpuptr f \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vgic_update_def vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp simp: obj_at_def in_omonad)

lemma vcpu_save_reg_sym_refs_hyp[wp]:
  "vcpu_save_reg vcpuptr r \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_save_reg_def vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp hoare_vcg_all_lift hoare_vcg_imp_lift)
     (simp add: obj_at_def in_omonad)

lemma vcpu_update_regs_sym_refs_hyp[wp]:
  "vcpu_update vcpu_ptr (vcpu_regs_update f) \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp)
     (simp add: obj_at_def in_omonad)

lemma vcpu_write_reg_sym_refs_hyp[wp]:
  "vcpu_write_reg vcpu_ptr reg val \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_write_reg_def by (wpsimp cong: vcpu.fold_congs)

lemma vcpu_update_vtimer_sym_refs_hyp[wp]:
  "vcpu_update vcpu_ptr (vcpu_vtimer_update f) \<lbrace>\<lambda>s. sym_refs (state_hyp_refs_of s)\<rbrace>"
  unfolding vcpu_update_def
  by (wpsimp wp: set_vcpu_sym_refs_refs_hyp get_vcpu_wp)
     (simp add: obj_at_def in_omonad)

crunches save_virt_timer, vcpu_disable, vcpu_invalidate_active, vcpu_restore, vcpu_save, vcpu_switch
  for sym_refs_hyp[wp]: "\<lambda>s. sym_refs (state_hyp_refs_of s)"
  (ignore: vcpu_update wp: crunch_wps)

lemma obj_at_hyp_live_vcpu_regs:
  "vcpus_of s vcpu_ptr = Some v \<Longrightarrow>
   obj_at hyp_live p (s\<lparr>kheap := kheap s(vcpu_ptr \<mapsto> ArchObj (VCPU (v\<lparr>vcpu_regs := x\<rparr>)))\<rparr>) =
   obj_at hyp_live p s"
  by (clarsimp simp: in_omonad obj_at_def)

lemma vcpu_save_reg_hyp_live[wp]:
  "vcpu_save_reg vcpu_ptr reg \<lbrace>obj_at hyp_live p\<rbrace>"
  unfolding vcpu_save_reg_def vcpu_update_def set_vcpu_def
  by (wpsimp wp: set_object_wp get_vcpu_wp hoare_vcg_imp_lift simp: obj_at_hyp_live_vcpu_regs)

lemma save_virt_timer_hyp_live[wp]:
  "save_virt_timer vcpu_ptr \<lbrace>obj_at hyp_live p\<rbrace>"
  unfolding save_virt_timer_def by wp

lemma vcpu_write_reg_hyp_live[wp]:
  "vcpu_write_reg vcpu_ptr reg val \<lbrace>obj_at hyp_live p\<rbrace>"
  unfolding vcpu_write_reg_def vcpu_update_def set_vcpu_def
  by (wpsimp wp: set_object_wp get_vcpu_wp hoare_vcg_imp_lift simp: obj_at_hyp_live_vcpu_regs)

crunches vcpu_disable, vcpu_restore, vcpu_save
  for hyp_live[wp]: "obj_at hyp_live p"
  (wp: crunch_wps)

lemma vcpu_switch_invs[wp]:
  "\<lbrace>invs and (\<lambda>s. v \<noteq> None \<longrightarrow> obj_at hyp_live (the v) s)\<rbrace> vcpu_switch v \<lbrace> \<lambda>_ . invs \<rbrace>"
  unfolding vcpu_switch_def
  apply (cases v; clarsimp)
   apply (wpsimp simp: cur_vcpu_at_def | strengthen invs_current_vcpu_update')+
   apply (clarsimp simp: invs_def valid_state_def valid_arch_state_def cur_vcpu_def
                         in_omonad obj_at_def hyp_live_def arch_live_def)
  apply (wpsimp simp: cur_vcpu_at_def | strengthen invs_current_vcpu_update')+
  done

crunches
  arm_context_switch, vcpu_update, vgic_update, vcpu_disable, vcpu_enable,
  vcpu_restore, vcpu_switch, set_vm_root
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps mapM_x_wp)

lemma set_vcpu_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace> set_vcpu t vcpu \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_vcpu_def set_object_def get_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update)

crunch cte_wp_at[wp]: vcpu_disable, vcpu_enable, vcpu_save, vcpu_restore "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma vcpu_switch_cte_wp_at[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
  apply (wp | wpc | clarsimp)+
  done

crunch global_refs_inv[wp]: vcpu_enable, vcpu_disable, vcpu_restore, vcpu_save "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps simp: crunch_simps global_refs_arch_update_eq)

lemma modify_valid_lift: "\<lbrakk> \<And>s. P s = P (f s) ; \<lbrace>P\<rbrace> f' \<lbrace> \<lambda>_ s. P s\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f' \<lbrace> \<lambda>rv s. P (f s)\<rbrace>"
  by simp

lemma vcpu_switch_global_refs_inv[wp]:
  "\<lbrace>\<lambda>s. P (global_refs s)\<rbrace> vcpu_switch vcpu \<lbrace>\<lambda>_ s. P (global_refs s)\<rbrace>"
  apply (simp add: vcpu_switch_def)
  apply (cases vcpu; simp)
  apply (wp | wpc | rule modify_valid_lift | clarsimp simp: global_refs_def)+
  done

lemma dmo_maskInterrupt_pspace_respects_device_region[wp]:
  "do_machine_op (maskInterrupt b irq) \<lbrace>pspace_respects_device_region\<rbrace>"
  unfolding maskInterrupt_def
  by (wpsimp wp: pspace_respects_device_region_dmo)

crunches vcpu_enable, vcpu_write_reg, vcpu_update, vcpu_restore, vcpu_enable, vcpu_disable
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (wp: crunch_wps dmo_maskInterrupt_pspace_respects_device_region
       pspace_respects_device_region_dmo
   simp: crunch_simps read_cntpct_def)

lemma set_vcpu_nonvcpu_at: (* generalise? this holds except when the ko is a vcpu *)
  "\<lbrace>\<lambda>s. P (ko_at ko x s) \<and> a_type ko \<noteq> AArch AVCPU\<rbrace>
   set_vcpu p v
   \<lbrace>\<lambda>_ s. P (ko_at ko x s)\<rbrace>"
  apply (simp add: set_vcpu_def)
  including unfold_objects
  by (wpsimp wp: set_object_wp_strong simp: a_type_def)

lemma set_vcpu_pt_at:
  "\<lbrace>\<lambda>s. P (ko_at (ArchObj (PageTable pt)) x s)\<rbrace>
   set_vcpu p v
   \<lbrace>\<lambda>_ s. P (ko_at (ArchObj (PageTable pt)) x s)\<rbrace>"
  by (wp set_vcpu_nonvcpu_at; auto)

crunches vcpu_switch
  for pt_at: "\<lambda>s. P (ko_at (ArchObj (PageTable pt)) x s)"
  (wp: crunch_wps simp: crunch_simps when_def)

end

context begin interpretation Arch .
requalify_facts
  do_machine_op_valid_kernel_mappings
end

end
