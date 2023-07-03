(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchKernelInit_AI
imports
  ADT_AI
  Tcb_AI
  Arch_AI
begin

context Arch begin global_naming AARCH64

text \<open>
  Showing that there is a state that satisfies the abstract invariants.
\<close>

lemmas ptr_defs = idle_thread_ptr_def init_irq_node_ptr_def arm_global_pt_ptr_def
lemmas state_defs = init_A_st_def init_kheap_def init_arch_state_def
                    init_vspace_uses_def ptr_defs global_pt_obj_def

lemma is_tcb_TCB[simp]: "is_tcb (TCB t)" by (simp add: is_tcb_def)

lemma ran_empty_cnode[simp]: "ran (empty_cnode n) = {NullCap}"
  apply (rule equalityI; clarsimp simp: ran_def empty_cnode_def)
  apply (rule_tac x="replicate n False" in exI)
  apply simp
  done

lemma empty_cnode_apply[simp]:
  "(empty_cnode n xs = Some cap) = (length xs = n \<and> cap = NullCap)"
  by (auto simp add: empty_cnode_def)

lemma valid_cs_size_empty[simp]:
  "valid_cs_size n (empty_cnode n) = (n < word_bits - cte_level_bits)"
  using wf_empty_bits [of n] by (simp add: valid_cs_size_def)

lemma init_cdt [simp]:
  "cdt init_A_st = init_cdt"
  by (simp add: state_defs)

lemma mdp_parent_empty[simp]:
  "\<not>Map.empty \<Turnstile> x \<rightarrow> y"
  by (auto simp: cdt_parent_of_def dest: tranclD)

lemma descendants_empty[simp]:
  "descendants_of x Map.empty = {}"
  by (clarsimp simp: descendants_of_def)

lemma is_reply_cap_NullCap[simp]: "\<not>is_reply_cap NullCap"
  by (simp add: is_reply_cap_def)

declare cap_range_NullCap [simp]

lemma pptr_base_num:
  "pptr_base = 0x8000000000"
  by (simp add: pptr_base_def pptrBase_def canonical_bit_def)

definition irq_node_bits :: nat where
  "irq_node_bits = cte_level_bits + LENGTH(irq_len)"

lemmas irq_node_bits_num = irq_node_bits_def[unfolded cte_level_bits_def, simplified]

(* Some other architectures need to prove more here, but if the init_irq_node is the last object
   in the init state, we only need info about  init_irq_node_ptr, and not about
   init_irq_node_ptr + mask irq_node bits *)
lemma init_irq_ptrs_ineqs:
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
proof -
  have P: "ucast irq < (2 ^ (irq_node_bits - cte_level_bits) :: machine_word)"
    apply (rule order_le_less_trans[OF
        ucast_le_ucast[where 'a=irq_len and 'b=machine_word_len, simplified, THEN iffD2, OF word_n1_ge]])
    apply (simp add: cte_level_bits_def minus_one_norm irq_node_bits_def)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
    apply (rule is_aligned_no_wrap'[where sz=irq_node_bits])
     apply (simp add: is_aligned_def init_irq_node_ptr_def pptr_base_num irq_node_bits_num)
    apply (rule shiftl_less_t2n[OF P])
    apply (simp add: irq_node_bits_num)
    done
qed

lemmas init_irq_ptrs_less_ineqs
   = init_irq_ptrs_ineqs(1)[THEN order_less_le_trans[rotated]]

lemmas init_irq_ptrs_all_ineqs[unfolded init_irq_node_ptr_def cte_level_bits_def]
   = init_irq_ptrs_ineqs(1)[THEN order_trans[rotated]]
     init_irq_ptrs_less_ineqs
     init_irq_ptrs_less_ineqs[THEN less_imp_neq]
     init_irq_ptrs_less_ineqs[THEN less_imp_neq, THEN not_sym]

lemma init_irq_ptrs_eq:
  "((ucast irq << cte_level_bits) = (ucast (irq' :: irq) << cte_level_bits :: machine_word))
   = (irq = irq')"
  by word_bitwise (clarsimp simp: cte_level_bits_def)

lemma pspace_aligned_init_A:
  "pspace_aligned init_A_st"
  apply (clarsimp simp: pspace_aligned_def state_defs wf_obj_bits [OF wf_empty_bits]
                        dom_if_Some cte_level_bits_def bit_simps pptr_base_num kernel_elf_base_def)
  apply (safe intro!: aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl],
           simp_all add: is_aligned_def word_bits_def)[1]
  done

lemma pspace_distinct_init_A:
  notes ineqs = pptr_base_num init_irq_ptrs_all_ineqs[simplified pptr_base_num mask_def, simplified]
  shows "pspace_distinct init_A_st"
  unfolding pspace_distinct_def
  apply (clarsimp simp: state_defs empty_cnode_bits cte_level_bits_def linorder_not_le
                  split del: if_split cong: if_cong)
  apply (clarsimp simp: ineqs split: if_split_asm)
    apply (simp add: bit_simps ineqs)
   apply (simp add: bit_simps ineqs)
  apply (cut_tac x="init_irq_node_ptr + (ucast irq << cte_level_bits)"
             and y="init_irq_node_ptr + (ucast irqa << cte_level_bits)"
             and sz=cte_level_bits in aligned_neq_into_no_overlap;
         simp add: init_irq_node_ptr_def pptr_base_num cte_level_bits_def)
    apply (rule aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl])
    apply (simp add: is_aligned_def)
   apply (rule aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl])
   apply (simp add: is_aligned_def)
  apply (simp add: linorder_not_le)
  done

lemma caps_of_state_init_A_st_Null:
  "caps_of_state (init_A_st::'z::state_ext state) x
     = (if cte_at x (init_A_st::'z::state_ext state) then Some NullCap else None)"
  apply (subgoal_tac "\<not> cte_wp_at ((\<noteq>) NullCap) x init_A_st")
   apply (auto simp add: cte_wp_at_caps_of_state)[1]
  apply (clarsimp, erule cte_wp_atE)
   apply (auto simp add: state_defs tcb_cap_cases_def split: if_split_asm)
  done

lemma cte_wp_at_init_A_st_Null:
  "cte_wp_at P p init_A_st \<Longrightarrow> P cap.NullCap"
  apply (subst(asm) cte_wp_at_caps_of_state)
  apply (simp add:caps_of_state_init_A_st_Null split: if_splits)
  done

lemmas cte_wp_at_caps_of_state_eq
    = cte_wp_at_caps_of_state[where P="(=) cap" for cap]

lemma pspace_respects_device_region_init[simp]:
  "pspace_respects_device_region init_A_st"
   apply (clarsimp simp: pspace_respects_device_region_def state_defs init_machine_state_def
                         device_mem_def in_device_frame_def obj_at_def a_type_def)
   apply (rule ext)
   apply clarsimp
   done

lemma cap_refs_respects_device_region_init[simp]:
  "cap_refs_respects_device_region init_A_st"
   apply (clarsimp simp: cap_refs_respects_device_region_def)
   apply (frule cte_wp_at_caps_of_state[THEN iffD1])
   apply clarsimp
   apply (subst(asm) caps_of_state_init_A_st_Null)
   apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_respects_device_region_def)
   done

lemma pool_for_asid_init_A_st[simp]:
  "pool_for_asid asid init_A_st = None"
  by (simp add: pool_for_asid_def state_defs)

lemma vspace_for_asid_init_A_st[simp]:
  "vspace_for_asid asid init_A_st = None"
  by (simp add: vspace_for_asid_def entry_for_asid_def obind_def)

lemma global_pt_init_A_st[simp]:
  "global_pt init_A_st = arm_global_pt_ptr"
  by (simp add: state_defs)

lemma is_alignedarm_global_pt_ptr[simp]:
  "is_aligned arm_global_pt_ptr (pt_bits VSRootPT_T)"
  by (simp add: arm_global_pt_ptr_def pptr_base_num bit_simps is_aligned_def)

lemma ptes_of_init_A_st_global:
  "ptes_of init_A_st =
   (\<lambda>pt_t p. if pt_t = VSRootPT_T \<and> table_base VSRootPT_T p = arm_global_pt_ptr \<and>
             is_aligned p pte_bits then Some InvalidPTE else None)"
  by (rule ext)+ (auto simp: state_defs level_pte_of_def obind_def opt_map_def split: option.splits)

lemma pt_walk_init_A_st[simp]:
  "pt_walk max_pt_level level arm_global_pt_ptr vref (ptes_of init_A_st) =
   Some (max_pt_level, arm_global_pt_ptr)"
  apply (subst pt_walk.simps)
  apply (simp add: in_omonad ptes_of_init_A_st_global
                   table_base_pt_slot_offset[where level=max_pt_level, simplified]
                   is_aligned_pt_slot_offset_pte[where pt_t=VSRootPT_T])
  done

lemma kernel_window_init_st:
  "kernel_window init_A_st = { pptr_base ..< pptr_base + (1 << 30) }"
  by (auto simp: state_defs kernel_window_def)

lemma valid_global_vspace_mappings_init_A_st[simp]:
  "valid_global_vspace_mappings init_A_st"
  unfolding valid_global_vspace_mappings_def
  by simp

lemma valid_uses_init_A_st[simp]: "valid_uses_2 init_vspace_uses"
proof -
  have [simp]: "pptr_base < pptr_base + 0x40000000"
    by (simp add: pptr_base_def pptrBase_def)
  have "\<And>p. p < pptr_base + 0x40000000 \<Longrightarrow> canonical_address p"
    by (simp add: canonical_address_range canonical_bit_def mask_def pptr_base_def pptrBase_def
                  word_le_nat_alt word_less_nat_alt)
  moreover
  have "pptr_base + 0x40000000 < pptrTop"
    by (simp add: pptrTop_def pptr_base_def pptrBase_def)
  moreover
  have "pptr_base + 0x40000000 < kdev_base"
    by (simp add: kdev_base_def kdevBase_def pptr_base_def pptrBase_def)
  ultimately
  show ?thesis
    unfolding valid_uses_2_def init_vspace_uses_def window_defs
    by auto
qed

lemma valid_global_arch_objs_init_A_st[simp]:
  "valid_global_arch_objs init_A_st"
  by (simp add: valid_global_arch_objs_def state_defs level_defs obj_at_def)

lemma vspace_for_pool_init_A_st[simp]:
  "vspace_for_pool ap asid (asid_pools_of init_A_st) = None"
  by (clarsimp simp: vspace_for_pool_def obind_def in_opt_map_eq state_defs entry_for_pool_def
               split: option.splits)

lemma user_region_vs_lookup_target_init_A_st[simp]:
  "vref \<in> user_region \<Longrightarrow> vs_lookup_target bot_level asid vref init_A_st = None"
  by (clarsimp simp: vs_lookup_target_def obind_def vs_lookup_slot_def vs_lookup_table_def
               split: option.splits)

lemma valid_vs_lookup_init_A_st[simp]:
  "valid_vs_lookup init_A_st"
  by (clarsimp simp: valid_vs_lookup_def)

lemma valid_vspace_objs_init_A_st[simp]:
  "valid_vspace_objs init_A_st"
  by (clarsimp simp: valid_vspace_objs_def in_omonad vs_lookup_table_def)

lemma idle_thread_in_kernel_window_init_arch_state[simp]:
  "{idle_thread_ptr..0x3FF + idle_thread_ptr} \<subseteq>
     kernel_window_2 (arm_kernel_vspace init_arch_state)"
  apply (clarsimp simp: state_defs pptr_base_num bit_simps kernel_window_def kernel_elf_base_def)
  apply (rule conjI; unat_arith)
  done

lemma irq_node_in_kernel_window_init_arch_state':
  "\<lbrakk> init_irq_node_ptr + m \<le> x; x \<le> init_irq_node_ptr + m + mask cte_level_bits;
     m \<le> mask (size (irq::irq)) << cte_level_bits\<rbrakk>
   \<Longrightarrow> x \<in> kernel_window_2 (arm_kernel_vspace init_arch_state)"
  apply (clarsimp simp: kernel_window_def init_vspace_uses_def init_arch_state_def)
  apply (rule conjI)
   apply (clarsimp simp: state_defs)
   apply (rule ccontr, simp add:not_le)
   apply (drule(1) le_less_trans)
   (* We pick 30 for alignment of pptr_base, because pttr_base is set to 2^40-2^30 *)
   apply (cut_tac is_aligned_no_wrap'[where ptr=pptr_base
                                      and off="0xc000 + m"
                                      and sz=30, simplified])
     apply (simp add: add_ac)
    apply (simp add: pptr_base_num canonical_bit_def is_aligned_def)
   apply (simp add: pptr_base_num cte_level_bits_def canonical_bit_def mask_def word_size)
   apply unat_arith
  apply (simp add: cte_level_bits_def mask_def init_irq_node_ptr_def pptr_base_num word_size)
  apply unat_arith
  done

lemma irq_node_in_kernel_window_init_arch_state[simp]:
  "\<lbrakk> init_irq_node_ptr + (ucast (irq::irq) << cte_level_bits) \<le> x;
     x \<le> init_irq_node_ptr + (ucast irq << cte_level_bits) + 2 ^ cte_level_bits - 1 \<rbrakk>
   \<Longrightarrow> x \<in> kernel_window_2 (arm_kernel_vspace init_arch_state)"
  apply (erule irq_node_in_kernel_window_init_arch_state')
   apply (simp add: mask_def add_diff_eq)
  apply (simp add: word_size mask_def cte_level_bits_def)
  apply (thin_tac P for P)
  apply word_bitwise
  done

lemma tcb_vcpu_init_arch_tcb_None[simp]:
  "tcb_vcpu init_arch_tcb = None"
  by (simp add: init_arch_tcb_def)

lemma pspace_in_kernel_window_init_A_st:
  "pspace_in_kernel_window init_A_st"
  apply (clarsimp simp: pspace_in_kernel_window_def init_A_st_def init_kheap_def)
  apply (safe; clarsimp)
       apply (clarsimp simp: ptr_defs pptr_base_num)
      apply (clarsimp simp: ptr_defs pptr_base_num kernel_window_def init_arch_state_def
                            init_vspace_uses_def)
      apply unat_arith
     apply (clarsimp simp: global_pt_obj_def bit_simps ptr_defs pptr_base_num kernel_window_def
                           init_arch_state_def init_vspace_uses_def
                     split: if_split_asm)
      apply unat_arith
     apply unat_arith
    apply (clarsimp simp: ptr_defs pptr_base_num kernel_window_def init_arch_state_def init_vspace_uses_def)
   apply (clarsimp simp: ptr_defs pptr_base_num kernel_window_def init_arch_state_def init_vspace_uses_def)
   apply unat_arith
  apply (clarsimp simp: global_pt_obj_def bit_simps ptr_defs pptr_base_num kernel_window_def
                        init_arch_state_def init_vspace_uses_def
                  split: if_split_asm)
   apply unat_arith
  apply unat_arith
  done

lemma invs_A:
  "invs init_A_st" (is "invs ?st")
  supply is_aligned_def[THEN iffD2, simp]
  supply image_cong_simp [cong del]
  supply pptr_base_num[simp] kernel_elf_base_def[simp]
  apply (simp add: invs_def)
  apply (rule conjI)
   prefer 2
   apply (simp add: cur_tcb_def state_defs obj_at_def)
  apply (simp add: valid_state_def)
  apply (rule conjI)
   apply (simp add: valid_pspace_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_objs_def state_defs wellformed_pte_def valid_pt_range_def
                          valid_obj_def valid_vm_rights_def vm_kernel_only_def
                          dom_if_Some cte_level_bits_def)
    apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def is_master_reply_cap_def
                          valid_cap_def obj_at_def valid_tcb_state_def valid_arch_tcb_def
                          cap_aligned_def word_bits_def valid_ipc_buffer_cap_simps)+
    apply (clarsimp simp: valid_cs_def word_bits_def cte_level_bits_def
                          valid_tcb_def
                   split: if_split_asm)
   apply (simp add: pspace_aligned_init_A pspace_distinct_init_A)
    apply (clarsimp simp: if_live_then_nonz_cap_def obj_at_def state_defs live_def hyp_live_def arch_live_def)
    apply (clarsimp simp: zombies_final_def cte_wp_at_cases state_defs ex_nonz_cap_to_def
                          tcb_cap_cases_def is_zombie_def)
   apply (clarsimp simp: sym_refs_def state_refs_of_def state_defs state_hyp_refs_of_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_mdb_def init_cdt_def no_mloop_def
                         mdb_cte_at_def)
   apply (clarsimp simp: untyped_mdb_def caps_of_state_init_A_st_Null
                         untyped_inc_def ut_revocable_def
                         irq_revocable_def reply_master_revocable_def
                         reply_mdb_def reply_caps_mdb_def
                         reply_masters_mdb_def valid_arch_mdb_def)
   apply (simp add:descendants_inc_def)
  apply (rule conjI)
   apply (simp add: valid_ioc_def init_A_st_def init_ioc_def cte_wp_at_cases2)
   apply (intro allI impI, elim exE conjE)
   apply (case_tac obj, simp_all add: cap_of_def)
   apply (clarsimp simp: init_kheap_def split: if_split_asm)
  apply (rule conjI)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def state_defs valid_arch_idle_def)
  apply (rule conjI, clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def state_defs)
  apply (rule conjI, clarsimp simp: if_unsafe_then_cap_def caps_of_state_init_A_st_Null)
  apply (subgoal_tac "valid_reply_caps ?st \<and> valid_reply_masters ?st \<and> valid_global_refs ?st")
   prefer 2
   subgoal
     using cte_wp_at_init_A_st_Null
     by (fastforce simp: valid_reply_caps_def unique_reply_caps_def
                         has_reply_cap_def is_reply_cap_to_def pred_tcb_at_def obj_at_def
                         caps_of_state_init_A_st_Null is_master_reply_cap_to_def
                         valid_reply_masters_def valid_global_refs_def
                         valid_refs_def[unfolded cte_wp_at_caps_of_state])
  apply (clarsimp, (thin_tac "_")+) (* use new proven assumptions, then drop them *)
  apply (rule conjI)
   apply (clarsimp simp: valid_arch_state_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_asid_table_def state_defs)
   apply (simp add: valid_arch_state_def state_defs obj_at_def a_type_def cur_vcpu_2_def
                    vmid_inv_def is_inv_def vmid_for_asid_2_def obind_def
                    valid_global_tables_2_def empty_pt_def valid_vmid_table_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_irq_node_def obj_at_def state_defs
                         is_cap_table_def wf_empty_bits
                         init_irq_ptrs_all_ineqs cte_level_bits_def
                         init_irq_ptrs_eq[unfolded cte_level_bits_def])
   apply (intro conjI)
    apply (rule inj_onI)
    apply (simp add: init_irq_ptrs_eq[unfolded cte_level_bits_def])
   apply (clarsimp; word_bitwise)
  apply (simp add: valid_irq_handlers_def caps_of_state_init_A_st_Null
                   ran_def cong: rev_conj_cong)
  apply (rule conjI)
   apply (clarsimp simp: valid_irq_states_def state_defs init_machine_state_def
                         valid_irq_masks_def init_irq_masks_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_machine_state_def state_defs
                         init_machine_state_def init_underlying_memory_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_arch_caps_def valid_asid_pool_caps_def unique_table_caps_def
                         caps_of_state_init_A_st_Null valid_table_caps_def unique_table_refs_def)
   apply (clarsimp simp: state_defs)
  apply (clarsimp simp: valid_global_objs_def valid_kernel_mappings_def valid_asid_map_def)
  apply (rule conjI)
   apply (clarsimp simp: equal_kernel_mappings_def)
  apply (simp add: pspace_in_kernel_window_init_A_st cap_refs_in_kernel_window_def
                   caps_of_state_init_A_st_Null valid_refs_def[unfolded cte_wp_at_caps_of_state])
  done


end

end
