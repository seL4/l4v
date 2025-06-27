(*
 * Copyright 2023, Proofcraft Pty Ltd
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

context Arch begin arch_global_naming

text \<open>
  Showing that there is a state that satisfies the abstract invariants.
\<close>

lemmas ptr_defs = idle_thread_ptr_def init_irq_node_ptr_def riscv_global_pt_ptr_def
lemmas state_defs = init_A_st_def init_kheap_def init_arch_state_def init_global_pt_def
                    init_vspace_uses_def ptr_defs

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
  "pptr_base = 0xFFFFFFC000000000"
  by (simp add: pptr_base_def pptrBase_def canonical_bit_def)

(* IRQ nodes occupy 11 bits of address space in this RISCV example state:
   6 for irq number, 5 for cte_level_bits. *)
lemma init_irq_ptrs_ineqs:
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + mask cte_level_bits
                \<le> init_irq_node_ptr + mask 11"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + mask 11"
proof -
  have P: "ucast irq < (2 ^ (11 - cte_level_bits) :: machine_word)"
    apply (rule order_le_less_trans[OF
        ucast_le_ucast[where 'a=6 and 'b=64, simplified, THEN iffD2, OF word_n1_ge]])
    apply (simp add: cte_level_bits_def minus_one_norm)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
    apply (rule is_aligned_no_wrap'[where sz=11])
     apply (simp add: is_aligned_def init_irq_node_ptr_def pptr_base_num)
    apply (rule shiftl_less_t2n[OF P])
    apply simp
    done
  show Q: "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + mask cte_level_bits
                \<le> init_irq_node_ptr + mask 11"
    apply (simp only: add_diff_eq[symmetric] add.assoc)
    apply (rule word_add_le_mono2)
     apply (simp only: trans [OF shiftl_t2n mult.commute] mask_def mult_1)
     apply (rule nasty_split_lt[OF P])
      apply (auto simp: cte_level_bits_def init_irq_node_ptr_def mask_def pptr_base_num)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + mask 11"
    apply (simp only: add_diff_eq[symmetric] mask_def mult_1 shiftl_t2n mult.commute)
    apply (rule word_add_le_mono2)
     apply (rule word_le_minus_one_leq)
     apply (rule shiftl_less_t2n[OF P, simplified shiftl_t2n mult.commute])
     apply simp
    apply (simp add: cte_level_bits_def init_irq_node_ptr_def pptr_base_num)
    done
qed

lemmas init_irq_ptrs_less_ineqs
   = init_irq_ptrs_ineqs(1)[THEN order_less_le_trans[rotated]]
     init_irq_ptrs_ineqs(2-3)[THEN order_le_less_trans]

lemmas init_irq_ptrs_all_ineqs[unfolded init_irq_node_ptr_def cte_level_bits_def]
   = init_irq_ptrs_ineqs(1)[THEN order_trans[rotated]]
     init_irq_ptrs_ineqs(2-3)[THEN order_trans]
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

lemma pspace_distinct_init_A: "pspace_distinct init_A_st"
  unfolding pspace_distinct_def
  apply (clarsimp simp: state_defs bit_simps empty_cnode_bits kernel_elf_base_def
                        cte_level_bits_def linorder_not_le cong: if_cong)
  apply (safe; simp add: pptr_base_num init_irq_ptrs_all_ineqs[simplified pptr_base_num mask_def, simplified])
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

declare ptrFormPAddr_addFromPPtr[simp]

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

lemma kernel_mapping_slot: "0x1FF \<in> kernel_mapping_slots"
  by (clarsimp simp: kernel_mapping_slots_def pptr_base_def pptrBase_def canonical_bit_def
                     pt_bits_left_def bit_simps level_defs)

lemma pool_for_asid_init_A_st[simp]:
  "pool_for_asid asid init_A_st = None"
  by (simp add: pool_for_asid_def state_defs)

lemma vspace_for_asid_init_A_st[simp]:
  "vspace_for_asid asid init_A_st = None"
  by (simp add: vspace_for_asid_def obind_def)

lemma global_pt_init_A_st[simp]:
  "global_pt init_A_st = riscv_global_pt_ptr"
  by (simp add: state_defs riscv_global_pt_def)

lemma is_aligned_riscv_global_pt_ptr[simp]:
  "is_aligned riscv_global_pt_ptr pt_bits"
  by (simp add: riscv_global_pt_ptr_def pptr_base_num bit_simps is_aligned_def)

lemma ptes_of_init_A_st_global:
  "ptes_of init_A_st =
   (\<lambda>p. if table_base p = riscv_global_pt_ptr \<and> is_aligned p pte_bits then
        Some ((un_PageTable (the_arch_obj init_global_pt)) (table_index p)) else None)"
  by (auto simp add: state_defs pte_of_def obind_def opt_map_def split: option.splits)

lemma pt_walk_init_A_st[simp]:
  "pt_walk max_pt_level level riscv_global_pt_ptr vref (ptes_of init_A_st) =
   Some (max_pt_level, riscv_global_pt_ptr)"
  apply (subst pt_walk.simps)
  apply (simp add: in_omonad ptes_of_init_A_st_global init_global_pt_def
                   is_aligned_pt_slot_offset_pte global_pte_def)
  done

(* Since the bottom 30 bits don't matter for 1GB pages, kernelELFPAddrBase and physBase don't have
   any influence on the index in the page table, i.e. the virtual address kernel_elf_base is always
   within the same 1GB page. *)
lemma elf_index_value:
  "elf_index = 0x1FE"
proof -
  have mask_0: "\<And>n m x. n < m \<Longrightarrow> - (1 << m) && x && mask n = 0"
    by (metis and.commute and_zero_eq word_mask_and_neg_shift_eq_0 word_bw_assocs(1))
  have "pt_index max_pt_level kernel_elf_base = 0x1FE"
    unfolding pt_index_def pt_bits_left_def level_defs bit_simps kernel_elf_base_def
              kernelELFBase_def pptrTop_def
    apply (subst word_plus_and_or_coroll)
     apply (subst mask_0; simp)
    apply (simp add: word_and_mask_shift_eq_0 shiftr_over_or_dist)
    apply (simp add: mask_def)
    done
  then show ?thesis
    unfolding elf_index_def
    by (simp add: bit_simps ucast_ucast_mask)
qed

lemma table_index_riscv_global_pt_ptr:
  "table_index (pt_slot_offset max_pt_level riscv_global_pt_ptr vref) =
  ucast ((vref >> toplevel_bits) && mask ptTranslationBits)"
  apply (simp add: pt_slot_offset_def pt_index_def pt_bits_left_def bit_simps level_defs
                   riscv_global_pt_ptr_def pptr_base_def pptrBase_def canonical_bit_def
                   toplevel_bits_def)
  apply (subst word_plus_and_or_coroll)
   apply word_bitwise
   apply simp
  apply word_bitwise
  apply (clarsimp simp: word_size)
  done

schematic_goal toplevel_bits_value:
  "toplevel_bits = ?v"
  by (simp add: toplevel_bits_def level_defs bit_simps pt_bits_left_def)

lemma kernel_window_bits_table_index:
  "\<lbrakk> pptr_base \<le> vref; vref < pptr_base + (1 << kernel_window_bits) \<rbrakk> \<Longrightarrow>
    table_index (pt_slot_offset max_pt_level riscv_global_pt_ptr vref) = 0x100"
  apply (simp add: table_index_riscv_global_pt_ptr toplevel_bits_value kernel_window_bits_def)
  apply (simp add: bit_simps pptr_base_def pptrBase_def neg_mask_le_high_bits word_size flip: NOT_mask)
  apply (subst (asm) mask_def)
  apply (simp add: canonical_bit_def)
  apply word_bitwise
  apply (clarsimp simp: word_size)
  done

lemma kernel_mapping_slots_0x100[simp]:
  "0x100 \<in> kernel_mapping_slots"
  by (simp add: kernel_mapping_slots_def pptr_base_def bit_simps pt_bits_left_def level_defs
                pptrBase_def canonical_bit_def)

lemma translate_address_kernel_window:
  "\<lbrakk> pptr_base \<le> vref; vref < pptr_base + (1 << kernel_window_bits) \<rbrakk>\<Longrightarrow>
   translate_address riscv_global_pt_ptr vref (ptes_of init_A_st) = Some (addrFromPPtr vref)"
  apply (clarsimp simp: translate_address_def in_omonad pt_lookup_target_def
                        pt_lookup_slot_from_level_def)
  apply (simp add: ptes_of_init_A_st_global[THEN fun_cong] init_global_pt_def global_pte_def pte_ref_def)
  apply (simp add: kernel_window_bits_table_index is_aligned_pt_slot_offset_pte)
  apply (simp add: bit_simps addr_from_ppn_def shiftl_shiftl)
  apply (simp add: ptrFromPAddr_def addrFromPPtr_def)
  apply (simp add: pptrBaseOffset_def paddrBase_def)
  apply (simp add: pt_bits_left_def bit_simps level_defs elf_index_value toplevel_bits_def)
  apply (rule conjI)
   apply (rule is_aligned_add)
    apply (simp add: mask_def)
   apply (simp add: pptrBase_def canonical_bit_def is_aligned_def)
  apply (simp add: pptr_base_def kernel_window_bits_def)
  apply (simp add: pptrBase_def neg_mask_le_high_bits flip: NOT_mask)
  apply (subst word_plus_and_or_coroll; simp add: canonical_bit_def word_size mask_def)
  apply word_bitwise
  apply clarsimp
  done

lemma kernelELF_plus_page:
  "((kernelELFPAddrBase && mask toplevel_bits) + 2^pageBits) \<le> 2^toplevel_bits"
  by (fastforce intro: aligned_mask_plus_bounded is_page_aligned_kernelELFPAddrBase
                simp: toplevel_bits_value bit_simps)

lemma elf_window_4k:
  "\<lbrakk> kernel_elf_base \<le> vref; vref < kernel_elf_base + (1 << pageBits) \<rbrakk> \<Longrightarrow>
    table_index (pt_slot_offset max_pt_level riscv_global_pt_ptr vref) = elf_index"
  using is_page_aligned_kernelELFPAddrBase
  apply (simp add: table_index_riscv_global_pt_ptr elf_index_value toplevel_bits_value
                   kernel_elf_base_def kernelELFBase_def)
  apply (simp add: bit_simps add_ac)
  apply (drule order_less_le_trans)
   apply (rule word_plus_mono_right)
    apply (rule kernelELF_plus_page[unfolded bit_simps toplevel_bits_value, simplified])
   apply (simp add: pptrTop_def)
  apply (simp add: bit_simps pptrTop_def mask_def is_aligned_nth)
  apply word_bitwise
  apply clarsimp
  done

lemma leq_elf_index:
  "0x100 \<le> elf_index"
  by (simp add: elf_index_value)

lemma kernel_mapping_slots_elf_index[simp]:
  "elf_index \<in> kernel_mapping_slots"
  by (simp add: kernel_mapping_slots_def pptr_base_def bit_simps pt_bits_left_def level_defs
                pptrBase_def canonical_bit_def leq_elf_index)

lemma rewrite_eq_minus_to_plus_eq:
  "(x = a - b) = (b + x = a)" for x :: "'a::ring"
  by auto

lemma merge_kernelELFPAddrBase_masks:
  "((kernelELFPAddrBase && ~~ mask 30) +
    (pptrTop + (kernelELFPAddrBase && mask 30) - kernelELFPAddrBase))
   = pptrTop"
  by (simp add: mask_out_sub_mask)

lemma is_aligned_ptrFromPAddr_kernelELFPAddrBase:
  "is_aligned
     (ptrFromPAddr
       (addr_from_ppn (ucast (kernelELFPAddrBase && ~~ mask toplevel_bits >> pageBits))))
     (pt_bits_left max_pt_level)"
  apply (simp add: addr_from_ppn_def ptrFromPAddr_def addrFromPPtr_def elf_index_value)
  apply (simp add: pt_bits_left_def bit_simps level_defs ucast_ucast_mask toplevel_bits_value)
  apply (simp add: pptrBase_def pptrBaseOffset_def paddrBase_def canonical_bit_def)
  apply (rule is_aligned_add)
   apply (metis and_not_mask is_aligned_andI1 is_aligned_shiftl_self shiftr_and_eq_shiftl)
  apply (simp add: is_aligned_def)
  done

lemma kernelELFPAddrBase_addrFromKPPtr:
  "\<lbrakk> kernel_elf_base \<le> vref; vref < kernel_elf_base + (1 << pageBits) \<rbrakk>
   \<Longrightarrow> addr_from_ppn (ucast (kernelELFPAddrBase && ~~ mask toplevel_bits >> pageBits)) +
       (vref && mask (pt_bits_left max_pt_level))
       = addrFromKPPtr vref"
  apply (simp add: addr_from_ppn_def ptrFromPAddr_def addrFromPPtr_def elf_index_value)
  apply (simp add: pt_bits_left_def bit_simps level_defs ucast_ucast_mask toplevel_bits_value)
  apply (simp add: addrFromKPPtr_def mask_shiftl_decompose flip: word_and_mask_shiftl)
  apply (simp add: ac_simps neg_mask_combine)
  apply (simp add: kernel_elf_base_def kernelELFBaseOffset_def)
  apply (simp only: kernelELFBase_def)
  apply (subst rewrite_eq_minus_to_plus_eq)
  apply (simp add: add_ac merge_kernelELFPAddrBase_masks)
  apply (subst word_plus_and_or_coroll)
   apply (simp add: pptrTop_def mask_def)
   apply word_bitwise
  apply (subst (asm) word_plus_and_or_coroll)
   apply (simp add: pptrTop_def mask_def)
   apply word_bitwise
  apply (drule order_less_le_trans)
   apply (rule word_plus_mono_right)
    apply (rule kernelELF_plus_page[unfolded bit_simps toplevel_bits_value, simplified])
   apply (simp add: pptrTop_def)
  apply (simp add: pptrTop_def mask_def)
  apply word_bitwise
  apply clarsimp
  done

lemma translate_address_kernel_elf_window:
  "\<lbrakk> kernel_elf_base \<le> vref; vref < kernel_elf_base + (1 << pageBits) \<rbrakk> \<Longrightarrow>
   translate_address riscv_global_pt_ptr vref (ptes_of init_A_st) = Some (addrFromKPPtr vref)"
  apply (clarsimp simp: translate_address_def in_omonad pt_lookup_target_def
                        pt_lookup_slot_from_level_def)
  apply (simp add: ptes_of_init_A_st_global[THEN fun_cong] init_global_pt_def global_pte_def pte_ref_def)
  apply (simp add: elf_window_4k is_aligned_pt_slot_offset_pte elf_index_value)
  apply (clarsimp simp: is_aligned_ptrFromPAddr_kernelELFPAddrBase kernelELFPAddrBase_addrFromKPPtr)
  done

lemma kernel_window_init_st:
  "kernel_window init_A_st = { pptr_base ..< pptr_base + (1 << kernel_window_bits) }"
  by (auto simp: state_defs kernel_window_def toplevel_bits_def bit_simps)

lemma abs_kernel_window_sufficient:
  "pptr_base + (1 << kernel_window_bits) \<le> kernel_elf_base"
  unfolding pptr_base_def kernel_elf_base_def
  using kernel_window_sufficient
  by simp

lemma abs_kernel_elf_window_at_least_page:
  "kernel_elf_base + 2 ^ pageBits \<le> kdev_base"
  unfolding kernel_elf_base_def kdev_base_def
  using kernel_elf_window_at_least_page
  by simp

lemma kernel_elf_base_no_overflow:
  "kernel_elf_base < kernel_elf_base + 2 ^ pageBits"
  unfolding kernel_elf_base_def
  by (rule kernelELFBase_no_overflow)

lemma kernel_elf_window_init_st:
  "kernel_elf_window init_A_st = { kernel_elf_base ..< kernel_elf_base + (1 << pageBits) }"
  using abs_kernel_window_sufficient
  by (force simp: state_defs kernel_elf_window_def)

lemma valid_global_vspace_mappings_init_A_st[simp]:
  "valid_global_vspace_mappings init_A_st"
  unfolding valid_global_vspace_mappings_def
  by (simp add: translate_address_kernel_window kernel_window_init_st
                translate_address_kernel_elf_window kernel_elf_window_init_st)

lemma valid_uses_init_A_st[simp]: "valid_uses_2 init_vspace_uses"
proof -
  note canonical_bit_def[simp]
  have [simplified, simp]: "pptr_base < pptr_base + (1 << kernel_window_bits)"
    by (simp add: pptr_base_def pptrBase_def kernel_window_bits_def)
  have [simp]: "p \<le> canonical_user \<Longrightarrow> \<not> pptr_base \<le> p" for p
    by (rule notI, drule (1) order_trans)
       (simp add: canonical_user_def mask_def pptr_base_def pptrBase_def)
  have [simp]: "p \<le> canonical_user \<Longrightarrow> \<not> kernel_elf_base \<le> p" for p
    using canonical_user_kernel_elf_base by simp
  have [simp]: "p \<le> canonical_user \<Longrightarrow> \<not> kdev_base \<le> p" for p
    by (rule notI, drule (1) order_trans)
       (simp add: canonical_user_def mask_def kdev_base_def kdevBase_def)
  have [simplified, simp]: "kernel_elf_base \<le> p \<Longrightarrow> \<not> p < pptr_base + (1 << kernel_window_bits)" for p
    using abs_kernel_window_sufficient by simp
  have [simp]: "kdev_base \<le> p \<Longrightarrow> \<not> p < kernel_elf_base + 2 ^ pageBits" for p
    using abs_kernel_elf_window_at_least_page by simp
  have "pptr_base + (1 << kernel_window_bits) < kernel_elf_base + 2 ^ pageBits"
    using abs_kernel_window_sufficient kernel_elf_base_no_overflow by simp
  thus ?thesis
    using canonical_user_pptr_base pptr_base_kernel_elf_base
    unfolding valid_uses_2_def init_vspace_uses_def window_defs
    by (auto simp: canonical_user_canonical above_pptr_base_canonical)
qed

lemma valid_global_arch_objs_init_A_st[simp]:
  "valid_global_arch_objs init_A_st"
  by (simp add: valid_global_arch_objs_def state_defs level_defs obj_at_def)

lemma valid_global_tables_init_A_st[simp]:
  "valid_global_tables init_A_st"
  apply (simp add: valid_global_tables_def Let_def riscv_global_pt_def[symmetric])
  apply (clarsimp simp: state_defs pte_rights_of_def vm_kernel_only_def global_pte_def)
  done

lemma vspace_for_pool_init_A_st[simp]:
  "vspace_for_pool ap asid (asid_pools_of init_A_st) = None"
  by (clarsimp simp: vspace_for_pool_def obind_def in_opt_map_eq state_defs split: option.splits)

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

lemma global_pt_kernel_window_init_arch_state[simp]:
  "obj_addrs init_global_pt riscv_global_pt_ptr \<subseteq>
     kernel_window_2 (riscv_kernel_vspace init_arch_state)"
  apply (clarsimp simp: state_defs pptr_base_num bit_simps kernel_window_def kernel_elf_base_def
                        kernel_window_bits_def)
  apply (rule conjI; unat_arith)
  done

lemma idle_thread_in_kernel_window_init_arch_state[simp]:
  "{idle_thread_ptr..0x3FF + idle_thread_ptr} \<subseteq>
     kernel_window_2 (riscv_kernel_vspace init_arch_state)"
  apply (clarsimp simp: state_defs pptr_base_num bit_simps kernel_window_def kernel_elf_base_def
                        kernel_window_bits_def)
  apply (rule conjI; unat_arith)
  done

lemma pptr_base_kernel_window_no_overflow:
  "pptr_base \<le> pptr_base + (1 << kernel_window_bits)"
  by (simp add: pptr_base_def pptrBase_def canonical_bit_def kernel_window_bits_def)

lemma irq_node_pptr_base_kernel_elf_base:
  fixes irq::irq
  assumes "x \<le> pptr_base + (m + (mask cte_level_bits + 0x3000))"
  assumes "m \<le> mask (size irq) << cte_level_bits"
  shows "\<not> kernel_elf_base \<le> x"
proof -
  have less:
    "\<And>m x. \<lbrakk> m \<le> x; x < 1 << kernel_window_bits \<rbrakk> \<Longrightarrow> pptr_base + m < kernel_elf_base"
    using order_le_less_trans word_plus_strict_mono_right pptr_base_kernel_elf_base
          pptr_base_kernel_window_no_overflow abs_kernel_window_sufficient
    by fastforce
  from assms show ?thesis
    apply (simp add: not_le)
    apply (erule order_le_less_trans)
    apply (rule less[where x="mask cte_level_bits + 0x3000 + mask (size irq) << cte_level_bits"];
           simp add: word_size cte_level_bits_def mask_def kernel_window_bits_def)
    apply unat_arith
    done
qed

lemma irq_node_in_kernel_window_init_arch_state':
  "\<lbrakk> init_irq_node_ptr + m \<le> x; x \<le> init_irq_node_ptr + m + mask cte_level_bits;
     m \<le> mask (size (irq::irq)) << cte_level_bits\<rbrakk>
   \<Longrightarrow> x \<in> kernel_window_2 (riscv_kernel_vspace init_arch_state)"
  apply (clarsimp simp: kernel_window_def init_vspace_uses_def init_arch_state_def)
  apply (rule conjI)
   apply (clarsimp simp: state_defs)
   apply (rule ccontr, simp add:not_le)
   apply (drule(1) le_less_trans)
   apply (cut_tac is_aligned_no_wrap'[where ptr=pptr_base
                                      and off="0x3000 + m"
                                      and sz=canonical_bit, simplified])
     apply (simp add: add_ac)
     apply (auto simp: pptr_base_kernel_elf_base irq_node_pptr_base_kernel_elf_base)[1]
    apply (simp add: pptr_base_num canonical_bit_def is_aligned_def)
   apply (simp add: pptr_base_num cte_level_bits_def canonical_bit_def mask_def word_size)
   apply unat_arith
  apply clarsimp
  apply (thin_tac "kernel_elf_base \<le> x \<longrightarrow> P" for x P)
  apply (simp add: cte_level_bits_def canonical_bit_def mask_def init_irq_node_ptr_def
                   pptr_base_num word_size kernel_window_bits_def)
  apply unat_arith
  apply clarsimp
  done

lemma irq_node_in_kernel_window_init_arch_state[simp]:
  "\<lbrakk> init_irq_node_ptr + (ucast (irq::irq) << cte_level_bits) \<le> x;
     x \<le> init_irq_node_ptr + (ucast irq << cte_level_bits) + 2 ^ cte_level_bits - 1 \<rbrakk>
   \<Longrightarrow> x \<in> kernel_window_2 (riscv_kernel_vspace init_arch_state)"
  apply (erule irq_node_in_kernel_window_init_arch_state')
   apply (simp add: mask_def add_diff_eq)
  apply (simp add: word_size mask_def cte_level_bits_def)
  apply (thin_tac P for P)
  apply word_bitwise
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
    apply (clarsimp simp: valid_objs_def state_defs wellformed_pte_def global_pte_def
                          valid_obj_def valid_vm_rights_def vm_kernel_only_def
                          dom_if_Some cte_level_bits_def)
    apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def is_master_reply_cap_def
                          valid_cap_def obj_at_def valid_tcb_state_def valid_arch_tcb_def
                          cap_aligned_def word_bits_def valid_ipc_buffer_cap_simps)+
    apply (clarsimp simp: valid_cs_def word_bits_def cte_level_bits_def
                          init_irq_ptrs_all_ineqs valid_tcb_def
                   split: if_split_asm)
    apply auto[1]
   apply (simp add: pspace_aligned_init_A pspace_distinct_init_A)
   apply (rule conjI)
    apply (clarsimp simp: if_live_then_nonz_cap_def obj_at_def state_defs live_def hyp_live_def
                          arch_tcb_live_def)
   apply (rule conjI)
    apply (clarsimp simp: zombies_final_def cte_wp_at_cases state_defs
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
   apply (clarsimp simp: init_kheap_def init_global_pt_def split: if_split_asm)
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
   apply (simp add: valid_arch_state_def state_defs obj_at_def a_type_def)
  apply (rule conjI, clarsimp simp: valid_cur_fpu_def)
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
  apply (rule conjI)
   apply (clarsimp simp: pspace_in_kernel_window_def init_A_st_def init_kheap_def)
  apply (simp add: cap_refs_in_kernel_window_def caps_of_state_init_A_st_Null
                  valid_refs_def[unfolded cte_wp_at_caps_of_state])
  done


end

end
