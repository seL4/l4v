(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Kernel init refinement. Currently axiomatised.
*)

theory ArchKernelInit_AI
imports
  ADT_AI
  Tcb_AI
  Arch_AI
begin

context Arch begin global_naming ARM (*FIXME: arch_split*)

text \<open>
  Showing that there is a state that satisfies the abstract invariants.
\<close>

lemma [simp]: "is_aligned (0x1000 :: word32) 9" by (simp add: is_aligned_def)
lemma [simp]: "is_aligned (0x2000 :: word32) 9" by (simp add: is_aligned_def)

lemmas ptr_defs = init_tcb_ptr_def idle_thread_ptr_def init_irq_node_ptr_def
                  init_globals_frame_def init_global_pd_def
lemmas state_defs = init_A_st_def init_kheap_def init_arch_state_def ptr_defs

lemma [simp]: "is_tcb (TCB t)" by (simp add: is_tcb_def)

lemma [simp]: "ran (empty_cnode n) = {Structures_A.NullCap}"
  apply (auto simp: ran_def empty_cnode_def)
  apply (rule_tac x="replicate n False" in exI)
  apply simp
  done

lemma empty_cnode_apply[simp]:
  "(empty_cnode n xs = Some cap) = (length xs = n \<and> cap = Structures_A.NullCap)"
  by (auto simp add: empty_cnode_def)

lemma valid_cs_size_empty[simp]:
  "valid_cs_size n (empty_cnode n) = (n < word_bits - cte_level_bits)"
  apply (simp add: valid_cs_size_def)
  apply (insert wf_empty_bits [of n])
  apply fastforce
  done

lemma init_cdt [simp]:
  "cdt init_A_st = init_cdt"
  by (simp add: state_defs)

lemma mdp_parent_empty [simp]:
  "\<not>Map.empty \<Turnstile> x \<rightarrow> y"
  apply clarsimp
  apply (drule tranclD)
  apply (clarsimp simp: cdt_parent_of_def)
  done

lemma descendants_empty [simp]:
  "descendants_of x Map.empty = {}"
  by (clarsimp simp: descendants_of_def)

lemma reply_Null [simp]: "\<not>is_reply_cap NullCap"
  by (simp add: is_reply_cap_def)

declare  cap_range_NullCap[simp]

lemma pde_mapping_bits_shift:
  fixes x :: "12 word"
  shows "x \<noteq> 0 \<Longrightarrow> 2 ^ pde_mapping_bits - 1 < (ucast x << pde_mapping_bits :: word32)"
  apply (simp only:shiftl_t2n pde_mapping_bits_def)
  apply (unfold word_less_alt)
  apply simp
  apply (unfold word_mult_def)
  apply (subst int_word_uint)
  apply (subst mod_pos_pos_trivial)
    apply simp
   apply simp
   apply (subst uint_up_ucast)
    apply (simp add: is_up_def source_size_def target_size_def word_size)
   apply (cut_tac 'a = "12" and x = x in uint_lt2p)
   apply simp
  apply (rule order_less_le_trans)
   prefer 2
   apply (rule pos_mult_pos_ge)
    apply (subst uint_up_ucast)
     apply (simp add: is_up_def source_size_def target_size_def word_size)
    apply (simp add: word_neq_0_conv word_less_alt)
   apply simp
  apply simp
  done

lemma mask_pde_mapping_bits:
  "(mask 20 :: machine_word) = 2^pde_mapping_bits - 1"
  by (simp add: mask_def pde_mapping_bits_def)

lemma init_irq_ptrs_ineqs:
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + 2 ^ cte_level_bits - 1
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
  "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
proof -
  have P: "ucast irq < (2 ^ (14 - cte_level_bits) :: word32)"
    apply (rule order_le_less_trans[OF
        ucast_le_ucast[where 'a=irq_len and 'b=32,simplified,THEN iffD2, OF word_n1_ge]])
    apply (simp add: cte_level_bits_def minus_one_norm)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) \<ge> init_irq_node_ptr"
    apply (rule is_aligned_no_wrap'[where sz=14])
     apply (simp add: is_aligned_def init_irq_node_ptr_def kernel_base_def)
    apply (rule shiftl_less_t2n[OF P])
    apply simp
    done
  show Q: "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits) + 2 ^ cte_level_bits - 1
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
    apply (simp only: add_diff_eq[symmetric] add.assoc)
    apply (rule word_add_le_mono2)
     apply (simp only: trans [OF shiftl_t2n mult.commute])
     apply (rule nasty_split_lt[OF P])
      apply (simp_all add: cte_level_bits_def
        word_bits_def kernel_base_def init_irq_node_ptr_def)
    done
  show "init_irq_node_ptr + (ucast (irq :: irq) << cte_level_bits)
                \<le> init_irq_node_ptr + 2 ^ 14 - 1"
    apply (simp only: add_diff_eq[symmetric])
    apply (rule word_add_le_mono2)
     apply (rule word_le_minus_one_leq, rule shiftl_less_t2n[OF P])
     apply simp
    apply (simp add: kernel_base_def
      cte_level_bits_def word_bits_def init_irq_node_ptr_def)
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

lemmas ucast_le_ucast_irq_32 = ucast_le_ucast[where 'a=irq_len and 'b=32,simplified]
lemma init_irq_ptrs_eq:
  "((ucast (irq :: irq) << cte_level_bits)
        = (ucast (irq' :: irq) << cte_level_bits :: word32))
      = (irq = irq')"
  apply safe
  apply (rule ccontr)
  apply (erule_tac bnd="ucast (max_word :: irq) + 1"
              in shift_distinct_helper[rotated 3],
         safe intro!: plus_one_helper2;
         simp add: ucast_le_ucast_irq_32 up_ucast_inj_eq cte_level_bits_def minus_1_eq_mask
                   ucast_leq_mask;
         simp add: mask_eq_exp_minus_1)
  done

lemma in_kernel_base:
"\<lbrakk>m < 0xFFFFF; n \<le> 0xFFFFF\<rbrakk> \<Longrightarrow> (\<forall>y\<in>{kernel_base + m .. n + kernel_base}.
              kernel_base \<le> y \<and> y \<le> kernel_base + 0xFFFFF)"
  apply (clarsimp simp:)
  apply (intro conjI)
   apply (rule ccontr,simp add:not_le)
   apply (drule(1) le_less_trans)
   apply (cut_tac is_aligned_no_wrap'[where ptr = kernel_base and off = m
     and sz = 28,simplified])
     apply (drule(1) less_le_trans)
     apply simp
    apply (simp add:kernel_base_def is_aligned_def)
   apply (rule ccontr,simp add:not_less)
   apply (drule less_le_trans[where z = "0x10000000"])
    apply simp
   apply simp
  apply (erule order_trans)
  apply (simp add:field_simps)
  apply (rule word_plus_mono_right)
   apply simp
  apply (simp add:kernel_base_def)
  done

lemma pspace_aligned_init_A:
  "pspace_aligned init_A_st"
  apply (clarsimp simp: pspace_aligned_def state_defs wf_obj_bits [OF wf_empty_bits]
                        dom_if_Some cte_level_bits_def)
  apply (safe intro!: aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl],
           simp_all add: is_aligned_def word_bits_def kernel_base_def)[1]
  done

lemma pspace_distinct_init_A:
  "pspace_distinct init_A_st"
  apply (clarsimp simp: pspace_distinct_def state_defs pageBits_def
                        empty_cnode_bits kernel_base_def
                        linorder_not_le cte_level_bits_def
                  cong: if_cong)
  apply (safe,
         simp_all add: init_irq_ptrs_all_ineqs
                       [simplified kernel_base_def, simplified])[1]
  apply (cut_tac x="init_irq_node_ptr + (ucast irq << cte_level_bits)"
             and y="init_irq_node_ptr + (ucast irqa << cte_level_bits)"
             and sz=cte_level_bits in aligned_neq_into_no_overlap;
         simp add: init_irq_node_ptr_def kernel_base_def cte_level_bits_def)
    apply (rule aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl])
    apply (simp add: is_aligned_def)
   apply (rule aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl])
   apply (simp add: is_aligned_def)
  apply (simp add: linorder_not_le)
  done

lemma caps_of_state_init_A_st_Null:
  "caps_of_state (init_A_st::'z::state_ext state) x
     = (if cte_at x (init_A_st::'z::state_ext state) then Some cap.NullCap else None)"
  apply (subgoal_tac "\<not> cte_wp_at ((\<noteq>) cap.NullCap) x init_A_st")
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
   apply (clarsimp simp: pspace_respects_device_region_def init_A_st_def init_machine_state_def device_mem_def
                         in_device_frame_def obj_at_def init_kheap_def a_type_def)
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

lemma invs_A:
  "invs init_A_st"

  apply (simp add: invs_def)
  apply (rule conjI)
   prefer 2
   apply (simp add: cur_tcb_def state_defs obj_at_def)
  apply (simp add: valid_state_def)
  apply (rule conjI)
   apply (simp add: valid_pspace_def)
   apply (rule conjI)
    apply (clarsimp simp: kernel_base_def valid_objs_def state_defs
                          valid_obj_def valid_vm_rights_def vm_kernel_only_def
                          dom_if_Some cte_level_bits_def)
    apply (rule conjI)
     apply (simp add: vmsz_aligned_def, rule is_aligned_addrFromPPtr_n;
            clarsimp simp: is_aligned_def)
    apply (rule conjI)
     apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def is_master_reply_cap_def
                           valid_cap_def obj_at_def valid_tcb_state_def valid_arch_tcb_def
                           cap_aligned_def word_bits_def valid_ipc_buffer_cap_simps)+
    apply (clarsimp simp: valid_cs_def word_bits_def cte_level_bits_def
                          init_irq_ptrs_all_ineqs valid_tcb_def
                   split: if_split_asm)
    apply (simp add: vmsz_aligned_def, rule is_aligned_addrFromPPtr_n;
           clarsimp simp: is_aligned_def)
   apply (rule conjI)
    apply (clarsimp simp: pspace_aligned_def state_defs wf_obj_bits [OF wf_empty_bits]
                          dom_if_Some cte_level_bits_def)
    apply (safe intro!: aligned_add_aligned[OF _ is_aligned_shiftl_self order_refl],
           simp_all add: is_aligned_def word_bits_def kernel_base_def)[1]
   apply (rule conjI)
    apply (simp add:pspace_distinct_init_A)
   apply (rule conjI)
    apply (clarsimp simp: if_live_then_nonz_cap_def obj_at_def state_defs live_def hyp_live_def)
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
                         reply_masters_mdb_def)
   apply (simp add:descendants_inc_def)
  apply (rule conjI)
   apply (simp add: valid_ioc_def init_A_st_def init_ioc_def cte_wp_at_cases2)
   apply (intro allI impI, elim exE conjE)
   apply (case_tac obj, simp_all add: cap_of_def)
   apply (clarsimp simp: init_kheap_def split: if_split_asm)
  apply (rule conjI)
   apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def state_defs valid_arch_idle_def)
  apply (rule conjI)
   apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def state_defs)
  apply (rule conjI)
   apply (clarsimp simp: if_unsafe_then_cap_def caps_of_state_init_A_st_Null)
  apply (subst conj_assoc[symmetric])
  apply (subst conj_assoc[symmetric])
  apply (subst conj_assoc)
  apply (rule conjI)
 using cte_wp_at_init_A_st_Null
   apply (fastforce simp: valid_reply_caps_def unique_reply_caps_def
                         has_reply_cap_def is_reply_cap_to_def pred_tcb_at_def obj_at_def
                         caps_of_state_init_A_st_Null is_master_reply_cap_to_def
                         valid_reply_masters_def valid_global_refs_def
                         valid_refs_def[unfolded cte_wp_at_caps_of_state])

  apply (rule conjI)
   apply (clarsimp simp: valid_arch_state_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_asid_table_def state_defs)
   apply (rule conjI)
    apply (clarsimp simp: valid_arch_state_def obj_at_def state_defs
                          a_type_def)
   apply (rule conjI)
    apply (simp add: valid_global_pts_def state_defs)
   apply (simp add: state_defs is_inv_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_irq_node_def obj_at_def state_defs
                         is_cap_table_def wf_empty_bits
                         init_irq_ptrs_all_ineqs cte_level_bits_def
                         init_irq_ptrs_eq[unfolded cte_level_bits_def])
   apply (intro conjI)
    apply (rule inj_onI)
    apply (simp add: init_irq_ptrs_eq[unfolded cte_level_bits_def])
   apply clarsimp
   apply word_bitwise
  apply (simp add: valid_irq_handlers_def caps_of_state_init_A_st_Null
                   ran_def cong: rev_conj_cong)
  apply (rule conjI)
   apply (clarsimp simp: valid_irq_states_def init_A_st_def init_machine_state_def valid_irq_masks_def init_irq_masks_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_machine_state_def init_A_st_def
                         init_machine_state_def init_underlying_memory_def)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def state_defs valid_vspace_objs_def)
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_arch_caps_def)
   apply (rule conjI)
    apply (clarsimp simp: valid_vs_lookup_def)
    apply (clarsimp simp: vs_lookup_pages_def state_defs vs_asid_refs_def)
   apply (clarsimp simp: valid_table_caps_def caps_of_state_init_A_st_Null
                         unique_table_caps_def unique_table_refs_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_global_objs_def state_defs)
   apply (clarsimp simp: valid_ao_at_def obj_at_def empty_table_def pde_ref_def
                         valid_pde_mappings_def valid_vso_at_def)
   apply (simp add: kernel_mapping_slots_def kernel_base_def)
   apply (rule is_aligned_addrFromPPtr_n; simp add: pageBits_def is_aligned_def)
  apply (rule conjI)
   apply (simp add: valid_kernel_mappings_def state_defs
                         valid_kernel_mappings_if_pd_def pde_ref_def
                         ran_def)
   apply (auto simp: pde_ref_def split: if_split_asm)[1]
  apply (rule conjI)
   apply (clarsimp simp: equal_kernel_mappings_def state_defs obj_at_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_asid_map_def state_defs)
  apply (rule conjI)
   apply (clarsimp simp: valid_global_vspace_mappings_def obj_at_def state_defs
                         valid_pd_kernel_mappings_def mask_pde_mapping_bits)
   apply (simp add: valid_pde_kernel_mappings_def kernel_base_def)
   apply (rule conjI)
    apply (fastforce simp:pde_mapping_bits_def)
   apply (intro ballI impI)
   apply (clarsimp simp:pde_mapping_bits_def)
   apply word_bitwise
   apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: pspace_in_kernel_window_def state_defs mask_def)
   apply (intro conjI impI)
            apply (rule in_kernel_base|simp)+
         apply (erule exE,drule sym,simp add:field_simps)
         apply (rule in_kernel_base[simplified add.commute])
          apply (rule word_less_add_right, simp add: cte_level_bits_def)
           apply (rule less_le_trans[OF shiftl_less_t2n'[OF ucast_less]],simp+)[1]
          apply simp
         apply (simp add:cte_level_bits_def field_simps)
         apply (subst add.commute)
         apply (rule le_plus')
          apply simp+
          apply (rule less_imp_le)
          apply (rule less_le_trans[OF shiftl_less_t2n'[OF ucast_less]],simp+)[1]
     apply (rule in_kernel_base|simp)+
  apply (simp add: cap_refs_in_kernel_window_def caps_of_state_init_A_st_Null
                  valid_refs_def[unfolded cte_wp_at_caps_of_state])
  done

end

end
