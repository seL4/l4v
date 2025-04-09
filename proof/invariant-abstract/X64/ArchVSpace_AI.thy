(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
X64-specific VSpace invariants
*)

theory ArchVSpace_AI
imports VSpacePre_AI
begin

context Arch begin arch_global_naming

abbreviation "canonicalise x \<equiv> (scast ((ucast x) :: 48 word)) :: 64 word"

lemma pptr_base_shift_cast_le:
  fixes x :: "9 word"
  shows  "((pptr_base >> pml4_shift_bits) && mask ptTranslationBits \<le> ucast x) =
        (ucast (pptr_base >> pml4_shift_bits) \<le> x)"
  apply (subgoal_tac "((pptr_base >> pml4_shift_bits) && mask ptTranslationBits) = ucast (ucast (pptr_base >> pml4_shift_bits) :: 9 word)")
   prefer 2
   apply (simp add: ucast_ucast_mask ptTranslationBits_def)
  apply (simp add: ucast_le_ucast)
  done

(* FIXME: move to Invariant_AI *)
definition
  glob_vs_refs_arch :: "arch_kernel_obj \<Rightarrow> (vs_ref \<times> obj_ref) set"
  where  "glob_vs_refs_arch \<equiv> \<lambda>ko. case ko of
    ASIDPool pool \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | PageMapL4 pm \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageMapL4), p)) ` graph_of (pml4e_ref \<circ> pm)
  | PDPointerTable pdpt \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APDPointerTable), p)) ` graph_of (pdpte_ref \<circ> pdpt)
  | PageDirectory pd \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) ` graph_of (pde_ref \<circ> pd)
  | _ \<Rightarrow> {}"

declare glob_vs_refs_arch_def[simp]

definition
  "glob_vs_refs \<equiv> arch_obj_fun_lift glob_vs_refs_arch {}"

crunch unmap_page, perform_page_invocation
  for pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps)

crunch find_vspace_for_asid_assert
  for inv[wp]: "P"
  (simp: crunch_simps wp: crunch_wps)

lemma asid_word_bits [simp]: "asid_bits < word_bits"
  by (simp add: asid_bits_def word_bits_def)


lemma asid_low_high_bits:
  "\<lbrakk> asid_low_bits_of x = asid_low_bits_of y;
     ucast (asid_high_bits_of x) = (ucast (asid_high_bits_of y)::machine_word);
     asid_wf x; asid_wf y \<rbrakk>
  \<Longrightarrow> x = y"
  apply (rule word_eqI)
  apply (simp add: upper_bits_unset_is_l2p_64[symmetric] bang_eq nth_ucast word_size asid_wf_def)
  apply (clarsimp simp: asid_bits_of_defs nth_ucast nth_shiftr)
  apply (simp add: asid_high_bits_def asid_bits_def asid_low_bits_def word_bits_def)
  subgoal premises prems[rule_format] for n
  apply (cases "n < asid_low_bits")
   using prems(1)
   apply (fastforce simp: asid_bits_defs)
  apply (cases "n < asid_bits")
   using prems(2)[where n="n - asid_low_bits"]
   apply (fastforce simp: asid_bits_defs)
  using prems(3-)
  by (simp add: linorder_not_less asid_bits_defs)
  done

lemma asid_low_high_bits':
  "\<lbrakk> asid_low_bits_of x = asid_low_bits_of y;
     asid_high_bits_of x = asid_high_bits_of y;
     asid_wf x; asid_wf y \<rbrakk>
  \<Longrightarrow> x = y"
  by (rule asid_low_high_bits; (assumption|word_eqI_solve simp: asid_low_bits_def)?)

lemma is_aligned_asid_low_bits_of_zero:
  "is_aligned asid asid_low_bits \<longleftrightarrow> asid_low_bits_of asid = 0"
  apply (simp add: is_aligned_mask word_eq_iff word_size asid_bits_defs asid_bits_of_defs nth_ucast)
  apply (intro iffI allI; drule_tac x=n in spec; fastforce)
  done

lemma table_cap_ref_at_eq:
  "table_cap_ref c = Some [x] \<longleftrightarrow> vs_cap_ref c = Some [x]"
  by (auto simp: table_cap_ref_def vs_cap_ref_simps vs_cap_ref_def
          split: cap.splits arch_cap.splits vmpage_size.splits option.splits)

lemma table_cap_ref_ap_eq:
  "table_cap_ref c = Some [x,y] \<longleftrightarrow> vs_cap_ref c = Some [x,y]"
  by (auto simp: table_cap_ref_def vs_cap_ref_simps vs_cap_ref_def
          split: cap.splits arch_cap.splits vmpage_size.splits option.splits)

lemma vspace_at_asid_unique:
  "\<lbrakk> vspace_at_asid asid pm s; vspace_at_asid asid' pm s;
     unique_table_refs (caps_of_state s);
     valid_vs_lookup s; valid_vspace_objs s; valid_global_objs s;
     valid_arch_state s; asid_wf asid; asid_wf asid' \<rbrakk>
       \<Longrightarrow> asid = asid'"
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule(1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])+
  apply (clarsimp simp: table_cap_ref_ap_eq[symmetric])
  apply (clarsimp simp: table_cap_ref_def
                 split: cap.split_asm arch_cap.split_asm option.split_asm)
  apply (drule(2) unique_table_refsD,
         simp+, clarsimp simp: table_cap_ref_def,
         erule(1) asid_low_high_bits)
   apply simp+
  done

lemma vspace_at_asid_unique2:
  "\<lbrakk> vspace_at_asid asid pm s; vspace_at_asid asid pm' s \<rbrakk>
         \<Longrightarrow> pm = pm'"
  apply (clarsimp simp: vspace_at_asid_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup_2ConsD vs_lookup_atD
                        vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def
                 split: kernel_object.splits
                        arch_kernel_obj.splits
                 dest!: graph_ofD)
  done


lemma valid_vs_lookupE:
  "\<lbrakk> valid_vs_lookup s; \<And>ref p. (ref \<unrhd> p) s' \<Longrightarrow> (ref \<unrhd> p) s;
           set (x64_global_pdpts (arch_state s)) \<subseteq> set (x64_global_pdpts (arch_state s'));
           caps_of_state s = caps_of_state s' \<rbrakk>
     \<Longrightarrow> valid_vs_lookup s'"
  by (simp add: valid_vs_lookup_def, blast)


lemma dmo_vspace_at_asid [wp]:
  "\<lbrace>vspace_at_asid a pd\<rbrace> do_machine_op f \<lbrace>\<lambda>_. vspace_at_asid a pd\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: vspace_at_asid_def)
  done

lemma find_vspace_for_asid_vspace_at_asid [wp]:
  "\<lbrace>\<top>\<rbrace> find_vspace_for_asid asid \<lbrace>\<lambda>pd. vspace_at_asid asid pd\<rbrace>, -"
  apply (simp add: find_vspace_for_asid_def assertE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply (clarsimp simp: vspace_at_asid_def)
  apply (rule vs_lookupI)
   apply (simp add: vs_asid_refs_def graph_of_def)
   apply fastforce
  apply (rule r_into_rtrancl)
  apply (erule vs_lookup1I)
   prefer 2
   apply (rule refl)
  apply (simp add: vs_refs_def graph_of_def asid_bits_of_defs)
  apply fastforce
  done

crunch do_machine_op
  for valid_vs_lookup[wp]: "valid_vs_lookup"


lemma vspace_at_asid_arch_up':
  "x64_asid_table (f (arch_state s)) = x64_asid_table (arch_state s)
    \<Longrightarrow> vspace_at_asid asid pml4 (arch_state_update f s) = vspace_at_asid asid pml4 s"
  by (clarsimp simp add: vspace_at_asid_def vs_lookup_def vs_lookup1_def)


lemmas ackInterrupt_irq_masks = no_irq[OF no_irq_ackInterrupt]


lemma ucast_ucast_low_bits:
  fixes x :: machine_word
  shows "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> ucast (ucast x:: 9 word) = x"
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
  "(rf \<rhd> p) (s\<lparr>arch_state := arch_state s
                \<lparr>x64_asid_table := (x64_asid_table (arch_state s))
                   (pptr := None)\<rparr>\<rparr>)
        \<longrightarrow> (rf \<rhd> p) s"
  apply (simp add: vs_lookup_def vs_lookup1_def)
  apply (rule impI, erule subsetD[rotated])
  apply (rule Image_mono[OF order_refl])
  apply (simp add: vs_asid_refs_def graph_of_def)
  apply (rule image_mono)
  apply (clarsimp split: if_split_asm)
  done


lemma vs_lookup_pages_clear_asid_table:
  "(rf \<unrhd> p) (s\<lparr>arch_state := arch_state s
                \<lparr>x64_asid_table := (x64_asid_table (arch_state s))
                   (pptr := None)\<rparr>\<rparr>)
   \<Longrightarrow> (rf \<unrhd> p) s"
  apply (simp add: vs_lookup_pages_def vs_lookup_pages1_def)
  apply (erule subsetD[rotated])
  apply (rule Image_mono[OF order_refl])
  apply (simp add: vs_asid_refs_def graph_of_def)
  apply (rule image_mono)
  apply (clarsimp split: if_split_asm)
  done

lemma valid_ioports_arch_state_simp[simp]:
  "x64_allocated_io_ports (f (arch_state s)) = x64_allocated_io_ports (arch_state s)
   \<Longrightarrow> valid_ioports_2 (caps_of_state s) (f (arch_state s)) = valid_ioports s"
  unfolding valid_ioports_def ioports_no_overlap_def all_ioports_issued_def issued_ioports_def
  by simp

lemma valid_arch_state_unmap_strg:
  "valid_arch_state s \<longrightarrow>
   valid_arch_state(s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := (x64_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
  apply (rule conjI)
   apply (clarsimp simp add: ran_def)
   apply blast
  apply (clarsimp simp: inj_on_def valid_ioports_def)
  done

lemma valid_vspace_objs_unmap_strg:
  "valid_vspace_objs s \<longrightarrow>
   valid_vspace_objs(s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := (x64_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vspace_objs_def)
  apply (drule vs_lookup_clear_asid_table [rule_format])
  apply blast
  done


lemma valid_vs_lookup_unmap_strg:
  "valid_vs_lookup s \<longrightarrow>
   valid_vs_lookup(s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := (x64_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vs_lookup_def)
  apply (drule vs_lookup_pages_clear_asid_table)
  apply blast
  done


lemma ex_asid_high_bits_plus:
  "asid \<le> mask asid_bits \<Longrightarrow> \<exists>x \<le> 2^asid_low_bits - 1. asid = (ucast (asid_high_bits_of asid) << asid_low_bits) + x"
  apply (rule_tac x="asid && mask asid_low_bits" in exI)
  apply (rule conjI)
   apply (simp add: mask_def)
   apply (rule word_and_le1)
  apply (subst (asm) mask_def)
  apply (simp add: upper_bits_unset_is_l2p_64 [symmetric])
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size nth_ucast nth_shiftl)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size nth_ucast nth_shiftl nth_shiftr asid_high_bits_of_def
                        asid_low_bits_def word_bits_def asid_bits_def)
  apply (rule iffI)
   prefer 2
   apply fastforce
  apply (clarsimp simp: linorder_not_less)
  apply (subgoal_tac "n < 12", fastforce)
  apply (clarsimp simp add: linorder_not_le [symmetric])
  done


lemma asid_high_bits_shl:
  "\<lbrakk> is_aligned base asid_low_bits; base \<le> mask asid_bits \<rbrakk> \<Longrightarrow> ucast (asid_high_bits_of base) << asid_low_bits = base"
  apply (simp add: mask_def upper_bits_unset_is_l2p_64 [symmetric])
  apply (rule word_eqI[rule_format])
  apply (simp add: is_aligned_nth nth_ucast nth_shiftl nth_shiftr asid_low_bits_def
                   asid_high_bits_of_def word_size asid_bits_def word_bits_def)
  apply (rule iffI, clarsimp)
  apply (rule context_conjI)
   apply (clarsimp simp add: linorder_not_less [symmetric])
  apply simp
  apply (subgoal_tac "n < 12", fastforce)
  apply (clarsimp simp add: linorder_not_le [symmetric])
  done


crunch hw_asid_invalidate
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"

crunch hw_asid_invalidate
  for aligned[wp]: pspace_aligned

crunch hw_asid_invalidate
  for "distinct"[wp]: pspace_distinct

crunch hw_asid_invalidate
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"

crunch hw_asid_invalidate
  for vspace_objs[wp]: valid_vspace_objs
  (simp: valid_vspace_objs_arch_update)

crunch hw_asid_invalidate
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"

lemmas hw_asid_invalidate_typ_ats [wp] =
  abs_typ_at_lifts [OF hw_asid_invalidate_typ_at]

crunch hw_asid_invalidate
  for cur[wp]: cur_tcb

crunch hw_asid_invalidate
  for valid_objs[wp]: valid_objs

crunch hw_asid_invalidate
  for obj_at[wp]: "\<lambda>s. P (obj_at Q p s)"

crunch hw_asid_invalidate
  for valid_vs_lookup[wp]: "valid_vs_lookup"

crunch hw_asid_invalidate
  for x64_asid_table_inv[wp]: "\<lambda>s. P (x64_asid_table (arch_state s))"

lemma dmo_invalidateASID_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (invalidateASID a b) \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: invalidateASID_def dmo_machine_op_lift_invs)

lemma hw_asid_invalidate_invs[wp]: "\<lbrace>invs\<rbrace> hw_asid_invalidate asid vspace \<lbrace>\<lambda>_. invs\<rbrace>"
  by (wpsimp simp: hw_asid_invalidate_def)


lemma asid_low_bits_word_bits:
  "asid_low_bits < word_bits"
  by (simp add: asid_low_bits_def word_bits_def)


lemma valid_global_objs_arch_update:
  "x64_global_pml4 (f (arch_state s)) = x64_global_pml4 (arch_state s)
    \<and> x64_global_pdpts (f (arch_state s)) = x64_global_pdpts (arch_state s)
    \<and> x64_global_pds (f (arch_state s)) = x64_global_pds (arch_state s)
    \<and> x64_global_pts (f (arch_state s)) = x64_global_pts (arch_state s)
     \<Longrightarrow> valid_global_objs (arch_state_update f s) = valid_global_objs s"
  by (simp add: valid_global_objs_def second_level_tables_def)


lemma find_vspace_for_asid_assert_wp:
  "\<lbrace>\<lambda>s. \<forall>pd. vspace_at_asid asid pd s \<and> asid \<noteq> 0 \<longrightarrow> P pd s\<rbrace> find_vspace_for_asid_assert asid \<lbrace>P\<rbrace>"
  apply (simp add: find_vspace_for_asid_assert_def
                   find_vspace_for_asid_def assertE_def
                 split del: if_split)
  apply (rule hoare_pre)
   apply (wp get_pde_wp get_asid_pool_wp | wpc)+
  apply clarsimp
  apply (drule spec, erule mp)
  apply (clarsimp simp: vspace_at_asid_def word_neq_0_conv)
  apply (rule vs_lookupI)
   apply (simp add: vs_asid_refs_def)
   apply (rule image_eqI[OF refl])
   apply (erule graph_ofI)
  apply (rule r_into_rtrancl, simp)
  apply (erule vs_lookup1I)
   apply (simp add: vs_refs_def)
   apply (rule image_eqI[rotated])
    apply (erule graph_ofI)
   apply simp
  apply (simp add: asid_low_bits_of_def)
  done

lemma valid_vs_lookup_arch_update:
  "x64_asid_table (f (arch_state s)) = x64_asid_table (arch_state s)
     \<Longrightarrow> valid_vs_lookup (arch_state_update f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def vs_lookup_pages_arch_update)

lemmas find_vspace_for_asid_typ_ats [wp] = abs_typ_at_lifts [OF find_vspace_for_asid_inv]

lemma find_vspace_for_asid_page_map_l4 [wp]:
  "\<lbrace>valid_vspace_objs\<rbrace>
  find_vspace_for_asid asid
  \<lbrace>\<lambda>pd. page_map_l4_at pd\<rbrace>, -"
  apply (simp add: find_vspace_for_asid_def assertE_def whenE_def split del: if_split)
  apply (wp|wpc|clarsimp|rule conjI)+
  apply (drule vs_lookup_atI)
  apply (drule (2) valid_vspace_objsD)
  apply clarsimp
  apply (drule bspec, blast)
  apply (clarsimp simp: obj_at_def)
  done


lemma find_vspace_for_asid_lookup_ref:
  "\<lbrace>\<top>\<rbrace> find_vspace_for_asid asid \<lbrace>\<lambda>pd. ([VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                                          VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd)\<rbrace>, -"
  apply (simp add: find_vspace_for_asid_def assertE_def whenE_def split del: if_split)
  apply (wp|wpc|clarsimp|rule conjI)+
  apply (drule vs_lookup_atI)
  apply (erule vs_lookup_step)
  apply (erule vs_lookup1I [OF _ _ refl])
  apply (simp add: vs_refs_def)
  apply (rule image_eqI[rotated], erule graph_ofI)
  apply (simp add: asid_bits_of_defs)
  done


lemma find_vspace_for_asid_lookup[wp]:
  "\<lbrace>\<top>\<rbrace> find_vspace_for_asid asid \<lbrace>\<lambda>pd. \<exists>\<rhd> pd\<rbrace>,-"
  apply (rule hoare_strengthen_postE_R, rule find_vspace_for_asid_lookup_ref)
  apply auto
  done


lemma find_vspace_for_asid_pde [wp]:
  "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace>
  find_vspace_for_asid asid
  \<lbrace>\<lambda>pd. pml4e_at (pd + (get_pml4_index vptr << word_size_bits))\<rbrace>, -"
proof -
  have x:
    "\<lbrace>valid_vspace_objs and pspace_aligned\<rbrace> find_vspace_for_asid asid
     \<lbrace>\<lambda>pd. pspace_aligned and page_map_l4_at pd\<rbrace>, -"
    by wpsimp
  show ?thesis
    apply (rule hoare_strengthen_postE_R, rule x)
    apply clarsimp
    apply (erule page_map_l4_pml4e_atI)
     prefer 2
     apply assumption
    apply (rule vptr_shiftr_le_2p)
    done
qed

lemma vs_lookup1_rtrancl_iterations:
  "(tup, tup') \<in> (vs_lookup1 s)\<^sup>*
    \<Longrightarrow> (length (fst tup) \<le> length (fst tup')) \<and>
       (tup, tup') \<in> ((vs_lookup1 s)
           ^^ (length (fst tup') - length (fst tup)))"
  apply (erule rtrancl_induct)
   apply simp
  apply (elim conjE)
  apply (subgoal_tac "length (fst z) = Suc (length (fst y))")
   apply (simp add: Suc_diff_le)
   apply (erule(1) relcompI)
  apply (clarsimp simp: vs_lookup1_def)
  done


lemma find_vspace_for_asid_lookup_none:
  "\<lbrace>\<top>\<rbrace>
    find_vspace_for_asid asid
   -, \<lbrace>\<lambda>e s. \<forall>p. \<not> ([VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
   VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p) s\<rbrace>"
  apply (simp add: find_vspace_for_asid_def assertE_def
                 split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply clarsimp
  apply (intro allI conjI impI)
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def up_ucast_inj_eq
                  dest!: vs_lookup1_rtrancl_iterations
                         graph_ofD vs_lookup1D)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: vs_lookup1_rtrancl_iterations
                        graph_ofD vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def up_ucast_inj_eq
                        asid_low_bits_of_def
                 dest!: graph_ofD)
  done


lemma find_vspace_for_asid_aligned_pm [wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace> find_vspace_for_asid asid \<lbrace>\<lambda>rv s. is_aligned rv table_size\<rbrace>,-"
  apply (simp add: find_vspace_for_asid_def assertE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply clarsimp
  apply (drule vs_lookup_atI)
  apply (drule (2) valid_vspace_objsD)
  apply clarsimp
  apply (drule bspec, blast)
  apply (thin_tac "ko_at ko p s" for ko p)
  apply (clarsimp simp: pspace_aligned_def obj_at_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: a_type_def bit_simps
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  done

lemma find_vspace_for_asid_aligned_pm_bits[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
      find_vspace_for_asid asid
   \<lbrace>\<lambda>rv s. is_aligned rv pml4_bits\<rbrace>, -"
  by (simp add: pml4_bits_def pageBits_def, rule find_vspace_for_asid_aligned_pm)

lemma find_vspace_for_asid_lots:
  "\<lbrace>\<lambda>s. (\<forall>rv. ([VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
   VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> rv) s
           \<longrightarrow> (valid_vspace_objs s \<longrightarrow> page_map_l4_at rv s)
           \<longrightarrow> Q rv s)
       \<and> ((\<forall>rv. \<not> ([VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
   VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> rv) s) \<longrightarrow> (\<forall>e. E e s))\<rbrace>
    find_vspace_for_asid asid
  \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  apply (clarsimp simp: validE_def valid_def)
  apply (frule in_inv_by_hoareD [OF find_vspace_for_asid_inv])
  apply (frule use_valid [OF _ find_vspace_for_asid_lookup_none
                                [unfolded validE_E_def validE_def]])
   apply simp
  apply (frule use_valid [OF _ find_vspace_for_asid_lookup_ref
                                [unfolded validE_R_def validE_def]])
   apply simp
  apply (clarsimp split: sum.split_asm)
  apply (drule spec, drule uncurry, erule mp)
  apply clarsimp
  apply (frule use_valid [OF _ find_vspace_for_asid_page_map_l4
                                [unfolded validE_R_def validE_def]])
   apply simp
  apply simp
  done

lemma vs_lookup1_inj:
  "\<lbrakk> ((ref, p), (ref', p')) \<in> vs_lookup1 s ^^ n;
     ((ref, p), (ref', p'')) \<in> vs_lookup1 s ^^ n \<rbrakk>
       \<Longrightarrow> p' = p''"
  apply (induct n arbitrary: ref ref' p p' p'')
   apply simp
  apply (clarsimp dest!: vs_lookup1D)
  apply (subgoal_tac "pa = pb", simp_all)
  apply (simp add: obj_at_def)
  apply (auto simp: vs_refs_def up_ucast_inj_eq dest!: graph_ofD
             split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  done

lemma vs_lookup_Cons_eq:
  "(ref \<rhd> p) s \<Longrightarrow> ((v # ref) \<rhd> p') s = ((ref, p) \<rhd>1 (v # ref, p')) s"
  apply (rule iffI)
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                  dest!: graph_ofD)
   apply (frule vs_lookup1_trans_is_append[where ys=ref])
   apply (frule vs_lookup1_trans_is_append[where ys="v # ref"])
   apply (clarsimp dest!: vs_lookup1_rtrancl_iterations vs_lookup1D)
   apply (clarsimp simp add: up_ucast_inj_eq)
   apply (drule(1) vs_lookup1_inj)
   apply (simp add: vs_lookup1I)
  apply (erule vs_lookup_trancl_step)
  apply simp
  done

definition
  valid_unmap :: "vmpage_size \<Rightarrow> asid * vspace_ref \<Rightarrow> bool"
where
  "valid_unmap sz \<equiv> \<lambda>(asid, vptr). 0 < asid \<and> is_aligned vptr (pageBitsForSize sz)"

lemma lookup_pdpt_slot_is_aligned:
  "\<lbrace>(\<exists>\<rhd> pm) and K (vmsz_aligned vptr sz) and K (is_aligned pm pml4_bits)
    and valid_arch_state and valid_vspace_objs and equal_kernel_mappings
    and pspace_aligned and valid_global_objs\<rbrace>
     lookup_pdpt_slot pm vptr
   \<lbrace>\<lambda>rv s. is_aligned rv word_size_bits\<rbrace>,-"
  apply (simp add: lookup_pdpt_slot_def)
  apply (wp get_pml4e_wp | wpc)+
  apply (clarsimp simp: lookup_pml4_slot_eq)
  apply (frule(2) valid_vspace_objsD[rotated])
  apply simp
  apply (rule is_aligned_add)
   apply (case_tac "ucast (lookup_pml4_slot pm vptr && mask pml4_bits >> word_size_bits) \<in> kernel_mapping_slots")
    apply (frule kernel_mapping_slots_empty_pml4eI)
     apply (simp add: obj_at_def)+
    apply (erule_tac x="ptrFromPAddr x" in allE)
    apply (simp add: pml4e_ref_def second_level_tables_def)
    apply (erule is_aligned_weaken[OF is_aligned_global_pdpt])
      apply ((simp add: invs_psp_aligned invs_vspace_objs invs_arch_state
                        pdpt_bits_def bit_simps
                 split: vmpage_size.split)+)[3]
   apply (drule_tac x="ucast (lookup_pml4_slot pm vptr && mask pml4_bits >> word_size_bits)" in bspec, simp)
   apply (clarsimp simp: obj_at_def a_type_def)
   apply (simp split: Structures_A.kernel_object.split_asm if_split_asm
                     arch_kernel_obj.split_asm)
   apply (erule is_aligned_weaken[OF pspace_alignedD], simp)
   apply (simp add: obj_bits_def bit_simps  split: vmpage_size.splits)
  apply (rule is_aligned_shiftl)
  apply (simp add: bit_simps)
  done

(* FIXME: remove *)
lemmas page_directory_at_aligned_pd_bits = is_aligned_pd

(* FIXME x64: check *)
definition
  "empty_refs m \<equiv> case m of (VMPDE pde, _) \<Rightarrow> pde_ref pde = None
                          | (VMPDPTE pdpte, _) \<Rightarrow> pdpte_ref pdpte = None
                      | _ \<Rightarrow> True"

definition
  "parent_for_refs entry \<equiv> \<lambda>cap.
     case entry of (VMPTE _, slot)
        \<Rightarrow> slot && ~~ mask pt_bits \<in> obj_refs cap \<and> is_pt_cap cap \<and> cap_asid cap \<noteq> None
      | (VMPDE _, slot)
        \<Rightarrow> slot && ~~ mask pd_bits \<in> obj_refs cap \<and> is_pd_cap cap \<and> cap_asid cap \<noteq> None
      | (VMPDPTE _, slot)
        \<Rightarrow> slot && ~~ mask pdpt_bits \<in> obj_refs cap \<and> is_pdpt_cap cap \<and> cap_asid cap \<noteq> None"

(* FIXME x64: check *)
definition
  "same_refs m cap s \<equiv>
      case m of
       (VMPTE pte, slot) \<Rightarrow>
         (\<exists>p. pte_ref_pages pte = Some p \<and> p \<in> obj_refs cap) \<and>
         (\<forall>ref. (ref \<rhd> (slot && ~~ mask pt_bits)) s \<longrightarrow>
           vs_cap_ref cap = Some (VSRef ((slot && mask pt_bits >> word_size_bits) && mask ptTranslationBits) (Some APageTable) # ref))
     | (VMPDE pde, slot) \<Rightarrow>
         (\<exists>p. pde_ref_pages pde = Some p \<and> p \<in> obj_refs cap) \<and>
         (\<forall>ref. (ref \<rhd> (slot && ~~ mask pd_bits)) s \<longrightarrow>
           vs_cap_ref cap = Some (VSRef ((slot && mask pd_bits >> word_size_bits) && mask ptTranslationBits) (Some APageDirectory) # ref))
     | (VMPDPTE pdpte, slot) \<Rightarrow>
         (\<exists>p. pdpte_ref_pages pdpte = Some p \<and> p \<in> obj_refs cap) \<and>
         (\<forall>ref. (ref \<rhd> (slot && ~~ mask pdpt_bits)) s \<longrightarrow>
           vs_cap_ref cap = Some (VSRef ((slot && mask pdpt_bits >> word_size_bits)&& mask ptTranslationBits) (Some APDPointerTable) # ref))"

definition
  "valid_page_inv page_inv \<equiv> case page_inv of
    PageMap cap ptr m vspace \<Rightarrow>
      cte_wp_at (is_arch_update cap) ptr
      and (cte_wp_at (\<lambda>c. vs_cap_ref c = None) ptr or (\<lambda>s. cte_wp_at (\<lambda>c. same_refs m c s) ptr s))
      and cte_wp_at is_pg_cap ptr
      and (\<lambda>s. same_refs m cap s)
      and valid_slots m
      and valid_cap cap
      and K (is_pg_cap cap \<and> empty_refs m)
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
  | PageUnmap cap ptr \<Rightarrow>
     \<lambda>s. \<exists>d r R maptyp sz m. cap = PageCap d r R maptyp sz m \<and>
         case_option True (valid_unmap sz) m \<and>
         cte_wp_at ((=) (cap.ArchObjectCap cap)) ptr s \<and>
         s \<turnstile> (cap.ArchObjectCap cap)
  | PageGetAddr ptr \<Rightarrow> \<top>"

crunch unmap_page
  for aligned[wp]: pspace_aligned
  (wp: crunch_wps simp: crunch_simps)


crunch unmap_page
  for "distinct"[wp]: pspace_distinct
  (wp: crunch_wps simp: crunch_simps)


crunch unmap_page
  for valid_objs[wp]: "valid_objs"
  (wp: crunch_wps simp: crunch_simps)


crunch unmap_page
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps set_arch_obj_simps)

lemma set_cap_valid_slots[wp]:
  "\<lbrace>valid_slots x2\<rbrace> set_cap cap (a, b)
          \<lbrace>\<lambda>rv s. valid_slots x2 s \<rbrace>"
   apply (case_tac x2)
   apply (simp only:)
   apply (case_tac aa; clarsimp simp: valid_slots_def)
    by (wp hoare_vcg_ball_lift)+

definition
  empty_pde_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "empty_pde_at p \<equiv> \<lambda>s.
  \<exists>pd. ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s \<and>
       pd (ucast (p && mask pd_bits >> word_size_bits)) = InvalidPDE"

definition
  empty_pdpte_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "empty_pdpte_at p \<equiv> \<lambda>s.
  \<exists>pdpt. ko_at (ArchObj (PDPointerTable pdpt)) (p && ~~ mask pdpt_bits) s \<and>
       pdpt (ucast (p && mask pdpt_bits >> word_size_bits)) = InvalidPDPTE"

definition
  empty_pml4e_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "empty_pml4e_at p \<equiv> \<lambda>s.
  \<exists>pml4. ko_at (ArchObj (PageMapL4 pml4)) (p && ~~ mask pml4_bits) s \<and>
       pml4 (ucast (p && mask pml4_bits >> word_size_bits)) = InvalidPML4E"

definition
  kernel_vsrefs :: "vs_ref set"
where
 "kernel_vsrefs \<equiv> {r. case r of VSRef x y \<Rightarrow>  (pptr_base >> pml4_shift_bits) && mask ptTranslationBits \<le> x}"

definition
  "valid_pti pti \<equiv> case pti of
     PageTableMap cap cptr pde p vspace\<Rightarrow>
        (\<lambda>s. p && ~~ mask pd_bits \<notin> global_refs s)
        and K(wellformed_pde pde)
        and valid_cap cap
        and valid_pde pde
        and pde_at p
        and cte_wp_at (\<lambda>c. is_arch_update cap c \<and> cap_asid c = None) cptr
        and (\<lambda>s. \<exists>x ref. (pde_ref_pages pde = Some x)
                 \<and> x \<in> obj_refs cap
                 \<and> obj_at (empty_table (set (second_level_tables (arch_state s)))) x s
                 \<and> (ref \<rhd> (p && ~~ mask pd_bits)) s
                 \<and> vs_cap_ref cap = Some (VSRef ((p && mask pd_bits >> word_size_bits) && mask ptTranslationBits) (Some APageDirectory) # ref))
        and K (is_pt_cap cap)
   | PageTableUnmap cap ptr \<Rightarrow>
     cte_wp_at ((=) cap) ptr and valid_cap cap
       and is_final_cap' cap
       and K (is_pt_cap cap)"

definition
  "valid_pdi pdi \<equiv> case pdi of
      PageDirectoryMap cap cptr pdpte p vspace\<Rightarrow>
        (\<lambda>s. p && ~~ mask pdpt_bits \<notin> global_refs s)
        and K(wellformed_pdpte pdpte)
        and valid_cap cap
        and valid_pdpte pdpte
        and pdpte_at p
        and cte_wp_at (\<lambda>c. is_arch_update cap c \<and> cap_asid c = None) cptr
        and (\<lambda>s. \<exists>x ref. (pdpte_ref_pages pdpte = Some x)
                 \<and> x \<in> obj_refs cap
                 \<and> obj_at (empty_table (set (second_level_tables (arch_state s)))) x s
                 \<and> (ref \<rhd> (p && ~~ mask pdpt_bits)) s
                 \<and> vs_cap_ref cap =
                       Some (VSRef ((p && mask pdpt_bits >> word_size_bits) && mask ptTranslationBits)
                       (Some APDPointerTable) # ref))
        and K (is_pd_cap cap)
    | PageDirectoryUnmap cap cptr \<Rightarrow>
      cte_wp_at ((=) cap) cptr and valid_cap cap and is_final_cap' cap and K (is_pd_cap cap)"

definition
  "valid_pdpti pdpti \<equiv> case pdpti of
      PDPTMap cap cptr pml4e p vspace\<Rightarrow>
        (\<lambda>s. p && ~~ mask pml4_bits \<notin> global_refs s)
        and K(wellformed_pml4e pml4e)
        and valid_cap cap and pml4e_at p
        and valid_pml4e pml4e and empty_pml4e_at p
        and cte_wp_at (\<lambda>c. is_arch_update cap c \<and> cap_asid c = None) cptr
        and (\<lambda>s. \<exists>x ref. (pml4e_ref_pages pml4e = Some x)
                 \<and> x \<in> obj_refs cap
                 \<and> obj_at (empty_table (set (second_level_tables (arch_state s)))) x s
                 \<and> (ref \<rhd> (p && ~~ mask pml4_bits)) s
                 \<and> vs_cap_ref cap =
                       Some (VSRef ((p && mask pml4_bits >> word_size_bits) && mask ptTranslationBits)
                       (Some APageMapL4) # ref)
                 \<and> hd (the (vs_cap_ref cap)) \<notin> kernel_vsrefs)
        and K (is_pdpt_cap cap)
    | PDPTUnmap cap cptr \<Rightarrow>
      cte_wp_at ((=) cap) cptr and valid_cap cap and is_final_cap' cap and K (is_pdpt_cap cap)"


lemmas mapM_x_wp_inv_weak = mapM_x_wp_inv[OF hoare_weaken_pre]

crunch unmap_page_table
  for aligned[wp]: pspace_aligned
  (wp: mapM_x_wp_inv_weak crunch_wps dmo_aligned simp: crunch_simps)
crunch unmap_pd
  for aligned[wp]: pspace_aligned
  (wp: mapM_x_wp_inv_weak crunch_wps dmo_aligned simp: crunch_simps)
crunch unmap_pdpt
  for aligned[wp]: pspace_aligned
  (wp: mapM_x_wp_inv_weak crunch_wps dmo_aligned simp: crunch_simps)

crunch unmap_page_table
  for valid_objs[wp]: valid_objs
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps)

crunch unmap_page_table
  for "distinct"[wp]: pspace_distinct
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps)

crunch unmap_page_table
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps)

crunch unmap_page_table
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: mapM_x_wp_inv_weak crunch_wps hoare_drop_imps)

crunch unmap_pd
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: mapM_x_wp_inv_weak crunch_wps hoare_drop_imps)

crunch unmap_pd
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps)

crunch unmap_pdpt
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: mapM_x_wp_inv_weak crunch_wps hoare_drop_imps)

crunch unmap_page
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps)

crunch unmap_pdpt
  for caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps set_arch_obj_simps)

lemmas flush_table_typ_ats [wp] = abs_typ_at_lifts [OF flush_table_typ_at]

definition
  "valid_apinv ap \<equiv> case ap of
  asid_pool_invocation.Assign asid p slot \<Rightarrow>
  (\<lambda>s. \<exists>pool. ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) p s \<and>
              pool (asid_low_bits_of asid) = None)
  and cte_wp_at (\<lambda>cap. is_pml4_cap cap \<and> cap_asid cap = None) slot
  and K (0 < asid \<and> asid_wf asid)
  and ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p)"


lemma dmo_ackInterrupt[wp]: "\<lbrace>invs\<rbrace> do_machine_op (ackInterrupt irq) \<lbrace>\<lambda>y. invs\<rbrace>"
  by (simp add: ackInterrupt_def dmo_machine_op_lift_invs)

lemmas writeCR3_irq_masks = no_irq[OF no_irq_writeCR3]

lemma dmo_writeCR3[wp]: "\<lbrace>invs\<rbrace> do_machine_op (writeCR3 vs asid) \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: writeCR3_def dmo_machine_op_lift_invs)

crunch get_current_cr3
  for inv[wp]: P

lemma get_current_cr3_rewrite_lift[wp]:
  "\<lbrace>P\<rbrace> get_current_cr3 \<lbrace>\<lambda>rv s. Q rv \<longrightarrow> P s\<rbrace>"
  by (wp hoare_drop_imps)

lemma arch_state_update_invs:
  assumes "invs s"
  assumes "x64_asid_table (f (arch_state s)) = x64_asid_table (arch_state s)"
  assumes "valid_global_refs s \<Longrightarrow> valid_global_refs (arch_state_update f s)"
  assumes "valid_arch_state s \<Longrightarrow> valid_arch_state (arch_state_update f s)"
  assumes "valid_table_caps s \<Longrightarrow> valid_table_caps (arch_state_update f s)"
  assumes "valid_global_objs s \<Longrightarrow> valid_global_objs (arch_state_update f s)"
  assumes "valid_kernel_mappings s \<Longrightarrow> valid_kernel_mappings (arch_state_update f s)"
  assumes "valid_global_vspace_mappings s \<Longrightarrow> valid_global_vspace_mappings (arch_state_update f s)"
  assumes "pspace_in_kernel_window s \<Longrightarrow> pspace_in_kernel_window (arch_state_update f s)"
  assumes "cap_refs_in_kernel_window s \<Longrightarrow> cap_refs_in_kernel_window (arch_state_update f s)"
  assumes "valid_ioports s \<Longrightarrow> valid_ioports (arch_state_update f s)"
  assumes "valid_cur_fpu s \<Longrightarrow> valid_cur_fpu (arch_state_update f s)"
  shows "invs (arch_state_update f s)"
  using assms by (simp add: invs_def valid_state_def valid_irq_node_def valid_irq_states_def
                            valid_machine_state_def valid_arch_caps_def valid_asid_map_def
                            valid_vspace_objs_arch_update valid_vs_lookup_arch_update)

lemma valid_ioports_cr3_update[iff]:
  "valid_ioports (s\<lparr>arch_state := arch_state s\<lparr>x64_current_cr3 := c\<rparr>\<rparr>) = valid_ioports s"
  by (clarsimp simp: valid_ioports_def all_ioports_issued_def issued_ioports_def)

crunch set_current_cr3
  for global_pml4[wp]: "\<lambda>s. P (x64_global_pml4 (arch_state s))"

lemma set_current_cr3_invs[wp]:
  "\<lbrace>invs and K (valid_cr3 c)\<rbrace> set_current_cr3 c \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (wpsimp simp: set_current_cr3_def; erule arch_state_update_invs)
  by (auto simp: valid_global_refs_def global_refs_def valid_arch_state_def valid_table_caps_def
                 valid_global_objs_def valid_kernel_mappings_def second_level_tables_def valid_cur_fpu_defs)

lemma valid_cr3_make_cr3:
  "asid_wf asid \<Longrightarrow> valid_cr3 (make_cr3 addr asid)"
  apply (clarsimp simp: valid_cr3_def make_cr3_def cr3_addr_mask_def bit_simps
                        is_aligned_andI2[OF is_aligned_shift])
  apply (rule order.trans[OF word_and_le1])
  apply (simp add: mask_def asid_bits_def)
  done

lemma set_current_vspace_root_invs[wp]:
  "\<lbrace>invs and K (asid_wf asid)\<rbrace> set_current_vspace_root vspace asid \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: set_current_vspace_root_def valid_cr3_make_cr3)

lemma drop_imp:
  "A \<Longrightarrow> B \<longrightarrow> A"
  by blast

lemma asid_wf_0:
  "asid_wf 0"
  by (simp add: asid_wf_def)

lemma svr_invs [wp]:
  "\<lbrace>invs\<rbrace> set_vm_root t' \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: set_vm_root_def)
  apply (wp whenE_wp
         | wpc
         | simp add: split_def if_apply_def2 cong: conj_cong if_cong
         | strengthen valid_cr3_make_cr3)+
    apply (strengthen drop_imp)
    apply (wpsimp wp: get_cap_wp simp: asid_wf_0)+
  apply (drule (1) cte_wp_valid_cap[OF _ invs_valid_objs])
  apply (simp add: valid_cap_def)
  done

crunch set_current_vspace_root, set_vm_root
  for pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"
  (simp: crunch_simps)

crunch get_current_cr3, set_vm_root
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (simp: crunch_simps)

lemmas set_vm_root_typ_ats [wp] = abs_typ_at_lifts [OF set_vm_root_typ_at]

lemma valid_pte_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pte pte s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pte pte s)\<rbrace>"
  apply (insert bool_function_four_cases[where f=P])
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (simp | wp)+
  done

lemma set_cap_valid_pte_stronger:
  "\<lbrace>\<lambda>s. P (valid_pte pte s)\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. P (valid_pte pte s)\<rbrace>"
  by (wp valid_pte_lift3 set_cap_typ_at)

lemma valid_pde_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pde pde s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pde pde s)\<rbrace>"
  apply (insert bool_function_four_cases[where f=P])
  apply (erule disjE)
   apply (cases pde)
     apply (simp add: data_at_def | wp hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (cases pde)
     apply (simp add: data_at_def | wp hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (simp | wp)+
  done

lemma set_cap_valid_pde_stronger:
  "\<lbrace>\<lambda>s. P (valid_pde pde s)\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. P (valid_pde pde s)\<rbrace>"
  by (wp valid_pde_lift3 set_cap_typ_at)

lemma valid_pdpte_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pdpte pdpte s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pdpte pdpte s)\<rbrace>"
  apply (insert bool_function_four_cases[where f=P])
  apply (erule disjE)
   apply (cases pdpte)
     apply (simp add: data_at_def | wp hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (cases pdpte)
     apply (simp add: data_at_def | wp hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (simp | wp)+
  done

lemma set_cap_valid_pdpte_stronger:
  "\<lbrace>\<lambda>s. P (valid_pdpte pdpte s)\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. P (valid_pdpte pdpte s)\<rbrace>"
  by (wp valid_pdpte_lift3 set_cap_typ_at)
end

context Arch begin arch_global_naming

(* FIXME: move *)
context
  fixes c :: cap and s :: "'a::state_ext state" and p :: obj_ref
  assumes vc: "valid_cap c s"
begin

lemma valid_cap_to_table_cap':
  assumes ref: "p \<in> obj_refs c"
  shows valid_cap_to_pt_cap'  : "page_table_at p s \<Longrightarrow> is_pt_cap c"
    and valid_cap_to_pd_cap'  : "page_directory_at p s \<Longrightarrow> is_pd_cap c"
    and valid_cap_to_pdpt_cap': "pd_pointer_table_at p s \<Longrightarrow> is_pdpt_cap c"
  using vc ref
  by (auto simp: valid_cap_def obj_at_def is_obj_defs is_pt_cap_def is_pd_cap_def is_pdpt_cap_def
          split: cap.splits option.splits arch_cap.splits if_splits)

lemma valid_cap_to_table_cap:
  assumes ref: "obj_refs c = {p}"
  shows valid_cap_to_pt_cap  : "page_table_at p s \<Longrightarrow> is_pt_cap c"
    and valid_cap_to_pd_cap  : "page_directory_at p s \<Longrightarrow> is_pd_cap c"
    and valid_cap_to_pdpt_cap: "pd_pointer_table_at p s \<Longrightarrow> is_pdpt_cap c"
  by (rule valid_cap_to_table_cap'; simp add: ref)+

end


lemma ref_is_unique:
  "\<lbrakk>(ref \<rhd> p) s; (ref' \<rhd> p) s; p \<notin> set (second_level_tables (arch_state s));
    valid_vs_lookup s; unique_table_refs (caps_of_state s);
    valid_vspace_objs s; valid_asid_table (x64_asid_table (arch_state s)) s;
    valid_caps (caps_of_state s) s\<rbrakk>
   \<Longrightarrow> ref = ref'"
  apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
      apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
          apply (clarsimp simp: valid_asid_table_def up_ucast_inj_eq)
          apply (erule (2) inj_on_domD)
         apply ((clarsimp simp: obj_at_def)+)[4]
     apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
         apply (clarsimp simp: obj_at_def)
        apply (drule (2) vs_lookup_apI)+
        apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI]
                               obj_ref_elemD
                         simp: table_cap_ref_ap_eq[symmetric])
        apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
       apply ((clarsimp simp: obj_at_def)+)[3]
    apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
        apply ((clarsimp simp: obj_at_def)+)[2]
      apply (simp add: pml4e_ref_def split: pml4e.splits)
      apply (drule (5) vs_lookup_pml4I)+
      apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI]
                             obj_ref_elemD)
      apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
      apply (drule (3) valid_capsD[THEN valid_cap_to_pdpt_cap])+
      apply (clarsimp simp: is_pdpt_cap_def table_cap_ref_simps vs_cap_ref_simps)
     apply ((clarsimp simp: obj_at_def)+)[2]
   apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
       apply ((clarsimp simp: obj_at_def)+)[3]
    apply (simp add: pdpte_ref_def split: pdpte.splits)
    apply (drule (7) vs_lookup_pdptI)+
    apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI] obj_ref_elemD)
    apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
    apply (drule (3) valid_capsD[THEN valid_cap_to_pd_cap])+
    apply (clarsimp simp: is_pd_cap_def table_cap_ref_simps vs_cap_ref_simps)
   apply (clarsimp simp: obj_at_def)
  apply (erule (1) vs_lookupE_alt[OF _ _ valid_asid_table_ran], clarsimp)
      apply ((clarsimp simp: obj_at_def)+)[4]
  apply (simp add: pde_ref_def split: pde.splits)
  apply (drule (9) vs_lookup_pdI)+
  apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI] obj_ref_elemD)
  apply (drule_tac cap=cap and cap'=capa in unique_table_refsD, simp+)[1]
  apply (drule (3) valid_capsD[THEN valid_cap_to_pt_cap])+
  apply (clarsimp simp: is_pt_cap_def table_cap_ref_simps vs_cap_ref_simps)
  done

lemma pml4_translation_bits:
  fixes p :: machine_word
  shows "p && mask pml4_bits >> word_size_bits < 2 ^ ptTranslationBits"
  apply (rule shiftr_less_t2n)
  apply (simp add: pml4_bits_def simple_bit_simps)
  apply (rule and_mask_less'[of 12 p, simplified])
  done

lemma ucast_ucast_mask_shift_helper:
  "ucast (ucast (p && mask pml4_bits >> word_size_bits :: machine_word) :: 9 word)
        = (p && mask pml4_bits >> word_size_bits :: machine_word)"
  apply (rule ucast_ucast_len)
  using pml4_translation_bits by (auto simp: ptTranslationBits_def)

lemma unat_ucast_pml4_bits_shift:
  "unat (ucast (p && mask pml4_bits >> word_size_bits :: machine_word) :: 9 word)
        = unat (p && mask pml4_bits >> word_size_bits)"
  apply (simp only: unat_ucast)
  apply (rule mod_less[OF unat_less_power])
  using pml4_translation_bits by (auto simp: ptTranslationBits_def)

lemma kernel_vsrefs_kernel_mapping_slots:
  "(ucast (p && mask pml4_bits >> word_size_bits) \<in> kernel_mapping_slots) =
    (VSRef (p && mask pml4_bits >> word_size_bits) (Some APageMapL4) \<in> kernel_vsrefs)"
  apply (clarsimp simp: kernel_mapping_slots_def kernel_vsrefs_def
                        word_le_nat_alt unat_ucast_pml4_bits_shift)
  apply (clarsimp simp: pptr_base_def pptrBase_def bit_simps mask_def)
  done

lemma vs_lookup_typI:
  "\<lbrakk>(r \<rhd> p) s; valid_vspace_objs s; valid_asid_table (x64_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> asid_pool_at p s \<or> vspace_table_at p s"
  apply (erule (1) vs_lookupE_alt)
     apply (clarsimp simp: ran_def)
     apply (drule (2) valid_asid_tableD)
    apply simp+
  done

lemma vs_lookup_vs_lookup_pagesI:
  "\<lbrakk>(r \<rhd> p) s; (r' \<unrhd> p) s; valid_vspace_objs s; valid_asid_table (x64_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> (r' \<rhd> p) s"
  by (erule (5) vs_lookup_vs_lookup_pagesI'[OF _ vs_lookup_typI])

(* FIXME: move *)
lemma valid_cap_to_pml4_cap:
  "\<lbrakk>valid_cap c s; obj_refs c = {p}; page_map_l4_at p s\<rbrakk> \<Longrightarrow> is_pml4_cap c"
  by (clarsimp simp: valid_cap_def obj_at_def is_obj_defs is_pml4_cap_def
              split: cap.splits option.splits arch_cap.splits if_splits)

lemma set_cap_empty_pde:
  "\<lbrace>empty_pde_at p and cte_at p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>_. empty_pde_at p\<rbrace>"
  apply (simp add: empty_pde_at_def)
  apply (rule hoare_pre)
   apply (wp set_cap_obj_at_other hoare_vcg_ex_lift)
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply (erule conjI)
  apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  done

lemma set_cap_empty_pml4e:
  "\<lbrace>empty_pml4e_at p and cte_at p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>_. empty_pml4e_at p\<rbrace>"
  apply (simp add: empty_pml4e_at_def)
  apply (rule hoare_pre)
   apply (wp set_cap_obj_at_other hoare_vcg_ex_lift)
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply (erule conjI)
  apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  done

lemma set_cap_empty_pdpte:
  "\<lbrace>empty_pdpte_at p and cte_at p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>_. empty_pdpte_at p\<rbrace>"
  apply (simp add: empty_pdpte_at_def)
  apply (rule hoare_pre)
   apply (wp set_cap_obj_at_other hoare_vcg_ex_lift)
  apply clarsimp
  apply (rule exI, rule conjI, assumption)
  apply (erule conjI)
  apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  done

lemma valid_cap_obj_ref_vspace:
  "\<lbrakk> s \<turnstile> cap; s \<turnstile> cap'; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> (is_pt_cap cap \<longrightarrow> is_pt_cap cap')
         \<and> (is_pd_cap cap \<longrightarrow> is_pd_cap cap')
         \<and> (is_pdpt_cap cap \<longrightarrow> is_pdpt_cap cap')
         \<and> (is_pml4_cap cap \<longrightarrow> is_pml4_cap cap')"
  by (auto simp: is_cap_simps valid_cap_def
                 obj_at_def is_ep is_ntfn is_cap_table
                 is_tcb a_type_def
          split: cap.split_asm if_split_asm
                 arch_cap.split_asm option.split_asm)

lemma is_vspace_cap_asid_None_table_ref:
  "is_pt_cap cap \<or> is_pd_cap cap \<or> is_pdpt_cap cap \<or> is_pml4_cap cap
     \<Longrightarrow> ((table_cap_ref cap = None) = (cap_asid cap = None))"
  by (auto simp: is_cap_simps table_cap_ref_def cap_asid_def
          split: option.split_asm)

lemma no_cap_to_obj_with_diff_ref_map:
  "\<lbrakk> caps_of_state s p = Some cap; is_pt_cap cap \<or> is_pd_cap cap \<or> is_pdpt_cap cap \<or> is_pml4_cap cap;
     table_cap_ref cap = None;
     unique_table_caps (caps_of_state s);
     valid_objs s; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid_cap[where p=p])
  apply (frule(1) caps_of_state_valid_cap[where p="(a, b)" for a b])
  apply (drule(1) valid_cap_obj_ref_vspace, simp)
  apply (drule(1) unique_table_capsD[rotated, where cps="caps_of_state s"])
      apply simp
     apply (simp add: is_vspace_cap_asid_None_table_ref)
    apply fastforce
   apply assumption
  apply simp
  done


lemmas store_pte_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pte_caps_of_state]

lemmas store_pde_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pde_caps_of_state]

lemmas store_pdpte_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pdpte_caps_of_state]

crunch store_pml4e
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
    (wp: get_object_wp)

crunch store_pde
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
    (wp: get_object_wp)

crunch store_pdpte
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
    (wp: get_object_wp)

crunch store_pte
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
    (wp: get_object_wp)

lemma mapM_swp_store_pte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pt_bits \<notin> global_refs s) and
    K (pte = InvalidPTE)\<rbrace>
  mapM (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (rule hoare_pre, wp store_pte_invs hoare_vcg_const_Ball_lift
                             hoare_vcg_ex_lift)
    apply (clarsimp simp: pte_ref_pages_def)+
  done

lemma mapM_swp_store_pde_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pd_bits \<notin> global_refs s) and
    K (pde = InvalidPDE)\<rbrace>
  mapM (swp store_pde pde) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (rule hoare_pre, wp store_pde_invs hoare_vcg_const_Ball_lift
                             hoare_vcg_ex_lift)
    apply clarsimp+
  done

lemma mapM_swp_store_pdpte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pdpt_bits \<notin> global_refs s) and
    K (pdpte = InvalidPDPTE)\<rbrace>
  mapM (swp store_pdpte pdpte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (rule hoare_pre, wp store_pdpte_invs hoare_vcg_const_Ball_lift
                             hoare_vcg_ex_lift)
    apply (clarsimp simp: pdpte_ref_pages_def)+
  done

lemma mapM_swp_store_pml4e_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots.
            ucast (sl && mask pml4_bits >> word_size_bits) \<notin> kernel_mapping_slots) and
    (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pml4_bits \<notin> global_refs s) and
    K (pml4e = InvalidPML4E)\<rbrace>
  mapM (swp store_pml4e pml4e) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (rule hoare_pre, wp store_pml4e_invs hoare_vcg_const_Ball_lift
                             hoare_vcg_ex_lift)
    apply (clarsimp simp: pml4e_ref_pages_def)+
  done

lemma vs_refs_pml4I3:
  "\<lbrakk>pml4e_ref (pml4 x) = Some p; x \<notin> kernel_mapping_slots\<rbrakk>
   \<Longrightarrow> (VSRef (ucast x) (Some APageMapL4), p) \<in> vs_refs (ArchObj (PageMapL4 pml4))"
  by (auto simp: pml4e_ref_def vs_refs_def graph_of_def)


lemma mapM_x_swp_store_pte_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl \<in> set slots. sl && ~~ mask pt_bits \<notin> global_refs s) and
    K (pde = InvalidPTE)\<rbrace>
  mapM_x (swp store_pte pde) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pte_invs_unmap)+

lemma mapM_x_swp_store_pde_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl \<in> set slots. sl && ~~ mask pd_bits \<notin> global_refs s) and
    K (pde = InvalidPDE)\<rbrace>
  mapM_x (swp store_pde pde) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pde_invs_unmap)+

lemma mapM_x_swp_store_pdpte_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl \<in> set slots. sl && ~~ mask pdpt_bits \<notin> global_refs s) and
    K (pdpte = InvalidPDPTE)\<rbrace>
  mapM_x (swp store_pdpte pdpte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pdpte_invs_unmap)+

lemma mapM_x_swp_store_pml4e_invs_unmap:
  "\<lbrace>invs and K (\<forall>sl\<in>set slots.
                   ucast (sl && mask pml4_bits >> word_size_bits) \<notin> kernel_mapping_slots) and
    (\<lambda>s. \<forall>sl \<in> set slots. sl && ~~ mask pml4_bits \<notin> global_refs s) and
    K (pml4e = InvalidPML4E)\<rbrace>
  mapM_x (swp store_pml4e pml4e) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pml4e_invs_unmap)+

(* FIXME: move *)
lemma vs_cap_ref_table_cap_ref_None:
  "vs_cap_ref x = None \<Longrightarrow> table_cap_ref x = None"
  by (simp add: vs_cap_ref_def table_cap_ref_simps
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_pg_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> is_pg_cap c = is_pg_cap d"
  by (simp add: cap_master_cap_def is_pg_cap_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_device_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> cap_is_device c = cap_is_device d"
  by (simp add: cap_master_cap_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemmas vs_cap_ref_eq_imp_table_cap_ref_eq' =
       vs_cap_ref_eq_imp_table_cap_ref_eq[OF master_cap_eq_is_pg_cap_eq]

lemma IOPortControlCap_cap_master_cap_eq[simp]:
  "(ArchObjectCap IOPortControlCap = cap_master_cap cap) = (cap = ArchObjectCap IOPortControlCap)"
  by (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)

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
             set_cap_irq_handlers set_cap_valid_arch_caps set_cap_no_new_ioports_arch_valid_arch_state
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
   apply (fastforce simp:is_valid_vtable_root_def vs_cap_ref_def split:arch_cap.splits vmpage_size.splits option.splits)
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
   apply (clarsimp simp: cap_ioports_def cap_master_cap_def split: arch_cap.splits cap.splits)
  apply (rule conjI, solves \<open>clarsimp simp: cap_master_cap_simps\<close>)
  apply (rule conjI, frule master_cap_obj_refs, simp)
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
                            is_cap_simps
                     split: cap.split_asm arch_cap.split_asm
                     dest!: cap_master_cap_eqDs)
     apply (simp add: valid_arch_caps_def)
    apply (simp add: valid_pspace_def)
   apply (erule swap)
   apply (erule vs_cap_ref_eq_imp_table_cap_ref_eq'[symmetric])
   apply (frule table_cap_ref_vs_cap_ref_Some)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp del: imp_disjL)
   apply ((erule disjE |
            ((clarsimp simp: is_cap_simps cap_master_cap_simps
                             cap_asid_def vs_cap_ref_def
                      dest!: cap_master_cap_eqDs
                      split: option.split_asm prod.split_asm),
              drule valid_table_capsD[OF caps_of_state_cteD],
             (clarsimp simp: invs_def valid_state_def valid_arch_caps_def is_cap_simps
                             cap_asid_def)+))+)[1]
  apply (clarsimp simp: is_cap_simps is_pt_cap_def cap_master_cap_simps
                        cap_asid_def vs_cap_ref_def ranI
                 dest!: cap_master_cap_eqDs split: option.split_asm if_split_asm
                 elim!: ranE
                  cong: master_cap_eq_is_device_cap_eq
             | rule conjI)+
  apply (clarsimp dest!: master_cap_eq_is_device_cap_eq)
  done

lemma arch_update_cap_invs_unmap_page:
  "\<lbrace>(\<lambda>s. cte_wp_at (\<lambda>c. (\<forall>p'\<in>obj_refs c. \<forall>ref. vs_cap_ref c = Some ref \<longrightarrow> \<not> (ref \<unrhd> p') s) \<and> is_arch_update cap c) p s)
             and invs and valid_cap cap
             and K (is_pg_cap cap)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps set_cap_no_new_ioports_arch_valid_arch_state
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
  apply (rule conjI[rotated])
   apply (frule(1) cap_refs_in_kernel_windowD)
   apply (simp add: cap_range_def)
  apply (drule unique_table_refs_no_cap_asidE[where S="{p}"])
   apply (simp add: valid_arch_caps_def)
  apply (simp add: no_cap_to_obj_with_diff_ref_def table_cap_ref_def Ball_def)
  done

lemma arch_update_cap_invs_unmap_page_table:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and obj_at (empty_table {}) (obj_ref_of cap)
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>r. vs_cap_ref c = Some r
                                \<longrightarrow> \<not> (r \<unrhd> obj_ref_of cap) s) p s)
             and K (is_pt_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps set_cap_no_new_ioports_arch_valid_arch_state
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
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply clarsimp
  apply fastforce
  done

lemma arch_update_cap_invs_unmap_page_directory:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and obj_at (empty_table {}) (obj_ref_of cap)
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>r. vs_cap_ref c = Some r
                                \<longrightarrow> \<not> (r \<unrhd> obj_ref_of cap) s) p s)
             and K (is_pd_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps set_cap_no_new_ioports_arch_valid_arch_state
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
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply clarsimp
  apply fastforce
  done

lemma arch_update_cap_invs_unmap_pd_pointer_table:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and obj_at (empty_table {}) (obj_ref_of cap)
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>r. vs_cap_ref c = Some r
                                \<longrightarrow> \<not> (r \<unrhd> obj_ref_of cap) s) p s)
             and K (is_pdpt_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps set_cap_no_new_ioports_arch_valid_arch_state
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
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply clarsimp
  apply fastforce
  done

lemma dmo_invalidateTLBEntry_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (invalidateTLBEntry a) \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: invalidateTLBEntry_def dmo_machine_op_lift_invs)

lemma invalidatePageStructureCache_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (invalidateTranslationSingleASID a b)\<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: invalidateTranslationSingleASID_def dmo_machine_op_lift_invs)

lemma flush_table_invs[wp]:
  "\<lbrace>invs\<rbrace> flush_table pm vaddr pt vspace \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wp mapM_x_wp_inv_weak get_cap_wp | wpc | simp add: flush_table_def)+

crunch flush_table
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"
  (wp: mapM_x_wp_inv_weak get_cap_wp simp: crunch_simps)

crunch flush_table
  for cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps)

lemma global_refs_arch_update_eq:
  "\<lbrakk> x64_global_pml4 (f (arch_state s)) = x64_global_pml4 (arch_state s);
     x64_global_pdpts (f (arch_state s)) = x64_global_pdpts (arch_state s);
     x64_global_pds (f (arch_state s)) = x64_global_pds (arch_state s);
     x64_global_pts (f (arch_state s)) = x64_global_pts (arch_state s)\<rbrakk>
       \<Longrightarrow> global_refs (arch_state_update f s) = global_refs s"
  by (simp add: global_refs_def)

crunch flush_table
  for global_refs_inv[wp]: "\<lambda>s. P (global_refs s)"
  (wp: mapM_x_wp_inv_weak crunch_wps simp: crunch_simps global_refs_arch_update_eq)

lemma lookup_pml4_slot_kernel_mappings:
  "\<lbrakk>vptr < pptr_base; canonical_address vptr; is_aligned pml4 pml4_bits\<rbrakk>
    \<Longrightarrow> ucast (lookup_pml4_slot pml4 vptr && mask pml4_bits >> word_size_bits) \<notin> kernel_mapping_slots"
  by (simp add: less_kernel_base_mapping_slots)

lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> p) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
        \<longrightarrow> p \<notin> global_refs s"
  apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply blast
  done

lemma flush_all_invs[wp]:
  "\<lbrace>invs\<rbrace> flush_all vspace asid \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: flush_all_def invalidateASID_def dmo_machine_op_lift_invs)

lemma valid_asid_table_inverse_injD:
  "\<lbrakk>(a,b) \<in> vs_asid_refs (x64_asid_table (arch_state s)); (a,c) \<in> vs_asid_refs (x64_asid_table (arch_state s))\<rbrakk>
  \<Longrightarrow> c = b"
  by (clarsimp simp: vs_asid_refs_def graph_of_def valid_asid_table_def up_ucast_inj_eq)

lemma valid_asid_table_injD:
  "\<lbrakk>(b,a) \<in> vs_asid_refs (x64_asid_table (arch_state s)); (c,a) \<in> vs_asid_refs (x64_asid_table (arch_state s));
    valid_asid_table (x64_asid_table (arch_state s)) s\<rbrakk>
  \<Longrightarrow> c = b"
  apply (clarsimp simp: vs_asid_refs_def graph_of_def valid_asid_table_def up_ucast_inj_eq)
  apply (drule(2) inj_on_domD,fastforce)
  done

lemma update_aobj_not_reachable:
  "\<lbrace>\<lambda>s. lookup_refs (Some (ArchObj aobj)) vs_lookup_pages1_on_heap_obj \<subseteq> lookup_refs (kheap s p) vs_lookup_pages1_on_heap_obj
    \<and> (b, p) \<in> (vs_lookup_pages s) \<and> (VSRef offset (Some ty), ptr) \<notin> vs_refs_pages (ArchObj aobj)
    \<and> valid_asid_table (x64_asid_table (arch_state s)) s\<rbrace>
  set_object p
        (ArchObj aobj)
  \<lbrace>\<lambda>yb s. ([VSRef offset (Some ty)] @ b, ptr) \<notin> vs_lookup_pages s\<rbrace>"
  apply (simp add: set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: vs_lookup_pages_def)
  apply (erule rtranclE[where b = "(VSRef offset (Some ty) # b, ptr)"])
   apply (clarsimp simp: vs_asid_refs_def)
  apply (case_tac y, clarsimp)
  apply (cut_tac s1 = s in lookup_bound_estimate[OF vs_lookup_pages1_is_wellformed_lookup, rotated -1])
     apply (simp add: Image_def)
     apply (rule_tac x = "(aa, baa)" in bexI[rotated])
     apply assumption
    apply (simp add: fun_upd_def[symmetric])
    apply (rule_tac s4 = s in vs_lookup_pages1_is_wellformed_lookup[where s = "s\<lparr>kheap := (kheap s)(p \<mapsto> ArchObj aobj)\<rparr>" for s
                ,simplified])
   apply (clarsimp simp: lookup_refs_def vs_lookup_pages1_on_heap_obj_def vs_refs_pages_def image_def obj_at_def
                         graph_of_def pde_ref_pages_def Image_def split: if_split_asm pde.split_asm)
  apply (clarsimp dest!: vs_lookup_pages1D)
  apply (subgoal_tac "p = pa")
   apply (clarsimp simp: obj_at_def)
  apply (subgoal_tac "a = ab")
   apply simp
   apply (drule valid_asid_table_inverse_injD)
    apply simp
   apply simp
   apply (erule wellformed_lookup.lookupable_is_unique[OF vs_lookup_pages1_is_wellformed_lookup])
   apply simp
  apply (clarsimp simp: vs_lookup_pages_def vs_asid_refs_def
                 dest!: wellformed_lookup.lookup_ref_step[OF vs_lookup_pages1_is_wellformed_lookup] vs_lookup_pages1D)
  done

lemma lookup_refs_pdpt_shrink_strg:
  "ko_at (ArchObj (PDPointerTable pdpt)) ptr s \<longrightarrow>
    lookup_refs (Some (ArchObj (PDPointerTable (pdpt(slot := InvalidPDPTE))))) vs_lookup_pages1_on_heap_obj
      \<subseteq> lookup_refs (kheap s ptr) vs_lookup_pages1_on_heap_obj"
  by (clarsimp simp: obj_at_def lookup_refs_def vs_lookup_pages1_on_heap_obj_def
                        vs_refs_pages_def graph_of_def pdpte_ref_pages_def image_def
                 split: if_splits)

lemma lookup_refs_pd_shrink_strg:
  "ko_at (ArchObj (PageDirectory pd)) ptr s \<longrightarrow>
    lookup_refs (Some (ArchObj (PageDirectory (pd(slot := InvalidPDE))))) vs_lookup_pages1_on_heap_obj
      \<subseteq> lookup_refs (kheap s ptr) vs_lookup_pages1_on_heap_obj"
  by (clarsimp simp: obj_at_def lookup_refs_def vs_lookup_pages1_on_heap_obj_def
                        vs_refs_pages_def graph_of_def pdpte_ref_pages_def image_def
                 split: if_splits)

lemma lookup_refs_pt_shrink_strg:
  "ko_at (ArchObj (PageTable pt)) ptr s \<longrightarrow>
    lookup_refs (Some (ArchObj (PageTable (pt(slot := InvalidPTE))))) vs_lookup_pages1_on_heap_obj
      \<subseteq> lookup_refs (kheap s ptr) vs_lookup_pages1_on_heap_obj"
  by (clarsimp simp: obj_at_def lookup_refs_def vs_lookup_pages1_on_heap_obj_def
                        vs_refs_pages_def graph_of_def pte_ref_pages_def image_def
                 split: if_splits)

crunch flush_all
  for vs_lookup_pages[wp]: "\<lambda>s. P (vs_lookup_pages s)"
crunch flush_all
  for obj_at[wp]: "\<lambda>s. P (obj_at Q q s)"
crunch flush_all
  for valid_arch_state[wp]: "\<lambda>s. valid_arch_state s"

crunch flush_table
  for vs_lookup_pages[wp]: "\<lambda>s. P (vs_lookup_pages s)"
 (wp: mapM_x_wp_inv_weak get_cap_wp simp: flush_table_def)

crunch flush_table
  for obj_at[wp]: "\<lambda>s. P (obj_at Q q s)"
 (wp: mapM_x_wp_inv_weak get_cap_wp simp: flush_table_def)

crunch flush_table
  for valid_arch_state[wp]: "\<lambda>s. valid_arch_state s"
 (wp: mapM_x_wp_inv_weak get_cap_wp simp: flush_table_def)

lemma valid_arch_state_asid_table_strg:
  "valid_arch_state s \<longrightarrow> valid_asid_table (x64_asid_table (arch_state s)) s"
  by (simp add: valid_arch_state_def)

lemma not_in_vs_refs_pages_strg:
  "ptr = ucast ptr' \<longrightarrow> (VSRef ptr (Some APDPointerTable), pd)
    \<notin> vs_refs_pages (ArchObj (PDPointerTable (pda(ptr' := InvalidPDPTE))))"
  by (clarsimp simp: vs_refs_pages_def graph_of_def pdpte_ref_pages_def)

lemma vs_lookup_pages_current_cr3[iff]:
  "(vs_lookup_pages (s\<lparr>arch_state := arch_state s\<lparr>x64_current_cr3 := p\<rparr>\<rparr>)) =
   vs_lookup_pages s"
  by (simp add: vs_lookup_pages_arch_update)

crunch invalidate_page_structure_cache_asid
  for vs_lookup_pages[wp]: "\<lambda>s. P (vs_lookup_pages s)"
  (simp: crunch_simps wp: crunch_wps)

lemma vs_ref_pages_simps:
  "vs_refs_pages (ArchObj aobj) = vs_refs_pages_arch aobj"
  by (simp add: vs_refs_pages_def)

lemma pml4e_ref_pages_SomeD:
  "pml4e_ref_pages c = Some b \<Longrightarrow> \<exists>x21 x22 x23. c = PDPointerTablePML4E x21 x22 x23 \<and> b = ptrFromPAddr x21"
  by (clarsimp simp: pml4e_ref_pages_def split: pml4e.split_asm)

lemma get_pml4_index_bit_def:
  "get_pml4_index vaddr = (vaddr >> 39) && mask 9"
   by (simp add: get_pml4_index_def bit_simps)

lemma get_pdpt_index_bit_def:
  "get_pdpt_index vaddr = (vaddr >> 30) && mask 9"
   by (simp add: get_pdpt_index_def bit_simps)

lemma get_pd_index_bit_def:
  "get_pd_index vaddr = (vaddr >> 21) && mask 9"
   by (simp add: get_pd_index_def bit_simps)

lemma obj_bits_from_vs_refs_pagesD:
  "(VSRef A (Some G), pd) \<in> vs_refs_pages ko \<Longrightarrow> if G = AASIDPool then  obj_bits ko = pageBits else obj_bits ko =  table_size"
  by (clarsimp simp: vs_refs_pages_def split: kernel_object.split_asm arch_kernel_obj.split_asm option.splits
                 dest!: graph_ofD)

lemma vs_lookup_pages1I:
  "\<lbrakk>ko_at ko p s; (r, q) \<in> vs_refs_pages ko\<rbrakk> \<Longrightarrow> ((a,p),r # a, q) \<in> vs_lookup_pages1 s"
  by (clarsimp simp: vs_lookup_pages1_def obj_at_def)

lemma asid_pool_refs_pagesD:
   "pool (asid_low_bits_of asid) = Some pml4
       \<Longrightarrow> (VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), pml4) \<in> vs_refs_pages (ArchObj (ASIDPool pool))"
  by (clarsimp simp: vs_refs_pages_def graph_of_def image_def)

lemma asid_pool_refsD:
   "pool (asid_low_bits_of asid) = Some xa
       \<Longrightarrow> (VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool) ,xa) \<in> vs_refs (ArchObj (ASIDPool pool))"
  by (clarsimp simp: vs_refs_def graph_of_def image_def)

lemma context_vs_lookup_pages_step:
  "\<lbrakk>(ref \<rhd> p) s \<Longrightarrow> ((ref, p), ref', p') \<in> vs_lookup_pages1 s; (ref \<rhd> p) s\<rbrakk>
    \<Longrightarrow> (ref' \<unrhd> p') s"
  apply (rule vs_lookup_pages_step)
   apply (intro vs_lookup_pages_vs_lookupI | simp)+
  done

lemma context_vs_lookup_step:
  "\<lbrakk>(ref \<rhd> p) s \<Longrightarrow> ((ref, p), ref', p') \<in> vs_lookup1 s; (ref \<rhd> p) s\<rbrakk>
    \<Longrightarrow> (ref' \<rhd>  p') s"
  apply (rule vs_lookup_step)
   apply (intro vs_lookup_pages_vs_lookupI | simp)+
  done

lemmas entry_ref_pages_simps = pdpte_ref_pages_def[split_simps pdpte.split] pte_ref_pages_def[split_simps pte.split]
                   pml4e_ref_pages_def[split_simps pml4e.split]
                   pde_ref_pages_def[split_simps pde.split]

method rewrite_lookup_when_aligned
   = (match premises in M: "P (lookup_pml4_slot p _)" and L: "pspace_aligned s"
            and KS : "kheap s p = Some _" for s p P \<Rightarrow> \<open>rule revcut_rl[OF pspace_alignedD[OF KS L]]\<close>
      , clarsimp simp: pml4_bits_def pml4_shifting[folded lookup_pml4_slot_def[unfolded Let_def], unfolded pml4_bits_def])
   | (match premises in M: "P (p + _)" and L: "pspace_aligned s"
            and TP : "typ_at (AArch APDPointerTable) p s" for s p P \<Rightarrow> \<open>rule revcut_rl[OF is_aligned_pdpt[OF TP L]]\<close>
      , clarsimp simp: pdpt_bits_def pdpt_shifting[folded lookup_pdpt_slot_def[unfolded Let_def], unfolded pdpt_bits_def])
   | (match conclusion in "P ((p::64 word) + _ && ~~ mask pdpt_bits)" for p P \<Rightarrow> \<open>(match premises in L: "pspace_aligned s"
            and TP : "typ_at (AArch APDPointerTable) p s" for s  \<Rightarrow> \<open>rule revcut_rl[OF is_aligned_pdpt[OF TP L]]\<close>
      , clarsimp simp: pdpt_bits_def pdpt_shifting[folded lookup_pdpt_slot_def[unfolded Let_def], unfolded pdpt_bits_def])\<close>)
   | (match premises in M: "P (p + _)" and L: "pspace_aligned s"
            and TP : "typ_at (AArch APageDirectory) p s" for s p P \<Rightarrow> \<open>rule revcut_rl[OF is_aligned_pd[OF TP L]]\<close>
      , clarsimp simp: pd_bits_def pd_shifting[folded lookup_pd_slot_def[unfolded Let_def], unfolded pd_bits_def])
   | (match conclusion in "P ((p::64 word) + _ && ~~ mask pd_bits)" for p P \<Rightarrow> \<open>(match premises in L: "pspace_aligned s"
            and TP : "typ_at (AArch APageDirectory) p s" for s \<Rightarrow> \<open>rule revcut_rl[OF is_aligned_pd[OF TP L]]\<close>
      , clarsimp simp: pd_bits_def pd_shifting[folded lookup_pd_slot_def[unfolded Let_def], unfolded pd_bits_def])\<close>)

   | (match premises in M: "P (p + _)" and L: "pspace_aligned s"
            and TP : "typ_at (AArch APageTable) p s" for s p P \<Rightarrow> \<open>rule revcut_rl[OF is_aligned_pt[OF TP L]]\<close>
      , clarsimp simp: pt_bits_def pt_shifting[folded lookup_pt_slot_def[unfolded Let_def], unfolded pt_bits_def])
   | (match conclusion in "P ((p::64 word) + _ && ~~ mask pt_bits)" for p P \<Rightarrow> \<open>(match premises in L: "pspace_aligned s"
            and TP : "typ_at (AArch APageTable) p s" for s  \<Rightarrow> \<open>rule revcut_rl[OF is_aligned_pt[OF TP L]]\<close>
      , clarsimp simp: pt_bits_def pt_shifting[folded lookup_pt_slot_def[unfolded Let_def], unfolded pt_bits_def])\<close>)

   | (match premises in M: "P (lookup_pml4_slot p _)" and L: "pspace_aligned s"
            and TP : "typ_at (AArch APageMapL4) p s" for s p P \<Rightarrow> \<open>rule revcut_rl[OF is_aligned_pml4[OF TP L]]\<close>
      , clarsimp simp: pml4_bits_def pml4_shifting[folded lookup_pml4_slot_def[unfolded Let_def], unfolded pml4_bits_def])

lemma valid_vspace_objs_asidpoolD:
  "\<lbrakk>valid_vspace_obj (ASIDPool pool) s; pool (asid_low_bits_of asid) = Some x\<rbrakk>  \<Longrightarrow> typ_at (AArch APageMapL4) x s"
  by fastforce

lemma vs_refs_get_pml4_index:
  "\<lbrakk>pm (ucast (get_pml4_index vaddr)) = PDPointerTablePML4E a b c; vaddr < pptr_base; canonical_address vaddr\<rbrakk>
  \<Longrightarrow> (VSRef (get_pml4_index vaddr) (Some APageMapL4), ptrFromPAddr a) \<in> vs_refs (ArchObj (PageMapL4 pm))"
  apply (clarsimp simp: vs_refs_def graph_of_def image_def)
  apply (drule(1) kernel_base_kernel_mapping_slots)
  apply (intro exI conjI)
  apply assumption
  apply (clarsimp simp: pml4e_ref_def get_pml4_index_def pml4_shift_bits_def bit_simps)
  apply word_bitwise
  apply (clarsimp simp: mask_def)
  done

lemma vs_refs_pages_pdpt:
  "\<lbrakk>pdpte_ref_pages (pdpta a) = Some pd\<rbrakk> \<Longrightarrow> (VSRef (ucast a) (Some APDPointerTable),pd) \<in> vs_refs_pages (ArchObj (PDPointerTable pdpta))"
  by (clarsimp simp: vs_refs_pages_def image_def graph_of_def)

lemma vs_refs_get_pdpt_index:
  "\<lbrakk>pdpt (ucast (get_pdpt_index vaddr)) = PageDirectoryPDPTE a b c\<rbrakk>
  \<Longrightarrow> (VSRef (get_pdpt_index vaddr) (Some APDPointerTable), ptrFromPAddr a) \<in> vs_refs (ArchObj (PDPointerTable pdpt))"
  apply (clarsimp simp: vs_refs_def graph_of_def image_def)
  apply (rule_tac x = "ucast (get_pdpt_index vaddr)" in exI)
   apply (clarsimp simp: pdpte_ref_def)
  apply (clarsimp simp: get_pdpt_index_def bit_simps)
  apply word_bitwise
  apply (clarsimp simp: mask_def)
  done

lemma vs_refs_get_pd_index:
  "\<lbrakk>pd (ucast (get_pd_index vaddr)) = PageTablePDE pt a b\<rbrakk>
  \<Longrightarrow> (VSRef (get_pd_index vaddr) (Some APageDirectory), (ptrFromPAddr pt)) \<in> vs_refs (ArchObj (PageDirectory pd))"
  apply (clarsimp simp: vs_refs_def graph_of_def image_def)
  apply (rule_tac x = "(ucast (get_pd_index vaddr))" in exI)
  apply (clarsimp simp: pdpte_ref_def)
  apply (clarsimp simp: get_pd_index_def bit_simps)
  apply word_bitwise
  apply (clarsimp simp: mask_def)
  done

lemma valid_vspace_objs_pml4D:
  "\<lbrakk>valid_vspace_obj (PageMapL4 pm) s; pm (ucast (get_pml4_index vaddr)) = PDPointerTablePML4E a b c;
     vaddr < pptr_base; canonical_address vaddr\<rbrakk>  \<Longrightarrow> typ_at (AArch APDPointerTable) (ptrFromPAddr a) s"
  apply (clarsimp)
  apply (drule bspec)
    apply (drule kernel_base_kernel_mapping_slots, simp+)
  done

lemma valid_vspace_objs_pdptD:
  "\<lbrakk>valid_vspace_obj (PDPointerTable pdpt) s; pdpt x = PageDirectoryPDPTE a b c\<rbrakk>
    \<Longrightarrow> typ_at (AArch APageDirectory) (ptrFromPAddr a) s"
  apply (clarsimp)
  apply (drule_tac x = x in  spec)
    apply fastforce
  done

lemma valid_vspace_objs_pdD:
  "\<lbrakk>valid_vspace_obj (PageDirectory pd) s; pd x = PageTablePDE a b c\<rbrakk>
    \<Longrightarrow> typ_at (AArch APageTable) (ptrFromPAddr a) s"
  apply (clarsimp)
  apply (drule_tac x = x in  spec)
    apply fastforce
  done

lemma valid_vspace_objs_largePage:
  "\<lbrakk>valid_vspace_obj (PageDirectory pd) s; pd x = LargePagePDE a b c; ko_at ko (ptrFromPAddr a) s\<rbrakk>
    \<Longrightarrow> vs_refs_pages ko = {}"
  apply (clarsimp)
  apply (drule_tac x = x in  spec)
    apply clarsimp
  apply (auto simp: data_at_def obj_at_def vs_refs_pages_def)
  done

lemma valid_vspace_objs_hugePage:
  "\<lbrakk>valid_vspace_obj (PDPointerTable pdpt) s; pdpt x = HugePagePDPTE a b c; ko_at ko (ptrFromPAddr a) s\<rbrakk>
    \<Longrightarrow> vs_refs_pages ko = {}"
  apply (clarsimp)
  apply (drule_tac x = x in  spec)
    apply clarsimp
  apply (auto simp: data_at_def obj_at_def vs_refs_pages_def)
  done

lemma ucast_ucast_get_index_simps[simp]:
  "(ucast (ucast (get_pml4_index vaddr):: 9 word)) = get_pml4_index vaddr"
  "(ucast (ucast (get_pdpt_index vaddr):: 9 word)) = get_pdpt_index vaddr"
  "(ucast (ucast (get_pd_index vaddr):: 9 word)) = get_pd_index vaddr"
  "(ucast (ucast (get_pt_index vaddr):: 9 word)) = get_pt_index vaddr"
  by (auto simp: get_pdpt_index_def get_pd_index_def get_pt_index_def get_pml4_index_def bit_simps mask_def ucast_ucast_mask)


method extract_vs_lookup =
  (match premises in at[thin]: "x64_asid_table (arch_state s) a = Some p" for s a p \<Rightarrow> \<open>rule revcut_rl[OF vs_lookup_atI[OF at]]\<close>)
  | (match premises in path[thin]: "(_ \<rhd> p) s"
         and ko_at: "ko_at (ArchObj (ASIDPool pool)) p s"
         and pool: "pool _ = Some _"
         and vs : "valid_vspace_objs s"  for pool p s
      \<Rightarrow> \<open>cut_tac vs_lookup_step[OF path vs_lookup1I[OF ko_at asid_pool_refsD refl], OF pool]
          , cut_tac valid_vspace_objs_asidpoolD[OF valid_vspace_objsD,OF path ko_at vs pool]\<close>)
  | (match premises in path[thin]: "(_ \<rhd> p) s"
         and ko_at: "ko_at (ArchObj (PageMapL4 pm)) p s"
         and pm:  "pm _ = _"
         and vaddr: "vaddr < pptr_base"
         and cano: "canonical_address vaddr"
         and vs : "valid_vspace_objs s"  for pm p s vaddr
      \<Rightarrow> \<open>cut_tac vs_lookup_step[OF path vs_lookup1I[OF ko_at vs_refs_get_pml4_index refl],OF pm vaddr cano]
          , cut_tac valid_vspace_objs_pml4D[OF valid_vspace_objsD,OF path ko_at vs pm vaddr cano]\<close>)
  | (match premises in path[thin]: "(_ \<rhd> p) s"
         and ko_at: "ko_at (ArchObj (PDPointerTable pdpt)) p s"
         and pdpt:  "pdpt (ucast (_::word64)) = PageDirectoryPDPTE _ _ _"
         and vs : "valid_vspace_objs s"  for pdpt p s
      \<Rightarrow> \<open>cut_tac vs_lookup_step[OF path vs_lookup1I[OF ko_at vs_refs_get_pdpt_index refl],OF pdpt]
          , cut_tac valid_vspace_objs_pdptD[OF valid_vspace_objsD,OF path ko_at vs pdpt]\<close>)
  | (match premises in path[thin]: "(_ \<rhd> p) s"
         and ko_at: "ko_at (ArchObj (PageDirectory pd)) p s"
         and pd:  "pd (ucast (_::word64)) = PageTablePDE _ _ _"
         and vs : "valid_vspace_objs s"  for pd p s
      \<Rightarrow> \<open>cut_tac vs_lookup_step[OF path vs_lookup1I[OF ko_at vs_refs_get_pd_index refl],OF pd]
          , cut_tac valid_vspace_objs_pdD[OF valid_vspace_objsD,OF path ko_at vs pd]\<close>)

lemma in_vs_asid_refsD:
  "(a,b)\<in> vs_asid_refs table \<Longrightarrow> \<exists>p. table p = Some b \<and> a = [VSRef (ucast p) None]"
  by (fastforce simp: vs_asid_refs_def dest!: graph_ofD)

lemma lookup_refs_pml4_shrink_strg:
  "ko_at (ArchObj (PageMapL4 pm)) ptr s \<longrightarrow>
    lookup_refs (Some (ArchObj (PageMapL4 (pm(slot := InvalidPML4E))))) vs_lookup_pages1_on_heap_obj
      \<subseteq> lookup_refs (kheap s ptr) vs_lookup_pages1_on_heap_obj"
  by (fastforce simp: obj_at_def lookup_refs_def vs_lookup_pages1_on_heap_obj_def
                        vs_refs_pages_def graph_of_def pml4e_ref_pages_def image_def
                 split: if_splits)

lemma vs_refs_pages_pml4:
  "\<lbrakk>pml4e_ref_pages (pml4a a) = Some pdpt; a \<notin> kernel_mapping_slots\<rbrakk> \<Longrightarrow> (VSRef (ucast a) (Some APageMapL4),pdpt) \<in> vs_refs_pages (ArchObj (PageMapL4 pml4a))"
  by (clarsimp simp: vs_refs_pages_def image_def graph_of_def)

lemma lookup_pml4_slot_mask:
  "is_aligned a table_size \<Longrightarrow> lookup_pml4_slot a b && mask pml4_bits = (get_pml4_index b << word_size_bits)"
  apply (simp add: lookup_pml4_slot_def is_aligned_mask bit_simps)
  apply (simp add: mask_inner_mask[symmetric])
  apply (simp add: get_pml4_index_def bit_simps mask_def)
  apply (word_bitwise)
  done

lemma unmap_pdpt_vs_lookup_pages_pre:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and typ_at (AArch APDPointerTable) pdpt
     and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
   unmap_pdpt asid vaddr pdpt
   \<lbrace>\<lambda>r s. (the (vs_cap_ref (ArchObjectCap (PDPointerTableCap pdpt (Some (asid,vaddr))))),pdpt) \<notin> vs_lookup_pages s\<rbrace>"
  proof -
  note ref_simps[simp] = vs_cap_ref_simps vs_ref_pages_simps
  note ucast_simps[simp] = up_ucast_inj_eq ucast_up_ucast mask_asid_low_bits_ucast_ucast ucast_ucast_id
  show ?thesis
  apply (clarsimp simp: unmap_pdpt_def vs_cap_ref_simps store_pml4e_def set_arch_obj_simps)
  apply wp
        apply (rule update_aobj_not_reachable[where b = "[b,c]" for b c,simplified])
       apply (strengthen lookup_refs_pml4_shrink_strg valid_arch_state_asid_table_strg not_in_vs_refs_pages_strg
              | clarsimp)+
       apply (strengthen | wp hoare_vcg_imp_lift hoare_vcg_all_lift  | clarsimp simp: conj_ac)+
     apply (wpc | wp)+
    apply (wp get_pml4e_wp)
   apply (simp add: find_vspace_for_asid_def | wp | wpc)+
   apply (wpc | wp get_pdpte_wp get_pml4e_wp assertE_wp | clarsimp simp: lookup_pml4_slot_def find_vspace_for_asid_def)
  apply clarsimp
  apply (case_tac "([VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
                             VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), VSRef (ucast (asid_high_bits_of asid)) None],
                            pdpt)
                           \<notin> vs_lookup_pages s")
   apply (clarsimp simp: graph_of_def split: if_splits)
   apply (extract_vs_lookup)
   apply (extract_vs_lookup)
   apply (rewrite_lookup_when_aligned)
   apply (clarsimp simp: get_pml4_index_def bit_simps vs_lookup_pages_vs_lookupI lookup_pml4_slot_def obj_at_def pml4e_ref_pages_def
                 split: if_splits)
   apply (drule_tac a2=a in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI vs_lookup_pages1I[OF _ vs_refs_pages_pml4 ]])
      apply (simp add: obj_at_def)
     apply (simp add: pml4e_ref_pages_def)
    apply assumption
   apply simp
  apply (clarsimp split:if_splits simp: vs_lookup_pages_def graph_of_def dest!: in_vs_asid_refsD)
  apply (erule wellformed_lookup.lookupE[OF vs_lookup_pages1_is_wellformed_lookup], simp)
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD simp: lookup_leaf_def)
  apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                         wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                   simp: obj_at_def)
  apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def)
  apply (extract_vs_lookup)+
  apply (rewrite_lookup_when_aligned)
  apply (clarsimp simp: obj_at_def pml4e_ref_pages_def dest!: graph_ofD split: if_splits pml4e.split_asm)
  apply (fold ko_at_def2 vs_asid_refs_def)
  apply (drule eq_ucast_ucast_eq[rotated], simp)
  apply clarsimp
  apply (frule vs_lookup_pages_vs_lookupI)
  apply (clarsimp simp: obj_at_def pdpte_ref_pages_def image_def vs_lookup_pages_def lookup_pml4_slot_mask triple_shift_fun
                        pml4e_ref_pages_def
                 dest!: graph_ofD split: if_splits pdpte.split_asm)
  done
qed

lemma unmap_pdpt_vs_lookup_pages:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and typ_at (AArch APDPointerTable) pd and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
    unmap_pdpt asid vaddr pd
  \<lbrace>\<lambda>r s. ([VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
                       VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), VSRef (ucast (asid_high_bits_of asid)) None],
        pd)
       \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_pdpt_vs_lookup_pages_pre])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done


lemma unmap_pt_vs_lookup_pages_pre:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state
        and typ_at (AArch APageTable) pt
        and K (vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
    unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>r s. (the (vs_cap_ref (ArchObjectCap (PageTableCap pt (Some (asid,vaddr))))),pt) \<notin> vs_lookup_pages s\<rbrace>"
  proof -
  note ref_simps[simp] = vs_cap_ref_simps vs_ref_pages_simps
  note ucast_simps[simp] = up_ucast_inj_eq ucast_up_ucast mask_asid_low_bits_ucast_ucast ucast_ucast_id
  show ?thesis
    apply (clarsimp simp: unmap_page_table_def)
    apply wp
      apply (clarsimp simp: unmap_pd_def store_pde_def set_arch_obj_simps)
    apply wp
          apply (rule update_aobj_not_reachable[where b = "[b,c,d,e]" for b c d e,simplified])
    apply (strengthen lookup_refs_pd_shrink_strg valid_arch_state_asid_table_strg not_in_vs_refs_pages_strg
           | clarsimp )+
        apply (strengthen | wp hoare_vcg_imp_lift hoare_vcg_all_lift  | clarsimp)+
      apply (wpc | wp get_pdpte_wp get_pml4e_wp get_pde_wp)+
    apply ((simp add: lookup_pdpt_slot_def lookup_pd_slot_def | wp get_pdpte_wp get_pml4e_wp | wpc)+)[1]
   apply (simp add: find_vspace_for_asid_def | wp | wpc)+
     apply (wpc | wp get_pdpte_wp get_pml4e_wp assertE_wp | clarsimp simp: lookup_pdpt_slot_def find_vspace_for_asid_def)
  apply clarsimp
  apply (case_tac "([VSRef ((vaddr >> 21) && mask 9) (Some APageDirectory),
                     VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
                     VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None], pt)  \<notin> vs_lookup_pages s")
   apply (clarsimp simp: graph_of_def split: if_splits)
   apply (extract_vs_lookup)+
   apply (rewrite_lookup_when_aligned)+
   apply (extract_vs_lookup)+
   apply (rewrite_lookup_when_aligned)+
   apply (extract_vs_lookup, rewrite_lookup_when_aligned)
   apply (clarsimp simp: get_pml4_index_def bit_simps vs_lookup_pages_vs_lookupI obj_at_def get_pdpt_index_def
                  split: if_splits)
   apply (drule vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI vs_lookup_pages1I])
     apply (simp add: obj_at_def)
    apply (erule subsetD[OF vs_refs_pages_subset vs_refs_get_pd_index])
   apply (clarsimp simp: get_pd_index_def bit_simps vs_lookup_pages_def Image_def ptrFormPAddr_addFromPPtr)
  apply (clarsimp split:if_splits simp: vs_lookup_pages_def graph_of_def dest!: in_vs_asid_refsD)
  apply (erule wellformed_lookup.lookupE[OF vs_lookup_pages1_is_wellformed_lookup], simp)
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD simp: lookup_leaf_def)
  apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
  apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
  apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                         wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                   simp: obj_at_def)
  apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
  apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
  apply (clarsimp simp: obj_at_def pml4e_ref_pages_def dest!: graph_ofD split: if_splits pml4e.split_asm)
  apply (fold ko_at_def2 vs_asid_refs_def)
  apply (drule eq_ucast_ucast_eq[rotated], simp)
  apply clarsimp
  apply (extract_vs_lookup, rewrite_lookup_when_aligned)+
  apply (clarsimp simp: obj_at_def pdpte_ref_pages_def image_def vs_lookup_pages_def
                 dest!: graph_ofD split: if_splits pdpte.split_asm)
  apply (fold ko_at_def2 vs_asid_refs_def)
  apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
  apply clarsimp
  apply (extract_vs_lookup, rewrite_lookup_when_aligned)+
  apply (clarsimp simp: obj_at_def pde_ref_pages_def image_def vs_lookup_pages_def
                 dest!: graph_ofD split: if_splits pde.split_asm)
   apply (frule vs_lookup_pages_vs_lookupI)
   apply (clarsimp simp: obj_at_def pdpte_ref_pages_def image_def vs_lookup_pages_def
                 dest!: graph_ofD split: if_splits pdpte.split_asm)
   apply (clarsimp dest!: in_vs_asid_refsD wellformed_lookup.lookup_ref_step[OF vs_lookup_pages1_is_wellformed_lookup])
   apply (drule valid_vspace_objsD)
     apply (simp add: ko_at_def2)
    apply simp
   apply clarsimp
   apply (drule_tac x = a in spec)
   apply (clarsimp simp: data_at_def obj_at_def a_type_simps)
  apply (clarsimp dest!: in_vs_asid_refsD wellformed_lookup.lookup_ref_step[OF vs_lookup_pages1_is_wellformed_lookup])
  apply (drule valid_vspace_objsD)
    apply (simp add: ko_at_def2)
   apply simp
  apply clarsimp
  apply (drule_tac x = a in spec)
  apply (clarsimp simp: data_at_def obj_at_def a_type_simps vs_refs_pages_def
                 split: kernel_object.split_asm arch_kernel_obj.split_asm)
  done
qed

lemma get_index_neq:
  "((a :: 9 word) \<noteq> ucast (get_pt_index vaddr)) \<Longrightarrow> ((get_pt_index vaddr) \<noteq> ucast a)"
  "((a :: 9 word) \<noteq> ucast (get_pdpt_index vaddr)) \<Longrightarrow> ((get_pdpt_index vaddr) \<noteq> ucast a)"
  by (auto simp: get_pt_index_def bit_simps up_ucast_inj_eq ucast_up_ucast ucast_ucast_id)

lemma unmap_page_vs_lookup_pages_pre:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state
     and data_at sz pg and K (vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
    unmap_page sz asid vaddr pg
   \<lbrace>\<lambda>r s. (the (vs_cap_ref (ArchObjectCap (PageCap dev pg R typ sz (Some (asid,vaddr))))),pg) \<notin> vs_lookup_pages s\<rbrace>"
  proof -
  note ref_simps[simp] = vs_cap_ref_simps vs_ref_pages_simps
  note ucast_simps[simp] = up_ucast_inj_eq ucast_up_ucast mask_asid_low_bits_ucast_ucast ucast_ucast_id get_index_neq
  note [wp_comb del] = hoare_vcg_conj_lift
  note [wp_comb] = hoare_post_comb_imp_conj hoare_weaken_pre hoare_vcg_conj_lift
    hoare_weaken_preE[OF valid_validE]
    hoare_weaken_preE_R[OF valid_validE_R]
    hoare_weaken_preE
    hoare_weaken_preE_R

  show ?thesis
    apply (clarsimp simp: unmap_page_def vs_cap_ref_simps)
    apply (wp | wpc)+
(* X64SmallPage *)
      apply (clarsimp simp: store_pte_def set_arch_obj_simps)
    apply wp
          apply (rule update_aobj_not_reachable[where b = "[b,c,d,e,f]" for b c d e f,simplified])
    apply (strengthen lookup_refs_pt_shrink_strg valid_arch_state_asid_table_strg not_in_vs_refs_pages_strg
           | clarsimp)+
       apply (wpsimp simp: unlessE_def split_del: if_split)+
      apply (wpc | wp get_pte_wp get_pml4e_wp get_pde_wp get_pdpte_wp)+
    apply ((simp add: lookup_pt_slot_def lookup_pd_slot_def lookup_pdpt_slot_def | wp get_pdpte_wp get_pml4e_wp get_pde_wp | wpc)+)[1]
(* X64LargePage *)
      apply (clarsimp simp: store_pde_def set_arch_obj_simps)
    apply wp
          apply (rule update_aobj_not_reachable[where b = "[b,c,d,e]" for b c d e,simplified])
    apply (strengthen lookup_refs_pd_shrink_strg valid_arch_state_asid_table_strg not_in_vs_refs_pages_strg
           | clarsimp )+
        apply (strengthen | wp hoare_vcg_imp_lift hoare_vcg_all_lift unlessE_wp  | clarsimp simp: conj_comms)+
      apply (wpc | wp get_pte_wp get_pml4e_wp get_pde_wp get_pdpte_wp)+
    apply ((simp add: lookup_pt_slot_def lookup_pd_slot_def lookup_pdpt_slot_def | wp get_pdpte_wp get_pml4e_wp get_pde_wp | wpc)+)[1]
(* X64HugePage *)
 apply (clarsimp simp: store_pdpte_def set_arch_obj_simps)
    apply wp
          apply (rule update_aobj_not_reachable[where b = "[b,c,d]" for b c d,simplified])
    apply (strengthen lookup_refs_pdpt_shrink_strg valid_arch_state_asid_table_strg not_in_vs_refs_pages_strg
           | clarsimp )+
        apply (strengthen | wp hoare_vcg_imp_lift hoare_vcg_all_lift unlessE_wp  | clarsimp simp: conj_ac)+
      apply (wpc | wp get_pte_wp get_pml4e_wp get_pde_wp get_pdpte_wp)+
    apply ((simp add: lookup_pt_slot_def lookup_pd_slot_def lookup_pdpt_slot_def | wp get_pdpte_wp get_pml4e_wp get_pde_wp | wpc)+)[1]
   apply (simp add: find_vspace_for_asid_def | wp | wpc)+
     apply (wpc | wp get_pdpte_wp get_pml4e_wp assertE_wp | clarsimp simp: lookup_pdpt_slot_def find_vspace_for_asid_def)
  apply clarsimp
  apply (case_tac "(the (vs_cap_ref (ArchObjectCap (PageCap dev pg R typ sz (Some (asid, vaddr))))), pg)
                       \<notin> vs_lookup_pages s")
   apply (clarsimp simp: graph_of_def vs_cap_ref_def split: if_splits vmpage_size.splits)
     apply (clarsimp simp: image_def pte_ref_pages_def[split_simps pte.split])
     apply (fold get_pt_index_def[simplified bit_simps])
     apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
     apply (clarsimp simp: obj_at_def bit_simps get_pd_index_def get_pml4_index_def get_pdpt_index_def
                    dest!: vs_lookup_pages_vs_lookupI)
    apply (clarsimp simp: image_def pde_ref_pages_def[split_simps pte.split])
    apply (fold get_pd_index_def[simplified bit_simps])
    apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
    apply (clarsimp simp: obj_at_def bit_simps get_pd_index_def get_pml4_index_def get_pdpt_index_def
                    dest!: vs_lookup_pages_vs_lookupI)
   apply (clarsimp simp: image_def pdpte_ref_pages_def[split_simps pte.split] split: pdpte.splits)
   apply (fold get_pdpt_index_def[simplified bit_simps])
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
   apply (clarsimp simp: obj_at_def bit_simps get_pd_index_def ucast_ucast_mask
                         get_pml4_index_def get_pdpt_index_def
                   dest!: vs_lookup_pages_vs_lookupI
                   split: pdpte.split_asm)
  apply (clarsimp split:if_splits simp: vs_lookup_pages_def graph_of_def dest!: in_vs_asid_refsD)
  apply (erule wellformed_lookup.lookupE[OF vs_lookup_pages1_is_wellformed_lookup], simp)
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD simp: lookup_leaf_def vs_cap_ref_def split: vmpage_size.splits)+
    apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
    apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                           wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                     simp: obj_at_def)
    apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
    apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
    apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
    apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                    simp:  obj_at_def pml4e_ref_pages_def
                    split: if_split_asm pml4e.split_asm)
    apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
    apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
    apply clarsimp
    apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
    apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
    apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                    simp:  obj_at_def pdpte_ref_pages_def
                    split: if_split_asm pdpte.split_asm)
     apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
     apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
     apply clarsimp
     apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
     apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
     apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                     simp:  obj_at_def pde_ref_pages_def
                     split: if_split_asm pde.split_asm)
      apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
      apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
      apply clarsimp
      apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
      apply (clarsimp simp: obj_at_def image_def pte_ref_pages_def[split_simps pte.split]
                     dest!: graph_ofD wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                     split: if_splits)
      apply (strengthen vs_lookup_pages_vs_lookupI[mk_strg, simplified vs_lookup_pages_def])
      apply (clarsimp simp: check_mapping_pptr_def get_pd_index_def get_pml4_index_def get_pdpt_index_def
                            ucast_ucast_mask bit_simps obj_at_def
                     dest!: vs_lookup_pages1D graph_ofD split: pte.split_asm)
       apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
       apply (clarsimp simp: get_pt_index_def bit_simps pte_ref_pages_def)
      apply (clarsimp simp: get_pt_index_def bit_simps
                     dest!: graph_ofD split: pte.split_asm)
      apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
      apply (clarsimp simp: pte_ref_pages_def)
     apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
     apply (clarsimp simp: check_mapping_pptr_def get_pd_index_def get_pml4_index_def get_pdpt_index_def
                           ucast_ucast_mask bit_simps obj_at_def
                    dest!: vs_lookup_pages1D graph_ofD wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                    split: pte.split_asm)
     apply (drule valid_vspace_objs_largePage[OF valid_vspace_objsD])
       apply (simp add: ko_at_def2)+
    apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
    apply (clarsimp simp: check_mapping_pptr_def get_pd_index_def get_pml4_index_def get_pdpt_index_def
                          ucast_ucast_mask bit_simps obj_at_def
                   dest!: vs_lookup_pages1D graph_ofD wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                          wellformed_lookup.lookup_rtrancl_stepsD[where r = "[a]" for a, simplified,OF vs_lookup_pages1_is_wellformed_lookup]
                   split: pte.split_asm)
    apply (drule valid_vspace_objs_hugePage[OF valid_vspace_objsD])
      apply (simp add: ko_at_def2)+
   apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
   apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                          wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                    simp: obj_at_def)
   apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
   apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
   apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                  simp:  obj_at_def pml4e_ref_pages_def
                  split: if_split_asm pml4e.split_asm)
   apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
   apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
   apply clarsimp
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
   apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
   apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                    simp:  obj_at_def pdpte_ref_pages_def
                   split: if_split_asm pdpte.split_asm)
    apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
    apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
    apply clarsimp
      apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
      apply (clarsimp simp: obj_at_def image_def pte_ref_pages_def[split_simps pte.split]
                     dest!: graph_ofD wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                     split: if_splits)
     apply (strengthen vs_lookup_pages_vs_lookupI[mk_strg, simplified vs_lookup_pages_def])
     apply (clarsimp simp: check_mapping_pptr_def get_pd_index_def get_pml4_index_def get_pdpt_index_def
                            ucast_ucast_mask obj_at_def bit_simps
                     dest!: vs_lookup_pages1D graph_ofD split: pde.split_asm)
     apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def ptTranslationBits_def)
     apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
     apply (clarsimp simp: pde_ref_pages_def split: pde.split_asm)
     apply (extract_vs_lookup)+
     apply (clarsimp simp: obj_at_def data_at_def a_type_simps)
    apply (clarsimp simp: mask_def)
   apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                          wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                    simp: obj_at_def)
   apply (drule valid_vspace_objs_hugePage[OF valid_vspace_objsD])
     apply (simp add: ko_at_def2)+
   apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
   apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                          wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                    simp: obj_at_def)
   apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
   apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
   apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                  simp:  obj_at_def pml4e_ref_pages_def
                  split: if_split_asm pml4e.split_asm)
   apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def get_pd_index_bit_def)
   apply (drule eq_ucast_ucast_eq[rotated,THEN sym], simp)
   apply clarsimp
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)+
   apply (strengthen vs_lookup_pages_vs_lookupI[mk_strg, simplified vs_lookup_pages_def])
   apply (clarsimp simp: check_mapping_pptr_def obj_at_def image_def pdpte_ref_pages_def[split_simps pdpte.split]
                  split: pdpte.splits)
   apply (clarsimp simp: check_mapping_pptr_def get_pd_index_def get_pml4_index_def get_pdpt_index_def
                         ucast_ucast_mask obj_at_def image_def bit_simps pdpte_ref_pages_def[split_simps pdpte.split]
                  dest!: vs_lookup_pages1D graph_ofD split: pdpte.splits)
  apply (intro conjI impI)
    apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                            wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                      simp: obj_at_def pdpte_ref_pages_def[split_simps pdpte.split])
   apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                          wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                    simp: obj_at_def pdpte_ref_pages_def[split_simps pdpte.split])
   apply (drule valid_vspace_objs_pdptD[OF valid_vspace_objsD])
     apply (simp add: ko_at_def2)+
   apply (clarsimp simp: obj_at_def data_at_def a_type_simps)
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                         wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                   simp: obj_at_def pdpte_ref_pages_def[split_simps pdpte.split])
  done
qed

(* FIXME x64: unmap_pdpt_vs_lookup_pages_pre might also needed here*)
lemma unmap_pd_vs_lookup_pages_pre:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and typ_at (AArch APageDirectory) pd and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
   unmap_pd asid vaddr pd
   \<lbrace>\<lambda>r s. (the (vs_cap_ref (ArchObjectCap (PageDirectoryCap pd (Some (asid,vaddr))))),pd) \<notin> vs_lookup_pages s\<rbrace>"
  proof -
  note ref_simps[simp] = vs_cap_ref_simps vs_ref_pages_simps
  note ucast_simps[simp] = up_ucast_inj_eq ucast_up_ucast mask_asid_low_bits_ucast_ucast ucast_ucast_id
  show ?thesis
  apply (clarsimp simp: unmap_pd_def store_pdpte_def set_arch_obj_simps)
  apply wp
        apply (rule update_aobj_not_reachable[where b = "[b,c,d]" for b c d,simplified])
  apply (strengthen lookup_refs_pdpt_shrink_strg valid_arch_state_asid_table_strg not_in_vs_refs_pages_strg
         | clarsimp )+
        apply (strengthen | wp hoare_vcg_imp_lift hoare_vcg_all_lift  | clarsimp)+
      apply (wpc | wp get_pdpte_wp get_pml4e_wp )+
    apply ((simp add: lookup_pdpt_slot_def | wp get_pml4e_wp | wpc)+)[1]
   apply (simp add: find_vspace_for_asid_def | wp | wpc)+
     apply (wpc | wp get_pdpte_wp get_pml4e_wp assertE_wp | clarsimp simp: lookup_pdpt_slot_def find_vspace_for_asid_def)
  apply clarsimp
  apply (case_tac "([VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
                     VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None], pd) \<notin> vs_lookup_pages s")
   apply (clarsimp simp: graph_of_def split: if_splits)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (clarsimp simp: get_pml4_index_def bit_simps vs_lookup_pages_vs_lookupI obj_at_def entry_ref_pages_simps
                 split: if_splits)
   apply (drule vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI vs_lookup_pages1I[OF _ vs_refs_pages_pdpt ]])
     apply (simp add: obj_at_def)
    apply assumption
   apply simp
  apply (clarsimp split:if_splits simp: vs_lookup_pages_def graph_of_def dest!: in_vs_asid_refsD)
  apply (erule wellformed_lookup.lookupE[OF vs_lookup_pages1_is_wellformed_lookup], simp)
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD simp: lookup_leaf_def)
  apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
  apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                         wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                   simp: obj_at_def)
  apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def)
  apply (extract_vs_lookup)+
  apply (rewrite_lookup_when_aligned)
  apply (clarsimp simp: obj_at_def pml4e_ref_pages_def dest!: graph_ofD split: if_splits pml4e.split_asm)
  apply (fold ko_at_def2 vs_asid_refs_def)
  apply (drule eq_ucast_ucast_eq[rotated], simp)
  apply clarsimp
  apply (extract_vs_lookup, rewrite_lookup_when_aligned)
  apply (frule vs_lookup_pages_vs_lookupI)
  apply (clarsimp simp: obj_at_def pdpte_ref_pages_def image_def vs_lookup_pages_def
                 dest!: graph_ofD split: if_splits pdpte.split_asm)
  apply (clarsimp dest!: in_vs_asid_refsD wellformed_lookup.lookup_ref_step[OF vs_lookup_pages1_is_wellformed_lookup])
  apply (drule valid_vspace_objsD)
    apply (simp add: ko_at_def2)
   apply simp
  apply clarsimp
  apply (drule_tac x = aa in spec)
  apply (clarsimp simp: data_at_def obj_at_def a_type_simps)
  done
qed

lemma unmap_pd_vs_lookup_pages:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and typ_at (AArch APageDirectory) pd and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace> unmap_pd asid vaddr pd
  \<lbrace>\<lambda>r s. ([VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable), VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
                       VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), VSRef (ucast (asid_high_bits_of asid)) None],
        pd)
       \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_pd_vs_lookup_pages_pre])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma unmap_pt_vs_lookup_pages:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and typ_at (AArch APageTable) pt and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace> unmap_page_table asid vaddr pt
           \<lbrace>\<lambda>rv s. ([VSRef ((vaddr >> 21) && mask 9) (Some APageDirectory), VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4), VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None],
                    pt) \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_pt_vs_lookup_pages_pre])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma unmap_page_vs_lookup_pages_small:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and data_at X64SmallPage pg and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_page X64SmallPage asid vaddr pg
           \<lbrace>\<lambda>rv s. ([VSRef ((vaddr >> 12) && mask 9) (Some APageTable), VSRef ((vaddr >> 21) && mask 9) (Some APageDirectory), VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4), VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None],
                    pg) \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_page_vs_lookup_pages_pre[where sz=X64SmallPage, simplified]])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma unmap_page_vs_lookup_pages_large:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and data_at X64LargePage pg and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_page X64LargePage asid vaddr pg
           \<lbrace>\<lambda>rv s. ([VSRef ((vaddr >> 21) && mask 9) (Some APageDirectory), VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4), VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None],
                    pg) \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_page_vs_lookup_pages_pre[where sz=X64LargePage, simplified]])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma unmap_page_vs_lookup_pages_huge:
  "\<lbrace>pspace_aligned and valid_vspace_objs and valid_arch_state and data_at X64HugePage pg and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_page X64HugePage asid vaddr pg
           \<lbrace>\<lambda>rv s. ([VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4), VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None],
                    pg) \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_page_vs_lookup_pages_pre[where sz=X64HugePage, simplified]])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma unmap_pdpt_invs[wp]:
  "\<lbrace>invs and K (vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_pdpt asid vaddr pdpt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_pdpt_def)
  apply (rule hoare_pre)
   apply (wp store_pml4e_invs do_machine_op_global_refs_inv get_pml4e_wp
             hoare_vcg_all_lift find_vspace_for_asid_lots
        | wpc | simp add: flush_all_def pml4e_ref_pages_def)+
  apply (strengthen lookup_pml4_slot_kernel_mappings[THEN notE[where R=False], rotated -1, mk_strg D], simp)
  apply (strengthen not_in_global_refs_vs_lookup)+
  apply (auto simp: vspace_at_asid_def is_aligned_pml4[simplified] invs_vspace_objs
                    invs_psp_aligned lookup_pml4_slot_eq pml4e_ref_def)
  done

crunch lookup_pdpt_slot
  for invs[wp]: "\<lambda>s. P s"
crunch lookup_pd_slot
  for invs[wp]: "\<lambda>s. P s"

lemma pdpte_at_strg:
  "pdpte_at p s \<Longrightarrow> typ_at (AArch APDPointerTable) (p && ~~ mask pdpt_bits) s"
  by (simp add: pdpte_at_def)
lemma pde_at_strg:
  "pde_at p s \<Longrightarrow> typ_at (AArch APageDirectory) (p && ~~ mask pd_bits) s"
  by (simp add: pde_at_def)

lemma vs_lookup1_archD:
  "(x \<rhd>1 y) s \<Longrightarrow> \<exists>rs r p p' ko. x = (rs,p) \<and> y = (r # rs,p')
                          \<and> ko_at (ArchObj ko) p s \<and> (r,p') \<in> vs_refs_arch ko"
  by (clarsimp dest!: vs_lookup1D simp: obj_at_def vs_refs_def split: kernel_object.splits)

lemma dmo_invalidateLocalPageStructureCacheASID[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (invalidateLocalPageStructureCacheASID vs asid) \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (simp add: invalidateLocalPageStructureCacheASID_def dmo_machine_op_lift_invs)

lemma invalidate_page_structure_cache_asid_invs[wp]:
  "\<lbrace>invs\<rbrace> invalidate_page_structure_cache_asid vs asid \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp simp: invalidate_page_structure_cache_asid_def)

lemma unmap_pd_invs[wp]:
  "\<lbrace>invs and K (vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_pd asid vaddr pd
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_pd_def)
   apply (wp store_pdpte_invs do_machine_op_global_refs_inv get_pdpte_wp
             hoare_vcg_all_lift find_vspace_for_asid_lots
        | wpc | simp add: flush_all_def pdpte_ref_pages_def
        | strengthen imp_consequent )+
   apply (strengthen not_in_global_refs_vs_lookup invs_valid_vs_lookup invs_valid_global_refs
           invs_arch_state invs_valid_global_objs | wp find_vspace_for_asid_aligned_pm_bits | simp)+
  apply (auto simp: vspace_at_asid_def is_aligned_pml4[simplified] invs_vspace_objs
                    invs_psp_aligned lookup_pml4_slot_eq pml4e_ref_def)
  done

lemma unmap_pt_invs[wp]:
  "\<lbrace>invs and K (vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_table_def)
  apply (rule hoare_pre)
   apply (wp store_pde_invs do_machine_op_global_refs_inv get_pde_wp
             hoare_vcg_all_lift find_vspace_for_asid_lots
        | wpc | simp add: flush_all_def pdpte_ref_pages_def
        | strengthen imp_consequent )+
      apply (strengthen not_in_global_refs_vs_lookup invs_valid_vs_lookup invs_valid_global_refs
           invs_arch_state invs_valid_global_objs | wp find_vspace_for_asid_aligned_pm_bits | simp)+
  apply (auto simp: vspace_at_asid_def is_aligned_pml4[simplified] invs_vspace_objs
                    invs_psp_aligned lookup_pml4_slot_eq pml4e_ref_def)
  done

lemma final_cap_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (is_final_cap' cap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_final_cap' cap s)\<rbrace>"
  by (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state, rule x)

lemmas dmo_final_cap[wp] = final_cap_lift [OF do_machine_op_caps_of_state]
lemmas store_pte_final_cap[wp] = final_cap_lift [OF store_pte_caps_of_state]
lemmas unmap_page_table_final_cap[wp] = final_cap_lift [OF unmap_page_table_caps_of_state]
lemmas unmap_page_directory_final_cap[wp] = final_cap_lift [OF unmap_pd_caps_of_state]
lemmas unmap_pdpt_final_cap[wp] = final_cap_lift [OF unmap_pdpt_caps_of_state]


lemma mapM_x_swp_store_empty_pt':
  "\<lbrace>obj_at (\<lambda>ko. \<exists>pt. ko = ArchObj (PageTable pt)
                 \<and> (\<forall>x. x \<in> (\<lambda>sl. ucast ((sl && mask pt_bits) >> word_size_bits)) ` set slots
                           \<or> pt x = InvalidPTE)) p
         and K (is_aligned p pt_bits \<and> (\<forall>x \<in> set slots. x && ~~ mask pt_bits = p))\<rbrace>
      mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (induct slots, simp_all add: mapM_x_Nil mapM_x_Cons)
   apply wp
   apply (clarsimp simp: obj_at_def empty_table_def fun_eq_iff)
  apply (rule bind_wp, assumption)
  apply (thin_tac "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q)
  apply (simp add: store_pte_def set_object_def set_arch_obj_simps)
  apply (wp get_object_wp | simp)
  apply (clarsimp simp: obj_at_def)
  apply auto
  done

lemma mapM_x_swp_store_empty_pd':
  "\<lbrace>obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PageDirectory pd)
                 \<and> (\<forall>x. x \<in> (\<lambda>sl. ucast ((sl && mask pd_bits) >> word_size_bits)) ` set slots
                           \<or> pd x = InvalidPDE)) p
         and K (is_aligned p pt_bits \<and> (\<forall>x \<in> set slots. x && ~~ mask pd_bits = p))\<rbrace>
      mapM_x (swp store_pde InvalidPDE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (induct slots, simp_all add: mapM_x_Nil mapM_x_Cons)
   apply wp
   apply (clarsimp simp: obj_at_def empty_table_def fun_eq_iff)
  apply (rule bind_wp, assumption)
  apply (thin_tac "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q)
  apply (simp add: store_pde_def set_object_def set_arch_obj_simps)
  apply (wp get_object_wp | simp)
  apply (clarsimp simp: obj_at_def)
  apply auto
  done

lemma mapM_x_swp_store_empty_pt:
  "\<lbrace>page_table_at p and pspace_aligned
       and K ((UNIV :: 9 word set) \<subseteq> (\<lambda>sl. ucast ((sl && mask pt_bits) >> word_size_bits)) ` set slots
                       \<and> (\<forall>x\<in>set slots. x && ~~ mask pt_bits = p))\<rbrace>
     mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (wp mapM_x_swp_store_empty_pt')
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.split_asm if_split_asm)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp: pt_bits_def pageBits_def image_def table_size_def ptTranslationBits_def word_size_bits_def)
  apply blast
  done

lemma mapM_x_swp_store_empty_pdpt':
  "\<lbrace>obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PDPointerTable pd)
                 \<and> (\<forall>x. x \<in> (\<lambda>sl. ucast ((sl && mask pdpt_bits) >> word_size_bits)) ` set slots
                           \<or> pd x = InvalidPDPTE)) p
         and K (is_aligned p pd_bits \<and> (\<forall>x \<in> set slots. x && ~~ mask pdpt_bits = p))\<rbrace>
      mapM_x (swp store_pdpte InvalidPDPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (induct slots, simp_all add: mapM_x_Nil mapM_x_Cons)
   apply wp
   apply (clarsimp simp: obj_at_def empty_table_def fun_eq_iff)
  apply (rule bind_wp, assumption)
  apply (thin_tac "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>" for P f Q)
  apply (simp add: store_pdpte_def set_object_def set_arch_obj_simps)
  apply (wp get_object_wp | simp)
  apply (clarsimp simp: obj_at_def)
  apply auto
  done

lemma mapM_x_swp_store_empty_pdpt:
  "\<lbrace>pd_pointer_table_at p and pspace_aligned
       and K ((UNIV :: 9 word set) \<subseteq> (\<lambda>sl. ucast ((sl && mask pdpt_bits) >> word_size_bits)) ` set slots
                       \<and> (\<forall>x\<in>set slots. x && ~~ mask pdpt_bits = p))\<rbrace>
     mapM_x (swp store_pdpte InvalidPDPTE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (wp mapM_x_swp_store_empty_pdpt')
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.split_asm if_split_asm)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp: pd_bits_def pageBits_def image_def table_size_def ptTranslationBits_def word_size_bits_def)
  apply blast
  done

lemma mapM_x_swp_store_empty_pd:
  "\<lbrace>page_directory_at p and pspace_aligned
       and K ((UNIV :: 9 word set) \<subseteq> (\<lambda>sl. ucast ((sl && mask pd_bits) >> word_size_bits)) ` set slots
                       \<and> (\<forall>x\<in>set slots. x && ~~ mask pd_bits = p))\<rbrace>
     mapM_x (swp store_pde InvalidPDE) slots
   \<lbrace>\<lambda>rv. obj_at (empty_table {}) p\<rbrace>"
  apply (wp mapM_x_swp_store_empty_pd')
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.split_asm if_split_asm)
  apply (frule(1) pspace_alignedD)
  apply (clarsimp simp: pt_bits_def pageBits_def image_def table_size_def ptTranslationBits_def word_size_bits_def)
  apply blast
  done

(* FIXME: move near Invariants_A.vs_lookup_2ConsD *)
lemma vs_lookup_pages_2ConsD:
  "((v # v' # vs) \<unrhd> p) s \<Longrightarrow>
   \<exists>p'. ((v' # vs) \<unrhd> p') s \<and> ((v' # vs, p') \<unrhd>1 (v # v' # vs, p)) s"
  apply (clarsimp simp: vs_lookup_pages_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def)
  apply (fastforce simp: vs_lookup_pages1_def)
  done

(* FIXME: move to Invariants_A *)
lemma vs_lookup_pages_eq_at:
  "[VSRef a None] \<rhd> pd = [VSRef a None] \<unrhd> pd"
  apply (simp add: vs_lookup_pages_def vs_lookup_def Image_def)
  apply (rule ext)
  apply (rule iffI)
   apply (erule bexEI)
   apply (erule rtranclE, simp)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  apply (erule bexEI)
  apply (erule rtranclE, simp)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  done

(* FIXME: move to Invariants_A *)
lemma vs_lookup_pages_eq_ap:
  "[VSRef b (Some AASIDPool), VSRef a None] \<rhd> pm =
   [VSRef b (Some AASIDPool), VSRef a None] \<unrhd> pm"
  apply (simp add: vs_lookup_pages_def vs_lookup_def Image_def)
  apply (rule ext)
  apply (rule iffI)
   apply (erule bexEI)
   apply (erule rtranclE, simp)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
   apply (erule rtranclE)
    apply (clarsimp simp: vs_asid_refs_def graph_of_def image_def)
    apply (rule converse_rtrancl_into_rtrancl[OF _ rtrancl_refl])
    apply (fastforce simp: vs_refs_pages_def graph_of_def image_def
                          vs_lookup_pages1_def)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def
                  dest!: vs_lookup1D
                  split: Structures_A.kernel_object.splits
                         arch_kernel_obj.splits)
  apply (erule bexEI)
  apply (erule rtranclE, simp)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def image_def)
   apply (rule converse_rtrancl_into_rtrancl[OF _ rtrancl_refl])
   apply (fastforce simp: vs_refs_def graph_of_def image_def
                         vs_lookup1_def)
  apply (clarsimp simp: vs_refs_pages_def graph_of_def image_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  done

(* FIXME: move to Invariants_A *)
lemma pte_ref_pages_invalid_None[simp]:
  "pte_ref_pages InvalidPTE = None"
  by (simp add: pte_ref_pages_def)

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

(* FIXME: move *)
lemma empty_table_pt_capI:
  "\<lbrakk>caps_of_state s p =
    Some (cap.ArchObjectCap (arch_cap.PageTableCap pt None));
    valid_table_caps s\<rbrakk>
   \<Longrightarrow> obj_at (empty_table (set (second_level_tables (arch_state s)))) pt s"
    apply (case_tac p)
    apply (clarsimp simp: valid_table_caps_def simp del: imp_disjL)
    apply (drule spec)+
    apply (erule impE, simp add: is_cap_simps)+
    by assumption

sublocale vs_refs_empty: vspace_only_obj_pred "\<lambda>ko. vs_refs ko = {}"
  by unfold_locales
     (fastforce simp: vspace_obj_pred_def arch_obj_pred_def non_arch_obj_def vs_refs_def
               split: kernel_object.splits arch_kernel_obj.splits)

sublocale vs_refs_pages_empty: vspace_only_obj_pred "\<lambda>ko. vs_refs_pages ko = {}"
  by unfold_locales
     (fastforce simp: vspace_obj_pred_def arch_obj_pred_def non_arch_obj_def vs_refs_pages_def
               split: kernel_object.splits arch_kernel_obj.splits)

lemma set_cap_cte_wp_at_ex:
  "\<lbrace>K (P cap) and cte_wp_at \<top> slot\<rbrace> set_cap cap slot \<lbrace>\<lambda>r s. \<exists>slot. cte_wp_at P slot s\<rbrace>"
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift set_cap_cte_wp_at)
  apply fastforce
  done

lemma vs_cap_ref_of_table_capNone:
  "\<lbrakk>is_pd_cap cap \<or> is_pt_cap cap \<or> is_pdpt_cap cap \<or> is_pml4_cap cap; cap_asid cap = None\<rbrakk> \<Longrightarrow> vs_cap_ref cap = None"
  by (auto simp: cap_asid_def is_cap_simps vs_cap_ref_def split: cap.splits arch_cap.splits option.split_asm)

lemma unique_table_caps_ptD2:
  "\<lbrakk> is_pt_cap cap; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs; valid_cap cap s; valid_cap cap' s\<rbrakk>
  \<Longrightarrow> p = p'"
  apply (erule(3) unique_table_caps_ptD)
    apply (clarsimp simp: is_cap_simps)
    apply (case_tac cap')
     apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits)+
     apply (rename_tac p acap pd)
     apply (case_tac acap)
      apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits if_splits)+
  done


lemma unique_table_caps_pdD2:
  "\<lbrakk> is_pd_cap cap; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs; valid_cap cap s; valid_cap cap' s\<rbrakk>
  \<Longrightarrow> p = p'"
  apply (erule(3) unique_table_caps_pdD)
    apply (clarsimp simp: is_cap_simps)
    apply (case_tac cap')
     apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits)+
     apply (rename_tac p acap pd)
     apply (case_tac acap)
      apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits if_splits)+
  done

lemma unique_table_caps_pdptD2:
  "\<lbrakk> is_pdpt_cap cap; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs; valid_cap cap s; valid_cap cap' s\<rbrakk>
  \<Longrightarrow> p = p'"
  apply (erule(3) unique_table_caps_pdptD)
    apply (clarsimp simp: is_cap_simps)
    apply (case_tac cap')
     apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits)+
     apply (rename_tac p acap pd)
     apply (case_tac acap)
      apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits if_splits)+
  done

lemma unique_table_caps_pml4D2:
  "\<lbrakk> is_pml4_cap cap; cs p = Some cap; cap_asid cap = None;
     cs p' = Some cap';
     obj_refs cap' = obj_refs cap;
     unique_table_caps cs; valid_cap cap s; valid_cap cap' s\<rbrakk>
  \<Longrightarrow> p = p'"
  apply (erule(3) unique_table_caps_pml4D)
    apply (clarsimp simp: is_cap_simps)
    apply (case_tac cap')
     apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits)+
     apply (rename_tac p acap pd)
     apply (case_tac acap)
      apply (clarsimp simp: valid_cap_simps obj_at_def is_ep_def is_ntfn_def is_cap_table_def is_tcb_def
                    split: option.splits if_splits)+
  done

lemma obj_refs_eqI:
  "\<lbrakk>a \<in> obj_refs c; a \<in> obj_refs b\<rbrakk> \<Longrightarrow> obj_refs c = obj_refs b"
  by (clarsimp dest!: obj_ref_elemD)

lemma valid_pd_cap_asidNone[simp]:
  "s \<turnstile> ArchObjectCap (PageDirectoryCap pa asid) \<Longrightarrow> s \<turnstile> ArchObjectCap (PageDirectoryCap pa None)"
  by (clarsimp simp: valid_cap_def cap_aligned_def)

lemma valid_pdpt_cap_asidNone[simp]:
  "s \<turnstile> ArchObjectCap (PDPointerTableCap pa asid) \<Longrightarrow> s \<turnstile> ArchObjectCap (PDPointerTableCap pa None)"
  by (clarsimp simp: valid_cap_def cap_aligned_def)

lemma valid_pt_cap_asidNone[simp]:
  "s \<turnstile> ArchObjectCap (PageTableCap pa asid) \<Longrightarrow> s \<turnstile> ArchObjectCap (PageTableCap pa None)"
  by (clarsimp simp: valid_cap_def cap_aligned_def)


lemma update_aobj_zombies[wp]:
  "\<lbrace>\<lambda>s. is_final_cap' cap s\<rbrace>
  set_object ptr (ArchObj obj)
  \<lbrace>\<lambda>_ s. is_final_cap' cap s\<rbrace>"
  apply (simp add: is_final_cap'_def2)
  apply (wp hoare_vcg_ex_lift hoare_vcg_all_lift set_aobject_cte_wp_at)
  done

crunch store_pde
  for is_final_cap'[wp]: "is_final_cap' cap"
  (wp: crunch_wps simp: crunch_simps set_arch_obj_simps ignore: set_object set_pd)

crunch store_pdpte
  for is_final_cap'[wp]: "is_final_cap' cap"
  (wp: crunch_wps simp: crunch_simps set_arch_obj_simps ignore: set_object set_pdpt)

crunch store_pml4e
  for is_final_cap'[wp]: "is_final_cap' cap"
  (wp: crunch_wps simp: crunch_simps set_arch_obj_simps ignore: set_object set_pml4)

lemma lookup_pages_shrink_store_pdpte:
  "\<lbrace>\<lambda>s. p \<notin> vs_lookup_pages s\<rbrace> store_pdpte slot InvalidPDPTE \<lbrace>\<lambda>rv s. p \<notin> vs_lookup_pages s\<rbrace>"
  apply (case_tac p)
  apply (simp add: store_pdpte_def set_object_def set_arch_obj_simps | wp get_object_wp | clarsimp)+
  apply (simp add: vs_lookup_pages_def)
  apply (drule_tac s1 = s in lookup_bound_estimate[OF vs_lookup_pages1_is_wellformed_lookup, rotated -1])
   apply (simp add: fun_upd_def[symmetric])
   apply (rule vs_lookup_pages1_is_wellformed_lookup[where s = "s\<lparr>kheap := (kheap s)(ptr \<mapsto> ArchObj obj)\<rparr>" for s ptr obj
                ,simplified])
   apply (clarsimp simp: lookup_refs_def vs_lookup_pages1_on_heap_obj_def vs_refs_pages_def image_def obj_at_def
                         graph_of_def pdpte_ref_pages_def split: if_split_asm pde.split_asm)
  apply clarsimp
  done

lemma lookup_pages_shrink_store_pde:
  "\<lbrace>\<lambda>s. p \<notin> vs_lookup_pages s\<rbrace> store_pde slot InvalidPDE \<lbrace>\<lambda>rv s. p \<notin> vs_lookup_pages s\<rbrace>"
  apply (case_tac p)
  apply (simp add: store_pde_def set_object_def set_arch_obj_simps | wp get_object_wp | clarsimp)+
  apply (simp add: vs_lookup_pages_def)
  apply (drule_tac s1 = s in lookup_bound_estimate[OF vs_lookup_pages1_is_wellformed_lookup, rotated -1])
   apply (simp add: fun_upd_def[symmetric])
   apply (rule vs_lookup_pages1_is_wellformed_lookup[where s = "s\<lparr>kheap := (kheap s)(ptr \<mapsto> ArchObj obj)\<rparr>" for s ptr obj
                ,simplified])
   apply (clarsimp simp: lookup_refs_def vs_lookup_pages1_on_heap_obj_def vs_refs_pages_def image_def obj_at_def
                         graph_of_def pde_ref_pages_def split: if_split_asm pde.split_asm)
  apply clarsimp
  done

lemma lookup_pages_shrink_store_pte:
  "\<lbrace>\<lambda>s. p \<notin> vs_lookup_pages s\<rbrace> store_pte slot InvalidPTE \<lbrace>\<lambda>rv s. p \<notin> vs_lookup_pages s\<rbrace>"
  apply (case_tac p)
  apply (simp add: store_pte_def set_object_def set_arch_obj_simps | wp get_object_wp | clarsimp)+
  apply (simp add: vs_lookup_pages_def)
  apply (drule_tac s1 = s in lookup_bound_estimate[OF vs_lookup_pages1_is_wellformed_lookup, rotated -1])
   apply (simp add: fun_upd_def[symmetric])
   apply (rule vs_lookup_pages1_is_wellformed_lookup[where s = "s\<lparr>kheap := (kheap s)(ptr \<mapsto> ArchObj obj)\<rparr>" for s ptr obj
                ,simplified])
   apply (clarsimp simp: lookup_refs_def vs_lookup_pages1_on_heap_obj_def vs_refs_pages_def image_def obj_at_def
                         graph_of_def pde_ref_pages_def split: if_split_asm pde.split_asm)
  apply clarsimp
  done

lemma store_invalid_pdpte_vs_lookup_pages_shrink:
  "\<lbrace>\<lambda>s. invs s \<and> p \<notin> vs_lookup_pages s\<rbrace> mapM_x (\<lambda>a. store_pdpte a InvalidPDPTE) ls \<lbrace>\<lambda>rv s. p \<notin> vs_lookup_pages s\<rbrace>"
  apply (wp mapM_x_wp lookup_pages_shrink_store_pdpte)
  apply force+
  done


lemma store_invalid_pde_vs_lookup_pages_shrink:
  "\<lbrace>\<lambda>s. invs s \<and> p \<notin> vs_lookup_pages s\<rbrace> mapM_x (\<lambda>a. store_pde a InvalidPDE) ls \<lbrace>\<lambda>rv s. p \<notin> vs_lookup_pages s\<rbrace>"
  apply (wp mapM_x_wp lookup_pages_shrink_store_pde)
  apply force+
  done

lemma store_invalid_pte_vs_lookup_pages_shrink:
  "\<lbrace>\<lambda>s. invs s \<and> p \<notin> vs_lookup_pages s\<rbrace> mapM_x (\<lambda>a. store_pte a InvalidPTE) ls \<lbrace>\<lambda>rv s. p \<notin> vs_lookup_pages s\<rbrace>"
  apply (wp mapM_x_wp lookup_pages_shrink_store_pte)
  apply force+
  done

lemma set_current_cr3_global_refs_inv[iff]:
  "global_refs (s\<lparr>arch_state := arch_state s\<lparr>x64_current_cr3 := param_a\<rparr>\<rparr>) = global_refs s"
  by (simp add: global_refs_def)

crunch unmap_pd
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"
crunch unmap_pdpt
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"
crunch unmap_page_table
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"

lemma range_neg_mask_strengthen:
  "\<lbrakk>is_aligned ptr table_size; P ptr\<rbrakk> \<Longrightarrow> (\<forall>x\<in>set [ptr , ptr + 2 ^ word_size_bits .e. ptr + 2 ^ table_size - 1]. P (x && ~~ mask table_size))"
  apply clarsimp
  apply (drule subsetD[OF upto_enum_step_subset])
  apply (fastforce dest!: mask_in_range)
  done

lemma vtable_range_univ:
  "is_aligned (ptr :: word64) table_size \<Longrightarrow>
    {y. \<exists>x\<in>set [ptr , ptr + 2 ^ word_size_bits .e. ptr + 2 ^ table_size - 1].
      (y :: 9 word) = ucast (x && mask table_size >> word_size_bits)} = UNIV"
  apply (intro set_eqI iffI | clarsimp)+
  apply (rule_tac x = "ptr + (ucast x << word_size_bits)" in bexI)
   apply (clarsimp simp: mask_add_aligned)
   apply (subst  le_mask_imp_and_mask)
    apply (subst le_mask_iff_lt_2n[THEN iffD1])
     apply (clarsimp simp: bit_simps)
    apply (rule shiftl_less_t2n)
    apply (clarsimp simp: bit_simps)
     apply word_bitwise
    apply (simp add: bit_simps)
   apply (simp add: shiftl_shiftr3 word_size bit_simps)
   apply word_bitwise
   apply (simp add: mask_def)
  apply (simp add: upto_enum_step_subtract[OF is_aligned_no_overflow])
  apply (clarsimp simp: upto_enum_step_def image_def)
  apply (rule_tac x = "ucast x" in exI)
  apply (clarsimp simp: shift_times_fold[where m= 0,simplified])
  apply word_bitwise
  apply (auto simp: bit_simps)
  done

lemma subset_refl_subst:
  "y = x \<Longrightarrow> x \<subseteq> y"
  by simp

lemma empty_refs_strg:
  "empty_table {} a \<longrightarrow> (vs_refs_pages a = {})"
  by (simp add: empty_table_def split: kernel_object.splits arch_kernel_obj.splits)

lemma obj_at_empty_refs_strg:
  "obj_at (empty_table (set (second_level_tables (arch_state s)))) ptr s \<longrightarrow> obj_at (\<lambda>a. vs_refs_pages a = {}) ptr s"
  apply (clarsimp simp: obj_at_def second_level_tables_def)
  done

lemma perform_page_directory_invocation_invs[wp]:
  "\<lbrace>invs and valid_pdi pdi\<rbrace>
     perform_page_directory_invocation pdi
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (cases pdi)
   apply (rename_tac cap cslot_ptr pdpte obj_ref vspace)
   apply (rule hoare_pre)
    apply (clarsimp simp: perform_page_directory_invocation_def)
    apply (wp hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_vcg_conj_lift
              store_pdpte_invs arch_update_cap_invs_map
           | strengthen obj_at_empty_refs_strg
           | simp add: empty_table.arch_only del: split_paired_All | wps
           | rule set_cap.aobj_at | wpc)+
      apply (rule set_cap_cte_wp_at_ex[simplified])
     apply wp+
   apply (clarsimp simp: valid_pdi_def is_arch_update_def cte_wp_at_caps_of_state
                         vs_cap_ref_of_table_capNone
               simp del: split_paired_All)
   apply (frule vs_lookup_pages_vs_lookupI)
   apply (rule conjI)
    apply (clarsimp dest!: same_master_cap_same_types simp: vs_cap_ref_of_table_capNone)
   apply (intro conjI allI)
    apply clarsimp
    apply (drule_tac ref = ref in valid_vs_lookupD)
     apply fastforce
    apply (rule ccontr, clarsimp)
    apply (frule_tac cap = x and cap' = cap in unique_table_caps_pdptD2[OF _ _ _ _ obj_refs_eqI invs_unique_table_caps])
            apply assumption+
      apply (erule caps_of_state_valid, fastforce)
     apply (erule caps_of_state_valid, fastforce)
    apply (clarsimp simp: is_cap_simps cap_asid_def vs_cap_ref_def split: option.split_asm)
   apply (clarsimp simp: is_cap_simps)
   apply (rule ref_is_unique)
          apply simp
         apply (erule(1) vs_lookup_vs_lookup_pagesI)
          apply fastforce+
        apply (simp add: global_refs_def)
        apply (fastforce simp: second_level_tables_def)+
   apply (clarsimp dest!: invs_valid_objs valid_objs_caps)
  apply (rename_tac cap cslot)
  apply (clarsimp simp: perform_page_directory_invocation_def)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: valid_pdi_def is_cap_simps)
  apply (rule hoare_pre)
   apply (wpc | clarsimp simp: cte_wp_at_caps_of_state | wp arch_update_cap_invs_unmap_page_directory get_cap_wp)+
    apply (rule_tac P = "is_pd_cap (ArchObjectCap (PageDirectoryCap p (Some (x1, x2a))))" in hoare_gen_asm)
    apply (rule_tac Q'="\<lambda>r. cte_wp_at ((=) (ArchObjectCap (PageDirectoryCap p (Some (x1, x2a))))) (a,b)
                             and invs and is_final_cap' (ArchObjectCap (PageDirectoryCap p (Some (x1, x2a))))
                             and (\<lambda>s. (the (vs_cap_ref (ArchObjectCap (PageDirectoryCap p (Some (x1, x2a))))), p) \<notin> vs_lookup_pages s)
                             and obj_at (empty_table {}) (the (aobj_ref (update_map_data
                                   (Structures_A.the_arch_cap (ArchObjectCap (PageDirectoryCap p (Some (x1, x2a))))) None None)))"
                             in hoare_post_imp)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps update_map_data_def
                           is_arch_update_def cap_master_cap_simps)
     apply (clarsimp dest!: caps_of_state_valid_cap[OF _ invs_valid_objs] split: option.split_asm
                      simp: mask_cap_def cap_rights_update_def acap_rights_update_def vs_cap_ref_simps)
    apply (wp hoare_vcg_conj_lift)
        apply (wp mapM_x_wp, force)
       apply (rule mapM_x_swp_store_pde_invs_unmap[unfolded swp_def])
      apply (wp mapM_x_wp)
      apply force
     apply (wp store_invalid_pde_vs_lookup_pages_shrink)
    apply (wp mapM_x_swp_store_empty_pd[unfolded swp_def])
   apply (clarsimp simp: cte_wp_at_caps_of_state vs_cap_ref_def
                         is_cap_simps mask_cap_def)
   apply (wp unmap_pd_vs_lookup_pages)
  apply (clarsimp simp: is_final_cap'_def2 gen_obj_refs_def acap_rights_update_def cte_wp_at_caps_of_state
                        mask_cap_def)
  apply (clarsimp simp: cap_rights_update_def acap_rights_update_def is_arch_update_def is_cap_simps
                        update_map_data_def vs_cap_ref_simps invs_psp_aligned pd_bits_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_cap_def)
   apply (drule valid_table_caps_pdD, force)
   apply (clarsimp simp: obj_at_def empty_table_def)
  apply (strengthen range_neg_mask_strengthen[mk_strg] vtable_range_univ[THEN subset_refl_subst, mk_strg])
  apply (frule valid_global_refsD2, force)
  apply (clarsimp simp: valid_cap_def wellformed_mapdata_def image_def le_mask_iff_lt_2n cap_aligned_def
                        cap_range_def invs_vspace_objs pd_bits_def vtable_range_univ invs_arch_state)
  done

lemmas valid_table_caps_empty_ptD = empty_table_pt_capI

lemma perform_page_table_invocation_invs[wp]:
  "\<lbrace>invs and valid_pti pti\<rbrace>
     perform_page_table_invocation pti
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (cases pti)
   apply (rename_tac cap cslot_ptr pdpte obj_ref vspace)
   apply (rule hoare_pre)
    apply (clarsimp simp: perform_page_table_invocation_def)
    apply (wp hoare_vcg_const_imp_lift hoare_vcg_all_lift  hoare_vcg_conj_lift
              store_pde_invs arch_update_cap_invs_map
           | strengthen obj_at_empty_refs_strg
           | simp add: empty_table.arch_only del: split_paired_all split_paired_All | wps
           | wp set_cap.aobj_at | wpc)+
      apply (rule set_cap_cte_wp_at_ex[simplified])
     apply wp+
   apply (clarsimp simp: valid_pti_def is_arch_update_def cte_wp_at_caps_of_state
                         vs_cap_ref_of_table_capNone
               simp del: split_paired_All)
   apply (frule vs_lookup_pages_vs_lookupI)
   apply (rule conjI)
    apply (clarsimp dest!: same_master_cap_same_types simp: vs_cap_ref_of_table_capNone)
   apply (intro conjI allI)
    apply clarsimp
    apply (drule_tac ref = ref in valid_vs_lookupD)
     apply fastforce
    apply (rule ccontr, clarsimp)
    apply (frule_tac cap = x and cap' = cap in unique_table_caps_pdD2[OF _ _ _ _ obj_refs_eqI invs_unique_table_caps])
            apply assumption+
      apply (erule caps_of_state_valid, fastforce)
     apply (erule caps_of_state_valid, fastforce)
    apply (clarsimp simp: is_cap_simps cap_asid_def vs_cap_ref_def split: option.split_asm)
   apply (clarsimp simp: is_cap_simps)
   apply (rule ref_is_unique)
          apply simp
         apply (erule(1) vs_lookup_vs_lookup_pagesI)
          apply fastforce+
        apply (simp add:global_refs_def)
        apply (fastforce simp: second_level_tables_def)+
   apply (clarsimp dest!: invs_valid_objs valid_objs_caps)
  apply (rename_tac cap cslot)
  apply (clarsimp simp: perform_page_table_invocation_def)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: valid_pti_def is_cap_simps)
  apply (rule hoare_pre)
   apply (wpc | clarsimp simp: cte_wp_at_caps_of_state | wp arch_update_cap_invs_unmap_page_table get_cap_wp)+
    apply (rule_tac P = "is_pt_cap (ArchObjectCap (PageTableCap p (Some (x1, x2a))))" in hoare_gen_asm)
    apply (rule_tac Q'="\<lambda>r. cte_wp_at ((=) (ArchObjectCap (PageTableCap p (Some (x1, x2a))))) (a,b)
                             and invs and is_final_cap' (ArchObjectCap (PageTableCap p (Some (x1, x2a))))
                             and (\<lambda>s. (the (vs_cap_ref (ArchObjectCap (PageTableCap p (Some (x1, x2a))))), p) \<notin> vs_lookup_pages s)
                             and obj_at (empty_table {}) (the (aobj_ref (update_map_data
                                   (Structures_A.the_arch_cap (ArchObjectCap (PageTableCap p (Some (x1, x2a))))) None None)))"
                             in hoare_post_imp)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps update_map_data_def
                           is_arch_update_def cap_master_cap_simps)
     apply (clarsimp dest!: caps_of_state_valid_cap[OF _ invs_valid_objs] split: option.split_asm
                      simp: mask_cap_def cap_rights_update_def acap_rights_update_def vs_cap_ref_simps)
    apply (wp hoare_vcg_conj_lift)
        apply (wp mapM_x_wp, force)
       apply (rule mapM_x_swp_store_pte_invs_unmap[unfolded swp_def])
      apply (wp mapM_x_wp)
      apply force
     apply (wp store_invalid_pte_vs_lookup_pages_shrink)
    apply (wp mapM_x_swp_store_empty_pt[unfolded swp_def])
   apply (clarsimp simp: cte_wp_at_caps_of_state vs_cap_ref_def is_cap_simps mask_cap_def)
   apply (wp unmap_pt_vs_lookup_pages unmap_page_table_caps_of_state)
  apply (clarsimp simp: is_final_cap'_def2 gen_obj_refs_def acap_rights_update_def cte_wp_at_caps_of_state
                        mask_cap_def)
  apply (clarsimp simp: cap_rights_update_def acap_rights_update_def is_arch_update_def is_cap_simps
                        update_map_data_def vs_cap_ref_simps invs_psp_aligned pt_bits_def
                 split: cap.split_asm arch_cap.split_asm)
  apply (rule conjI)
   apply (clarsimp simp: valid_cap_def)
   apply (drule valid_table_caps_empty_ptD, force)
   apply (clarsimp simp: obj_at_def empty_table_def)
  apply (strengthen  range_neg_mask_strengthen[mk_strg])
  apply (frule valid_global_refsD2, force)
  apply (clarsimp simp: valid_cap_def wellformed_mapdata_def image_def le_mask_iff_lt_2n cap_range_def
                        invs_vspace_objs vtable_range_univ invs_arch_state cap_aligned_def)
  done

lemma pml4_mask_shift_mask_irrelevant[simp]: "(((obj_ref::machine_word) && mask pml4_bits >> word_size_bits) &&
          mask ptTranslationBits) = (obj_ref && mask pml4_bits >> word_size_bits)"
  apply (clarsimp simp: bit_simps mask_def)
  by word_bitwise

lemma valid_table_caps_pdptD:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PDPointerTableCap pd None));
     valid_table_caps s \<rbrakk> \<Longrightarrow>
    obj_at (empty_table (set (second_level_tables (arch_state s)))) pd s"
  apply (clarsimp simp: valid_table_caps_def simp del: split_paired_All)
  apply (erule allE)+
  apply (erule (1) impE)
  apply (fastforce simp add: is_pdpt_cap_def cap_asid_def)
  done

lemma valid_global_refs_pdptD:
  "\<lbrakk>caps_of_state s (a,b) = Some (ArchObjectCap (PDPointerTableCap p asid)); valid_global_refs s\<rbrakk>
   \<Longrightarrow> p \<notin> set (second_level_tables (arch_state s))"
  apply (clarsimp simp: valid_global_refs_def valid_refs_def
                          cte_wp_at_caps_of_state is_cap_simps)
  apply (drule_tac x=a in spec)
  apply (drule_tac x=b in spec)
  apply (drule_tac x="ArchObjectCap (PDPointerTableCap p asid)" in spec)
  apply (clarsimp simp: cap_range_def global_refs_def second_level_tables_def)
  done

lemma perform_pdpt_invocation_invs[wp]:
  "\<lbrace>invs and valid_pdpti pdpti\<rbrace>
     perform_pdpt_invocation pdpti
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (cases pdpti)
   apply (rename_tac cap cslot_ptr pml4e obj_ref vspace)
   apply (rule hoare_pre)
    apply (clarsimp simp: perform_pdpt_invocation_def)
    apply (wp hoare_vcg_const_imp_lift hoare_vcg_all_lift  hoare_vcg_conj_lift
              store_pml4e_invs arch_update_cap_invs_map
           | strengthen obj_at_empty_refs_strg
           | simp add: empty_table.arch_only del: split_paired_all split_paired_All | wps
           | rule set_cap.aobj_at | wpc)+
       apply (rule set_cap_cte_wp_at_ex[simplified])
      apply (wp hoare_vcg_all_lift set_cap.aobj_at, simp)
     apply wp+
   apply (clarsimp simp: valid_pdpti_def is_arch_update_def cte_wp_at_caps_of_state
                         vs_cap_ref_of_table_capNone
               simp del: split_paired_All)
   apply (frule vs_lookup_pages_vs_lookupI)
   apply (rule conjI)
    apply (clarsimp dest!: same_master_cap_same_types simp: vs_cap_ref_of_table_capNone)
   apply (rule conjI)
    apply (frule same_master_cap_same_types)
    apply (clarsimp simp: is_cap_simps cap_master_cap_def kernel_vsrefs_kernel_mapping_slots
                   dest!: valid_global_refs_pdptD[OF _ invs_valid_global_refs])
   apply (intro conjI allI)
     apply clarsimp
     apply (drule_tac ref = ref in valid_vs_lookupD)
      apply fastforce
     apply (rule ccontr, clarsimp)
     apply (frule_tac cap = x and cap' = cap in unique_table_caps_pml4D2[OF _ _ _ _ obj_refs_eqI invs_unique_table_caps])
             apply assumption+
       apply (erule caps_of_state_valid, fastforce)
      apply (erule caps_of_state_valid, fastforce)
     apply (clarsimp simp: is_cap_simps cap_asid_def vs_cap_ref_def split: option.split_asm)
    apply (clarsimp simp: is_cap_simps)
    apply (rule ref_is_unique)
           apply simp
          apply (erule(1) vs_lookup_vs_lookup_pagesI)
           apply fastforce+
         apply (simp add:global_refs_def)
         apply (fastforce simp: second_level_tables_def)+
    apply (clarsimp dest!:invs_valid_objs valid_objs_caps)
   apply (clarsimp simp: kernel_vsrefs_kernel_mapping_slots)
  apply (rename_tac cap cslot)
  apply (clarsimp simp: perform_pdpt_invocation_def)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: valid_pdpti_def is_cap_simps)
  apply (rule hoare_pre)
   apply (wpc | clarsimp simp: cte_wp_at_caps_of_state | wp arch_update_cap_invs_unmap_pd_pointer_table get_cap_wp)+
    apply (rule_tac P = "is_pdpt_cap (ArchObjectCap (PDPointerTableCap p (Some (x1, x2a))))" in hoare_gen_asm)
    apply (rule_tac Q'="\<lambda>r. cte_wp_at ((=) (ArchObjectCap (PDPointerTableCap p (Some (x1, x2a))))) (a,b)
                             and invs and is_final_cap' (ArchObjectCap (PDPointerTableCap p (Some (x1, x2a))))
                             and (\<lambda>s. (the (vs_cap_ref (ArchObjectCap (PDPointerTableCap p (Some (x1, x2a))))), p) \<notin> vs_lookup_pages s)
                             and obj_at (empty_table {}) (the (aobj_ref (update_map_data
                                   (Structures_A.the_arch_cap (ArchObjectCap (PDPointerTableCap p (Some (x1, x2a))))) None None)))"
                             in hoare_post_imp)
     apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps update_map_data_def
                           is_arch_update_def cap_master_cap_simps)
     apply (clarsimp dest!: caps_of_state_valid_cap[OF _ invs_valid_objs] split: option.split_asm
                      simp: mask_cap_def cap_rights_update_def acap_rights_update_def vs_cap_ref_simps)
    apply (wp hoare_vcg_conj_lift)
        apply (wp mapM_x_wp, force)
       apply (rule mapM_x_swp_store_pdpte_invs_unmap[unfolded swp_def])
      apply (wp mapM_x_wp)
      apply force
     apply (wp store_invalid_pdpte_vs_lookup_pages_shrink)
    apply (wp mapM_x_swp_store_empty_pdpt[unfolded swp_def])
   apply (clarsimp simp: cte_wp_at_caps_of_state vs_cap_ref_def is_cap_simps mask_cap_def)
   apply (wp unmap_pdpt_vs_lookup_pages)
  apply (clarsimp simp: is_final_cap'_def2 gen_obj_refs_Int acap_rights_update_def cte_wp_at_caps_of_state
                        mask_cap_def)
  apply (clarsimp simp: cap_rights_update_def acap_rights_update_def is_arch_update_def is_cap_simps
                        update_map_data_def vs_cap_ref_simps invs_psp_aligned pd_bits_def
                 split: cap.split_asm arch_cap.split_asm)
  apply (intro conjI impI)
   apply (clarsimp simp: valid_cap_def)
   apply (drule valid_table_caps_pdptD, force)
   apply (clarsimp simp: obj_at_def empty_table_def)
  apply (simp add: pdpt_bits_def)
  apply (strengthen range_neg_mask_strengthen[mk_strg] vtable_range_univ[THEN subset_refl_subst, mk_strg])
  apply (frule valid_global_refsD2, force)
  apply (clarsimp simp: valid_cap_def wellformed_mapdata_def image_def le_mask_iff_lt_2n cap_aligned_def
                        cap_range_def invs_vspace_objs pdpt_bits_def vtable_range_univ invs_arch_state)
  done

lemma valid_kernel_mappingsD:
  "\<lbrakk> kheap s pml4ptr = Some (ArchObj (PageMapL4 pml4));
     valid_kernel_mappings s \<rbrakk>
      \<Longrightarrow> \<forall>x r. pml4e_ref (pml4 x) = Some r \<longrightarrow>
                  (r \<in> set (second_level_tables (arch_state s)))
                       = (ucast (pptr_base >> pml4_shift_bits) \<le> x)"
  apply (simp add: valid_kernel_mappings_def)
  apply (drule bspec, erule ranI)
  unfolding valid_kernel_mappings_if_pm_def valid_kernel_mappings_if_pm_arch_def
  apply (simp add: valid_kernel_mappings_if_pm_def
                   kernel_mapping_slots_def)
  done

lemma set_mi_invs[wp]: "\<lbrace>invs\<rbrace> set_message_info t a \<lbrace>\<lambda>x. invs\<rbrace>"
  by (simp add: set_message_info_def, wp)

lemma reachable_page_table_not_global:
  "\<lbrakk>(ref \<rhd> p) s; valid_kernel_mappings s; valid_global_pdpts s;
    valid_vspace_objs s; valid_asid_table (x64_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> p \<notin> set (second_level_tables (arch_state s))"
  apply clarsimp
  apply (erule (2) vs_lookupE_alt[OF _ _valid_asid_table_ran])
      apply (fastforce simp: second_level_tables_def valid_global_pdpts_def obj_at_def)+
    apply (clarsimp simp: second_level_tables_def valid_global_pdpts_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: obj_at_def)
    apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pm_def ran_def)
    apply (drule_tac x="ArchObj (PageMapL4 pm)" in spec)
    apply (drule mp, erule_tac x=p\<^sub>2 in exI)
    apply (clarsimp simp: second_level_tables_def)
   apply (fastforce simp: second_level_tables_def valid_global_pdpts_def obj_at_def)+
  done

lemma invs_valid_global_pdpts[elim]:
  "invs s \<Longrightarrow> valid_global_pdpts s"
  by (clarsimp simp: invs_def valid_arch_state_def valid_state_def)

lemmas valid_table_caps_ptD = empty_table_pt_capI

lemma empty_ref_pageD[elim]:
  "\<lbrakk> data_at X64LargePage page s \<rbrakk> \<Longrightarrow>
    obj_at (\<lambda>ko. vs_refs_pages ko = {}) page s"
  "\<lbrakk> data_at X64HugePage page s \<rbrakk> \<Longrightarrow>
    obj_at (\<lambda>ko. vs_refs_pages ko = {}) page s"
  by (fastforce simp: vs_refs_pages_def data_at_def obj_at_def)+

lemma empty_refs_pageCapD[elim]:
  "s \<turnstile> ArchObjectCap (PageCap dev p Ra tpa sz ma) \<Longrightarrow> obj_at (\<lambda>ko. vs_refs_pages ko = {}) p s"
  by (clarsimp simp: valid_cap_def vs_refs_pages_def obj_at_def split: if_splits)

lemma reachable_pd_not_global:
  "\<lbrakk>(ref \<rhd> p) s; valid_kernel_mappings s; valid_global_pdpts s;
    valid_vspace_objs s; valid_asid_table (x64_asid_table (arch_state s)) s\<rbrakk>
   \<Longrightarrow> p \<notin> set (second_level_tables (arch_state s))"
  apply clarsimp
  apply (erule (2) vs_lookupE_alt[OF _ _valid_asid_table_ran])
      apply (fastforce simp: second_level_tables_def valid_global_pdpts_def obj_at_def)+
    apply (clarsimp simp: second_level_tables_def valid_global_pdpts_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: obj_at_def)
    apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pm_def ran_def)
    apply (drule_tac x="ArchObj (PageMapL4 pm)" in spec)
    apply (drule mp, erule_tac x=p\<^sub>2 in exI)
    apply clarsimp
   apply (fastforce simp: second_level_tables_def valid_global_pdpts_def obj_at_def)+
  done

lemma vs_lookup_invs_ref_is_unique: "\<lbrakk> (ref \<rhd> p) s; (ref' \<rhd> p) s; invs s \<rbrakk> \<Longrightarrow> ref = ref'"
  apply (erule (1) ref_is_unique)
  apply (erule reachable_pd_not_global)
  by (auto elim: invs_valid_kernel_mappings intro!: valid_objs_caps)

crunch pte_check_if_mapped, pde_check_if_mapped
  for invs[wp]: "invs"

crunch pte_check_if_mapped, pde_check_if_mapped
  for vs_lookup[wp]: "\<lambda>s. P (vs_lookup s)"

crunch pte_check_if_mapped
  for valid_pte[wp]: "\<lambda>s. P (valid_pte p s)"

crunch lookup_pt_slot
  for invs[wp]: invs

lemma unmap_page_invs[wp]:
  "\<lbrace>invs and K (vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_page pgsz asid vaddr pptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_page_def)
  apply (rule hoare_pre)
   apply (wpc | wp | strengthen imp_consequent)+
   apply ((wp store_pde_invs store_pte_invs unlessE_wp do_machine_op_global_refs_inv get_pde_wp
             hoare_vcg_all_lift find_vspace_for_asid_lots get_pte_wp store_pdpte_invs get_pdpte_wp
             hoare_vcg_all_liftE_R
        | wpc | simp add: flush_all_def pdpte_ref_pages_def if_apply_def2
        | strengthen not_in_global_refs_vs_lookup
                     not_in_global_refs_vs_lookup invs_valid_vs_lookup
                      invs_valid_global_refs
           invs_arch_state invs_valid_global_objs | clarsimp simp: conj_comms
        | wp (once) hoare_drop_imps)+)
  apply (auto simp: vspace_at_asid_def is_aligned_pml4[simplified] invs_vspace_objs
                    invs_psp_aligned lookup_pml4_slot_eq pml4e_ref_def)
  done

lemma unmap_page_unmapped:
  "\<lbrace>pspace_aligned and valid_vspace_objs and data_at sz pptr and valid_arch_state and
    valid_objs and (\<lambda>s. valid_asid_table (x64_asid_table (arch_state s)) s) and
    K ((sz = X64SmallPage \<longrightarrow> ref =
             [VSRef ((vaddr >> 12) && mask 9) (Some APageTable),
              VSRef ((vaddr >> 21) && mask 9) (Some APageDirectory),
              VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
              VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
              VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
              VSRef (ucast (asid_high_bits_of asid)) None]) \<and>
       (sz = X64LargePage \<longrightarrow> ref =
             [VSRef ((vaddr >> 21) && mask 9) (Some APageDirectory),
              VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
              VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
              VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
              VSRef (ucast (asid_high_bits_of asid)) None]) \<and>
       (sz = X64HugePage \<longrightarrow> ref =
             [VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
              VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
              VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool),
              VSRef (ucast (asid_high_bits_of asid)) None]) \<and>
        p = pptr \<and> vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
  unmap_page sz asid vaddr pptr
  \<lbrace>\<lambda>rv s. \<not> (ref \<unrhd> p) s\<rbrace>"
  apply (rule hoare_gen_asm, clarsimp)
  apply (cases sz; simp)
    by (wpsimp wp: unmap_page_vs_lookup_pages_small unmap_page_vs_lookup_pages_large
                      unmap_page_vs_lookup_pages_huge)+

lemma set_cap_obj_at_vs_refs_pages[wp]:
  "set_cap p cap \<lbrace>obj_at (\<lambda>ko. vs_refs_pages ko = {}) ptr\<rbrace>"
  by (wpsimp wp: set_cap.aobj_at simp: vs_refs_pages_empty.arch_only)

lemmas invs_implies =
  invs_equal_kernel_mappings
  invs_arch_state
  invs_valid_asid_map
  invs_valid_global_objs
  invs_valid_ioports
  invs_valid_vs_lookup
  invs_vspace_objs
  invs_psp_aligned
  invs_distinct
  invs_cur
  invs_iflive
  invs_ifunsafe
  invs_valid_global_refs
  invs_valid_idle
  invs_valid_irq_node
  invs_valid_irq_states
  invs_mdb
  invs_valid_objs
  invs_valid_pspace
  invs_valid_reply_caps
  invs_valid_reply_masters
  invs_valid_stateI
  invs_zombies
  invs_unique_table_caps
  invs_unique_refs
  invs_hyp_sym_refs
  invs_sym_refs
  invs_valid_asid_table
  tcb_at_invs
  invs_valid_kernel_mappings

lemma vs_cap_ref_None:
  "vs_cap_ref (ArchObjectCap (PageCap dev pg_ptr rghts maptype pg_sz mapdata)) = None \<longleftrightarrow> mapdata = None"
  by (cases mapdata; clarsimp simp: vs_cap_ref_def split: vmpage_size.splits)

lemma perform_page_invs [wp]:
  "\<lbrace>invs and valid_page_inv page_inv\<rbrace> perform_page_invocation page_inv \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  apply (cases page_inv, simp_all)
    \<comment> \<open>PageMap\<close>
    apply (rename_tac cap cslot_ptr sum)
    apply clarsimp
    apply (rule hoare_pre)
     apply (wpsimp wp: store_pte_invs store_pde_invs store_pdpte_invs hoare_vcg_const_imp_lift
                       hoare_vcg_all_lift set_cap_arch_obj arch_update_cap_invs_map
                 simp: pte_check_if_mapped_def pde_check_if_mapped_def
             simp_del: fun_upd_apply split_paired_Ex)
        apply (wp set_cap_cte_wp_at_ex hoare_vcg_imp_lift hoare_vcg_all_lift arch_update_cap_invs_map
                  set_cap.aobj_at[OF vs_refs_pages_empty.arch_only] | wps)+
    apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state valid_slots_def is_cap_simps
                          parent_for_refs_def empty_refs_def same_refs_def pt_bits_def
                          is_arch_update_def cap_master_cap_def
                   split: vm_page_entry.splits
                simp del: split_paired_Ex split_paired_All
           | strengthen not_in_global_refs_vs_lookup invs_valid_global_refs invs_arch_state
             invs_valid_vs_lookup invs_valid_global_objs)+
      apply (rule conjI, fastforce)
      apply (intro conjI impI allI)
        apply (clarsimp simp del: split_paired_Ex split_paired_All)
        apply (frule(2) unique_table_caps_ptD[OF _ _ _ _ _ _ invs_unique_table_caps],
               simp add: is_cap_simps, fastforce simp: is_cap_simps)
          apply (clarsimp dest!: caps_of_state_valid[OF _ invs_valid_objs]
                                 is_aligned_pt[OF _ invs_psp_aligned]
                           simp: obj_refs_def valid_cap_def pt_bits_def)
         apply simp
        apply clarsimp
       apply (rule ref_is_unique[OF  _ vs_lookup_vs_lookup_pagesI reachable_page_table_not_global])
                     apply ((fastforce simp: local.invs_valid_kernel_mappings
                                       elim: valid_objs_caps[OF invs_valid_objs])+)[16]
     apply (drule_tac x = ref in spec)
     apply (clarsimp simp: vs_cap_ref_def pde_ref_pages_def split: pde.splits)
     apply (clarsimp simp: valid_pde_def split: pde.splits
                    split: vmpage_size.splits option.split_asm pde.splits)
      apply (intro conjI impI allI)
         apply fastforce
        apply (clarsimp simp del: split_paired_Ex split_paired_All)
        apply (frule(2) unique_table_caps_pdD[OF _ _ _ _ _ _ invs_unique_table_caps],
               simp add: is_cap_simps, fastforce simp: is_cap_simps)
          apply (clarsimp dest!: caps_of_state_valid[OF _ invs_valid_objs] is_aligned_pd[OF _ invs_psp_aligned]
                           simp: obj_refs_def valid_cap_def pt_bits_def)
         apply simp
        apply clarsimp
       apply (rule ref_is_unique[OF  _ vs_lookup_vs_lookup_pagesI reachable_page_table_not_global])
                     apply ((fastforce simp: local.invs_valid_kernel_mappings
                                       elim: valid_objs_caps[OF invs_valid_objs])+)[16]
      apply (frule(1) caps_of_state_valid[OF _ invs_valid_objs])
      apply (match premises in P: \<open>caps_of_state _ _ = Some (ArchObjectCap (PageDirectoryCap _ _))\<close>
              \<Rightarrow> \<open>rule revcut_rl[OF valid_global_refsD2[OF P]]\<close>, fastforce)
      apply (clarsimp dest!: is_aligned_pd[OF _ invs_psp_aligned]
                       simp: cap_range_def valid_cap_def)
     apply (simp add: empty_ref_pageD)
     apply (match premises in P: \<open>caps_of_state _ _ = Some (ArchObjectCap (PageDirectoryCap _ _))\<close>
             \<Rightarrow> \<open>rule revcut_rl[OF valid_global_refsD2[OF P]]\<close>, fastforce)
     apply (clarsimp dest!: is_aligned_pd[OF _ invs_psp_aligned]
                      simp: cap_range_def valid_cap_def)
     apply (rule conjI)
      apply (rename_tac pd_cap_cnode pd_cap_idx pd_asid pd_map_data pg_rghts pg_map_ty
                        map_asid map_vaddr pde_paddr pde_attrs pde_rghts pg_asid pg_vaddr)
      apply (intro allI impI, rename_tac pd_cap_cnode' pd_cap_idx' pd_cap')
      apply (case_tac pd_cap'; clarsimp; rename_tac pd_acap'; case_tac pd_acap'; clarsimp)
      apply (frule_tac ptr="(pd_cap_cnode, pd_cap_idx)" and ptr'="(pd_cap_cnode', pd_cap_idx')"
             in unique_table_capsD[OF invs_unique_table_caps]; assumption?; clarsimp simp: is_cap_simps)
     apply (clarsimp, frule (1) vs_lookup_invs_ref_is_unique[OF vs_lookup_vs_lookup_pagesI]
            ; assumption?; clarsimp)
    apply (rule conjI, fastforce)
    apply (clarsimp dest!: empty_refs_pageCapD)
    apply (intro conjI impI allI)
      apply (clarsimp simp del: split_paired_Ex split_paired_All)
      apply (frule(2) unique_table_caps_pdptD[OF _ _ _ _ _ _ invs_unique_table_caps],
             simp add: is_cap_simps, fastforce simp: is_cap_simps)
        apply (clarsimp dest!: caps_of_state_valid[OF _ invs_valid_objs]
                               is_aligned_pdpt[OF _ invs_psp_aligned]
                         simp: obj_refs_def valid_cap_def pdpt_bits_def)
       apply simp
      apply clarsimp
     apply (rule ref_is_unique[OF _ vs_lookup_vs_lookup_pagesI reachable_page_table_not_global])
                   apply ((fastforce simp: local.invs_valid_kernel_mappings
                                     elim: valid_objs_caps[OF invs_valid_objs])+)[16]
    apply (frule(1) caps_of_state_valid[
                      OF _ invs_valid_objs,
                      where c = "(ArchObjectCap (PDPointerTableCap pc asid))" for pc asid])
    apply (drule valid_global_refsD2[
                   where cap = "(ArchObjectCap (PDPointerTableCap pc asid))" for pc asid], fastforce)
    apply (clarsimp dest!: is_aligned_pdpt[OF _ invs_psp_aligned]
                     simp: cap_range_def valid_cap_def cap_aligned_def)
  \<comment> \<open>PageUnmap\<close>
   apply (rename_tac arch_cap cslot_ptr)
   apply (rule hoare_pre)
    apply (wp dmo_invs arch_update_cap_invs_unmap_page get_cap_wp
         | wpc | simp add: perform_page_invocation_unmap_def)+
        apply (rule_tac Q'="\<lambda>_ s. invs s \<and>
                                 cte_wp_at (\<lambda>c. is_pg_cap c \<and>
                                   (\<forall>ref. vs_cap_ref c = Some ref \<longrightarrow>
                                          \<not> (ref \<unrhd> obj_ref_of c) s)) cslot_ptr s"
                     in hoare_strengthen_post)
         prefer 2
         apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps
                               update_map_data_def
                               is_arch_update_def cap_master_cap_simps)
         apply (drule caps_of_state_valid, fastforce)
         apply (clarsimp simp: valid_cap_def cap_aligned_def vs_cap_ref_def
                        split: option.splits vmpage_size.splits cap.splits)
        apply (simp add: cte_wp_at_caps_of_state)
        apply (wp unmap_page_invs hoare_vcg_ex_lift hoare_vcg_all_lift hoare_vcg_imp_lift
                  unmap_page_unmapped)+
   apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps is_arch_update_def
                         update_map_data_def cap_rights_update_def
                         acap_rights_update_def)
   using valid_validate_vm_rights[simplified valid_vm_rights_def]
   apply (auto simp: valid_cap_simps cap_aligned_def mask_def vs_cap_ref_def data_at_def
              split: vmpage_size.splits option.splits if_splits)[1]
  apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state valid_cap_def mask_def)
  done


lemma not_kernel_slot_not_global_pml4:
  "\<lbrakk>pml4e_ref (pml4 x) = Some p; x \<notin> kernel_mapping_slots;
    kheap s p' = Some (ArchObj (PageMapL4 pml4)); valid_kernel_mappings s\<rbrakk>
   \<Longrightarrow> p \<notin> set (second_level_tables (arch_state s))"
  apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pm_def)
   apply (drule_tac x="ArchObj (PageMapL4 pml4)" in bspec)
    apply ((fastforce simp: ran_def)+)[1]
   apply (simp split: arch_kernel_obj.split_asm)
  done

lemma valid_table_caps_asid_upd:
  "\<lbrakk>invs s; typ_at (AArch AASIDPool) p s\<rbrakk>
  \<Longrightarrow> valid_table_caps_aobj (caps_of_state s) (arch_state s) (ArchObj (ASIDPool (pool(asid_low_bits_of asid := pml4base)))) p"
  by (fastforce dest!: caps_of_state_valid_cap[OF _ invs_valid_objs]
                 simp: valid_table_caps_aobj_def is_cap_simps valid_cap_simps obj_at_def)

lemma vs_refs_of_set_diff:
  "set_diff (vs_refs (ArchObj (ASIDPool (pool(ucast asid := pml4base))))) (vs_refs (ArchObj (ASIDPool pool)))
   \<subseteq> (case pml4base of Some a \<Rightarrow> {(VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), a)} | _ \<Rightarrow> {})
     \<union> (case pool (ucast asid) of Some a \<Rightarrow> {(VSRef (ucast (asid_low_bits_of asid)) (Some AASIDPool), a)} | _ \<Rightarrow> {})"
  by (fastforce simp: set_diff_def vs_refs_def graph_of_def image_def ucast_ucast_id asid_low_bits_of_def
               split: if_split_asm)

lemma asid_lvl_lookup1D:
  "([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p) s \<Longrightarrow> ([VSRef (ucast (asid_high_bits_of asid)) None], p) \<in> vs_asid_refs (x64_asid_table (arch_state s))"
  apply (clarsimp simp: vs_lookup_def)
  apply (erule rtranclE)
   apply clarsimp
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def vs_lookup1_def)
  apply (clarsimp dest!: wellformed_lookup.lookup1_is_append[OF vs_lookup1_is_wellformed_lookup])
  done

lemma valid_kernel_mappings_if_pm_asid:
  "\<lbrakk>valid_kernel_mappings s; kheap s p = Some (ArchObj (ASIDPool pool))\<rbrakk>
    \<Longrightarrow> valid_kernel_mappings_if_pm (set (second_level_tables (arch_state s))) (ArchObj (ASIDPool (pool(asid_low_bits_of asid := pml4base))))"
  by (fastforce simp: pml4e_ref_def valid_kernel_mappings_if_pm_def valid_kernel_mappings_def
                  dest!: bspec split: option.split_asm pml4e.split_asm)

lemma valid_global_objs_upd_invalid_asid_slot:
  "\<lbrakk>valid_global_objs s; kheap s p = Some (ArchObj (ASIDPool pool))\<rbrakk>
    \<Longrightarrow> valid_global_objs_upd p (ASIDPool (pool(slot := e))) (arch_state s)"
  by (clarsimp simp: valid_global_objs_def valid_global_objs_upd_def obj_at_def valid_ao_at_def
                     empty_table_def global_refs_def)


lemma refs_diff_empty_simps_vslookup1_asid[simp]:
  "kheap s p = Some (ArchObj (ASIDPool pool)) \<Longrightarrow>
    (refs_diff vs_lookup1_on_heap_obj (ASIDPool (pool(a := b))) p s) = (case b of None \<Rightarrow> {}
     | Some x \<Rightarrow>
         if b = (pool a)
         then {}
         else {([VSRef (ucast a)
                  (Some AASIDPool)],
                x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup1_on_heap_obj_def lookup_refs_def vs_refs_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma refs_diff_empty_simps_vslookup_pages1_asid[simp]:
  "kheap s p = Some (ArchObj (ASIDPool pool)) \<Longrightarrow>
    (refs_diff vs_lookup_pages1_on_heap_obj (ASIDPool (pool(a := b))) p s) = (case b of None \<Rightarrow> {}
     | Some x \<Rightarrow>
         if b = (pool a)
         then {}
         else {([VSRef (ucast a)
                  (Some AASIDPool)],
                x)})"
  apply (clarsimp simp: refs_diff_def vs_lookup_pages1_on_heap_obj_def lookup_refs_def vs_refs_pages_def)
  apply (auto simp: graph_of_def image_def split: if_splits option.splits)
  done

lemma asid_is_zeroI:
  "\<lbrakk> ucast (asid_low_bits_of asid) = (0 :: word64);
     ucast (asid_high_bits_of asid) = (0 :: word64);
     asid_wf asid \<rbrakk> \<Longrightarrow> asid = 0"
  apply (clarsimp simp: bit_simps asid_bits_of_defs asid_low_bits_def asid_bits_def mask_def asid_wf_def)
  apply word_bitwise
  apply simp
  done

lemma store_asid_pool_entry_invs:
  "\<lbrace>invs and K (0 < asid \<and> asid_wf asid) and
    (\<lambda>s. case pml4base of None \<Rightarrow> True
    | Some ptr \<Rightarrow> obj_at (empty_table (set (second_level_tables (arch_state s)))) ptr s
          \<and> typ_at (AArch APageMapL4) ptr s \<and> (\<forall>pool. ko_at (ArchObj (ASIDPool pool)) p s \<longrightarrow> pool (asid_low_bits_of asid) = None)
          \<and> p \<notin> set (second_level_tables (arch_state s))
          \<and> (\<exists>slot. cte_wp_at (\<lambda>cap. is_pml4_cap cap \<and>  ptr \<in> obj_refs cap \<and> cap_asid cap = Some asid) slot s))
    and  [VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> p
   \<rbrace>
  store_asid_pool_entry p asid pml4base \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding store_asid_pool_entry_def
  apply (simp add: set_arch_obj_simps)
  apply wp
  apply simp
  apply (intro impI allI conjI valid_table_caps_aobj_upd_invalid_pml4e invs_valid_table_caps , simp_all add: obj_at_def)
             apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask a_type_simps
                            split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                    | intro valid_table_caps_asid_upd)+
           apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                          split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs
                     | intro valid_kernel_mappings_if_pm_asid invs_valid_kernel_mappings valid_global_objs_upd_invalid_asid_slot
                     | fastforce)+
         apply (fastforce dest!: valid_vspace_obj_from_invs ran_del_subset simp: obj_at_def)+
        apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                        split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs)
        apply (rule ccontr)
        apply (erule(1) unmapped_cap_lookup_refs_empty[OF _ rtrancl_into_trancl1])
         apply (drule wellformed_lookup.lookup1_cut[OF vs_lookup1_is_wellformed_lookup],fastforce,fastforce)
       apply (clarsimp simp: aa_type_simps obj_at_def split: option.split_asm if_split_asm)
      apply (clarsimp simp: obj_at_def aa_type_simps aobj_upd_invalid_slots_simps ucast_ucast_mask
                     split: if_split_asm option.split_asm dest:valid_vspace_obj_from_invs valid_obj_from_invs)
      apply (rule ccontr)
      apply (erule unmapped_cap_lookup_refs_pages_empty[OF _ ])
       apply (erule rtrancl_into_trancl1)
       apply (drule wellformed_lookup.lookup1_cut[OF vs_lookup_pages1_is_wellformed_lookup],fastforce,fastforce)
     apply (clarsimp split: option.split_asm if_split_asm simp: aa_type_simps obj_at_def)
    apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def obj_at_def)
    apply (frule(2) empty_table_lookup_refs_refl)
    apply (clarsimp simp: empty_table_def)
   apply (clarsimp split: if_split_asm option.split_asm dest!:ref_pages_Some simp: lookupable_refs_def obj_at_def)
   apply (frule(2) empty_table_lookup_refs_pages_refl)
   apply clarsimp
   apply (drule vs_lookup_vs_lookup_pagesI')
      apply (clarsimp simp: obj_at_def aa_type_simps a_type_simps)
     apply force
    apply force
   apply (drule(1) ref_is_unique)
         apply force+
    apply (clarsimp dest!: invs_valid_objs valid_objs_caps)
   apply clarsimp
   apply (frule (2) asid_is_zeroI, simp)
  apply (clarsimp simp: lookupable_refs_def obj_at_def split: option.split_asm if_split_asm)
  apply (frule(2) empty_table_lookup_refs_pages_refl)
  apply clarsimp
  apply (drule vs_lookup_vs_lookup_pagesI')
     apply (clarsimp simp: obj_at_def aa_type_simps a_type_simps)
    apply force
   apply force
  apply (drule(1) ref_is_unique)
        apply force+
   apply (clarsimp dest!: invs_valid_objs valid_objs_caps)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
  apply (intro exI conjI)
    apply assumption
   apply (fastforce simp: vs_cap_ref_def cap_asid_def split: option.split_asm)+
  done

lemma valid_table_caps_pml4D:
  "\<lbrakk> caps_of_state s p = Some (ArchObjectCap (PML4Cap pool None));
     valid_table_caps s \<rbrakk> \<Longrightarrow>
    obj_at (empty_table (set (second_level_tables (arch_state s)))) pool s"
  apply (clarsimp simp: valid_table_caps_def simp del: split_paired_All)
  apply (erule allE)+
  apply (erule (1) impE)
  apply (fastforce simp add: is_cap_simps cap_asid_def)
  done

lemma perform_asid_pool_invs [wp]:
  "\<lbrace>invs and valid_apinv api\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: perform_asid_pool_invocation_def split: asid_pool_invocation.splits)
  apply (wp arch_update_cap_invs_map store_asid_pool_entry_invs
            get_cap_wp set_cap_typ_at empty_table_lift[OF _ hoare_weaken_pre]
            set_cap_obj_at_other hoare_vcg_all_lift set_cap_cte_wp_at_ex
         | wpc | simp del: split_paired_Ex)+
  apply (rename_tac asid pml4base a b s)
  apply (clarsimp simp: valid_apinv_def cap_asid_def cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps vs_cap_ref_simps
                 split: option.split_asm)
  apply (frule caps_of_state_cteD)
  apply (drule cte_wp_valid_cap, fastforce)
  apply (frule valid_table_caps_pml4D)
   apply force
  apply (simp add: valid_cap_def cap_aligned_def obj_at_def)
  apply (drule caps_of_state_cteD)
  apply (clarsimp simp: obj_at_def cte_wp_at_cases a_type_def second_level_tables_def)
  apply (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits if_split_asm)
  apply (fastforce dest!: invs_valid_global_objs simp: valid_global_objs_def obj_at_def)
  done

lemma invs_aligned_pml4D:
  "\<lbrakk> pspace_aligned s; valid_arch_state s \<rbrakk> \<Longrightarrow> is_aligned (x64_global_pml4 (arch_state s)) pml4_bits"
  apply (clarsimp simp: valid_arch_state_def)
  apply (drule (1) is_aligned_pml4)
  apply (simp add: pml4_bits_def pageBits_def)
  done

(* is this the right way? we need this fact globally but it's proven with
   X64 defns. *)
lemma set_cap_valid_arch_caps_simple:
  "\<lbrace>\<lambda>s. valid_arch_caps s
      \<and> valid_objs s
      \<and> cte_wp_at (Not o is_arch_cap) ptr s
      \<and> (obj_refs cap \<noteq> {} \<longrightarrow> s \<turnstile> cap)
      \<and> \<not> (is_arch_cap cap)\<rbrace>
     set_cap cap ptr
   \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (wp set_cap_valid_arch_caps)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid_cap)
  apply (rename_tac cap')
  apply (subgoal_tac "\<forall>x \<in> {cap, cap'}. \<not> is_pt_cap x \<and> \<not> X64.is_pd_cap x")
   apply simp
   apply (rule conjI)
    apply (clarsimp simp: vs_cap_ref_def is_cap_simps split: cap.splits)
   apply (erule impCE)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state is_cap_simps
                          obj_ref_none_no_asid)
   apply (clarsimp simp: is_cap_simps)
   apply (rule no_cap_to_obj_with_diff_ref_triv, simp_all)
   apply (rule ccontr, clarsimp simp: table_cap_ref_def is_cap_simps)
  apply (auto simp: is_cap_simps table_cap_ref_def split: cap.splits)
  done

crunch in8, in16, in32, out8, out16, out32
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"

lemmas in8_irq_masks = no_irq[OF no_irq_in8]
lemmas in16_irq_masks = no_irq[OF no_irq_in16]
lemmas in32_irq_masks = no_irq[OF no_irq_in32]

lemmas out8_irq_masks = no_irq[OF no_irq_out8]
lemmas out16_irq_masks = no_irq[OF no_irq_out16]
lemmas out32_irq_masks = no_irq[OF no_irq_out32]

lemma dmo_in8[wp]: "\<lbrace>invs\<rbrace> do_machine_op (in8 irq) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: in8_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ in8_irq_masks])
  done

lemma dmo_in16[wp]: "\<lbrace>invs\<rbrace> do_machine_op (in16 irq) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: in16_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ in16_irq_masks])
  done

lemma dmo_in32[wp]: "\<lbrace>invs\<rbrace> do_machine_op (in32 irq) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: in32_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ in32_irq_masks])
  done

lemma dmo_out8[wp]: "\<lbrace>invs\<rbrace> do_machine_op (out8 irq b) \<lbrace>\<lambda>y. invs\<rbrace>"
  by (clarsimp simp: out8_def dmo_machine_op_lift_invs)

lemma dmo_out16[wp]: "\<lbrace>invs\<rbrace> do_machine_op (out16 irq b) \<lbrace>\<lambda>y. invs\<rbrace>"
  by (clarsimp simp: out16_def dmo_machine_op_lift_invs)

lemma dmo_out32[wp]: "\<lbrace>invs\<rbrace> do_machine_op (out32 irq b) \<lbrace>\<lambda>y. invs\<rbrace>"
  by (clarsimp simp: out32_def dmo_machine_op_lift_invs)

lemma perform_io_port_invocation_invs[wp]:
  "\<lbrace>invs\<rbrace> perform_io_port_invocation iopinv \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: perform_io_port_invocation_def)
  apply (rule hoare_pre)
   apply (wpsimp simp: port_in_def port_out_def)
  apply (clarsimp simp: tcb_at_invs)
  done

lemma user_vtop_mask: "user_vtop = mask 47"
  by (simp add: user_vtop_def pptrUserTop_def mask_def)

lemma user_vtop_le: "p && user_vtop \<le> mask 47"
  by (simp add: user_vtop_mask word_and_le1)

lemma canonical_address_user_vtop_p: "p = p' && user_vtop \<Longrightarrow> canonical_address p"
  by (simp add: canonical_address_range user_vtop_le)

lemmas canonical_address_user_vtop [simp] = canonical_address_user_vtop_p[OF refl]

lemma user_vtop_less_pptr_base [simp]: "p && user_vtop < pptr_base"
  by (rule le_less_trans[OF user_vtop_le];
      simp add: mask_def user_vtop_def pptr_base_def pptrBase_def)

lemma user_vtop_kernel_mapping_slots:
  "ucast (get_pml4_index (p && user_vtop)) \<notin> kernel_mapping_slots"
  by (rule kernel_base_kernel_mapping_slots; simp)

lemma kernel_vsrefs_kernel_mapping_slots':
  "VSRef (get_pml4_index p) (Some APageMapL4) \<in> kernel_vsrefs
    \<longleftrightarrow> ucast (p >> pml4_shift_bits) \<in> kernel_mapping_slots"
  using kernel_vsrefs_kernel_mapping_slots[of "p >> (pml4_shift_bits - word_size_bits)", symmetric]
  apply (clarsimp simp: shiftr_over_and_dist get_pml4_index_def bit_simps shiftr_mask2 shiftr_shiftr)
  apply (subst ucast_mask_drop; clarsimp)
  done

lemma user_vtop_kernel_vsrefs:
  "VSRef (get_pml4_index (p && user_vtop)) (Some APageMapL4) \<notin> kernel_vsrefs"
  using user_vtop_kernel_mapping_slots kernel_vsrefs_kernel_mapping_slots'
  by (simp add: get_pml4_index_def bit_simps ucast_mask_drop)

context
  fixes c :: cap
  assumes vsc: "is_vspace_table_cap c"
begin

end

context begin

private lemma is_vspace_table_cap:
  "is_vspace_table_cap (ArchObjectCap (PageTableCap ptr mapped))"
  "is_vspace_table_cap (ArchObjectCap (PageDirectoryCap ptr mapped))"
  "is_vspace_table_cap (ArchObjectCap (PDPointerTableCap ptr mapped))"
  "is_vspace_table_cap (ArchObjectCap (PML4Cap ptr asid))"
  by (auto simp: is_cap_simps)

end

lemma valid_vspace_obj_default:
  assumes tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  shows "ArchObj ao = default_object ty dev us d \<Longrightarrow> valid_vspace_obj ao s'"
  apply (cases ty, simp_all add: default_object_def tyunt)
  apply (simp add: valid_vspace_obj_default')
  done

end
end
