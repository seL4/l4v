(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Retype refinement
*)

theory Retype_AI
imports VSpace_AI
begin

lemmas atLeastAtMost_simps =
  atLeastatMost_subset_iff atLeastLessThan_iff Int_atLeastAtMost atLeastatMost_empty_iff
  atLeastAtMost_iff split_paired_Ex

abbreviation "up_aligned_area ptr sz \<equiv> {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)}"
abbreviation "down_aligned_area ptr sz \<equiv> {(ptr && ~~ mask sz) + (2 ^ sz - 1) .. ptr}"

context begin interpretation Arch .
requalify_facts
  valid_vspace_obj_default
requalify_consts
  clearMemory
  clearMemoryVM
end


locale Retype_AI_clearMemoryVM =
  assumes clearMemoryVM_return [simp]: "\<And> a b. clearMemoryVM a b = return ()"

context Retype_AI_clearMemoryVM begin
lemmas clearMemoryVM_return_raw = clearMemoryVM_return[abs_def]
end


lemma default_object_tcbE:
  "\<lbrakk> default_object ty dev us p = TCB tcb; ty \<noteq> Untyped;
   \<lbrakk> tcb = default_tcb p; ty = Structures_A.TCBObject \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding default_object_def by (cases ty, auto)


locale Retype_AI_slot_bits =
  assumes slot_bits_def2: "slot_bits = cte_level_bits"
     and  arch_kobj_size_cong:
            "\<And>a a1 c c1. \<lbrakk>a = a1; c=c1\<rbrakk> \<Longrightarrow> arch_kobj_size (default_arch_object a b c)
                 = arch_kobj_size (default_arch_object a1 b1 c1)"


lemma (in Retype_AI_slot_bits) obj_bits_cong:
  "\<lbrakk>a = a1; c=c1\<rbrakk> \<Longrightarrow> obj_bits (default_object a b c d) = obj_bits (default_object a1 b1 c1 d1)"
  by (simp add: default_object_def arch_kobj_size_cong
         split: if_splits apiobject_type.splits)

lemma (in Retype_AI_slot_bits) obj_bits_api_default_object:
  "\<lbrakk> ty \<noteq> Untyped; ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us\<rbrakk> \<Longrightarrow> obj_bits_api ty us = obj_bits (default_object ty dev us p)"
  unfolding obj_bits_api_def default_object_def
  by (cases ty)
     (simp_all add: slot_bits_def2 arch_kobj_size_cong wf_empty_bits)


lemma obj_bits_api_default_CapTableObject:
  "obj_bits (default_object Structures_A.apiobject_type.CapTableObject dev us p)
  = cte_level_bits + us"
  by (simp add: default_object_def wf_empty_bits)


lemma empty_cnode_dom:
  "x \<in> dom (empty_cnode n) \<Longrightarrow> length x = n"
  unfolding dom_def empty_cnode_def by (simp split: if_split_asm)


context Retype_AI_slot_bits begin

lemma obj_bits_api_def2:
  "type = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> obj_size_bits \<Longrightarrow>
    obj_bits_api type obj_size_bits =
   (case type of Structures_A.Untyped \<Rightarrow> obj_size_bits
           | _ \<Rightarrow> obj_bits (default_object type False obj_size_bits dm))"
  by (simp add: obj_bits_api_def default_object_def
                wf_empty_bits dom_empty_cnode ex_with_length
                slot_bits_def2
         split: apiobject_type.split)

lemma obj_bits_api_def3:
  "type = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> obj_size_bits \<Longrightarrow>
   obj_bits_api type obj_size_bits =
   (if type = Structures_A.Untyped then obj_size_bits
     else obj_bits (default_object type False obj_size_bits dm))"
  by (simp add: obj_bits_api_def default_object_def
                wf_empty_bits dom_empty_cnode ex_with_length
                slot_bits_def2
         split: apiobject_type.split)

lemma obj_bits_api_def4:
  "type = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> obj_size_bits \<Longrightarrow>
   obj_bits_api type obj_size_bits =
   (if type = Structures_A.Untyped then obj_size_bits
     else obj_bits (default_object type True obj_size_bits dm))"
  by (simp add: obj_bits_api_def default_object_def arch_kobj_size_cong
                wf_empty_bits dom_empty_cnode ex_with_length
                slot_bits_def2
         split: apiobject_type.split)

lemma obj_bits_dev_irr:
  "\<lbrakk>ty \<noteq> Untyped; ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us\<rbrakk>
     \<Longrightarrow> obj_bits (default_object ty dev us p) = obj_bits_api ty us"
  by (simp add: obj_bits_api_def3[where dm=0] cong: obj_bits_cong)

lemma default_obj_range:
  "\<lbrakk>ty \<noteq> Untyped; ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us\<rbrakk> \<Longrightarrow>
  obj_range p (default_object ty dev us dm) = {p..p + 2 ^ (obj_bits_api ty us) - 1}"
  by (simp add: obj_range_def obj_bits_dev_irr)

end


definition
  "retype_addrs \<equiv> \<lambda>(ptr' :: obj_ref) ty n us. map (\<lambda>p. ptr_add ptr' (p * 2 ^ obj_bits_api ty us))
                                           [0..< n]"


lemma retype_addrs_base [simp]:
  "0 < n \<Longrightarrow> x \<in> set (retype_addrs x ty n us)"
  unfolding retype_addrs_def
  apply (simp add: ptr_add_def)
  apply (rule image_eqI [where x = 0])
   apply simp
  apply (simp add: power_sub[symmetric])
  done


lemma retype_addrs_aligned:
  assumes xin: "x \<in> set (retype_addrs ptr ty n us)"
  and      al: "is_aligned ptr (obj_bits_api ty us)"
  and      nv: "sz < word_bits"
  and     oav: "obj_bits_api ty us \<le> sz"
  shows   "is_aligned x (obj_bits_api ty us)"
  using xin unfolding retype_addrs_def ptr_add_def
  apply (clarsimp simp: word_unat_power [symmetric])
  apply (subst mult.commute, subst shiftl_t2n [symmetric])
  apply (rule aligned_add_aligned[OF al is_aligned_shift])
   apply (insert assms)
   apply simp+
  done


lemma (in pspace_update_eq) pspace_no_overlap_update [simp]:
  "pspace_no_overlap S (f s) = pspace_no_overlap S s"
  by (simp add: pspace_no_overlap_def pspace)



lemmas machine_word_plus_mono_right_split = word_plus_mono_right_split[where 'a=machine_word_len, folded word_bits_def]


\<comment>\<open>
  Sets up assumptions for working with an aligned subregion of an aligned region.

  Treats `ptr` as an `sbit`-aligned pointer into an `sz`-aligned, `2 ^ sz`-long region.
  Then, `n` is the index of a `2 ^ sbit`-sized region between `ptr` and the end of the
  larger region.

  Here is a graphical example where `sz - sbit = 2`:

  sz-aligned
  v
  |<----------------------------2 ^ sz--------------------------->|
  |
  |                              ptr
  |<---2 ^ sbit-->|               v
  |---------------|---------------|---------------|---------------|
                                n = 0           n = 1           n = 2
                            sbit-aligned

  Together, `ptr` and `n` specify a "subslice" of the larger region. Notice that `n`
  indexes the *end* of the subslice/subregion; equivalently, `n` is the *length* of
  the subregion.
\<close>
locale range_cover =
  fixes ptr :: "'a :: len word"
  and   sz sbit n
  assumes aligned: "is_aligned ptr sbit"
  and sz:"sz< len_of TYPE('a)" "sbit \<le> sz" "n + unat (ptr && mask sz >> sbit) \<le> 2 ^ (sz - sbit)"


context range_cover begin

lemma range_cover_compare_bound:
 "n * 2 ^ sbit + unat (ptr && mask sz) \<le> 2 ^ sz"
proof -
  have mask_before_neg_mask: "(ptr && mask sz) && ~~ mask sbit = ptr && mask sz"
    using aligned sz
    by (simp add:mask_twice is_aligned_mask mask_out_sub_mask min_def)
  show ?thesis using aligned sz
  apply (drule_tac i = "a +b" for a b in Nat.mult_le_mono[where k = "2^sbit",OF _ le_refl])
  apply (subst (asm) add_mult_distrib)
  apply (clarsimp simp: power_add[symmetric])
  apply (subst (asm) unat_shiftl_absorb[where p = "sz - sbit"])
    apply (rule less_imp_le)
    apply (rule shiftr_less_t2n)
    apply (rule less_le_trans)
     apply (rule and_mask_less')
     apply (simp add:word_bits_def)
    apply (rule two_power_increasing)
      apply simp
    apply (simp add:word_bits_def field_simps)
   apply simp
  apply (subst (asm) mult.commute[where b = "2^sbit"],
         subst (asm) shiftl_t2n[symmetric])
  apply (subst (asm) and_not_mask[symmetric])
  apply (simp add:mask_before_neg_mask)
  done
qed


lemma range_cover_compare:
  assumes pointer:"p < n"
  shows "unat (ptr && mask sz) + unat (((of_nat p) :: 'a :: len word) * 2 ^ sbit) < 2 ^ sz"
proof -
  have mask_before_neg_mask: "(ptr && mask sz) && ~~ mask sbit = ptr && mask sz"
    using aligned sz
    by (simp add:mask_twice is_aligned_mask mask_out_sub_mask min_def)

  have absolute_compare:"n * 2 ^ sbit + unat (ptr && mask sz) \<le> 2 ^ sz"
    by (rule range_cover_compare_bound)

  have no_overflow_n:"n * 2^sbit < 2^len_of TYPE('a)"
    using aligned sz
    apply (clarsimp dest!:add_leD1)
    apply (rule le_less_trans)
    apply (drule Nat.mult_le_mono[where i = n and k = "2^sbit",OF _ le_refl])
    apply (clarsimp simp: power_add[symmetric])
     apply (assumption)
    apply clarsimp
    done

  have no_overflow_p:"p * 2^sbit < 2^len_of TYPE('a)"
    apply (rule le_less_trans[OF _ no_overflow_n])
    apply (simp add:pointer less_imp_le)
    done

  show ?thesis
  apply (rule less_le_trans[OF _ absolute_compare])
  apply (subst add.commute)
  apply clarsimp
  apply (case_tac "p = 0")
   apply (insert pointer)
   apply (clarsimp simp: range_cover_def pointer)
   apply (simp add:unat_word_ariths)
   apply (rule le_less_trans[OF mod_less_eq_dividend])
   apply (rule less_le_trans[OF mult_less_mono1[where j = n]])
   apply (cut_tac no_overflow_p)
     apply (drule multi_lessD[OF no_overflow_p],simp)
     apply (clarsimp simp:unat_of_nat word_bits_def)
   using sz
   apply (simp add:unat_gt_0 range_cover_def)
  apply (rule mult_le_mono2)
  apply (rule unat_le_helper)
  apply simp
  done
 qed

lemma no_overflow_n:"n * 2^sbit < 2^len_of TYPE('a)"
  using aligned sz
  apply (clarsimp dest!:add_leD1)
  apply (rule le_less_trans)
  apply (drule Nat.mult_le_mono[where i = n and k = "2^sbit",OF _ le_refl])
  apply (clarsimp simp: power_add[symmetric])
   apply (assumption)
  apply clarsimp
  done

lemma range_cover_n_le:
  "n \<le> 2 ^ (len_of TYPE('a) - sbit)"
  "n \<le> 2 ^ (sz - sbit)"
  using aligned sz
  by (auto elim: le_trans[OF add_leD1])


lemma range_cover_n_less:
  shows weak: "n < 2 ^ len_of TYPE('a)"
  and string: "n < 2 ^ (len_of TYPE('a) - sbit)"
proof -
  show str: "n < 2 ^ (len_of TYPE('a) - sbit)"
    using aligned sz
    by (auto intro: le_less_trans range_cover_n_le(2))

  show "n<2^len_of TYPE('a)"
    using str by (rule less_le_trans) simp
qed


lemma range_cover_le_n_less:
  "p \<le> n \<Longrightarrow> p < 2^ len_of TYPE('a)"
  "p \<le> n \<Longrightarrow> p < 2^ (len_of TYPE('a) - sbit)"
  apply (erule le_less_trans[OF _ range_cover_n_less(1)])
  apply (erule le_less_trans[OF _ range_cover_n_less(2)])
  done


lemma unat_of_nat_n :"unat ((of_nat n):: 'a :: len word) = n"
  using range_cover_n_less
  by (simp add:unat_of_nat)


lemma unat_of_nat_n_shift:
  "gbits \<le> sbit \<Longrightarrow> unat (((of_nat n):: 'a :: len word) << gbits) = (n * 2^ gbits)"
   apply (simp add:shiftl_t2n field_simps)
   apply (subst mult.commute)
   apply (subst unat_mult_power_lem)
     apply (case_tac "gbits = sbit")
      apply (rule le_less_trans[OF range_cover_n_le(2)])
      apply clarsimp
       apply (rule diff_less_mono)
      apply (rule sz)
     apply (rule sz)
    apply (rule le_less_trans[OF range_cover_n_le(1)])
    apply clarsimp
    apply (rule diff_less_mono2)
     apply simp
    using sz
    apply simp
   apply simp
   done


lemma unat_of_nat_shift:
  "\<lbrakk>gbits \<le> sbit;p\<le> n\<rbrakk> \<Longrightarrow> (unat (((of_nat p):: 'a :: len word) * 2 ^ gbits)) = (p * 2^ gbits)"
   apply (subst mult.commute[where a = "of_nat p"])
   apply (subst mult.commute[where a = "p "])
   apply (subst unat_mult_power_lem)
     apply (case_tac "gbits = sbit")
      apply simp
      apply (erule le_less_trans[OF _ range_cover_le_n_less(2) ])
       apply simp
       apply (erule le_less_trans)
     apply (rule less_le_trans[OF range_cover_n_less(2)])
     apply clarsimp
    apply (erule diff_le_mono2)
  apply (simp add:range_cover_def)+
 done


lemma range_cover_base_le:
  "(ptr && mask sz) \<le> (ptr && mask sz) + (of_nat n << sbit)"
  apply (clarsimp simp:no_olen_add_nat shiftl_t2n unat_of_nat_shift field_simps)
  apply (subst add.commute)
  apply (rule le_less_trans[OF range_cover_compare_bound])
  apply (rule less_le_trans[OF power_strict_increasing])
    using sz
    apply simp+
  done

end


lemma range_cover_subset:
  fixes ptr :: "'a :: len word"
  assumes cover:   "range_cover ptr sz sbit n"
  assumes pointer: "p<n"
  assumes not_0:   "n \<noteq> 0"
  shows  "{ptr + of_nat p * 2^sbit .. ptr + of_nat p * 2 ^ sbit + 2 ^ sbit - 1} \<subseteq> {ptr .. ptr + of_nat n * 2 ^ sbit - 1}"
  apply clarsimp
  apply (intro conjI)
  apply (rule word_plus_mono_right_split[OF range_cover.range_cover_compare[OF cover pointer]])
  using cover
  apply (simp add:range_cover_def)
  proof -
    note n_less = range_cover.range_cover_n_less[OF cover]
    have unat_of_nat_m1: "unat (of_nat n - (1 :: 'a :: len word)) < n"
      using not_0 n_less
       by (simp add:unat_of_nat_minus_1)
    have decomp:"of_nat n * 2 ^ sbit = of_nat (n - 1) * 2 ^ sbit + (2 :: 'a :: len word) ^ sbit"
      apply (simp add:distrib_right[where b = "1::'a word",simplified,symmetric])
      using not_0 n_less
      apply (simp add:unat_of_nat_minus_1)
      done
    show "ptr + of_nat p * 2 ^ sbit + 2 ^ sbit - 1 \<le> ptr + of_nat n * 2 ^ sbit - 1"
      using cover
      apply (subst decomp)
      apply (simp add:add.assoc[symmetric])
      apply (simp add:p_assoc_help)
      apply (rule order_trans[OF word_plus_mono_left word_plus_mono_right])
         apply (rule word_plus_mono_right)
          apply (rule word_mult_le_mono1[OF word_of_nat_le])
          apply (insert n_less not_0 pointer)
            apply (simp add:unat_of_nat_minus_1)
           apply (rule p2_gt_0[THEN iffD2])
           apply (simp add:word_bits_def range_cover_def)
          apply (simp only: word_bits_def[symmetric] unat_power_lower range_cover_def)
          apply (clarsimp simp: unat_of_nat_minus_1 )
          apply (rule nat_less_power_trans2[OF range_cover.range_cover_le_n_less(2),OF cover])
          apply (simp add:unat_of_nat_m1 less_imp_le)
         apply (simp add:range_cover_def)
        apply (rule word_plus_mono_right_split[where sz = sz])
        using range_cover.range_cover_compare[OF cover,where p = "unat (of_nat n - (1 :: 'a :: len word))"]
        apply (clarsimp simp:unat_of_nat_m1)
       apply (simp add:range_cover_def)
      apply (rule olen_add_eqv[THEN iffD2])
      apply (subst add.commute[where a = "2^sbit - 1"])
     apply (subst p_assoc_help[symmetric])
     apply (rule is_aligned_no_overflow)
     apply (insert cover)
     apply (clarsimp simp:range_cover_def)
     apply (erule aligned_add_aligned[OF _  is_aligned_mult_triv2])
       apply (simp add:range_cover_def)+
      using is_aligned_add is_aligned_mult_triv2 is_aligned_no_overflow'
      by blast
  qed

lemma range_cover_rel:
  assumes cover: "range_cover ptr sz sbit n"
  assumes le:"sbit' \<le> sbit"
  assumes num_r: "m = 2 ^ (sbit - sbit') * n"
  shows "range_cover ptr sz sbit' m"
  using cover
  apply (clarsimp simp:num_r range_cover_def)
  apply (intro conjI)
    apply (erule is_aligned_weaken[OF _ le])
    apply (erule le_trans[OF le])
    apply (drule is_aligned_weaken[OF _ le])+
    apply (drule mult_le_mono2[where j = "2^(sz-sbit)" and k = "2^(sbit-sbit')"])
    apply (subst (asm) power_add[symmetric])
    apply (clarsimp simp:field_simps le)
    apply (erule le_trans[rotated])
  apply clarsimp
  apply (rule unat_le_helper)
  apply clarsimp
  apply (insert le)
  apply (fold shiftl_t2n)
  apply (simp add: shiftr_shiftl1)
  apply (rule eq_refl[OF is_aligned_neg_mask_eq[symmetric]])
  apply (rule is_aligned_shiftr[OF is_aligned_weaken])
    apply (rule aligned_already_mask[where n = "sbit"])
    apply (insert cover)
    apply (simp add:range_cover_def)
  apply simp
done


lemma retype_addrs_subset_ptr_bits:
  assumes cover: "range_cover ptr sz (obj_bits_api ty us) n"
  shows "set (retype_addrs ptr ty n us) \<subseteq> {ptr .. (ptr &&~~ mask sz) + (2 ^ sz - 1)}"
  apply (clarsimp simp:retype_addrs_def ptr_add_def)
  apply (intro conjI)
    apply (rule word_plus_mono_right_split)
    apply (erule range_cover.range_cover_compare[OF cover])
   using cover
   apply (simp add:range_cover_def)
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
  apply (subst add.commute)
  apply (subst add.assoc)
  apply (rule word_plus_mono_right)
  apply (insert cover)
  apply (drule(1) range_cover.range_cover_compare)
  apply (rule iffD1[OF le_m1_iff_lt,THEN iffD2])
    using cover
    apply (simp add: p2_gt_0 range_cover_def word_bits_def)
   apply (rule iffD2[OF word_less_nat_alt])
   apply (rule le_less_trans[OF unat_plus_gt])
    using cover
   apply (clarsimp simp: range_cover_def)
  apply (insert cover)
  apply (rule is_aligned_no_wrap'[where sz=sz])
   apply (simp add: range_cover_def)+
done


lemma pspace_no_overlapE:
  "\<lbrakk> pspace_no_overlap S s; kheap s x = Some ko;
  {x..x + (2 ^ obj_bits ko - 1)} \<inter> S = {} \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  unfolding pspace_no_overlap_def by auto


lemma base_member_set:
  fixes x :: "'a :: len word"
  assumes al: "is_aligned x sz"
  and    szv: "sz < len_of TYPE('a)"
  shows "x \<in> {x .. x + (2 ^ sz - 1)}"
proof (simp, rule is_aligned_no_wrap')
  show "(2 :: 'a :: len word) ^ sz - 1 < 2 ^ sz" using szv
    by (simp add: word_less_nat_alt word_neq_0_conv unat_minus_one)
qed fact+

abbreviation(input)
  "pspace_no_overlap_range_cover ptr bits
    \<equiv> pspace_no_overlap {ptr .. (ptr && ~~ mask bits) + (2 ^ bits - 1)}"

lemma pspace_no_overlap_into_Int_none:
  assumes ps: "pspace_no_overlap_range_cover ptr sz s"
  and     vp: "valid_pspace s"
  and  cover: "range_cover ptr sz (obj_bits_api ty us) n"
  shows   "set (retype_addrs ptr ty n us) \<inter> dom (kheap s) = {}"
proof -
  {
    fix x ko
    assume ps': "kheap s x = Some ko"
    have "x \<notin> {ptr .. (ptr && ~~ mask sz) + (2 ^ sz - 1)}"
    proof (rule orthD1)
      show "x \<in> {x .. x + (2 ^ obj_bits ko - 1)}"
      proof (rule base_member_set)
        from vp show "is_aligned x (obj_bits ko)" using ps'
          by (auto elim!: valid_pspaceE)
        show "obj_bits ko < len_of TYPE(machine_word_len)"
          by (rule valid_pspace_obj_sizes [OF _ ranI, unfolded word_bits_def]) fact+
      qed

      show "{x..x + (2 ^ obj_bits ko - 1)} \<inter> {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} = {}" using ps
        by (rule pspace_no_overlapE) fact+
    qed

    hence "x \<notin> set (retype_addrs ptr ty n us)"
      using assms subsetD[OF retype_addrs_subset_ptr_bits[OF cover]]
      by auto
  }
  thus ?thesis by auto
qed


lemma pspace_no_overlapD1:
  "\<lbrakk> pspace_no_overlap_range_cover ptr sz s; kheap s x = Some ko;
  range_cover ptr sz (obj_bits_api ty us) n;
  valid_pspace s\<rbrakk> \<Longrightarrow>
  x \<notin> set (retype_addrs ptr ty n us)"
  apply (drule(2) pspace_no_overlap_into_Int_none)
   apply (simp add:range_cover_def)
  apply (erule orthD2)
  apply (erule domI)
  done


lemma pspace_no_overlapD2:
  "\<lbrakk> pspace_no_overlap_range_cover ptr sz s; x \<in> set (retype_addrs ptr ty n us);
  range_cover ptr sz (obj_bits_api ty us) n;
   valid_pspace s \<rbrakk> \<Longrightarrow> x \<notin> dom (kheap s)"
  apply (drule(2) pspace_no_overlap_into_Int_none)
   apply (simp add:range_cover_def)
  apply (erule(1) orthD1)
done


lemma pspace_no_overlapC:
  "\<lbrakk> pspace_no_overlap_range_cover ptr sz s; x \<in> set (retype_addrs ptr ty n us); kheap s x = Some ko;
  range_cover ptr sz (obj_bits_api ty us) n;valid_pspace s \<rbrakk> \<Longrightarrow> P"
  by (auto dest: pspace_no_overlapD1)


lemma null_filterE:
  "\<lbrakk> null_filter cps x = Some cap;
      \<lbrakk> cps x = Some cap; cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow> R \<rbrakk>
     \<Longrightarrow> R"
  by (simp add: null_filter_def split: if_split_asm)


lemma across_null_filter_eq:
  assumes eq: "null_filter xs = null_filter ys"
  shows "\<lbrakk> xs x = Some v; ys x = Some v \<Longrightarrow> R;
           \<lbrakk> v = cap.NullCap; ys x = None \<rbrakk> \<Longrightarrow> R \<rbrakk>
          \<Longrightarrow> R"
  apply (cases "null_filter xs x")
   apply (subgoal_tac "null_filter ys x = None")
    apply (simp add: null_filter_def split: if_split_asm)
   apply (simp add: eq)
  apply (subgoal_tac "null_filter ys x = Some a")
   apply (simp add: null_filter_def split: if_split_asm)
  apply (simp add: eq)
  done


lemma mdb_cte_at_no_descendants:
  "\<lbrakk> mdb_cte_at f m; \<not> f x \<rbrakk> \<Longrightarrow> descendants_of x m = {}"
  apply (clarsimp simp add: descendants_of_def)
  apply (erule tranclE2)
   apply (simp add: cdt_parent_of_def)
   apply (drule(1) mdb_cte_atD)
   apply simp
  apply (simp add: cdt_parent_of_def)
  apply (drule(1) mdb_cte_atD)
  apply simp
  done


lemma caps_of_state_foldr:
  assumes tyun: "ty \<noteq> Untyped"
  fixes s sz ptr us addrs dev dm
  defines "s' \<equiv> (s\<lparr>kheap := foldr (\<lambda>p ps. ps(p \<mapsto> default_object ty dev us dm))
                  addrs (kheap s)\<rparr>)"
  shows
  "caps_of_state s' =
  (\<lambda>(oref,cref). if oref \<in> set addrs
                 then (case ty of Structures_A.CapTableObject \<Rightarrow> empty_cnode us
                               | Structures_A.TCBObject \<Rightarrow> option_map (\<lambda>x. cap.NullCap) \<circ> tcb_cap_cases
                               | _ \<Rightarrow> Map.empty) cref
                 else caps_of_state s (oref,cref))"
  apply (rule ext)+
  apply (case_tac x)
  apply (rename_tac oref cref)
  apply (simp add: caps_of_state_cte_wp_at split del: if_split)
  apply (case_tac "\<exists>cap. cte_wp_at ((=) cap) (oref, cref) s'")
   apply clarsimp
   apply (simp add: s'_def cte_wp_at_cases)
   apply (erule disjE)
    apply (clarsimp simp add: foldr_upd_app_if default_object_def caps_of_state_cte_wp_at
                     cte_wp_at_cases tyun empty_cnode_def
           split: if_split_asm Structures_A.apiobject_type.splits)
   apply (clarsimp simp add: foldr_upd_app_if default_object_def caps_of_state_cte_wp_at
                             cte_wp_at_cases tyun empty_cnode_def default_tcb_def
          split: if_split_asm Structures_A.apiobject_type.splits)
   apply (clarsimp simp: tcb_cap_cases_def split: if_split_asm)
  apply simp
  apply (simp add: cte_wp_at_cases s'_def foldr_upd_app_if)
  apply (rule conjI)
   apply (clarsimp simp: default_object_def wf_empty_bits
                  split: Structures_A.apiobject_type.split_asm)
   apply (fastforce simp: tcb_cap_cases_def split: if_split_asm)
  apply clarsimp
  apply (simp add: caps_of_state_cte_wp_at)
  apply (simp add: cte_wp_at_cases)
  done


lemma null_filter_caps_of_state_foldr:
  fixes s sz ptr us addrs dev dm
  assumes tyun: "ty \<noteq> Untyped"
    and nondom: "\<forall>x \<in> set addrs. x \<notin> dom (kheap s)"
  defines "s' \<equiv> (s\<lparr>kheap := foldr (\<lambda>p ps. ps(p \<mapsto> default_object ty dev us dm))
                  addrs (kheap s)\<rparr>)"
  shows
  "null_filter (caps_of_state s') =
   null_filter (caps_of_state s)"
  unfolding s'_def
  apply (subst caps_of_state_foldr[OF tyun])
  apply (rule ext)
  apply (clarsimp simp add: null_filter_def split_def empty_cnode_def
                     split: Structures_A.apiobject_type.splits)
  apply (subgoal_tac "a \<in> set addrs \<longrightarrow> caps_of_state s (a, b) \<noteq> Some cap.NullCap
           \<longrightarrow> None = caps_of_state s (a, b)", simp)
   apply clarsimp
   apply (subgoal_tac "tcb_cap_cases b = None", simp)
   apply (rule ccontr, clarsimp)
  apply clarsimp
  apply (rule sym, rule ccontr, clarsimp)
  apply (drule bspec[OF nondom])
  apply (drule caps_of_state_cteD)
  apply (erule cte_wp_atE, fastforce+)
  done


lemma retype_addrs_fold:
  " map (\<lambda>p. ptr_add ptr' (p * 2 ^ obj_bits_api ty us)) [0..< n ]
  = retype_addrs ptr' ty n us"
  by (simp add: retype_addrs_def power_sub)


lemma mult_div_rearrange:
  "(b::nat) \<le> a \<Longrightarrow> (2::nat) ^ a * (p div 2 ^ b) =
   2 ^ (a - b) * (2 ^ b * (p div 2 ^ b))"
  by (auto simp:field_simps power_add[symmetric])


lemma shiftr_mask_cmp:
  "\<lbrakk>c \<le> n; n \<le> len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> ((a::('a::len) word) \<le> mask n) = ((a >> c) \<le> mask (n - c))"
  apply (rule iffI)
    apply (drule le_shiftr[where n = c])
    apply (simp add:mask_2pm1[symmetric] shiftr_mask2)+
    apply (simp add:le_mask_iff shiftr_shiftr)
done


locale Retype_AI_no_gs_types =
  fixes no_gs_types :: "apiobject_type set"
  assumes no_gs_types_simps [simp]:
    "Untyped \<in> no_gs_types"
    "TCBObject \<in> no_gs_types"
    "EndpointObject \<in> no_gs_types"
    "NotificationObject \<in> no_gs_types"


lemma  measure_unat': "p \<noteq> 0 \<Longrightarrow> unat (p - 1) \<le>  unat p - 1"
  apply (insert measure_unat[where p = p])
  apply simp
done


(* FIXME: move *)
lemma range_cover_not_zero:
  "\<lbrakk>n \<noteq> 0; range_cover (ptr :: 'a :: len word) sz bits n\<rbrakk> \<Longrightarrow> ((of_nat n) :: 'a :: len word) \<noteq> 0"
    apply (rule of_nat_neq_0)
    apply simp
   apply (drule range_cover.range_cover_n_less)
   apply simp
  done


lemma range_cover_not_zero_shift:
  "\<lbrakk>n \<noteq> 0; range_cover (ptr :: 'a :: len word) sz bits n; gbits \<le> bits\<rbrakk>
   \<Longrightarrow> ((of_nat n) :: 'a :: len word) << gbits \<noteq> 0"
  apply (rule word_shift_nonzero[where m = "sz-gbits"])
     prefer 2
      apply (clarsimp simp:range_cover_def)
   apply (clarsimp simp:word_le_nat_alt)
   apply (subst unat_power_lower)
    apply (rule less_le_trans[OF diff_less_Suc])
    apply (simp add:range_cover_def)
   apply (simp add:range_cover.unat_of_nat_n)
   apply (erule le_trans[OF range_cover.range_cover_n_le(2)])
   apply (rule power_increasing)
     apply simp+
   using range_cover_not_zero
   apply auto
  done


lemma mult_plus_1: "(a::nat) + b * a = a * (b + 1)" by simp


lemma range_cover_cell_subset:
  "\<lbrakk>range_cover ptr sz us n;x < of_nat n\<rbrakk>
       \<Longrightarrow> {ptr + x * 2 ^ us..ptr + x * 2 ^ us + 2 ^ us - 1} \<subseteq> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"
  proof -
  assume cover:"range_cover ptr sz us n"
  and      cmp:"x<of_nat n"
  have sh: "(2^us * (ptr && mask sz >> us)) = ptr && mask sz"
     apply (subst shiftl_t2n[symmetric])
     apply (subst and_not_mask[symmetric])
     apply (rule is_aligned_neg_mask_eq)
     using cover
     apply (simp add:is_aligned_mask mask_twice range_cover_def min_def)
     done
  show ?thesis
  using cover cmp
  apply clarsimp
  apply (intro conjI)
    apply (rule word_plus_mono_right_split)
    apply (drule range_cover.range_cover_compare[where p = "unat x"])
      apply (erule unat_less_helper)
      apply (simp add: range_cover.unat_of_nat_shift[where gbits = us])
   apply (simp add:range_cover_def)
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
  apply (subst add.commute)
  apply (simp add:p_assoc_help)
  apply (subst add.assoc)+
  apply (rule word_plus_mono_right)
   apply (cut_tac nasty_split_lt[where x="((ptr && mask sz) >> us) + x" and n=us and m=sz])
      apply (simp add: sh field_simps)
     apply (clarsimp simp:range_cover_def word_less_nat_alt)
     apply (rule le_less_trans[OF unat_plus_gt])
     apply (erule less_le_trans[rotated])
     apply (clarsimp simp:range_cover.unat_of_nat_n[OF cover])
    apply (simp add:range_cover_def p_assoc_help[symmetric])+
  apply (simp add: is_aligned_no_overflow)
  done
 qed

lemma is_aligned_ptr_add_helper:
  "\<lbrakk> is_aligned ptr d; d < word_bits; c \<le> d; c \<le> a + b;
     a + b < word_bits \<rbrakk> \<Longrightarrow> is_aligned (ptr_add ptr (x * 2 ^ a * 2 ^ b)) c"
  apply (simp add: ptr_add_def)
  apply (erule aligned_add_aligned)
    apply (rule is_aligned_weaken)
     apply (simp add: field_simps
                      power_add[symmetric])
     apply (rule is_aligned_mult_triv2)
     apply assumption+
  done


lemma range_cover_no_0:
  "\<lbrakk> ptr \<noteq> 0; range_cover (ptr :: 'a :: len word) sz sbit n;p < n\<rbrakk> \<Longrightarrow>
   ptr + of_nat p * 2 ^ sbit \<noteq> 0"
  apply (subst word_plus_and_or_coroll2[symmetric, where w = "mask sz"])
  apply (case_tac  "(ptr && ~~ mask sz) \<noteq> 0")
   apply (subst add.commute)
   apply (subst add.assoc)
   apply (rule aligned_offset_non_zero)
     apply (rule is_aligned_neg_mask[OF le_refl])
    apply (simp add:word_less_nat_alt)
    apply (rule le_less_trans[OF unat_plus_gt])
    apply (rule less_le_trans[OF range_cover.range_cover_compare])
      apply simp
     apply ((simp add:range_cover_def)+)[3]
  apply (subgoal_tac "(ptr && mask sz) \<noteq> 0")
   apply (rule unat_gt_0[THEN iffD1])
   apply (simp add:not_less)
   apply (subst iffD1[OF unat_add_lem])
    apply (rule less_le_trans[OF range_cover.range_cover_compare])
      apply simp+
    apply (simp add:range_cover_def word_bits_def)
   apply simp
   apply (rule disjI1)
   apply unat_arith
  apply (rule ccontr)
  apply (subst (asm) word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
  apply (clarsimp simp:not_less)
done


lemma range_cover_mem:
  "\<lbrakk>x < n; range_cover ptr sz us n\<rbrakk>
       \<Longrightarrow> ptr + (of_nat x) * 2 ^ us \<in> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"
  apply (clarsimp)
  apply (intro conjI)
    apply (rule word_plus_mono_right_split[where sz = sz])
       apply (erule range_cover.range_cover_compare)
     apply ((simp add:range_cover_def)+)[2]
    apply (subst p_assoc_help)
    apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
    apply (subst add.commute)
    apply (subst add.assoc)
    apply (rule word_plus_mono_right)
    apply (simp add:word_le_nat_alt)
    apply (rule le_trans[OF unat_plus_gt])
    apply (subst unat_minus_one[OF power_not_zero])
     apply (simp add:range_cover_def)
    apply (frule(1) range_cover.range_cover_compare)
    apply (clarsimp simp:range_cover_def le_m1_iff_lt power_not_zero nat_le_Suc_less_imp)
   apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask,OF le_refl ])
   apply (simp add:range_cover_def)
  done


lemma range_cover_mem':
  "\<lbrakk>x < of_nat n; range_cover ptr sz us n\<rbrakk>
   \<Longrightarrow> ptr + x * 2 ^ us \<in> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"
  apply (drule range_cover_mem[where x = "unat x",rotated])
    apply (erule unat_less_helper)
  apply auto
  done


lemma range_cover_subset_not_empty:
  "\<lbrakk>x < of_nat n; range_cover ptr sz us n\<rbrakk>
   \<Longrightarrow> {ptr + x * 2 ^ us..ptr + x * 2 ^ us + 2 ^ us - 1} \<noteq> {}"
  apply (clarsimp simp:p_assoc_help)
  apply (rule is_aligned_no_overflow')
  apply (rule is_aligned_add_multI)
    apply (fastforce simp:range_cover_def)+
  done

crunch retype_region
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"
  (simp: crunch_simps)

locale Retype_AI_retype_region_ret =
  fixes state_ext_t :: "'state_ext :: state_ext itself"
  assumes retype_region_ret_folded:
    "\<And> y n bits ty dev.
      \<lbrace>\<top>\<rbrace> retype_region y n bits ty dev
      \<lbrace>\<lambda>r (s :: 'state_ext state). r = retype_addrs y ty n bits\<rbrace>"


context Retype_AI_retype_region_ret begin

lemmas retype_region_ret = retype_region_ret_folded[unfolded retype_addrs_def]

lemma retype_region_global_refs_disjoint:
  "\<lbrace>(\<lambda>s::'state_ext state. {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> global_refs s = {})
            and K (range_cover ptr sz (obj_bits_api apiobject_type obits) n)\<rbrace>
     retype_region ptr n obits apiobject_type dev
   \<lbrace>\<lambda>r s. global_refs s \<inter> set r = {}\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_lift_Pf3[where f=global_refs])
   apply (rule hoare_assume_pre)
   apply (clarsimp simp: Int_commute)
   apply (rule hoare_chain)  apply(rule retype_region_ret)
    apply simp
   apply (erule disjoint_subset2[rotated])
   apply (rule subsetI, simp only: mask_in_range[symmetric])
   apply (clarsimp simp: ptr_add_def)
   apply (intro conjI)
     apply (rule machine_word_plus_mono_right_split[where sz = sz])
       apply (erule(1) range_cover.range_cover_compare)
     apply (simp add:range_cover_def word_bits_def)
    apply (subst p_assoc_help)
    apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
    apply (subst add.commute)
    apply (subst add.assoc)
    apply (rule word_plus_mono_right)
    apply (simp add:word_le_nat_alt)
    apply (rule le_trans[OF unat_plus_gt])
    apply (subst unat_minus_one[OF power_not_zero])
     apply (simp add:range_cover_def)
    apply (frule(1) range_cover.range_cover_compare)
    apply (clarsimp simp:range_cover_def le_m1_iff_lt power_not_zero nat_le_Suc_less_imp)
   apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask,OF le_refl ])
    apply (simp add:range_cover_def)
   apply (simp add:range_cover_def)
  apply wp
done

end

crunch do_machine_op
  for valid_pspace: "valid_pspace"


lemma do_machine_op_return_foo:
  "do_machine_op (do x\<leftarrow>a;return () od) = (do (do_machine_op a); return () od)"
  apply (clarsimp simp:do_machine_op_def bind_def' gets_def
    get_def return_def select_f_def split_def simpler_modify_def)
  apply (rule ext)+
  apply (clarsimp simp:image_def)
  apply (rule set_eqI)
  apply clarsimp
  apply blast
  done

abbreviation(input)
 "all_invs_but_equal_kernel_mappings_restricted S
    \<equiv> (\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>))
       and valid_pspace and valid_mdb and valid_idle and only_idle
       and if_unsafe_then_cap
       and valid_global_refs and valid_arch_state
       and valid_irq_node and valid_irq_handlers and valid_vspace_objs
       and valid_irq_states and valid_global_objs
       and valid_arch_caps and valid_kernel_mappings
       and valid_asid_map and valid_global_vspace_mappings
       and pspace_in_kernel_window and cap_refs_in_kernel_window
       and pspace_respects_device_region and cap_refs_respects_device_region
       and cur_tcb and cur_sc_tcb and valid_ioc and valid_machine_state and valid_ioports"

lemma all_invs_but_equal_kernel_mappings_restricted_eq:
  "all_invs_but_equal_kernel_mappings_restricted {}
        = invs"
  by (rule ext, simp add: invs_def valid_state_def conj_comms restrict_map_def)


locale Retype_AI_dmo_eq_kernel_restricted =
  fixes
    state_ext_t :: "'state_ext::state_ext itself" and
    machine_op_t :: "'machine_op_t itself"
  assumes dmo_eq_kernel_restricted[wp]:
    "\<And> f m.
      \<lbrace>\<lambda>s::'state_ext state. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>
        do_machine_op m :: ('state_ext state, 'machine_op_t) nondet_monad
      \<lbrace>\<lambda>rv s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>"


crunch do_machine_op
  for only_idle[wp]: "only_idle"
crunch do_machine_op
  for valid_global_refs[wp]: "valid_global_refs"
crunch do_machine_op
  for cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"


locale Retype_AI_post_retype_invs =
  fixes state_ext_t :: "'state_ext::state_ext itself"
    and post_retype_invs_check :: "apiobject_type \<Rightarrow> bool"
    and post_retype_invs :: "apiobject_type \<Rightarrow> machine_word list \<Rightarrow> 'state_ext state \<Rightarrow> bool"
  assumes post_retype_invs_def':
    "post_retype_invs tp refs \<equiv>
      if post_retype_invs_check tp
        then all_invs_but_equal_kernel_mappings_restricted (set refs)
        else invs"

lemma  (in Retype_AI_retype_region_ret)  retype_region_aligned_for_init[wp]:
  "\<lbrace>\<lambda>s::'state_ext state. range_cover ptr sz (obj_bits_api new_type obj_sz) n\<rbrace>
     retype_region ptr n obj_sz new_type dev
   \<lbrace>\<lambda>rv s. \<forall>ref \<in> set rv. is_aligned ref (obj_bits_api new_type obj_sz)\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain, rule retype_region_ret)
   apply simp
  apply (clarsimp simp: ptr_add_def
                 dest!: less_two_pow_divD)
  apply (rule aligned_add_aligned)
    apply (fastforce simp:range_cover_def)
    apply (subst mult.commute, subst shiftl_t2n[symmetric],
           rule is_aligned_shiftl)
    apply simp
   apply (simp add:range_cover_def)+
  done


lemma honestly_16_10:
  "is_aligned (p :: word32) 10 \<Longrightarrow> p + 16 \<in> {p .. p + 1023}"
  apply simp
  apply (intro conjI is_aligned_no_wrap' word_plus_mono_right,
         (assumption | simp add: word_bits_def)+)
  done


definition
  caps_no_overlap :: "machine_word \<Rightarrow> nat \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "caps_no_overlap ptr sz s \<equiv> \<forall>cap \<in> ran (caps_of_state s).
               untyped_range cap \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<noteq> {}
               \<longrightarrow> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<subseteq> untyped_range cap"

definition caps_overlap_reserved :: "machine_word set \<Rightarrow> ('z::state_ext) state \<Rightarrow> bool"
where
 "caps_overlap_reserved S (s :: ('z::state_ext) state) \<equiv> \<forall>cap \<in> ran (caps_of_state s).
  (is_untyped_cap cap \<longrightarrow> usable_untyped_range cap \<inter> S = {})"



lemma of_nat_2: "((of_nat (2::nat))::word32) = 2" by simp


lemma subset_le_imp_less: "\<not> A \<subseteq> B \<Longrightarrow> \<not> A \<subset> B" by auto


lemma non_disjoing_subset: "\<lbrakk>A \<subseteq> B; A \<inter> C \<noteq> {}\<rbrakk> \<Longrightarrow> B \<inter> C \<noteq> {}" by blast


lemma pspace_no_overlap_same_type:
  "\<lbrakk>pspace_no_overlap S s; ko_at k p s; a_type ko = a_type k\<rbrakk>
    \<Longrightarrow> pspace_no_overlap S (kheap_update (\<lambda>_. (kheap s)(p \<mapsto> ko)) s)"
  unfolding pspace_no_overlap_def
  by (clarsimp simp: obj_at_def obj_bits_T)


lemma set_object_no_overlap:
  "\<lbrace>pspace_no_overlap S and obj_at (\<lambda>k. a_type ko = a_type k) p\<rbrace>
  set_object p ko \<lbrace>\<lambda>r. pspace_no_overlap S\<rbrace>"
  unfolding set_object_def get_object_def
  apply simp
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (drule obj_at_ko_at, erule exE)
  apply (rule pspace_no_overlap_same_type)
  apply auto
  done

lemma set_cap_no_overlap:
  "\<lbrace>pspace_no_overlap S\<rbrace> set_cap cap cte \<lbrace>\<lambda>r. pspace_no_overlap S\<rbrace>"
  unfolding set_cap_def
  by (wpsimp wp: set_object_no_overlap get_object_wp
           simp: split_beta obj_at_def a_type_def wf_cs_upd [unfolded fun_upd_def])

definition
  if_unsafe_then_cap2 :: "(cslot_ptr \<rightharpoonup> cap) \<Rightarrow> (irq \<Rightarrow> obj_ref) \<Rightarrow> bool"
where
 "if_unsafe_then_cap2 f x \<equiv> \<forall>cref. (f cref \<noteq> None \<and> (the (f cref)) \<noteq> cap.NullCap)
                               \<longrightarrow> (\<exists>cref'. f cref' \<noteq> None \<and> cref \<in> cte_refs (the (f cref')) x
                                              \<and> appropriate_cte_cap (the (f cref)) (the (f cref')))"


lemma null_filter_same:
  "cps p \<noteq> Some cap.NullCap \<Longrightarrow> null_filter cps p = cps p"
  by (simp add: null_filter_def)


lemma cte_wp_at_not_Null:
  "cte_wp_at (\<lambda>cp. cp \<noteq> cap.NullCap) p s \<Longrightarrow> caps_of_state s p \<noteq> Some cap.NullCap"
  by (clarsimp simp: cte_wp_at_caps_of_state)


lemma unsafe_rep2:
  "if_unsafe_then_cap =
    (\<lambda>s. if_unsafe_then_cap2 (null_filter (caps_of_state s)) (interrupt_irq_node s))"
  apply (simp only: if_unsafe_then_cap2_def o_def)
  apply (subst P_null_filter_caps_of_cte_wp_at, simp)+
  apply (simp add: null_filter_same [where cps="caps_of_state s" for s, OF cte_wp_at_not_Null])
  apply (fastforce simp: if_unsafe_then_cap2_def cte_wp_at_caps_of_state
                        if_unsafe_then_cap_def ex_cte_cap_wp_to_def)
  done


lemma descendants_inc_null_filter:
  "\<lbrakk>mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrakk>
   \<Longrightarrow> descendants_inc (cdt s) (null_filter (caps_of_state s)) =
       descendants_inc (cdt s) (caps_of_state s)"
  apply (simp add:descendants_inc_def descendants_of_def del:split_paired_All)
  apply (intro iffI allI impI)
   apply (drule spec)+
   apply (erule(1) impE)
   apply (frule tranclD)
   apply (drule tranclD2)
   apply (simp add:cdt_parent_rel_def is_cdt_parent_def del:split_paired_All)
   apply (elim conjE exE)
   apply (drule(1) mdb_cte_atD)+
   apply (simp add:swp_def cte_wp_at_caps_of_state null_filter_def del:split_paired_All)
   apply (elim conjE exE)
   apply simp
  apply (drule spec)+
  apply (erule(1) impE)
  apply (frule tranclD)
  apply (drule tranclD2)
  apply (simp add:cdt_parent_rel_def is_cdt_parent_def del:split_paired_All)
  apply (elim conjE exE)
  apply (drule(1) mdb_cte_atD)+
  apply (simp add:swp_def cte_wp_at_caps_of_state null_filter_def del:split_paired_All)
  apply (elim conjE exE)
  apply simp
  done


definition
  valid_mdb2
    :: "[cslot_ptr \<rightharpoonup> cap, cslot_ptr \<rightharpoonup> cslot_ptr, cslot_ptr \<Rightarrow> bool] \<Rightarrow> bool"
where
 "valid_mdb2 cps m r \<equiv>
     (\<forall>p p'. m p' = Some p \<longrightarrow> {cps p, cps p'} \<inter> {None, Some cap.NullCap} = {})
   \<and> (\<forall>p p' c c'. cps p = Some c \<longrightarrow> is_untyped_cap c \<longrightarrow> cps p' = Some c'
               \<longrightarrow> obj_refs c' \<inter> untyped_range c \<noteq> {} \<longrightarrow> p' \<in> descendants_of p m)
   \<and> descendants_inc m cps
   \<and> (\<forall>p. \<not> m \<Turnstile> p \<rightarrow> p) \<and> untyped_inc m cps \<and> ut_revocable r cps
   \<and> irq_revocable r cps \<and> valid_arch_mdb r cps"


lemma conj_cong2: "\<lbrakk>P = P'; P \<Longrightarrow> Q = Q'\<rbrakk> \<Longrightarrow> (P \<and> Q) = (P' \<and> Q')" by auto

lemma valid_mdb_rep2:
  "valid_mdb = (\<lambda>s. valid_mdb2 (null_filter (caps_of_state s)) (cdt s) (is_original_cap s))"
  apply (simp add: valid_mdb_def valid_mdb2_def
                   untyped_mdb_def no_mloop_def untyped_inc_def)
  apply (rule ext)
  apply (rule conj_cong2)
   apply (simp add: mdb_cte_at_def)
   apply (rule arg_cong[where f=All, OF ext])+
   apply ((clarsimp simp: cte_wp_at_caps_of_state null_filter_def
                | rule conjI iffI
                | drule iffD1 [OF not_None_eq, OF not_sym])+)[1]
  apply (rule conj_cong)
   apply (rule arg_cong[where f=All, OF ext])+
   apply (clarsimp simp: null_filter_def)
  apply (rule conj_cong)
   apply (simp add:descendants_inc_null_filter)
  apply (rule arg_cong2 [where f="(\<and>)"])
   apply (rule refl)
  apply (rule arg_cong2 [where f="(\<and>)"])
   prefer 2
   apply (rule arg_cong2 [where f="(\<and>)"])
    apply (simp add: ut_revocable_def null_filter_def del: split_paired_All)
    apply (auto simp: is_cap_simps)[1]
    apply (simp add: irq_revocable_def null_filter_def del: split_paired_All)
    apply auto[1]
   apply ((fastforce simp: valid_arch_mdb_null_filter[simplified null_filter_def])+)[2]
  apply (rule arg_cong[where f=All, OF ext])+
  apply ((clarsimp simp: cte_wp_at_caps_of_state null_filter_def
               | rule conjI iffI
               | drule iffD1 [OF not_None_eq, OF not_sym])+)[1]
  done


lemma valid_mdb_rep3:
  "valid_mdb = (\<lambda>s. \<exists>m r. cdt s = m \<and> is_original_cap s = r \<and> valid_mdb2 (null_filter (caps_of_state s)) m r)"
  by (simp add: valid_mdb_rep2)


lemma retype_region_mdb[wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> retype_region ptr n us ty dev \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  apply (simp add: retype_region_def split del: if_split cong: if_cong)
  apply (wp|clarsimp)+
  done


lemma retype_region_revokable[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> retype_region ptr n us ty dev \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
  apply (simp add: retype_region_def split del: if_split cong: if_cong)
  apply (wp|clarsimp)+
  done


lemma pspace_no_overlap_obj_not_in_range:
  "\<lbrakk> pspace_no_overlap S s; obj_at P ptr' s;
       pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> ptr' \<notin> S"
  apply (clarsimp simp add: pspace_no_overlap_def obj_at_def)
  apply (elim allE, drule(1) mp)
  apply (simp add: field_simps)
  apply (drule_tac x=ptr' in eqset_imp_iff)
  apply (erule pspace_alignedE, erule domI)
  apply (drule valid_obj_sizes, erule ranI)
  apply (clarsimp simp: add_diff_eq[symmetric])
  apply (simp add: is_aligned_no_wrap')
  done


lemma obj_at_kheap_trans_state[simp]:"obj_at P ptr (kheap_update f (trans_state f' s)) = obj_at P ptr (kheap_update f s)"
  apply (simp only: trans_state_update[symmetric] more_update.obj_at_update)
  done


lemma retype_region_obj_at:
  assumes tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  shows "\<lbrace>\<top>\<rbrace> retype_region ptr n us ty dev
  \<lbrace>\<lambda>r s. \<forall>x \<in> set (retype_addrs ptr ty n us). obj_at (\<lambda>ko. ko = default_object ty dev us (cur_domain s)) x s\<rbrace>"
  using tyunt unfolding retype_region_def
  apply (simp only: return_bind bind_return foldr_upd_app_if fun_app_def K_bind_def)
  apply wp
  apply (clarsimp simp: retype_addrs_fold obj_at_def)
  done


lemma retype_region_obj_at_other:
  assumes ptrv: "ptr \<notin> set (retype_addrs ptr' ty n us)"
  shows "\<lbrace>\<lambda>s. N (obj_at P ptr s)\<rbrace> retype_region ptr' n us ty dev \<lbrace>\<lambda>r s. N (obj_at P ptr s)\<rbrace>"
  using ptrv unfolding retype_region_def retype_addrs_def
  apply (simp only: foldr_upd_app_if fun_app_def K_bind_def)
  apply (wpsimp simp: obj_at_def)
  done


lemma retype_region_obj_at_other2:
  "\<lbrace>\<lambda>s. ptr \<notin> set (retype_addrs ptr' ty n us)
       \<and> N (obj_at P ptr s)\<rbrace> retype_region ptr' n us ty dev \<lbrace>\<lambda>rv s. N (obj_at P ptr s)\<rbrace>"
  by (rule hoare_assume_pre) (wpsimp wp: retype_region_obj_at_other)


lemma retype_region_obj_at_other3_ex:
  "\<lbrace>\<lambda>s. obj_at P p s \<and> valid_objs s \<and> pspace_aligned s
        \<and> (\<exists>sz. pspace_no_overlap_range_cover ptr sz s \<and> range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
   retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  apply (rule hoare_pre)
   apply (rule retype_region_obj_at_other2)
  apply clarsimp
  apply (drule subsetD [rotated, OF _ retype_addrs_subset_ptr_bits])
   apply simp
  apply (drule(3) pspace_no_overlap_obj_not_in_range)
  apply (simp add: field_simps)
  done

lemma retype_region_obj_at_other3:
  "\<lbrace>\<lambda>s. obj_at P p s \<and> valid_objs s \<and> pspace_aligned s
        \<and> pspace_no_overlap_range_cover ptr sz s \<and> range_cover ptr sz (obj_bits_api ty us) n\<rbrace>
   retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  by (wp retype_region_obj_at_other3_ex, fastforce)

lemma retype_region_st_tcb_at_ex:
  "\<lbrace>\<lambda>s. pred_tcb_at proj P t s \<and> valid_objs s \<and> pspace_aligned s
        \<and> (\<exists>sz. pspace_no_overlap_range_cover ptr sz s \<and> range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
   retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  by (simp add: retype_region_obj_at_other3_ex pred_tcb_at_def)

lemma retype_region_st_tcb_at:
  "\<lbrace>\<lambda>s. pred_tcb_at proj P t s \<and> valid_objs s \<and> pspace_aligned s
        \<and> pspace_no_overlap_range_cover ptr sz s \<and> range_cover ptr sz (obj_bits_api ty us) n\<rbrace>
   retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  by (wp retype_region_st_tcb_at_ex, fastforce)

lemma retype_region_cur_tcb[wp]:
  "\<lbrace>pspace_no_overlap_range_cover ptr sz and cur_tcb and K (range_cover ptr sz (obj_bits_api ty us) n)
     and K (is_aligned ptr sz \<and> sz < word_bits)
     and valid_objs and pspace_aligned\<rbrace>
     retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  supply
    is_aligned_neg_mask_eq[simp del]
    is_aligned_neg_mask_weaken[simp del]
  apply (rule hoare_post_imp[where Q'="\<lambda>rv s. \<exists>tp. tcb_at tp s \<and> cur_thread s = tp"])
   apply (simp add: cur_tcb_def)
  apply (wpsimp wp: hoare_vcg_ex_lift retype_region_obj_at_other3 simp: retype_region_def)
  apply (auto simp: cur_tcb_def cong: if_cong)
  done


lemma retype_addrs_mem_sz_0_is_ptr:
  assumes "x \<in> set (retype_addrs ptr ty n us)"
  and     "n = 0"
  shows   "x = ptr"
  using assms unfolding retype_addrs_def by (clarsimp simp: ptr_add_def)


locale Retype_AI_obj_bits_api_neq_0 =
  assumes obj_bits_api_neq_0:
  "\<And>ty us. ty \<noteq> Untyped \<Longrightarrow> ty \<noteq> SchedContextObject \<Longrightarrow> 0 < obj_bits_api ty us"
  (* for SchedContextObject, us \<ge> 8 is imposed but this cannot be shown only from
     the definition of obj_bits_api *)

lemma retype_addrs_range_subset:
  "\<lbrakk>  p \<in> set (retype_addrs ptr ty n us);
     range_cover ptr sz (obj_bits_api ty us) n \<rbrakk>
  \<Longrightarrow> {p .. p + 2 ^ obj_bits_api ty us - 1} \<subseteq> {ptr..(ptr && ~~ mask sz) + 2^sz - 1}"
  apply (clarsimp simp: retype_addrs_def ptr_add_def
              simp del: atLeastatMost_subset_iff atLeastAtMost_iff)
  apply (frule_tac x = "of_nat x" in range_cover_cell_subset)
    apply (erule of_nat_mono_maybe[rotated])
    apply (drule range_cover.range_cover_n_less)
   apply (simp add:word_bits_def)
  apply fastforce
  done


context Retype_AI_slot_bits begin

lemma retype_addrs_obj_range_subset:
  "\<lbrakk> p \<in> set (retype_addrs ptr ty n us);
     range_cover ptr sz (obj_bits (default_object ty dev us dm)) n;
     ty \<noteq> Untyped; ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us \<rbrakk>
  \<Longrightarrow> obj_range p (default_object ty dev us dm) \<subseteq> {ptr..(ptr && ~~ mask sz) + (2^sz - 1)}"
  by (simp add: obj_range_def obj_bits_api_default_object[symmetric]
                retype_addrs_range_subset p_assoc_help[symmetric]
           del: atLeastatMost_subset_iff)

lemma retype_addrs_obj_range_subset_strong:
  "\<lbrakk> p \<in> set (retype_addrs ptr ty n us);
    range_cover ptr sz (obj_bits_api ty us) n;
    ty \<noteq> Untyped; ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us \<rbrakk>
   \<Longrightarrow> obj_range p (default_object ty dev us dm) \<subseteq>  {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}"
  unfolding obj_range_def
  apply (frule retype_addrs_obj_range_subset)
   apply (simp add:obj_bits_dev_irr)
  apply (simp add:obj_range_def)+
  apply (intro conjI impI)
  apply (erule(1) impE)
  apply clarsimp
  apply (case_tac "n = 0")
   apply (clarsimp simp:retype_addrs_def)
proof -
  assume cover:"range_cover ptr sz (obj_bits_api ty us) n"
    and  mem_p:"p \<in> set (retype_addrs ptr ty n us)"
    and  not_0:"n\<noteq> 0"
    and  tyunt:"ty\<noteq> Untyped"
    and  tysc : "ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us"
  note n_less = range_cover.range_cover_n_less[OF cover]
  have unat_of_nat_m1: "unat (of_nat n - (1::machine_word)) < n"
    using not_0 n_less
    by (simp add:unat_of_nat_minus_1)
  have decomp:"of_nat n * 2 ^ obj_bits_api ty us = of_nat (n - 1) * 2 ^ (obj_bits (default_object ty dev us dm))
    + (2 :: machine_word) ^ obj_bits (default_object ty dev us dm)"
    apply (simp add:distrib_right[where b = "1::'a::len word",simplified,symmetric])
    using not_0 n_less
    apply (simp add: unat_of_nat_minus_1 obj_bits_api_def3[where dm=0] tyunt tysc
               cong: obj_bits_cong)
    done
  show  "p + 2 ^ obj_bits (default_object ty dev us dm) - 1 \<le> ptr + of_nat n * 2 ^ obj_bits_api ty us - 1"
    using cover
    apply (subst decomp)
    apply (simp add:add.assoc[symmetric])
    apply (simp add:p_assoc_help)
    apply (rule order_trans[OF word_plus_mono_left word_plus_mono_right])
    using mem_p not_0
       apply (clarsimp simp: retype_addrs_def ptr_add_def shiftl_t2n tyunt tysc
                             obj_bits_dev_irr)
       apply (rule word_plus_mono_right)
        apply (rule word_mult_le_mono1[OF word_of_nat_le])
          using n_less not_0
          apply (simp add:unat_of_nat_minus_1)
         apply (rule p2_gt_0[THEN iffD2])
         apply (simp add: word_bits_def range_cover_def obj_bits_dev_irr tyunt)
        apply (simp only: word_bits_def[symmetric])
        using not_0 n_less
        apply (clarsimp simp: unat_of_nat_minus_1 obj_bits_dev_irr tyunt)
        apply (subst unat_power_lower)
         apply (simp add:range_cover_def)
        apply (rule nat_less_power_trans2[OF range_cover.range_cover_le_n_less(2),OF cover, folded word_bits_def])
         apply (simp add:unat_of_nat_m1 less_imp_le)
        apply (simp add:range_cover_def word_bits_def)
       apply (rule machine_word_plus_mono_right_split[where sz = sz])
        using range_cover.range_cover_compare[OF cover,where p = "unat (of_nat n - (1::machine_word))"]
        apply (clarsimp simp:unat_of_nat_m1)
       apply (simp add:range_cover_def word_bits_def)
      apply (rule olen_add_eqv[THEN iffD2])
      apply (subst add.commute[where a = "2^(obj_bits (default_object ty dev us dm)) - 1"])
      apply (subst p_assoc_help[symmetric])
      apply (rule is_aligned_no_overflow)
      apply (insert cover)
      apply (clarsimp simp:range_cover_def)
      apply (erule aligned_add_aligned[OF _  is_aligned_mult_triv2])
      apply (simp add: obj_bits_dev_irr range_cover_def tysc tyunt)+
    by (meson is_aligned_add is_aligned_mult_triv2 is_aligned_no_overflow')
qed


lemma retype_addrs_mem_subset_ptr_bits:
  assumes cover:"range_cover ptr sz (obj_bits_api ty us) n"
  and tynunt: "ty \<noteq> Untyped"
  and  tysc : "ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us"
  and     xv: "x \<in> set (retype_addrs ptr ty n us)"
  shows "{x .. x + (2 ^ obj_bits_api ty us - 1)} \<subseteq> {ptr .. (ptr && ~~ mask sz) + (2 ^ sz - 1)}"
  apply (insert cover)
  using retype_addrs_obj_range_subset [OF xv _ tynunt tysc]
  by (simp add: obj_bits_dev_irr tynunt tysc obj_range_def field_simps)

lemma pspace_no_overlap_retype_addrs_empty:
  assumes nptr: "pspace_no_overlap_range_cover ptr sz s"
  and xv: "x \<in> set (retype_addrs ptr ty n us)"
  and yv: "y \<notin> set (retype_addrs ptr ty n us)"
  and kov: "kheap s y = Some ko"
  and tyv: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  and tysc: "ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us"
  and cover: "range_cover ptr sz (obj_bits_api ty us) n"
  and oab: "obj_bits_api ty us \<le> sz"
  shows "{x..x + (2 ^ obj_bits (default_object ty dev us dm) - 1)} \<inter> {y..y + (2 ^ obj_bits ko - 1)} = {}"
proof -
  have "{x..x + (2 ^ obj_bits (default_object ty dev us dm) - 1)} \<subseteq> {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)}"
   by (subst obj_bits_api_default_object [OF tyv tysc, symmetric],
      rule retype_addrs_mem_subset_ptr_bits) fact+

  moreover have "{ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<inter> {y..y + (2 ^ obj_bits ko - 1)} = {}"
    by (subst Int_commute, rule pspace_no_overlapE) fact+

  ultimately show ?thesis by auto
qed

end


lemma valid_obj_default_object:
  assumes tyunt: "ty \<noteq> Untyped"
  and      tyct: "ty = CapTableObject \<Longrightarrow> us < word_bits - cte_level_bits \<and> 0 < us"
  and      tysc: "ty = SchedContextObject \<Longrightarrow> min_sched_context_bits \<le> us \<and> us \<le> untyped_max_bits"
  and      arch: "valid_arch_tcb default_arch_tcb s"
  shows "valid_obj ptr (default_object ty dev us dm) s"
  unfolding valid_obj_def default_object_def
  apply (cases ty)
         apply (simp add: tyunt)
        apply (simp add: valid_tcb_def default_tcb_def valid_tcb_state_def
                         tcb_cap_cases_def valid_ipc_buffer_cap_def
                         word_bits_def arch)
       apply (simp add: valid_ep_def default_ep_def)
      apply (simp add: valid_ntfn_def default_notification_def default_ntfn_def valid_bound_obj_def)
     apply (frule tyct)
     apply (clarsimp simp: valid_cs_def empty_cnode_def well_formed_cnode_n_def)
     apply safe
      apply (erule ranE)
      apply (simp split: if_split_asm)
     apply (simp add: valid_cs_size_def well_formed_cnode_n_def)
     apply safe
      apply (simp split: if_split_asm)
     apply (clarsimp split: if_split_asm)
    apply (frule tysc)
    apply (simp add: valid_sched_context_def valid_bound_obj_def default_sched_context_def valid_sched_context_size_def)
   apply (simp add: valid_reply_def valid_bound_obj_def default_reply_def)
  apply (clarsimp simp add: wellformed_arch_default)
  done

lemma usable_range_subseteq:
  "\<lbrakk>cap_aligned cap;is_untyped_cap cap\<rbrakk> \<Longrightarrow> usable_untyped_range cap \<subseteq> untyped_range cap"
  apply (clarsimp simp:is_cap_simps cap_aligned_def split:if_splits)
  apply (erule order_trans[OF is_aligned_no_wrap'])
   apply (erule of_nat_power)
   apply (simp add:word_bits_def)+
 done


lemma usable_range_emptyD:
  "\<lbrakk>cap_aligned cap;is_untyped_cap cap ;usable_untyped_range cap = {}\<rbrakk> \<Longrightarrow> 2 ^ cap_bits cap \<le> free_index_of cap"
  apply (clarsimp simp:is_cap_simps not_le free_index_of_def cap_aligned_def split:if_splits)
  apply (drule(1) of_nat_power [where 'a=machine_word_len, folded word_bits_def])
  apply (drule word_plus_mono_right[OF _ is_aligned_no_overflow[unfolded p_assoc_help],rotated])
   apply simp
  apply (simp add:p_assoc_help)
  done


locale Retype_AI_valid_untyped_helper =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes valid_untyped_helper:
    "\<And>s c q ty ptr sz us n dev.
      \<lbrakk> (s :: 'state_ext state) \<turnstile> c;
        cte_wp_at ((=) c) q s;
        ty \<noteq> Untyped;ty = SchedContextObject \<Longrightarrow> min_sched_context_bits \<le> us \<and> us \<le> untyped_max_bits;
        range_cover ptr sz (obj_bits_api ty us) n;
        is_untyped_cap c \<Longrightarrow>
          usable_untyped_range c \<inter> {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api ty us)) - 1} = {};
        pspace_no_overlap_range_cover ptr sz s;
        caps_no_overlap ptr sz s;
        valid_pspace s \<rbrakk>
      \<Longrightarrow> valid_cap c
           (s\<lparr>kheap := \<lambda>x. if x \<in> set (retype_addrs ptr ty n us)
                             then Some (default_object ty dev us (cur_domain s))
                             else kheap s x\<rparr>)"


lemma cap_refs_respects_device_region_cap_range:
  "\<lbrakk>cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s;
    cap_refs_respects_device_region s\<rbrakk>
    \<Longrightarrow> up_aligned_area ptr sz \<subseteq> (if dev then device_region s else - device_region s)"
  unfolding cap_refs_respects_device_region_def
  apply (drule spec[where x = slot])
  apply (clarsimp simp: cte_wp_at_caps_of_state cap_range_respects_device_region_def)
  apply fastforce
  done


locale retype_region_proofs =
  fixes s :: "'state_ext :: state_ext state"
    and ty us ptr sz n ps s' dev
  assumes    vp: "valid_pspace s"
      and    vm: "valid_mdb s"
      and   res: "caps_overlap_reserved {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api ty us)) - 1} s"
      and tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
      and  tyct: "ty = CapTableObject \<Longrightarrow> us < word_bits - cte_level_bits \<and> 0 < us"
      and  tysc: "ty = SchedContextObject \<Longrightarrow> min_sched_context_bits \<le> us \<and> us \<le> untyped_max_bits"
      and   orth: "pspace_no_overlap_range_cover ptr sz s"
      and  mem :  "caps_no_overlap ptr sz s"
      and cover: "range_cover ptr sz (obj_bits_api ty us) n"
      and dev: "\<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s"
  defines "ps \<equiv> (\<lambda>x. if x \<in> set (retype_addrs ptr ty n us) then Some (default_object ty dev us (cur_domain s))
                       else kheap s x)"
      and "s' \<equiv> kheap_update (\<lambda>y. ps) s"

locale retype_region_proofs_gen
  = retype_region_proofs s ty us ptr sz n ps s' dev
  + Retype_AI_slot_bits
  + Retype_AI_valid_untyped_helper "TYPE('state_ext)"
  for s :: "'state_ext :: state_ext state"
  and ty us ptr sz n ps s' dev +
  assumes hyp_refs_eq:
    "state_hyp_refs_of s' = state_hyp_refs_of s"
  assumes valid_arch_tcb_default[simp]:
    "\<And>s :: 'state_ext :: state_ext state. valid_arch_tcb default_arch_tcb s"
  assumes  wellformed_default_obj:
   "\<lbrakk> ptra \<notin> set (retype_addrs ptr ty n us);
        kheap s ptra = Some (ArchObj x5); arch_valid_obj x5 s\<rbrakk> \<Longrightarrow>
          arch_valid_obj x5 s'"

context retype_region_proofs begin

lemma obj_at_pres: "\<And>P x. obj_at P x s \<Longrightarrow> obj_at P x s'"
  by (clarsimp simp: obj_at_def s'_def ps_def dest: domI)
     (rule pspace_no_overlapC [OF orth _ _ cover vp])

lemma orthr:
  "\<And>x obj. kheap s x = Some obj \<Longrightarrow> x \<notin> set (retype_addrs ptr ty n us)"
  apply (rule ccontr)
  apply (frule pspace_no_overlapC[OF orth _ _ _ vp,rotated])
    apply (rule cover)
  apply auto
  done

lemma cte_at_pres: "\<And>p. cte_at p s \<Longrightarrow> cte_at p s'"
  unfolding cte_at_cases s'_def ps_def
  apply (erule disjE)
   apply (clarsimp simp: well_formed_cnode_n_def orthr)+
  done

lemma pred_tcb_at_pres: "\<And>P t. pred_tcb_at proj P t s \<Longrightarrow> pred_tcb_at proj P t s'"
  unfolding pred_tcb_at_def
  by (erule obj_at_pres)

end


context retype_region_proofs_gen begin

lemma psp_dist:
  shows "pspace_distinct s'"
proof -
  define dm where "dm = cur_domain s"
  have distinct:"pspace_distinct s"
    apply (rule valid_pspaceE)
    apply (rule vp)
    apply simp
   done
  moreover
  {
    fix x y
    assume xne: "x \<noteq> y" and xv: "x \<in> set (retype_addrs ptr ty n us)" and yv: "y \<in> set (retype_addrs ptr ty n us)"

    have "is_aligned x (obj_bits_api ty us)"
      apply (rule retype_addrs_aligned)
      apply fact+
      apply (insert cover)
        apply (auto simp: range_cover_def word_bits_def)
      done
    moreover
    have "is_aligned y (obj_bits_api ty us)"
      apply (rule retype_addrs_aligned)
      apply fact+
      apply (insert cover)
      apply (auto simp: range_cover_def word_bits_def)
      done
    ultimately have
      "{x..x + (2 ^ obj_bits (default_object ty dev us dm) - 1)} \<inter>
       {y..y + (2 ^ obj_bits (default_object ty dev us dm) - 1)} = {}"
      using xne tyunt tysc cover
      apply -
      apply (rule aligned_neq_into_no_overlap)
      apply (simp_all add: range_cover_def word_bits_def obj_bits_dev_irr)
      done
  } note inter = this
  moreover
  {
    fix x y ko'
    assume xne: "x \<noteq> y" and xv: "x \<in> set (retype_addrs ptr ty n us)"
        and yv: "y \<notin> set (retype_addrs ptr ty n us)" and  "kheap s y = Some ko'"
    have "{x..x + (2 ^ obj_bits (default_object ty dev us dm) - 1)} \<inter> {y..y + (2 ^ obj_bits ko' - 1)} = {}"
      apply (rule pspace_no_overlap_retype_addrs_empty [OF orth])
      apply fact+
      apply (insert cover tyunt tysc)
      apply (simp add: range_cover_def word_bits_def)+
      done
  }note inter' = this
  show ?thesis
    unfolding pspace_distinct_def s'_def ps_def
    apply (fold dm_def)
    apply (clarsimp split: if_split_asm option.splits
              simp del: Int_atLeastAtMost)
    apply (intro conjI impI allI)
      apply (erule(2) inter)
     apply clarify
     apply (erule(3) inter')
    apply clarify
    apply (subst Int_commute)
    apply (erule(3) inter'[OF neq_commute[THEN iffD1]])
   apply clarify
   apply (insert vp[unfolded valid_pspace_def pspace_distinct_def])
   apply clarify
   apply (drule_tac x = x in spec)
   apply (drule_tac x = y in spec)
   apply (erule allE impE)+
     apply fastforce
  apply simp
  done
qed


lemma psp_al:
  shows "pspace_aligned s'"
  unfolding pspace_aligned_def s'_def ps_def
proof (clarsimp split: if_split_asm)
  fix x
  assume "x \<in> set (retype_addrs ptr ty n us)"
  thus "is_aligned x (obj_bits (default_object ty dev us (cur_domain s)))"
    apply -
    apply (drule retype_addrs_aligned)
    apply (insert cover tyunt tysc)
      apply (fastforce simp:range_cover_def word_bits_def)+
    apply (simp add: obj_bits_dev_irr
              split: Structures_A.apiobject_type.splits)
    done
next
  fix x y
  assume "x \<notin> set (retype_addrs ptr ty n us)" and px: "kheap s x = Some y"

  have "pspace_aligned s"
    by (rule valid_pspaceE[OF vp],simp)

  thus "is_aligned x (obj_bits y)"
  proof
    show "x \<in> dom (kheap s)" by (rule domI) fact+
  next
    assume "is_aligned x (obj_bits (the (kheap s x)))"
    thus "is_aligned x (obj_bits y)" using px by simp
  qed
qed

end


lemma le_subset: "\<lbrakk>(a::('g::len) word) \<le> c\<rbrakk> \<Longrightarrow> {c..b} \<subseteq> {a..b}" by clarsimp


context retype_region_proofs_gen begin

lemma valid_cap_pres:
  "\<lbrakk> s \<turnstile> c; cte_wp_at ((=) c) (oref,cref) s \<rbrakk> \<Longrightarrow> s' \<turnstile> c"
  using cover mem orth
  apply (simp add:s'_def ps_def)
  apply (rule valid_untyped_helper[ OF _ _ tyunt tysc cover _ _ _ vp ])
      apply simp+
     apply (simp add:cte_wp_at_caps_of_state)
     apply (drule res[unfolded caps_overlap_reserved_def,THEN bspec,OF ranI])
     apply simp
    apply simp+
  done

lemma valid_objs: "valid_objs s'"
  apply (clarsimp simp:valid_objs_def)
  apply (rule valid_pspaceE[OF vp])
  apply (clarsimp simp:valid_objs_def s'_def ps_def split:if_splits)
   apply (simp add:valid_obj_default_object[OF tyunt tyct tysc])
  apply (simp (no_asm) add:valid_obj_def)
  apply (drule bspec)
   apply (erule domI)
  apply (clarsimp simp:valid_obj_def split:Structures_A.kernel_object.splits)
        apply (clarsimp simp: valid_cs_def)
        apply (drule (1) bspec)
        apply (clarsimp simp: ran_def)
        apply (erule valid_cap_pres[unfolded s'_def ps_def])
        apply (clarsimp simp add: cte_wp_at_cases valid_cs_size_def s'_def ps_def)
        apply fastforce
       apply (clarsimp simp: valid_tcb_def)
       apply (rule conjI)
        apply (rule ballI, drule(1) bspec, clarsimp elim!: ranE)
        apply (erule valid_cap_pres[unfolded s'_def ps_def])
        apply (rule cte_wp_at_tcbI, fastforce+)[1]
       apply (fastforce simp: valid_tcb_state_def valid_bound_obj_def
                       elim!: obj_at_pres[unfolded s'_def ps_def] valid_arch_tcb_typ_at
                       split: Structures_A.thread_state.splits option.splits)
      apply (fastforce simp: valid_ep_def
                      elim!: obj_at_pres[unfolded s'_def ps_def]
                      split: Structures_A.endpoint.splits)
     apply (fastforce simp: valid_ntfn_def valid_bound_obj_def
                     elim!: obj_at_pres[unfolded s'_def ps_def]
                     split: Structures_A.ntfn.splits option.splits)
    apply (fastforce simp: valid_sched_context_def valid_bound_obj_def foldl_conj_list_all
                           list_all_def
                    elim!: obj_at_pres[unfolded s'_def ps_def]
                    split: option.splits)
   apply (fastforce simp: valid_reply_def valid_bound_obj_def
                   elim!: obj_at_pres[unfolded s'_def ps_def]
                   split: option.splits)
  apply (clarsimp simp: wellformed_default_obj[unfolded s'_def ps_def])
  done

end


context retype_region_proofs begin

lemma refs_eq:
  "state_refs_of s' = state_refs_of s"
  unfolding s'_def ps_def
  apply (clarsimp intro!: ext simp: state_refs_of_def
                    simp: orthr
                   split: option.splits)
  apply (cases ty, simp_all add: tyunt default_object_def
                                 default_tcb_def default_ep_def
                                 default_sched_context_def default_reply_def
                                 default_notification_def default_ntfn_def)
  done


lemma cte_retype:
    "\<And>P p. \<not> P cap.NullCap \<Longrightarrow>
     cte_wp_at P p s' = cte_wp_at P p s"
  unfolding s'_def ps_def
  apply (safe elim!: cte_wp_atE)
       apply (clarsimp split: if_split_asm
                              Structures_A.apiobject_type.split_asm
                        simp: default_object_def tyunt default_tcb_def
                              empty_cnode_def cte_wp_at_cases
                       dest!: orthr
                  | simp add: tcb_cap_cases_def)+
  done


lemma iflive_s: "if_live_then_nonz_cap s" by (rule valid_pspaceE [OF vp])

lemma default_object_not_live: "\<not> live (default_object ty dev us dm)"
  apply (cases ty, simp_all add: tyunt default_object_def default_tcb_not_live default_arch_object_not_live)
  apply (simp add: live_def live_ntfn_def live_sc_def live_reply_def default_ep_def
                   default_notification_def default_ntfn_def default_sched_context_def default_reply_def)+
  done

lemma iflive:
  "if_live_then_nonz_cap s'"
  using iflive_s unfolding if_live_then_nonz_cap_def s'_def ps_def
  apply -
  apply (clarsimp elim!: obj_atE simp: default_object_not_live split: if_split_asm)

  apply (frule(1) if_live_then_nonz_capD2[OF iflive_s])
  apply (simp add: ex_nonz_cap_to_def
                   cte_retype[unfolded s'_def ps_def])
  done


lemma final_retype: "is_final_cap' cap s' = is_final_cap' cap s"
  by (simp add: is_final_cap'_def2 cte_retype)


lemma not_final_NullCap: "\<And>s. \<not> is_final_cap' cap.NullCap s"
  by (simp add: is_final_cap'_def)


lemma zombies_s: "zombies_final s" by (rule valid_pspaceE[OF vp])


lemma zombies: "zombies_final s'"
  unfolding zombies_final_def
  by (clarsimp simp: final_retype is_zombie_def cte_retype not_final_NullCap
              elim!: zombies_finalD [OF _ zombies_s])

lemma replies_with_sc_subset:
  "replies_with_sc s' \<subseteq> replies_with_sc s"
  unfolding s'_def ps_def
  by (auto simp: replies_with_sc_def sc_at_ppred_def obj_at_def
                 default_object_def tyunt default_sched_context_def
          split: apiobject_type.splits)

lemma replies_blocked_subset:
  "replies_blocked s \<subseteq> replies_blocked s'"
  by (auto intro!: pred_tcb_at_pres simp: replies_blocked_def)

lemma valid_replies:
  "valid_replies s'"
  apply (rule valid_pspaceE[OF vp])
  apply (clarsimp simp: valid_replies_2_def)
  apply (rule conjI)
   apply (rule subset_trans[OF image_mono[OF replies_with_sc_subset]])
   apply (erule subset_trans[OF _ image_mono[OF replies_blocked_subset]])
  apply (clarsimp simp: inj_on_subset[OF _ replies_with_sc_subset])
  done

lemma fault_tcbs_valid_states:
  "fault_tcbs_valid_states s \<Longrightarrow> fault_tcbs_valid_states s'"
  apply (clarsimp simp: fault_tcbs_valid_states_def)
  apply (clarsimp simp: s'_def pred_tcb_at_def obj_at_def ps_def split: if_split_asm)
  apply (simp add: default_object_def tyunt split: Structures_A.apiobject_type.splits)
  apply (clarsimp simp: default_tcb_def)
  done

end

lemma (in retype_region_proofs_gen) valid_pspace: "valid_pspace s'"
  using vp by (simp add: valid_pspace_def valid_objs psp_al psp_dist
                         iflive zombies refs_eq hyp_refs_eq valid_replies
                         fault_tcbs_valid_states)

lemma caps_of_state_Some_simp: "\<And>x c s. (caps_of_state s x = Some c) = (cte_wp_at ((=) c) x s)"
  apply (simp add: caps_of_state_cte_wp_at)
  apply (fastforce simp: cte_wp_at_def)
  done

lemma null_filter_Some_simp: "\<And>x c s. (null_filter (caps_of_state s) x = Some c)
             = (cte_wp_at (\<lambda>cap. cap \<noteq> cap.NullCap \<and> cap = c) x s)"
  apply (simp add: null_filter_def caps_of_state_Some_simp)
  apply (fastforce simp: cte_wp_at_def)
  done

lemma None_null_filter_simp:
  "\<And>x s. (None = null_filter (caps_of_state s) x)
          = (\<forall>c. \<not> cte_wp_at (\<lambda>cap. cap \<noteq> cap.NullCap \<and> cap = c) x s)"
  apply safe
   apply (simp add: null_filter_Some_simp[symmetric])
  apply (rule sym, rule ccontr, clarsimp simp: null_filter_Some_simp)
  done

lemma (in retype_region_proofs) null_filter:
  "null_filter (caps_of_state s') = null_filter (caps_of_state s)"
  apply (rule ext)
  apply (case_tac "null_filter (caps_of_state s) x")
   apply (simp add: eq_commute)
   apply (simp add: None_null_filter_simp cte_retype)
  apply simp
  apply (simp add: null_filter_Some_simp cte_retype)
  done

context retype_region_proofs begin

lemma idle_s':
  "idle_thread s' = idle_thread s"
  by (simp add: s'_def ps_def)

lemma valid_idle:
  "valid_idle s \<Longrightarrow> valid_idle s'"
  by (clarsimp simp add: valid_idle_def s'_def ps_def pred_tcb_at_def obj_at_def orthr)

lemma arch_state [simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)

lemma irq_node [simp]:
  "interrupt_irq_node s' = interrupt_irq_node s"
  by (simp add: s'_def)

lemma caps_retype:
  assumes nonnull: "cap \<noteq> cap.NullCap"
  and      newcap: "caps_of_state s' p = Some cap"
  shows            "caps_of_state s p = Some cap"
proof -
  from newcap have "cte_wp_at ((=) cap) p s'"
    by (simp add: cte_wp_at_caps_of_state)
  hence "cte_wp_at ((=) cap) p s"
    by (rule_tac subst [OF cte_retype], rule_tac nonnull, assumption)
  thus ?thesis
    by (simp add: cte_wp_at_caps_of_state)
qed

end


lemma ran_null_filter:
  "ran (null_filter m) = (ran m - {cap.NullCap})"
  apply (simp add: null_filter_def ran_def cong: conj_cong)
  apply force
  done


lemma valid_irq_handlers_def2:
  "valid_irq_handlers =
     (\<lambda>s. \<forall>cap \<in> ran (null_filter (caps_of_state s)).
          \<forall>irq \<in> cap_irqs cap. interrupt_states s irq = irq_state.IRQSignal)"
  apply (rule ext)
  apply (simp add: valid_irq_handlers_def irq_issued_def
                   ran_null_filter)
  apply auto
  done


lemma p_in_obj_range:
  "\<lbrakk> kheap s p = Some ko; pspace_aligned s; valid_objs s \<rbrakk> \<Longrightarrow> p \<in> obj_range p ko"
  apply (simp add: pspace_aligned_def)
  apply (drule bspec, erule domI)
  apply (drule valid_obj_sizes, erule ranI)
  apply (simp add: obj_range_def add_diff_eq[symmetric])
  apply (erule is_aligned_no_wrap')
  apply (erule word_power_less_1[where 'a=machine_word_len, folded word_bits_def])
  done

lemma p_in_obj_range_internal:
  "\<lbrakk> kheap s (p && ~~ mask (obj_bits ko))= Some ko; pspace_aligned s; valid_objs s \<rbrakk>
  \<Longrightarrow> p \<in> obj_range (p && ~~ mask (obj_bits ko)) ko"
  apply (drule p_in_obj_range,simp+)
  apply (simp add: obj_range_def word_and_le2 word_neg_and_le p_assoc_help)
  done


context retype_region_proofs begin

lemma interrupt_states:
  "interrupt_states s' = interrupt_states s"
  by (simp add: s'_def)

lemma valid_irq_handlers:
  "valid_irq_handlers s \<Longrightarrow> valid_irq_handlers s'"
  by (simp add: valid_irq_handlers_def2 null_filter
                interrupt_states)

lemma mdb_and_revokable:
  "cdt s' = cdt s"
  "is_original_cap s' = is_original_cap s"
  by (simp add: s'_def)+

lemma cur_tcb:
  "cur_tcb s \<Longrightarrow> cur_tcb s'"
  apply (simp add: cur_tcb_def, rule obj_at_pres)
  apply (simp add: s'_def)
  done

lemma cur_sc_tcb:
  "cur_sc_tcb s \<Longrightarrow> cur_sc_tcb s'"
  apply (simp add: cur_sc_tcb_def sc_tcb_sc_at_def, rule obj_at_pres)
  apply (simp add: s'_def)
  done

lemma only_idle:
  "only_idle s \<Longrightarrow> only_idle s'"
  apply (clarsimp simp: only_idle_def)
  apply (clarsimp simp: s'_def pred_tcb_at_def obj_at_def ps_def split: if_split_asm)
  apply (simp add: default_object_def tyunt split: Structures_A.apiobject_type.splits)
  apply (clarsimp simp: default_tcb_def)
  done

lemma valid_irq_states:
  "valid_irq_states s \<Longrightarrow> valid_irq_states s'"
  apply(simp add: s'_def valid_irq_states_def)
  done

lemma cap_refs_in_kernel_window:
  "cap_refs_in_kernel_window s \<Longrightarrow> cap_refs_in_kernel_window s'"
  apply (simp add: cap_refs_in_kernel_window_def valid_refs_def)
  apply (simp add: cte_retype cap_range_def)
  done

lemma valid_ioc:
  "valid_ioc s \<Longrightarrow> valid_ioc s'"
  using cte_retype
  by (simp add: valid_ioc_def s'_def)

end

locale retype_region_proofs_invs
  = retype_region_proofs_gen s ty us ptr sz n ps s' dev
  + Retype_AI_post_retype_invs "TYPE('state_ext)" post_retype_invs_check post_retype_invs
  for s :: "'state_ext :: state_ext state"
  and ty us ptr sz n ps s' dev dm post_retype_invs_check
  and post_retype_invs :: "apiobject_type \<Rightarrow> machine_word list \<Rightarrow> 'state_ext state \<Rightarrow> bool" +
  fixes region_in_kernel_window :: "machine_word set \<Rightarrow> 'state_ext state \<Rightarrow> bool"
  assumes valid_global_refs: "valid_global_refs s \<Longrightarrow> valid_global_refs s'"
  assumes valid_arch_state: "valid_arch_state s \<Longrightarrow> valid_arch_state s'"
  assumes valid_vspace_objs': "\<lbrakk> invs s; valid_vspace_objs s \<rbrakk> \<Longrightarrow> valid_vspace_objs s'"
  assumes valid_cap:
    "(s::'state_ext state) \<turnstile> cap \<and>
        untyped_range cap \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} = {}
      \<Longrightarrow> s' \<turnstile> cap"
  assumes post_retype_invs:
    "\<lbrakk> invs (s :: 'state_ext state); region_in_kernel_window {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} s \<rbrakk>
        \<Longrightarrow> post_retype_invs ty (retype_addrs ptr ty n us) s'"

context Retype_AI_slot_bits begin

lemma use_retype_region_proofs':
  assumes x: "\<And>s. \<lbrakk> retype_region_proofs s ty us ptr sz n dev; P s \<rbrakk>
   \<Longrightarrow> Q (retype_addrs ptr ty n us) (s\<lparr>kheap :=
           \<lambda>x. if x \<in> set (retype_addrs ptr ty n us)
             then Some (default_object ty dev us (cur_domain s))
             else kheap s x\<rparr>)"
  assumes y: "\<And>x s f. Q x (trans_state f s) = Q x s"
  shows
    "\<lbrakk> ty = CapTableObject \<Longrightarrow> 0 < us;
       ty = SchedContextObject \<Longrightarrow> min_sched_context_bits \<le> us \<and> us \<le> untyped_max_bits;
         \<And>s. P s \<longrightarrow> Q (retype_addrs ptr ty n us) s \<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>s. valid_pspace s \<and> valid_mdb s \<and> range_cover ptr sz (obj_bits_api ty us) n
        \<and> caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1} s
        \<and> caps_no_overlap ptr sz s \<and> pspace_no_overlap_range_cover ptr sz s
        \<and> (\<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
        \<and> P s\<rbrace> retype_region ptr n us ty dev \<lbrace>Q\<rbrace>"
  apply (simp add: retype_region_def split del: if_split)
  apply (rule hoare_pre, (wp|simp add:y trans_state_update[symmetric] del: trans_state_update)+)
  apply (clarsimp simp: retype_addrs_fold
                        foldr_upd_app_if fun_upd_def[symmetric])
  apply safe
  apply (rule x)
   apply (rule retype_region_proofs.intro, simp_all)[1]

   apply (fastforce simp add: range_cover_def obj_bits_api_def
     slot_bits_def2 word_bits_def)+
  done
end


locale Retype_AI
  = Retype_AI_clearMemoryVM
  + Retype_AI_slot_bits
  + Retype_AI_retype_region_ret state_ext_t
  + Retype_AI_post_retype_invs state_ext_t post_retype_invs_check post_retype_invs
  + Retype_AI_obj_bits_api_neq_0
  + Retype_AI_no_gs_types no_gs_types
  + Retype_AI_dmo_eq_kernel_restricted state_ext_t machine_op_t
  for state_ext_t :: "'state_ext::state_ext itself"
  and post_retype_invs_check
  and post_retype_invs :: "apiobject_type \<Rightarrow> machine_word list \<Rightarrow> 'state_ext state \<Rightarrow> bool"
  and no_gs_types
  and machine_op_t :: "'machine_op_t itself" +
  fixes state_ext'_t :: "'state_ext'::state_ext itself"
  fixes region_in_kernel_window :: "machine_word set \<Rightarrow> 'state_ext state \<Rightarrow> bool"
  assumes invs_post_retype_invs:
    "\<And>(s::'state_ext state) ty refs. invs s \<Longrightarrow> post_retype_invs ty refs s"
  assumes equal_kernel_mappings_trans_state[simp]:
    "\<And>(f::'state_ext \<Rightarrow> 'state_ext') (s::'state_ext state).
      equal_kernel_mappings (trans_state f s) = equal_kernel_mappings s"
  assumes retype_region_proofs_assms:
    "\<And>s ty us ptr sz n dev.
      retype_region_proofs (s::'state_ext state) ty us ptr sz n dev
        \<Longrightarrow> retype_region_proofs_invs s ty us ptr sz n dev
                                      post_retype_invs_check post_retype_invs
                                      region_in_kernel_window"


context Retype_AI begin

lemmas use_retype_region_proofs
    = use_retype_region_proofs'[where Q="\<lambda>_. Q" and P=Q, simplified]
      for Q


lemma retype_region_proofs_assms':
  assumes "retype_region_proofs (s::'state_ext state) ty us ptr sz n dev"
  shows "retype_region_proofs_gen s ty us ptr sz n dev"
  using assms retype_region_proofs_assms
  by (auto simp: retype_region_proofs_invs_def)


lemmas retype_region_valid_pspace = use_retype_region_proofs
  [where Q=valid_pspace,
         OF retype_region_proofs_gen.valid_pspace[OF retype_region_proofs_assms'],
         simplified]


lemmas retype_region_caps_of = use_retype_region_proofs
  [where Q="\<lambda>s. P (null_filter (caps_of_state s))",
         OF ssubst [where P=P, OF retype_region_proofs.null_filter],
         simplified] for P


lemma retype_region_valid_cap:
  "\<lbrakk>ty = Structures_A.apiobject_type.CapTableObject \<Longrightarrow> 0 < us;
    ty = SchedContextObject \<Longrightarrow> min_sched_context_bits \<le> us \<and> us \<le> untyped_max_bits\<rbrakk>
   \<Longrightarrow> \<lbrace>(\<lambda>s::'state_ext state. valid_pspace s \<and> caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1} s \<and>
           valid_mdb s \<and> range_cover ptr sz (obj_bits_api ty us) n \<and>
           caps_no_overlap ptr sz s \<and> pspace_no_overlap_range_cover ptr sz s  \<and>
           (\<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s) \<and>
           s \<turnstile> cap) and K (untyped_range cap \<inter> {ptr..(ptr &&~~ mask sz) + 2 ^ sz - 1} = {})\<rbrace>
        retype_region ptr n us ty dev
      \<lbrace>\<lambda>r s. s \<turnstile> cap\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (rule use_retype_region_proofs)
    apply (erule retype_region_proofs_invs.valid_cap[OF retype_region_proofs_assms])
    apply simp+
  done


lemmas retype_region_aligned = use_retype_region_proofs
  [where Q=pspace_aligned,
         OF retype_region_proofs_gen.psp_al[OF retype_region_proofs_assms'],
         simplified]


lemmas retype_region_valid_idle = use_retype_region_proofs
  [where Q=valid_idle,
         OF retype_region_proofs.valid_idle,
         simplified]


lemmas retype_region_valid_arch = use_retype_region_proofs
  [where Q=valid_arch_state,
         OF retype_region_proofs_invs.valid_arch_state[OF retype_region_proofs_assms],
         simplified]


lemmas retype_region_valid_globals = use_retype_region_proofs
  [where Q=valid_global_refs,
         OF retype_region_proofs_invs.valid_global_refs[OF retype_region_proofs_assms],
         simplified]


lemmas retype_region_arch_objs = use_retype_region_proofs
  [where Q=valid_vspace_objs,
         OF retype_region_proofs_invs.valid_vspace_objs'[OF retype_region_proofs_assms],
         simplified]


crunch retype_region
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)

crunch retype_region
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps)


lemma invs_trans_state[simp]:
  "invs (trans_state f s) = invs s"
  apply (simp add: invs_def valid_state_def)
  done


lemma post_retype_invs_trans_state[simp]:
  "post_retype_invs ty refs (trans_state f s) = post_retype_invs ty refs s"
  apply (simp add: post_retype_invs_def')
  apply (simp add: trans_state_update[symmetric] del: trans_state_update)
  done


lemma retype_region_post_retype_invs:
  "\<lbrace>(invs::'state_ext state \<Rightarrow> bool) and caps_no_overlap ptr sz and pspace_no_overlap_range_cover ptr sz
      and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
      and region_in_kernel_window {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}
      and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
      and K (ty = Structures_A.CapTableObject \<longrightarrow> 0 < us)
      and K (ty = SchedContextObject \<longrightarrow> min_sched_context_bits \<le> us \<and> us \<le> untyped_max_bits)
      and K (range_cover ptr sz (obj_bits_api ty us) n) \<rbrace>
      retype_region ptr n us ty dev\<lbrace>\<lambda>rv. post_retype_invs ty rv\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule hoare_pre,
         rule use_retype_region_proofs'[where sz = sz
      and P="invs and region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1}"])
      apply (rule retype_region_proofs_invs.post_retype_invs
                  [OF retype_region_proofs_assms], simp+)
   apply (simp add: invs_post_retype_invs)
  apply (clarsimp simp:invs_def valid_state_def)
  done


lemma subset_not_le_trans: "\<lbrakk>\<not> A \<subset> B; C \<subseteq> B\<rbrakk> \<Longrightarrow> \<not> A \<subset> C" by auto


lemma cte_wp_at_trans_state[simp]: "cte_wp_at P ptr (kheap_update f (trans_state f' s)) =
       cte_wp_at P ptr (kheap_update f s)"
  by (simp add: trans_state_update[symmetric] del: trans_state_update)


lemma retype_region_cte_at_other:
  assumes cover: "range_cover ptr' sz (obj_bits_api ty us) n"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap_range_cover ptr' sz s \<and> cte_wp_at P ptr s \<and> valid_pspace s\<rbrace>
  retype_region ptr' n us ty dev \<lbrace>\<lambda>r. cte_wp_at P ptr\<rbrace>"
  unfolding retype_region_def
  apply (simp only: foldr_upd_app_if fun_app_def K_bind_def)
  apply wp
  apply (clarsimp simp: cte_wp_at_cases retype_addrs_fold del: disjCI)
  apply (auto dest!: pspace_no_overlapD1[OF _ _ cover])
  done


lemma retype_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at P ptr s \<and> pspace_no_overlap_range_cover ptr' sz s \<and>
       valid_pspace s \<and> range_cover ptr' sz (obj_bits_api ty us) n\<rbrace>
  retype_region ptr' n us ty dev
  \<lbrace>\<lambda>r. cte_wp_at P ptr\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_pre)
   apply (rule retype_region_cte_at_other)
   apply fastforce
  apply simp
  done


lemma pspace_no_overlap_typ_at_def:
  "pspace_no_overlap S =
  (\<lambda>s. \<forall>T x. typ_at T x s \<longrightarrow> {x..x + (2 ^ obj_bits_type T - 1)} \<inter> S = {})"
  apply (simp add: pspace_no_overlap_def obj_at_def)
  apply (rule ext)
  apply (auto simp: obj_bits_T)
  done


lemma pspace_no_overlap_typ_at_lift:
  assumes f: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows "\<lbrace>pspace_no_overlap S\<rbrace> f \<lbrace>\<lambda>rv. pspace_no_overlap S\<rbrace>"
  apply (clarsimp simp: pspace_no_overlap_typ_at_def)
  apply (wp hoare_vcg_all_lift f)
  done


lemma swp_clearMemoryVM [simp]:
  "swp clearMemoryVM x = (\<lambda>_. return ())"
  by (rule ext,simp)


(* FIXME: move *)
lemmas do_machine_op_bind =
    submonad_bind [OF submonad_do_machine_op submonad_do_machine_op
                      submonad_do_machine_op]


(* FIXME: move *)
lemmas do_machine_op_return =
    submonad_do_machine_op.return


lemma ioc_more_swap[simp]: "
    s'\<lparr>exst := sa',
         is_original_cap := sa\<rparr> =
    s'\<lparr>is_original_cap := sa,
         exst := sa'\<rparr>"
  apply simp
  done


lemma is_final_cap'_more_update[simp]:
  "is_final_cap' cap (trans_state f s) = is_final_cap' cap s"
  by (simp add: is_final_cap'_def)


lemma no_cap_to_obj_with_diff_ref_more_update[simp]:
  "no_cap_to_obj_with_diff_ref cap sl (trans_state f s) =
   no_cap_to_obj_with_diff_ref cap sl s"
  by (simp add: no_cap_to_obj_with_diff_ref_def)

end

(* FIXME: irq_state stuff moved from CNodeInv_AI, not clear it makes sense here. *)

lemma cte_wp_at_irq_state_independent[intro!, simp]:
  "is_final_cap' x (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = is_final_cap' x s"
  by (simp add: is_final_cap'_def)

lemma ex_cte_cap_wp_to_irq_state_independent[intro!, simp]:
  "ex_cte_cap_wp_to x y (s\<lparr>machine_state := machine_state s\<lparr>irq_state := f (irq_state (machine_state s))\<rparr>\<rparr>)
   = ex_cte_cap_wp_to x y s"
  by (simp add: ex_cte_cap_wp_to_def)

lemma cte_wp_at_machine_state_time_update_independent[intro!, simp]:
  "is_final_cap' x (s\<lparr>machine_state := machine_state s\<lparr>time_state := f (time_state (machine_state s))\<rparr>\<rparr>)
   = is_final_cap' x s"
  "is_final_cap' x (s\<lparr>machine_state := machine_state s\<lparr>last_machine_time :=
                             g (last_machine_time (machine_state s)) (time_state (machine_state s))\<rparr>\<rparr>)
   = is_final_cap' x s"
  by (simp add: is_final_cap'_def)+

lemma cte_wp_at_update_time_stamp_independent[intro!, simp]:
  "is_final_cap' x (s\<lparr>cur_time := f (cur_time s)\<rparr>)
   = is_final_cap' x s"
  "is_final_cap' x (s\<lparr>consumed_time := g (consumed_time s) (cur_time s)\<rparr>)
   = is_final_cap' x s"
  by (simp add: is_final_cap'_def)+

lemma ex_cte_cap_wp_to_machine_state_time_update_independent[intro!, simp]:
  "ex_cte_cap_wp_to x y (s\<lparr>machine_state := machine_state s\<lparr>time_state := f (time_state (machine_state s))\<rparr>\<rparr>)
   = ex_cte_cap_wp_to x y s"
  "ex_cte_cap_wp_to x y (s\<lparr>machine_state := machine_state s\<lparr>last_machine_time :=
                           g (last_machine_time (machine_state s)) (time_state (machine_state s))\<rparr>\<rparr>)
   = ex_cte_cap_wp_to x y s"
  by (simp add: ex_cte_cap_wp_to_def)+

lemma ex_cte_cap_wp_to_update_time_stamp_independent[intro!, simp]:
  "ex_cte_cap_wp_to x y (s\<lparr>cur_time := f (cur_time s)\<rparr>)
   = ex_cte_cap_wp_to x y s"
  "ex_cte_cap_wp_to x y (s\<lparr>consumed_time := g (consumed_time s) (cur_time s)\<rparr>)
   = ex_cte_cap_wp_to x y s"
  by (simp add: ex_cte_cap_wp_to_def)+

end
