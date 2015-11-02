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
Retype refinement
*)

theory Retype_AI
imports VSpace_AI
begin

lemma upto_enum_inc_1:
  "a < 2^word_bits - 1 \<Longrightarrow> [(0::word32).e.1 + a] = [0.e.a] @ [(1+a)]"
  apply (simp add:upto_enum_word)
  apply (subgoal_tac "unat (1 +a) = 1 + unat a")
    apply simp
   apply (subst unat_plus_simple[THEN iffD1])
   apply (rule word_plus_mono_right2[where b = "2^32 - 2"])
    apply (simp add:word_bits_def minus_one_norm)+
    apply unat_arith
   apply simp
 done

(* FIXME: move *)
lemma monad_eq_split: 
  assumes tail:"\<And>r s. Q r s \<Longrightarrow> f r s = f' r s"
  and hoare:   "\<lbrace>P\<rbrace>g\<lbrace>\<lambda>r s. Q r s\<rbrace>" "P s"
  shows "(g>>=f) s = (g>>= f') s"
proof -
  have pre: "\<And>aa bb. \<lbrakk>(aa, bb) \<in> fst (g s)\<rbrakk> \<Longrightarrow> Q aa bb"
  using hoare
  apply (clarsimp simp:valid_def)
  apply (erule_tac x = s in allE)
  apply simp
  apply (drule bspec)
   apply simp
  apply simp
  done
  show ?thesis
  apply (simp add:bind_def image_def)
  apply (intro conjI)
   apply (rule set_eqI)+
   apply (clarsimp simp:Union_eq)
   apply (rule iffI)
    apply clarsimp
    apply (rule_tac x=x in exI)
    apply (clarsimp simp: tail[OF pre])
    apply (rule exI)
    apply (rule_tac x = "(aa,bb)" in bexI)
     apply simp
    apply clarsimp+
   apply (rule_tac x=x in exI)
   apply (clarsimp simp: tail[symmetric,OF pre])
   apply (rule exI)
   apply (rule_tac x = "(aa,bb)" in bexI)
    apply simp
   apply clarsimp
  apply (rule iffI)
   apply (clarsimp simp: tail[OF pre])
   apply (rule exI)
   apply (rule_tac x = "(aa,b)" in bexI)
    apply simp
   apply (clarsimp simp: tail[symmetric,OF pre])+
  apply (rule exI)
  apply (rule_tac x = "(aa,b)" in bexI)
   apply simp
  apply clarsimp
  done
qed


lemma clearMemoryVM_return [simp]:
  "clearMemoryVM a b = return ()"
  by (simp add: clearMemoryVM_def storeWordVM_def)


lemma clearMemoryVM_return_raw:
  "clearMemoryVM  = (\<lambda>x y. return ())"
  apply (rule ext)+
  by (simp add: clearMemoryVM_def storeWordVM_def)

lemma unat_of_nat_minus_1:
  "\<lbrakk>n < 2^len_of TYPE('a);n\<noteq> 0\<rbrakk> \<Longrightarrow> (unat (((of_nat n):: 'a :: len word) - 1)) = n - 1"
  apply (subst unat_minus_one)
   apply (rule of_nat_neq_0)
     apply simp
   apply (simp add:of_nat_neq_0 word_bits_def)
   apply (simp add:unat_of_nat word_bits_def)
  done


definition monad_commute where
  "monad_commute P a b \<equiv> 
  (\<forall>s. (P s \<longrightarrow> ((do x\<leftarrow>a;y\<leftarrow>b; return (x, y) od) s) = ((do y\<leftarrow>b;x\<leftarrow>a; return (x, y) od) s)))"


lemma monad_eq:
  "a s = b s \<Longrightarrow>  (a >>= g) s = (b >>= g) s"
  by (auto simp:bind_def)


lemma monad_commute_simple:
  "\<lbrakk>monad_commute P a b;P s\<rbrakk> \<Longrightarrow> ((do x\<leftarrow>a;y\<leftarrow>b; g x y od) s) = ((do y\<leftarrow>b;x\<leftarrow>a; g x y od) s)"
  apply (clarsimp simp:monad_commute_def)
  apply (drule spec)
  apply (erule(1) impE)
  apply (drule_tac g = "(\<lambda>t. g (fst t) (snd t))" in monad_eq)
  apply (simp add:bind_assoc)
  done


lemma commute_commute:
  "monad_commute P f h \<Longrightarrow> monad_commute P h f"
  apply (simp (no_asm) add: monad_commute_def)
  apply (clarsimp)
  apply (erule monad_commute_simple[symmetric])
  apply simp
  done


lemma assert_commute: "monad_commute (K G) (assert G) f"
  by (clarsimp simp:assert_def monad_commute_def)


lemma cond_fail_commute: "monad_commute (K (\<not>G)) (when G fail) f"
  by (clarsimp simp:when_def fail_def monad_commute_def)


lemma return_commute: "monad_commute \<top> (return a) f"
  by (clarsimp simp: return_def bind_def monad_commute_def)


lemma monad_commute_guard_imp:
  "\<lbrakk>monad_commute P f h; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow> monad_commute Q f h"
  by (clarsimp simp:monad_commute_def)


lemma monad_commute_split:
  "\<lbrakk>\<And>r. monad_commute (Q r) f (g r); monad_commute P f h;
         \<lbrace>P'\<rbrace> h \<lbrace>\<lambda>r. Q r\<rbrace>\<rbrakk>
   \<Longrightarrow> monad_commute (P and P') f (h>>=g)"
  apply (simp (no_asm) add:monad_commute_def)
   apply (clarsimp simp:bind_assoc)
   apply (subst monad_commute_simple)
    apply simp+
   apply (rule_tac Q = "(\<lambda>x. Q x)" in monad_eq_split)
   apply (subst monad_commute_simple[where a = f])
    apply assumption
    apply simp+
  done


lemma monad_commute_get:
  assumes hf: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>r. P\<rbrace>"
  and hg: "\<And>P. \<lbrace>P\<rbrace> g \<lbrace>\<lambda>r. P\<rbrace>"
  and eptyf: "empty_fail f" "empty_fail g"
  shows "monad_commute \<top> f g"
proof -
  have fsame: "\<And>a b s. (a,b) \<in> fst (f s) \<Longrightarrow> b = s"
    by (drule use_valid[OF _ hf],auto)
  have gsame: "\<And>a b s. (a,b) \<in> fst (g s) \<Longrightarrow> b = s"
    by (drule use_valid[OF _ hg],auto)
  note ef = empty_fail_not_snd[OF _ eptyf(1)]
  note eg = empty_fail_not_snd[OF _ eptyf(2)]
  show ?thesis
  apply (simp add:monad_commute_def)
  apply (clarsimp simp:bind_def split_def return_def)
  apply (intro conjI)
   apply (rule set_eqI)
    apply (rule iffI)
    apply (clarsimp simp:Union_eq dest!: singletonD)
    apply (frule fsame)
    apply clarsimp
    apply (frule gsame)
    apply (metis fst_conv snd_conv)
   apply (clarsimp simp:Union_eq dest!: singletonD)
   apply (frule gsame)
   apply clarsimp
   apply (frule fsame)
   apply clarsimp
   apply (metis fst_conv snd_conv)
  apply (rule iffI)
   apply (erule disjE)
    apply (clarsimp simp:image_def)
    apply (metis fsame)
   apply (clarsimp simp:image_def)
   apply (drule eg)
   apply clarsimp
   apply (rule bexI [rotated], assumption)
   apply (frule gsame)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp:image_def dest!:gsame)
  apply (clarsimp simp:image_def)
  apply (drule ef)
  apply clarsimp
  apply (frule fsame)
  apply (erule bexI[rotated])
  apply simp
  done
qed


lemma range_to_bl':
  "\<lbrakk> is_aligned (ptr :: 'a :: len word) bits; bits < len_of TYPE('a) \<rbrakk> \<Longrightarrow>
   {ptr .. ptr + (2 ^ bits) - 1} = {x. take (len_of TYPE('a) - bits) (to_bl x)
                                        = take (len_of TYPE('a) - bits) (to_bl ptr)}"
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (subgoal_tac "\<exists>y. x = ptr + y \<and> y < 2 ^ bits")
    apply clarsimp
    apply (subst is_aligned_add_conv)
       apply assumption
      apply simp
    apply simp
   apply (rule_tac x="x - ptr" in exI)
   apply (simp add: add_diff_eq[symmetric])
   apply (simp only: word_less_sub_le[symmetric])
   apply (rule word_diff_ls')
    apply (simp add: field_simps)
   apply assumption
  apply simp
  apply (subgoal_tac "\<exists>y. y < 2 ^ bits \<and> to_bl (ptr + y) = to_bl x")
   apply clarsimp
   apply (rule conjI)
    apply (erule(1) is_aligned_no_wrap')
   apply (simp only: add_diff_eq[symmetric])
   apply (rule word_plus_mono_right)
    apply simp
   apply (erule is_aligned_no_wrap')
   apply simp
  apply (rule_tac x="of_bl (drop (len_of TYPE('a) - bits) (to_bl x))" in exI)
  apply (rule context_conjI)
   apply (rule order_less_le_trans [OF of_bl_length])
    apply simp
   apply simp
  apply (subst is_aligned_add_conv)
     apply assumption
    apply simp
  apply (drule sym)
  apply (simp add: word_rep_drop)
  done


lemma range_to_bl:
  "is_aligned (ptr :: 'a :: len word) bits \<Longrightarrow>
   {ptr..ptr + 2 ^ bits - 1} =
     {x. take (len_of TYPE('a) - bits) (to_bl x) =
         take (len_of TYPE('a) - bits) (to_bl ptr)}"
  apply (erule is_aligned_get_word_bits)
   apply (erule(1) range_to_bl')
  apply (rule set_eqI)
  apply (simp add: power_overflow)
  done


lemma aligned_ranges_subset_or_disjoint:
  "\<lbrakk> is_aligned (p :: 'a :: len word) n; is_aligned (p' :: 'a :: len word) n' \<rbrakk>
     \<Longrightarrow> {p .. p + 2 ^ n - 1} \<inter> {p' .. p' + 2 ^ n' - 1} = {}
      \<or> {p .. p + 2 ^ n - 1} \<subseteq> {p' .. p' + 2 ^ n' - 1}
      \<or> {p .. p + 2 ^ n - 1} \<supseteq> {p' .. p' + 2 ^ n' - 1}"
  apply (simp add: range_to_bl)
  apply (rule disjCI2)
  apply (erule nonemptyE)
  apply simp
  apply (subgoal_tac "(\<exists>n''. len_of TYPE('a) - n = (len_of TYPE('a) - n') + n'')
                    \<or> (\<exists>n''. len_of TYPE('a) - n' = (len_of TYPE('a) - n) + n'')")
   apply (elim conjE disjE exE)
    apply (rule disjI1)
    apply (clarsimp simp: take_add)
   apply (rule disjI2)
   apply (clarsimp simp: take_add)
  apply arith
  done

lemma aligned_diff:
  "\<lbrakk>is_aligned (dest :: 'a :: len word) bits; is_aligned (ptr :: 'a :: len word) sz; bits \<le> sz; sz < len_of TYPE('a);
    dest < ptr\<rbrakk>
   \<Longrightarrow> (2^ bits - 1) + dest < ptr"
  apply (frule_tac p' = ptr in aligned_ranges_subset_or_disjoint)
   apply assumption
  apply (elim disjE)
    apply clarsimp
    apply (drule_tac ptr = dest in is_aligned_no_overflow)
     apply simp
    apply (drule is_aligned_no_overflow)
    apply clarsimp
    apply (erule impE)
     apply (erule order_trans[OF less_imp_le])
     apply (clarsimp simp:field_simps)
    apply (clarsimp simp:not_less field_simps not_le)
   apply clarsimp
   apply (drule_tac ptr = dest in is_aligned_no_overflow)
    apply simp
   apply fastforce
  apply clarsimp
  apply (frule is_aligned_no_overflow)
  apply (erule impE)
  apply (frule(1) is_aligned_no_overflow)
  apply (rule ccontr)
  apply (clarsimp simp:not_less p_assoc_help)
  apply (subst (asm) add.commute[where b = "(2^ sz - 1)"])
  apply (subst (asm) add.commute[where b = "(2^ bits - 1)"])+
  apply (drule word_sub_mono2)
   apply (rule word_le_minus_mono_left)
   apply (erule(1) two_power_increasing)
   apply (simp add:word_1_le_power)
   apply (simp add:field_simps is_aligned_no_overflow)+
  done


lemma default_object_tcbE:
  "\<lbrakk> default_object ty us = TCB tcb; ty \<noteq> Untyped; 
   \<lbrakk> tcb = default_tcb; ty = Structures_A.TCBObject \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding default_object_def by (cases ty, auto)


lemma obj_bits_api_default_object:
  "\<lbrakk> ty \<noteq> Untyped\<rbrakk> \<Longrightarrow> obj_bits_api ty us
          = obj_bits (default_object ty us)"
  unfolding obj_bits_api_def default_object_def
  by (cases ty) 
     (simp_all add: slot_bits_def wf_empty_bits cte_level_bits_def)


lemma obj_bits_api_default_CapTableObject:
  "obj_bits (default_object Structures_A.apiobject_type.CapTableObject us) 
  = cte_level_bits + us"
  unfolding default_object_def 
  by (simp add: cte_level_bits_def wf_empty_bits)


lemma empty_cnode_dom:
  "x \<in> dom (empty_cnode n) \<Longrightarrow> length x = n"
  unfolding dom_def empty_cnode_def by (simp split: split_if_asm)


lemma obj_bits_api_def2:
  "obj_bits_api type obj_size_bits =
   (case type of Structures_A.Untyped \<Rightarrow> obj_size_bits
           | _ \<Rightarrow> obj_bits (default_object type obj_size_bits))" 
  by (simp add: obj_bits_api_def default_object_def obj_bits.simps
                wf_empty_bits dom_empty_cnode ex_with_length
                slot_bits_def cte_level_bits_def
         split: Structures_A.apiobject_type.split)


lemma obj_bits_api_def3:
  "obj_bits_api type obj_size_bits =
   (if type = Structures_A.Untyped then obj_size_bits
     else obj_bits (default_object type obj_size_bits))"
  by (simp add: obj_bits_api_def2 split: Structures_A.apiobject_type.split)


definition
  "retype_addrs \<equiv> \<lambda>ptr' ty n us. map (\<lambda>p. ptr_add ptr' (p * 2 ^ obj_bits_api ty us))
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
  "pspace_no_overlap ptr bits (f s) = pspace_no_overlap ptr bits s"
  by (simp add: pspace_no_overlap_def pspace)

(* FIXME: move *)
lemma multi_lessD:
  "\<lbrakk>(a::nat)*b < c;0<a;0<b\<rbrakk> \<Longrightarrow> a < c \<and> b < c"
  by (cases a, simp_all,cases b,simp_all)

lemma unat_le_helper:
  "(x :: 'a :: len word) \<le> of_nat n \<Longrightarrow> unat x \<le> n"
  apply (case_tac "x = of_nat n")
    apply (simp add:unat_of_nat)
  apply (rule less_imp_le[OF unat_less_helper])
  apply simp
  done


lemma word_of_nat_plus:
  "of_nat (a + b) = of_nat a + (of_nat b :: ('a :: len) word)"
  by (rule of_nat_add)


lemma word_of_nat_minus:
   "b<= a ==> of_nat (a - b) = of_nat a - (of_nat b :: ('a :: len) word)"
   by (simp add: word_of_nat word_of_int_hom_syms)


lemma unat_shiftl_absorb:
  "\<lbrakk>x \<le> 2^p ; p + k < len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> unat (x :: 'a :: len word) * 2^k = unat (x * 2^k)"
  apply (simp add:unat_word_ariths)
  apply (subst mod_less)
   apply (rule le_less_trans[OF mult_le_mono1])
    apply (erule iffD1[OF word_le_nat_alt])
   apply (clarsimp simp: power_add[symmetric])+
  done


lemma word_up_bound:
  "(ptr::('a::len) word) \<le> 2^(len_of TYPE('a)) - 1 "
  by auto


lemma word_plus_mono_right_split:
  "\<lbrakk>unat ((x :: 'a :: len word) && mask sz) + unat z < 2 ^ sz ; sz < len_of TYPE('a)\<rbrakk>
   \<Longrightarrow>x \<le> x + z"
  (is "\<lbrakk>?bound;?len\<rbrakk> \<Longrightarrow>?rhs \<le> ?lhs")
  apply (subgoal_tac "(x && ~~ mask sz) + (x && mask sz) \<le> (x && ~~ mask sz) + ((x && mask sz) + z)")
   apply (simp add:word_plus_and_or_coroll2 field_simps)
  apply (rule word_plus_mono_right)
    apply (simp add:no_olen_add )
    apply (rule less_le_trans)
    apply (simp add:uint_nat)
    apply (subst zadd_int)
    apply (drule iffD2[OF zless_int])
    apply simp
    apply (rule less_imp_le)
    apply (rule less_le_trans[where y = "2^len_of TYPE('a)"] )
    apply simp
   apply (simp add:word_bits_def)
  apply (rule word_plus_mono_right2)
    apply (rule is_aligned_no_overflow')
    apply (rule is_aligned_neg_mask[OF le_refl])
   apply (rule le_m1_iff_lt[THEN iffD1,THEN iffD2])
     apply (simp add:p2_gt_0 word_bits_def)
   apply (rule iffD2[OF word_less_nat_alt])
   apply (auto simp:unat_plus_if_size word_size word_bits_def not_less)
  done

lemmas word32_plus_mono_right_split = word_plus_mono_right_split[where 'a=32, folded word_bits_def]


(* range_cover locale:
   proves properties when a small range is inside in a large range
 *)
locale range_cover = 
  fixes ptr :: "'a :: len word"
  and   sz sbit n
  assumes aligned: "is_aligned ptr sbit"
  and sz:"sz< len_of TYPE('a)" "sbit \<le> sz" "n + unat (ptr && mask sz >> sbit) \<le> 2 ^ (sz - sbit)"
begin
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
   apply (rule le_less_trans[OF mod_le_dividend])
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
  apply (simp add:unat_of_nat)
  done


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
  using assms
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
      apply (subst decomp)
      apply (simp add:add.assoc[symmetric])
      apply (simp add:p_assoc_help)
      apply (rule order_trans[OF word_plus_mono_left word_plus_mono_right])
         apply (rule word_plus_mono_right)
          apply (rule word_mult_le_mono1[OF word_of_nat_le])
          apply (insert n_less not_0 pointer)
            apply (simp add:unat_of_nat_minus_1)
           apply (rule p2_gt_0[THEN iffD2])
           using cover
           apply (simp add:word_bits_def range_cover_def)
          using cover
          apply (simp only: word_bits_def[symmetric] unat_power_lower range_cover_def)
          apply (clarsimp simp: unat_of_nat_minus_1 )
          apply (rule nat_less_power_trans2[OF range_cover.range_cover_le_n_less(2),OF cover])
          apply (simp add:unat_of_nat_m1 less_imp_le)
         using cover
         apply (simp add:range_cover_def)
        apply (rule word_plus_mono_right_split[where sz = sz])
        using range_cover.range_cover_compare[OF cover,where p = "unat (of_nat n - (1 :: 'a :: len word))"]
        apply (clarsimp simp:unat_of_nat_m1)
       using cover
       apply (simp add:range_cover_def)
      apply (rule olen_add_eqv[THEN iffD2])
      apply (subst add.commute[where a = "2^sbit - 1"])
     apply (subst p_assoc_help[symmetric])
     apply (rule is_aligned_no_overflow)
     apply (insert cover)
     apply (clarsimp simp:range_cover_def)
     apply (erule aligned_add_aligned[OF _  is_aligned_mult_triv2])
       apply (simp add:range_cover_def)+
   done
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


lemma unat_plus_gt:
  "unat ((a::('a::len word)) + b) \<le>  (unat a + unat b)"
  by (clarsimp simp:unat_plus_if_size)


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
   apply (clarsimp simp:unat_power_lower range_cover_def)
  apply (insert cover)
  apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask,OF le_refl ])
   apply (simp add:range_cover_def)+
done


lemma pspace_no_overlapE:
  "\<lbrakk> pspace_no_overlap ptr sz s; kheap s x = Some ko;
  {x..x + (2 ^ obj_bits ko - 1)} \<inter> {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} = {} \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
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


lemma pspace_no_overlap_into_Int_none:
  assumes ps: "pspace_no_overlap ptr sz s"
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
          by (auto elim!: valid_pspaceE pspace_alignedE)
        show "obj_bits ko < len_of TYPE(32)"
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
  "\<lbrakk> pspace_no_overlap ptr sz s; kheap s x = Some ko;
  range_cover ptr sz (obj_bits_api ty us) n; 
  valid_pspace s\<rbrakk> \<Longrightarrow>
  x \<notin> set (retype_addrs ptr ty n us)"
  apply (drule(2) pspace_no_overlap_into_Int_none)
   apply (simp add:range_cover_def)
  apply (erule orthD2)
  apply (erule domI)
  done


lemma pspace_no_overlapD2:
  "\<lbrakk> pspace_no_overlap ptr sz s; x \<in> set (retype_addrs ptr ty n us);
  range_cover ptr sz (obj_bits_api ty us) n;
   valid_pspace s \<rbrakk> \<Longrightarrow> x \<notin> dom (kheap s)"
  apply (drule(2) pspace_no_overlap_into_Int_none)
   apply (simp add:range_cover_def)
  apply (erule(1) orthD1)
done


lemma pspace_no_overlapC:
  "\<lbrakk> pspace_no_overlap ptr sz s; x \<in> set (retype_addrs ptr ty n us); kheap s x = Some ko;
  range_cover ptr sz (obj_bits_api ty us) n;valid_pspace s \<rbrakk> \<Longrightarrow> P"
  by (auto dest: pspace_no_overlapD1)


lemma null_filterE:
  "\<lbrakk> null_filter cps x = Some cap;
      \<lbrakk> cps x = Some cap; cap \<noteq> cap.NullCap \<rbrakk> \<Longrightarrow> R \<rbrakk>
     \<Longrightarrow> R"
  by (simp add: null_filter_def split: split_if_asm)


lemma across_null_filter_eq:
  assumes eq: "null_filter xs = null_filter ys"
  shows "\<lbrakk> xs x = Some v; ys x = Some v \<Longrightarrow> R;
           \<lbrakk> v = cap.NullCap; ys x = None \<rbrakk> \<Longrightarrow> R \<rbrakk>
          \<Longrightarrow> R"
  apply (cases "null_filter xs x")
   apply (subgoal_tac "null_filter ys x = None")
    apply (simp add: null_filter_def split: split_if_asm)
   apply (simp add: eq)
  apply (subgoal_tac "null_filter ys x = Some a")
   apply (simp add: null_filter_def split: split_if_asm)
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
  fixes s sz ptr us addrs
  defines "s' \<equiv> (s\<lparr>kheap := foldr (\<lambda>p ps. ps(p \<mapsto> default_object ty us)) 
                  addrs (kheap s)\<rparr>)"
  shows
  "caps_of_state s' =
  (\<lambda>(oref,cref). if oref \<in> set addrs
                 then (case ty of Structures_A.CapTableObject \<Rightarrow> empty_cnode us
                               | Structures_A.TCBObject \<Rightarrow> option_map (\<lambda>x. cap.NullCap) \<circ> tcb_cap_cases
                               | _ \<Rightarrow> empty) cref
                 else caps_of_state s (oref,cref))"
  apply (rule ext)+
  apply (case_tac x)
  apply (rename_tac oref cref)
  apply (simp add: caps_of_state_cte_wp_at split del: split_if)
  apply (case_tac "\<exists>cap. cte_wp_at (op = cap) (oref, cref) s'")
   apply clarsimp
   apply (simp add: s'_def cte_wp_at_cases)
   apply (erule disjE)
    apply (clarsimp simp add: foldr_upd_app_if default_object_def caps_of_state_cte_wp_at
                     cte_wp_at_cases tyun empty_cnode_def
           split: split_if_asm Structures_A.apiobject_type.splits)
   apply (clarsimp simp add: foldr_upd_app_if default_object_def caps_of_state_cte_wp_at
                             cte_wp_at_cases tyun empty_cnode_def default_tcb_def
          split: split_if_asm Structures_A.apiobject_type.splits)
   apply (clarsimp simp: tcb_cap_cases_def split: split_if_asm)
  apply simp
  apply (simp add: cte_wp_at_cases s'_def foldr_upd_app_if)
  apply (rule conjI)
   apply (clarsimp simp: default_object_def wf_empty_bits
                  split: Structures_A.apiobject_type.split_asm)
   apply (fastforce simp: tcb_cap_cases_def split: split_if_asm)
  apply clarsimp
  apply (simp add: caps_of_state_cte_wp_at)
  apply (simp add: cte_wp_at_cases)
  done


lemma null_filter_caps_of_state_foldr:
  fixes s sz ptr us addrs
  assumes tyun: "ty \<noteq> Untyped"
    and nondom: "\<forall>x \<in> set addrs. x \<notin> dom (kheap s)"
  defines "s' \<equiv> (s\<lparr>kheap := foldr (\<lambda>p ps. ps(p \<mapsto> default_object ty us)) 
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


definition
  "no_gs_types \<equiv> UNIV - {Structures_A.CapTableObject,
     ArchObject SmallPageObj, ArchObject LargePageObj,
     ArchObject SectionObj, ArchObject SuperSectionObj}"


lemma no_gs_types_simps[simp]:
  "Untyped \<in> no_gs_types"
  "Structures_A.TCBObject \<in> no_gs_types"
  "Structures_A.EndpointObject \<in> no_gs_types"
  "Structures_A.NotificationObject \<in> no_gs_types"
  "ArchObject PageTableObj \<in> no_gs_types"
  "ArchObject PageDirectoryObj \<in> no_gs_types"
  "ArchObject ASIDPoolObj \<in> no_gs_types"
by (simp_all add: no_gs_types_def)


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
  apply (rule is_aligned_no_overflow[OF is_aligned_neg_mask ,OF le_refl])
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
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
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


lemma list_all2_same:
  "list_all2 P xs xs = (\<forall>x \<in> set xs. P x x)"
  apply (simp add: list_all2_iff set_zip in_set_conv_nth Ball_def)
  apply fastforce
  done


lemma retype_region_ret_folded:
  "\<lbrace>\<top>\<rbrace> retype_region y n bits ty 
   \<lbrace>\<lambda>r s. r = retype_addrs y ty n bits\<rbrace>"
  unfolding retype_region_def
  apply (simp add: pageBits_def)
  apply wp
   apply (simp add:retype_addrs_def)
done


lemmas retype_region_ret = retype_region_ret_folded[unfolded retype_addrs_def]


crunch global_refs[wp]: retype_region "\<lambda>s. P (global_refs s)"
  (simp: crunch_simps)


lemma retype_region_global_refs_disjoint:
  "\<lbrace>(\<lambda>s. {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<inter> global_refs s = {})
            and K (range_cover ptr sz (obj_bits_api apiobject_type obits) n)\<rbrace>
     retype_region ptr n obits apiobject_type 
   \<lbrace>\<lambda>r s. global_refs s \<inter> set r = {}\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_lift_Pf3[where f=global_refs])
   apply (rule hoare_assume_pre)
   apply (clarsimp simp: Int_commute)
   apply (rule hoare_chain, rule retype_region_ret)
    apply simp
   apply (erule disjoint_subset2[rotated])
   apply (rule subsetI, simp only: mask_in_range[symmetric])
   apply (clarsimp simp: ptr_add_def)
   apply (intro conjI)
     apply (rule word32_plus_mono_right_split[where sz = sz])
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


crunch valid_pspace: do_machine_op "valid_pspace"


declare store_pde_state_refs_of [wp]


(* FIXME: move to Machine_R.thy *)
lemma clearMemory_corres:
  "corres_underlying Id True dc \<top> (\<lambda>_. is_aligned y 2)
     (clearMemory y a) (clearMemory y a)"
  apply (rule corres_Id)
   apply simp+
  done


(* These also prove facts about copy_global_mappings *)
crunch pspace_aligned[wp]: init_arch_objects "pspace_aligned"
  (ignore: clearMemory wp: crunch_wps)
crunch pspace_distinct[wp]: init_arch_objects "pspace_distinct"
  (ignore: clearMemory wp: crunch_wps)
crunch mdb_inv[wp]: init_arch_objects "\<lambda>s. P (cdt s)"
  (ignore: clearMemory wp: crunch_wps)
crunch valid_mdb[wp]: init_arch_objects "valid_mdb"
  (ignore: clearMemory wp: crunch_wps)
crunch cte_wp_at[wp]: init_arch_objects "\<lambda>s. P (cte_wp_at P' p s)"
  (ignore: clearMemory wp: crunch_wps)
crunch typ_at[wp]: init_arch_objects "\<lambda>s. P (typ_at T p s)"
  (ignore: clearMemory wp: crunch_wps)

lemma mdb_cte_at_store_pde[wp]:
  "\<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)\<rbrace>
   store_pde y pde
   \<lbrace>\<lambda>r s. mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wp hoare_vcg_disj_lift hoare_vcg_all_lift)
done

lemma get_pde_valid[wp]:
  "\<lbrace>valid_arch_objs 
    and \<exists>\<rhd> (x && ~~mask pd_bits) 
    and K (ucast (x && mask pd_bits >> 2) \<notin> kernel_mapping_slots)\<rbrace> 
   get_pde x 
   \<lbrace>valid_pde\<rbrace>"
  apply (simp add: get_pde_def)
  apply wp
  apply clarsimp
  apply (drule (2) valid_arch_objsD)
  apply simp
  done

lemma get_master_pde_valid[wp]:
  "\<lbrace>valid_arch_objs
    and \<exists>\<rhd> (x && ~~mask pd_bits)
    and K (ucast (x && mask pd_bits >> 2) \<notin> kernel_mapping_slots)\<rbrace>
   get_master_pde x
   \<lbrace>valid_pde\<rbrace>"
  apply (simp add: get_master_pde_def get_pde_def)
  apply (wp hoare_vcg_imp_lift hoare_vcg_all_lift | wpc)+
     defer
     apply (clarsimp simp: mask_lower_twice pd_bits_def pageBits_def)+
  apply (drule sym)
  apply (drule (1) ko_at_obj_congD, clarsimp)
  apply (drule (2) valid_arch_objsD)
  apply simp
  apply (erule notE, erule bspec)
  apply (clarsimp simp: kernel_mapping_slots_def not_le)
  apply (erule le_less_trans[rotated])
  apply (rule ucast_mono_le)
   apply (rule le_shiftr)
   apply (clarsimp simp: word_bw_comms)
   apply (clarsimp simp: word_bool_alg.conj_assoc[symmetric])
   apply (subst word_bw_comms, rule word_and_le2)
  apply (rule shiftr_less_t2n)
  apply (clarsimp simp: pd_bits_def pageBits_def and_mask_less'[where n=14, simplified])
  done


lemma get_pde_wellformed[wp]:
  "\<lbrace>valid_objs\<rbrace> get_pde x \<lbrace>\<lambda>rv _. wellformed_pde rv\<rbrace>"
  apply (simp add: get_pde_def)
  apply wp
  apply (fastforce simp add: valid_objs_def dom_def obj_at_def valid_obj_def)
  done


crunch valid_objs[wp]: init_arch_objects "valid_objs"
  (ignore: clearMemory wp: crunch_wps)


lemma set_pd_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_pd ptr val \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift, wp)


crunch valid_arch_state[wp]: init_arch_objects "valid_arch_state"
  (ignore: clearMemory set_object wp: crunch_wps)


lemmas init_arch_objects_valid_cap[wp] = valid_cap_typ [OF init_arch_objects_typ_at]

lemmas init_arch_objects_cap_table[wp] = cap_table_at_lift_valid [OF init_arch_objects_typ_at]


lemma clearMemory_vms:
  "valid_machine_state s \<Longrightarrow>
   \<forall>x\<in>fst (clearMemory ptr bits (machine_state s)).
     valid_machine_state (s\<lparr>machine_state := snd x\<rparr>)"
  apply (clarsimp simp: valid_machine_state_def
                        disj_commute[of "in_user_frame p s" for p s])
  apply (drule_tac x=p in spec, simp)
  apply (drule_tac P4="\<lambda>m'. underlying_memory m' p = 0"
         in use_valid[where P=P and Q="\<lambda>_. P" for P], simp_all)
  apply (simp add: clearMemory_def cleanCacheRange_PoU_def machine_op_lift_def
                   machine_rest_lift_def split_def)
  apply (wp hoare_drop_imps | simp | wp mapM_x_wp_inv)+
  apply (simp add: storeWord_def | wp)+
  apply (simp add: word_rsplit_0)
  done

lemma do_machine_op_return_foo:
  "do_machine_op (do x\<leftarrow>a;return () od) = (do (do_machine_op a); return () od)"
  apply (clarsimp simp:do_machine_op_def bind_def gets_def 
    get_def return_def select_f_def split_def simpler_modify_def)
  apply (rule ext)+
  apply (clarsimp simp:image_def)
  apply (rule set_eqI)
  apply clarsimp
  done


lemma create_word_objects_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace>
   create_word_objects ptr bits sz
   \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (clarsimp simp: create_word_objects_def
    reserve_region_def mapM_x_mapM do_machine_op_return_foo)
  apply (rule hoare_pre)
  apply wp
  apply (subst dom_mapM)
    apply ((simp add:clearMemory_def
      | wp empty_fail_cleanCacheRange_PoU ef_storeWord
      empty_fail_mapM_x empty_fail_bind)+)[1]
   apply (wp mapM_wp')
  apply (clarsimp simp: create_word_objects_def reserve_region_def
    clearMemory_vms
    do_machine_op_def split_def | wp)+
  done

lemma create_word_objects_valid_irq_states[wp]:
  "\<lbrace>valid_irq_states\<rbrace>
   create_word_objects ptr bits sz
   \<lbrace>\<lambda>_. valid_irq_states\<rbrace>"
  apply (clarsimp simp: create_word_objects_def
    reserve_region_def mapM_x_mapM do_machine_op_return_foo)
  apply (rule hoare_pre)
  apply wp
  apply (subst dom_mapM)
    apply ((simp add:clearMemory_def
      | wp empty_fail_cleanCacheRange_PoU ef_storeWord
      empty_fail_mapM_x empty_fail_bind)+)[1]
   apply (wp mapM_wp' | simp add: do_machine_op_def | wpc)+
   apply clarsimp
   apply (erule use_valid)
   apply (simp add: valid_irq_states_def | wp no_irq_clearMemory)+
  done

lemma create_word_objects_invs[wp]:
  "\<lbrace>invs\<rbrace> create_word_objects ptr bits sz \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add:invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule hoare_vcg_conj_lift[OF create_word_objects_vms])
    apply (rule hoare_vcg_conj_lift[OF create_word_objects_valid_irq_states])
    prefer 2
    apply clarsimp
    apply assumption
   apply (clarsimp simp: create_word_objects_def reserve_region_def
                        split_def do_machine_op_def)
   apply wp
  apply (simp add: invs_def cur_tcb_def valid_state_def)
  done

crunch invs [wp]: reserve_region "invs"

crunch invs [wp]: reserve_region "invs"


abbreviation(input)
 "all_invs_but_equal_kernel_mappings_restricted S
    \<equiv> (\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>))
       and valid_pspace and valid_mdb and valid_idle and only_idle
       and if_unsafe_then_cap and valid_reply_caps
       and valid_reply_masters and valid_global_refs and valid_arch_state
       and valid_irq_node and valid_irq_handlers and valid_arch_objs
       and valid_irq_states
       and valid_arch_caps and valid_global_objs and valid_kernel_mappings 
       and valid_asid_map and valid_global_pd_mappings
       and pspace_in_kernel_window and cap_refs_in_kernel_window
       and cur_tcb and valid_ioc and valid_machine_state"


lemma all_invs_but_equal_kernel_mappings_restricted_eq:
  "all_invs_but_equal_kernel_mappings_restricted {}
        = invs"
  by (rule ext, simp add: invs_def valid_state_def conj_comms restrict_map_def)


crunch iflive[wp]: copy_global_mappings "if_live_then_nonz_cap"
  (wp: crunch_wps)

crunch zombies[wp]: copy_global_mappings "zombies_final"
  (wp: crunch_wps)

crunch state_refs_of[wp]: copy_global_mappings "\<lambda>s. P (state_refs_of s)"
  (wp: crunch_wps)

crunch valid_idle[wp]: copy_global_mappings "valid_idle"
  (wp: crunch_wps)

crunch only_idle[wp]: copy_global_mappings "only_idle"
  (wp: crunch_wps)

crunch ifunsafe[wp]: copy_global_mappings "if_unsafe_then_cap"
  (wp: crunch_wps)

crunch reply_caps[wp]: copy_global_mappings "valid_reply_caps"
  (wp: crunch_wps)

crunch reply_masters[wp]: copy_global_mappings "valid_reply_masters"
  (wp: crunch_wps)

crunch valid_global[wp]: copy_global_mappings "valid_global_refs"
  (wp: crunch_wps)

crunch irq_node[wp]: copy_global_mappings "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch irq_states[wp]: copy_global_mappings "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

crunch caps_of_state[wp]: copy_global_mappings "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps)

crunch pspace_in_kernel_window[wp]: copy_global_mappings "pspace_in_kernel_window"
  (wp: crunch_wps)

crunch cap_refs_in_kernel_window[wp]: copy_global_mappings "cap_refs_in_kernel_window"
  (wp: crunch_wps)


(* FIXME: move to VSpace_R *)
lemma vs_refs_add_one'':
  "p \<in> kernel_mapping_slots \<Longrightarrow>
   vs_refs (ArchObj (PageDirectory (pd(p := pde)))) =
   vs_refs (ArchObj (PageDirectory pd))"
 by (auto simp: vs_refs_def graph_of_def split: split_if_asm)


lemma glob_vs_refs_add_one':
  "glob_vs_refs (ArchObj (PageDirectory (pd(p := pde)))) =
   glob_vs_refs (ArchObj (PageDirectory pd)) 
   - Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref (pd p)) 
   \<union> Pair (VSRef (ucast p) (Some APageDirectory)) ` set_option (pde_ref pde)"
  apply (simp add: glob_vs_refs_def)
  apply (rule set_eqI)
  apply clarsimp
  apply (rule iffI)
   apply (clarsimp del: disjCI dest!: graph_ofD split: split_if_asm)
   apply (rule disjI1)
   apply (rule conjI)
    apply (rule_tac x="(aa, ba)" in image_eqI)
     apply simp
    apply (simp add:  graph_of_def)
   apply clarsimp
  apply (erule disjE)
   apply (clarsimp dest!: graph_ofD)
   apply (rule_tac x="(aa,ba)" in image_eqI)
    apply simp
   apply (clarsimp simp: graph_of_def)
  apply clarsimp
  apply (rule_tac x="(p,x)" in image_eqI)
   apply simp
  apply (clarsimp simp: graph_of_def)
  done


lemma store_pde_map_global_valid_arch_caps:
  "\<lbrace>valid_arch_caps and valid_objs and valid_arch_objs
     and valid_arch_state and valid_global_objs
     and K (valid_pde_mappings pde)
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> set (arm_global_pts (arch_state s)))\<rbrace>
      store_pde p pde
   \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_valid_arch_caps
            [where T="{}" and S="{}" and T'="{}" and S'="{}"])
  apply (clarsimp simp:obj_at_def kernel_vsrefs_kernel_mapping_slots[symmetric])
  apply (intro conjI)
       apply (erule vs_refs_add_one'')
      apply (rule set_eqI)
      apply (clarsimp simp add:  vs_refs_pages_def graph_of_def image_def)
      apply (rule arg_cong[where f=Ex], rule ext, fastforce)
     apply clarsimp
     apply (rule conjI, clarsimp)
     apply (drule valid_arch_objsD, simp add: obj_at_def, simp+)[1]
    apply (rule impI, rule disjI2)
    apply (simp add: empty_table_def)
   apply clarsimp
   apply (rule conjI, clarsimp)
   apply (thin_tac "All P" for P)
   apply clarsimp
   apply (frule_tac ref'="VSRef (ucast c) (Some APageDirectory) # r" and
                    p'=q in vs_lookup_pages_step)
    apply (clarsimp simp: vs_lookup_pages1_def vs_refs_pages_def
                          obj_at_def graph_of_def image_def)
   apply (clarsimp simp: valid_arch_caps_def valid_vs_lookup_def)
  apply clarsimp
  apply (rule conjI, clarsimp)
  apply (thin_tac "All P" for P)
  apply clarsimp
  apply (drule_tac ref'="VSRef (ucast c) (Some APageDirectory) # r" and
                   p'=q in vs_lookup_pages_step)
   apply (clarsimp simp: vs_lookup_pages1_def vs_refs_pages_def
                         obj_at_def graph_of_def image_def)
  apply (drule_tac ref'="VSRef (ucast d) (Some APageTable) #
                         VSRef (ucast c) (Some APageDirectory) # r" and
                   p'=q' in vs_lookup_pages_step)
   apply (fastforce simp: vs_lookup_pages1_def vs_refs_pages_def
                         obj_at_def graph_of_def image_def)
  apply (clarsimp simp: valid_arch_caps_def valid_vs_lookup_def)
  done


lemma store_pde_map_global_valid_arch_objs:
  "\<lbrace>valid_arch_objs and valid_arch_state and valid_global_objs
     and K (valid_pde_mappings pde)
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> set (arm_global_pts (arch_state s)))\<rbrace>
        store_pde p pde
   \<lbrace>\<lambda>rv. valid_arch_objs\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_arch_objs_map[where T="{}" and S="{}"])
  apply (clarsimp simp:obj_at_def kernel_vsrefs_kernel_mapping_slots[symmetric])
  apply (intro conjI)
   apply (erule vs_refs_add_one'')
  apply clarsimp
  apply (drule valid_arch_objsD, simp add: obj_at_def, simp+)
  apply clarsimp
  done


lemma store_pde_global_objs[wp]:
  "\<lbrace>valid_global_objs and valid_global_refs and
    valid_arch_state and
    (\<lambda>s. (\<forall>pd. (obj_at (empty_table (set (arm_global_pts (arch_state s))))
                   (p && ~~ mask pd_bits) s
           \<and> ko_at (ArchObj (PageDirectory pd)) (p && ~~ mask pd_bits) s
             \<longrightarrow> empty_table (set (arm_global_pts (arch_state s)))
                                 (ArchObj (PageDirectory (pd(ucast (p && mask pd_bits >> 2) := pde))))))
        \<or> (\<exists>slot. cte_wp_at (\<lambda>cap. p && ~~ mask pd_bits \<in> obj_refs cap) slot s))\<rbrace>
     store_pde p pde \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (simp add: store_pde_def)
  apply wp
  apply clarsimp
  done


lemma store_pde_valid_kernel_mappings_map_global:
  "\<lbrace>valid_kernel_mappings and valid_arch_state and valid_global_objs
     and K (VSRef (p && mask pd_bits >> 2) (Some APageDirectory)
                \<in> kernel_vsrefs)
     and (\<lambda>s. \<forall>p. pde_ref pde = Some p
             \<longrightarrow> p \<in> set (arm_global_pts (arch_state s)))\<rbrace>
     store_pde p pde
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: store_pde_def)
  apply (wp set_pd_valid_kernel_mappings_map)
  apply (clarsimp simp: obj_at_def)
  apply (rule conjI, rule glob_vs_refs_add_one')
  apply (clarsimp simp: ucast_ucast_mask_shift_helper)
  done


crunch valid_asid_map[wp]: store_pde "valid_asid_map"

crunch cur[wp]: store_pde "cur_tcb"


lemma mapM_x_store_pde_eq_kernel_mappings_restr:
  "pd \<in> S \<and> is_aligned pd pd_bits \<and> is_aligned pd' pd_bits
        \<and> set xs \<subseteq> {..< 2 ^ (pd_bits - 2)}
     \<Longrightarrow>
   \<lbrace>\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)\<rbrace>
     mapM_x (\<lambda>idx. get_pde (pd' + (idx << 2)) >>=
                   store_pde (pd + (idx << 2))) xs
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)
               \<and> (\<forall>x \<in> set xs.
                    (\<exists>pdv pdv'. ko_at (ArchObj (PageDirectory pdv)) pd s
                      \<and> ko_at (ArchObj (PageDirectory pdv')) pd' s
                      \<and> pdv (ucast x) = pdv' (ucast x)))\<rbrace>"
  apply (induct xs rule: rev_induct, simp_all add: mapM_x_Nil mapM_x_append mapM_x_singleton)
  apply (erule hoare_seq_ext[rotated])
  apply (simp add: store_pde_def set_pd_def set_object_def cong: bind_cong)
  apply (wp get_object_wp get_pde_wp)
  apply (clarsimp simp: obj_at_def split del: split_if)
  apply (frule shiftl_less_t2n)
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: is_aligned_add_helper split del: split_if)
  apply (cut_tac x=x and n=2 in shiftl_shiftr_id)
    apply (simp add: word_bits_def)
   apply (simp add: word_bits_def pd_bits_def pageBits_def)
   apply (erule order_less_le_trans, simp)
  apply (clarsimp simp: fun_upd_def[symmetric] is_aligned_add_helper)
  done


lemma equal_kernel_mappings_specific_def:
  "ko_at (ArchObj (PageDirectory pd)) p s
    \<Longrightarrow> equal_kernel_mappings s
          = (\<forall>p' pd'. ko_at (ArchObj (PageDirectory pd')) p' s
                        \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pd' w = pd w))"
  apply (rule iffI)
   apply (clarsimp simp: equal_kernel_mappings_def)
  apply (clarsimp simp: equal_kernel_mappings_def)
  apply (subgoal_tac "pda w = pd w \<and> pd' w = pd w")
   apply (erule conjE, erule(1) trans[OF _ sym])
  apply blast
  done   

lemma copy_global_equal_kernel_mappings_restricted:
  "is_aligned pd pd_bits \<Longrightarrow>
   \<lbrace>\<lambda>s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- (insert pd S)) \<rparr>)
              \<and> arm_global_pd (arch_state s) \<notin> (insert pd S)
              \<and> pspace_aligned s \<and> valid_arch_state s\<rbrace>
     copy_global_mappings pd
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (s \<lparr> kheap := restrict_map (kheap s) (- S) \<rparr>)\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule_tac P="global_pd \<notin> (insert pd S)" in hoare_vcg_prop)
    apply (rule_tac P="is_aligned global_pd pd_bits"
           in hoare_gen_asm(1))
    apply (rule_tac S="insert pd S" in mapM_x_store_pde_eq_kernel_mappings_restr)
    apply clarsimp
    apply (erule order_le_less_trans)
    apply (simp add: pd_bits_def pageBits_def)
   apply (clarsimp simp: invs_aligned_pdD)
  apply clarsimp
  apply (frule_tac x="kernel_base >> 20" in spec)
  apply (drule mp)
   apply (simp add: kernel_base_def pd_bits_def pageBits_def)
  apply (clarsimp simp: obj_at_def)
  apply (case_tac "global_pd = pd")
   apply simp
  apply (subst equal_kernel_mappings_specific_def)
   apply (fastforce simp add: obj_at_def restrict_map_def)
  apply (subst(asm) equal_kernel_mappings_specific_def)
   apply (fastforce simp add: obj_at_def restrict_map_def)
  apply (clarsimp simp: restrict_map_def obj_at_def)
  apply (drule_tac x="ucast w" in spec, drule mp)
   apply (clarsimp simp: kernel_mapping_slots_def)
   apply (rule conjI)
    apply (simp add: word_le_nat_alt unat_ucast_kernel_base_rshift)
    apply (simp only: unat_ucast, subst mod_less)
     apply (rule order_less_le_trans, rule unat_lt2p)
     apply simp
    apply simp
   apply (rule minus_one_helper3)
   apply (rule order_less_le_trans, rule ucast_less)
    apply simp
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: ucast_down_ucast_id word_size source_size_def
                   target_size_def is_down_def)
  apply (drule_tac x=p' in spec)
  apply (simp split: split_if_asm)
  done

lemma store_pde_valid_global_pd_mappings[wp]:
  "\<lbrace>valid_global_objs and valid_global_pd_mappings
          and (\<lambda>s. p && ~~ mask pd_bits \<notin> global_refs s)\<rbrace>
     store_pde p pde
   \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>"
  apply (simp add: store_pde_def set_pd_def)
  apply (wp set_object_global_pd_mappings get_object_wp)
  apply simp
  done

lemma store_pde_valid_ioc[wp]:
 "\<lbrace>valid_ioc\<rbrace> store_pde ptr pde \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (simp add: store_pde_def, wp) simp


lemma store_pde_vms[wp]:
 "\<lbrace>valid_machine_state\<rbrace> store_pde ptr pde \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: store_pde_def, wp) clarsimp

crunch valid_irq_states[wp]: store_pde "valid_irq_states"

lemma copy_global_invs_mappings_restricted:
  "\<lbrace>(\<lambda>s. all_invs_but_equal_kernel_mappings_restricted (insert pd S) s)
          and (\<lambda>s. insert pd S \<inter> global_refs s = {})
          and K (is_aligned pd pd_bits)\<rbrace>
     copy_global_mappings pd
   \<lbrace>\<lambda>rv. all_invs_but_equal_kernel_mappings_restricted S\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: valid_pspace_def pred_conj_def)
  apply (rule hoare_conjI, wp copy_global_equal_kernel_mappings_restricted)
    apply assumption
   apply (clarsimp simp: global_refs_def)
  apply (rule valid_prove_more, rule hoare_vcg_conj_lift, rule hoare_TrueI)
  apply (simp add: copy_global_mappings_def valid_pspace_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp[where S="{x. kernel_base >> 20 \<le> x
                                       \<and> x < 2 ^ (pd_bits - 2)}"])
    apply simp_all
   apply (rule hoare_pre)
    apply (wp valid_irq_node_typ valid_irq_handlers_lift
              store_pde_map_global_valid_arch_caps
              store_pde_map_global_valid_arch_objs
              store_pde_valid_kernel_mappings_map_global
              get_pde_wp)
   apply (clarsimp simp: valid_global_objs_def)
   apply (frule(1) invs_aligned_pdD)
   apply (frule shiftl_less_t2n)
    apply (simp add: pd_bits_def pageBits_def)
   apply (clarsimp simp: is_aligned_add_helper)
   apply (cut_tac x=x and n=2 in shiftl_shiftr_id)
     apply (simp add: word_bits_def)
    apply (erule order_less_le_trans)
    apply (simp add: word_bits_def pd_bits_def pageBits_def)
   apply (rule conjI)
    apply (simp add: valid_objs_def dom_def obj_at_def valid_obj_def)
    apply (drule spec, erule impE, fastforce, clarsimp)
   apply (clarsimp simp: obj_at_def empty_table_def kernel_vsrefs_def)
  apply clarsimp
  apply (erule minus_one_helper5[rotated])
  apply (simp add: pd_bits_def pageBits_def)
  done

lemma copy_global_mappings_valid_ioc[wp]:
 "\<lbrace>valid_ioc\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  by (simp add: copy_global_mappings_def, wp mapM_x_wp[of UNIV]) simp+

lemma copy_global_mappings_vms[wp]:
 "\<lbrace>valid_machine_state\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  by (simp add: copy_global_mappings_def, wp mapM_x_wp[of UNIV]) simp+

lemma copy_global_mappings_invs:
  "\<lbrace>invs and (\<lambda>s. pd \<notin> global_refs s)
         and K (is_aligned pd pd_bits)\<rbrace>
     copy_global_mappings pd \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (fold all_invs_but_equal_kernel_mappings_restricted_eq)
  apply (rule hoare_pre, rule copy_global_invs_mappings_restricted)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
                        restrict_map_def)
  done


crunch global_refs_inv[wp]: copy_global_mappings "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)

lemma mapM_copy_global_invs_mappings_restricted:
  "\<lbrace>\<lambda>s. all_invs_but_equal_kernel_mappings_restricted (set pds) s
            \<and> (set pds \<inter> global_refs s = {})
            \<and> (\<forall>pd \<in> set pds. is_aligned pd pd_bits)\<rbrace>
     mapM_x copy_global_mappings pds
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (fold all_invs_but_equal_kernel_mappings_restricted_eq)
  apply (induct pds, simp_all only: mapM_x_Nil mapM_x_Cons K_bind_def)
   apply (wp, simp)
  apply (rule hoare_seq_ext, assumption, thin_tac "P" for P)
  apply (rule hoare_conjI)
   apply (rule hoare_pre, rule copy_global_invs_mappings_restricted)
   apply clarsimp
  apply (rule hoare_pre, wp)
  apply clarsimp
  done

lemma dmo_eq_kernel_restricted[wp]:
  "\<lbrace>\<lambda>s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>
       do_machine_op m
   \<lbrace>\<lambda>rv s. equal_kernel_mappings (kheap_update (f (kheap s)) s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: equal_kernel_mappings_def obj_at_def)
  done


crunch only_idle[wp]: do_machine_op "only_idle"
crunch valid_global_refs[wp]: do_machine_op "valid_global_refs"
crunch valid_kernel_mappings[wp]: do_machine_op "valid_kernel_mappings"
crunch global_pd_mappings[wp]: do_machine_op "valid_global_pd_mappings"
crunch cap_refs_in_kernel_window[wp]: do_machine_op "cap_refs_in_kernel_window"

definition
  post_retype_invs :: "Structures_A.apiobject_type \<Rightarrow> word32 list \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "post_retype_invs tp refs \<equiv>
    if tp = ArchObject PageDirectoryObj
    then all_invs_but_equal_kernel_mappings_restricted (set refs)
    else invs"


lemma dmo_mapM_x_ccr_invs[wp]:
  "\<lbrace>invs\<rbrace>
   do_machine_op (mapM_x (\<lambda>ptr. cleanCacheRange_PoU ptr (w ptr) (addrFromPPtr ptr)) xs)
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (clarsimp simp: mapM_x_mapM do_machine_op_return_foo)
  apply (rule hoare_pre)
  apply (subst dom_mapM)
    apply ((simp add:clearMemory_def
      | wp empty_fail_cleanCacheRange_PoU ef_storeWord
      empty_fail_mapM_x empty_fail_bind)+)[1]
   apply (wp mapM_wp' | clarsimp)+
  done

lemma init_arch_objects_invs_from_restricted:
  "\<lbrace>post_retype_invs new_type refs
         and (\<lambda>s. global_refs s \<inter> set refs = {})
         and K (\<forall>ref \<in> set refs. is_aligned ref (obj_bits_api new_type obj_sz))\<rbrace>
     init_arch_objects new_type ptr bits obj_sz refs
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: init_arch_objects_def)
  apply (rule hoare_pre)
   apply (wp mapM_copy_global_invs_mappings_restricted
             hoare_vcg_const_Ball_lift
             valid_irq_node_typ
                  | wpc)+
  apply (auto simp: post_retype_invs_def default_arch_object_def
                    pd_bits_def pageBits_def obj_bits_api_def
                    global_refs_def)
  done

lemma retype_region_aligned_for_init[wp]:
  "\<lbrace>\<lambda>s. range_cover ptr sz (obj_bits_api new_type obj_sz) n\<rbrace>
     retype_region ptr n obj_sz new_type
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
  caps_no_overlap :: "word32 \<Rightarrow> nat \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "caps_no_overlap ptr sz s \<equiv> \<forall>cap \<in> ran (caps_of_state s).
               untyped_range cap \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<noteq> {}
               \<longrightarrow> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} \<subseteq> untyped_range cap"

definition caps_overlap_reserved :: "word32 set \<Rightarrow> ('z::state_ext) state \<Rightarrow> bool"
where
 "caps_overlap_reserved S (s :: ('z::state_ext) state) \<equiv> \<forall>cap \<in> ran (caps_of_state s).
  (is_untyped_cap cap \<longrightarrow> usable_untyped_range cap \<inter> S = {})"


lemma of_nat_2: "((of_nat (2::nat))::word32) = 2" by simp


lemma subset_le_imp_less: "\<not> A \<subseteq> B \<Longrightarrow> \<not> A \<subset> B" by auto


lemma non_disjoing_subset: "\<lbrakk>A \<subseteq> B; A \<inter> C \<noteq> {}\<rbrakk> \<Longrightarrow> B \<inter> C \<noteq> {}" by blast


lemma pspace_no_overlap_same_type:
  "\<lbrakk>pspace_no_overlap ptr sz s; ko_at k p s; a_type ko = a_type k\<rbrakk>
    \<Longrightarrow> pspace_no_overlap ptr sz (kheap_update (\<lambda>_. (kheap s(p \<mapsto> ko))) s)"
  unfolding pspace_no_overlap_def
  by (clarsimp simp: obj_at_def obj_bits_T)


lemma set_object_no_overlap:
  "\<lbrace>pspace_no_overlap ptr sz and obj_at (\<lambda>k. a_type ko = a_type k) p\<rbrace>
  set_object p ko \<lbrace>\<lambda>r. pspace_no_overlap ptr sz\<rbrace>"
  unfolding set_object_def
  apply simp
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (drule obj_at_ko_atD, erule exE)
  apply (rule pspace_no_overlap_same_type)
  apply auto
  done
  

lemma set_cap_no_overlap:
  "\<lbrace>pspace_no_overlap ptr sz\<rbrace> set_cap cap cte \<lbrace>\<lambda>r. pspace_no_overlap ptr sz\<rbrace>"
  unfolding set_cap_def
  apply (simp add: split_beta)
  apply (wp set_object_no_overlap)
   defer
   apply (rule get_object_sp)
  apply (rule validI)
  apply (clarsimp simp: in_monad return_def fail_def 
                 split: Structures_A.kernel_object.splits split_if_asm
                  cong: if_cong
                 elim!: obj_at_weakenE)
  apply (clarsimp simp add: a_type_def wf_cs_upd)
  done


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
                        if_unsafe_then_cap_def ex_cte_cap_wp_to_def
                intro!: ext)
  done


lemma descendants_inc_null_filter:
  "\<lbrakk>mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)\<rbrakk>
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
   \<and> irq_revocable r cps \<and> reply_master_revocable r cps \<and> reply_mdb m cps"


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
  apply (rule arg_cong2 [where f="op \<and>"])
   apply (rule refl)
  apply (rule arg_cong2 [where f="op \<and>"])
   prefer 2
   apply (rule arg_cong2 [where f="op \<and>"])
    apply (simp add: ut_revocable_def null_filter_def del: split_paired_All)
    apply (auto simp: is_cap_simps)[1]
   apply (rule arg_cong2 [where f="op \<and>"])
    apply (simp add: irq_revocable_def null_filter_def del: split_paired_All)
    apply auto[1]
   apply (rule arg_cong2 [where f="op \<and>"])
    apply (simp add: reply_master_revocable_def null_filter_def del: split_paired_All)
    apply (auto simp: is_cap_simps)[1]
   apply (simp add: reply_mdb_def null_filter_def)
   apply (rule arg_cong2 [where f="op \<and>"])
    apply (simp add: reply_caps_mdb_def
                del: split_paired_Ex split_paired_All)
    apply (fastforce intro!: iffI elim!: allEI exEI
                  simp del: split_paired_Ex split_paired_All)
   apply (fastforce simp: reply_masters_mdb_def intro!: iffI elim!: allEI
               simp del: split_paired_All split: split_if_asm) 
  apply (rule arg_cong[where f=All, OF ext])+
  apply ((clarsimp simp: cte_wp_at_caps_of_state null_filter_def
               | rule conjI iffI
               | drule iffD1 [OF not_None_eq, OF not_sym])+)[1]
  done


lemma valid_mdb_rep3:
  "valid_mdb = (\<lambda>s. \<exists>m r. cdt s = m \<and> is_original_cap s = r \<and> valid_mdb2 (null_filter (caps_of_state s)) m r)"
  by (simp add: valid_mdb_rep2)


lemma retype_region_mdb[wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> retype_region ptr n us ty \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  apply (simp add: retype_region_def split del: split_if cong: if_cong)
  apply (wp|clarsimp)+
  done


lemma retype_region_revokable[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> retype_region ptr n us ty \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
  apply (simp add: retype_region_def split del: split_if cong: if_cong)
  apply (wp|clarsimp)+
  done


lemma pspace_no_overlap_obj_not_in_range:
  "\<lbrakk> pspace_no_overlap ptr sz s; obj_at P ptr' s;
       pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> ptr' \<notin> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}"
  apply (clarsimp simp add: pspace_no_overlap_def obj_at_def)
  apply (elim allE, drule(1) mp)
  apply (simp add: field_simps)
  apply (erule pspace_alignedE, erule domI)
  apply (drule valid_obj_sizes, erule ranI)
  apply (clarsimp simp: add_diff_eq[symmetric])
  apply (simp add: is_aligned_no_wrap')
  apply (auto simp: order_trans [OF _ is_aligned_no_overflow] field_simps)
  done

lemma obj_at_kheap_trans_state[simp]:"obj_at P ptr (kheap_update f (trans_state f' s)) = obj_at P ptr (kheap_update f s)"
  apply (simp only: trans_state_update[symmetric] more_update.obj_at_update)
  done

lemma retype_region_obj_at:
  assumes tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  shows "\<lbrace>\<top>\<rbrace> retype_region ptr n us ty 
  \<lbrace>\<lambda>r s. \<forall>x \<in> set (retype_addrs ptr ty n us). obj_at (\<lambda>ko. ko = default_object ty us) x s\<rbrace>"
  using tyunt unfolding retype_region_def
  apply (simp only: return_bind bind_return foldr_upd_app_if fun_app_def K_bind_def)
  apply wp
  apply (simp only: obj_at_kheap_trans_state)
  apply wp
  apply (simp only: simp_thms if_True)
  apply (rule ballI)
  apply (subst retype_addrs_fold)
  apply simp
  apply (unfold obj_at_def)
  apply clarsimp
  done


lemma retype_region_obj_at_other:
  assumes ptrv: "ptr \<notin> set (retype_addrs ptr' ty n us)"
  shows "\<lbrace>obj_at P ptr\<rbrace> retype_region ptr' n us ty \<lbrace>\<lambda>r. obj_at P ptr\<rbrace>"
  using ptrv unfolding retype_region_def retype_addrs_def 
  apply (simp only: foldr_upd_app_if fun_app_def K_bind_def)
  apply wp
      apply (simp only: obj_at_kheap_trans_state)
      apply wp
  apply (clarsimp simp: power_sub)
  apply (unfold obj_at_def)
  apply (erule exEI)
  apply (clarsimp)
  done


lemma retype_region_obj_at_other2:
  "\<lbrace>\<lambda>s. ptr \<notin> set (retype_addrs ptr' ty n us)
       \<and> obj_at P ptr s\<rbrace> retype_region ptr' n us ty \<lbrace>\<lambda>rv. obj_at P ptr\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (wp retype_region_obj_at_other)
   apply simp_all
  done


lemma retype_region_obj_at_other3:
  "\<lbrace>\<lambda>s. pspace_no_overlap ptr sz s \<and> obj_at P p s \<and> range_cover ptr sz (obj_bits_api ty us) n
           \<and> valid_objs s \<and> pspace_aligned s\<rbrace>
     retype_region ptr n us ty
   \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
   apply (rule hoare_pre)
    apply (rule retype_region_obj_at_other2)
   apply clarsimp
   apply (drule subsetD [rotated, OF _ retype_addrs_subset_ptr_bits])
     apply simp
   apply (drule(3) pspace_no_overlap_obj_not_in_range)
   apply (simp add: field_simps)
done

lemma retype_region_st_tcb_at:
  "\<lbrace>\<lambda>s. pspace_no_overlap ptr' sz s \<and> pred_tcb_at proj P t s \<and> range_cover ptr' sz (obj_bits_api ty us) n
          \<and> valid_objs s \<and> pspace_aligned s\<rbrace>
     retype_region ptr' n us ty \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  by (simp add: retype_region_obj_at_other3 pred_tcb_at_def)


lemma retype_region_cur_tcb[wp]:
  "\<lbrace>pspace_no_overlap ptr sz and cur_tcb and K (range_cover ptr sz (obj_bits_api ty us) n)
     and K (is_aligned ptr sz \<and> sz < word_bits)
     and valid_objs and pspace_aligned\<rbrace>
     retype_region ptr n us ty
   \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  apply (rule hoare_post_imp [where Q="\<lambda>rv s. \<exists>tp. tcb_at tp s \<and> cur_thread s = tp"])
   apply (simp add: cur_tcb_def)
  apply (rule hoare_pre, wp hoare_vcg_ex_lift retype_region_obj_at_other3)
   apply (simp add: retype_region_def split del: split_if cong: if_cong)
   apply (wp|simp)+
  apply (clarsimp simp: cur_tcb_def cong: if_cong)
  apply auto
  done


lemma retype_addrs_mem_sz_0_is_ptr:
  assumes xv: "x \<in> set (retype_addrs ptr ty n us)"
  and     sz: "n = 0"
  shows   "x = ptr"
  using sz xv unfolding retype_addrs_def
  apply (clarsimp simp add: ptr_add_def
                  simp del: power_0
                     dest!: less_two_pow_divD)
  done


lemma obj_bits_api_neq_0:
  "ty \<noteq> Untyped \<Longrightarrow> 0 < obj_bits_api ty us"
  unfolding obj_bits_api_def
  by (clarsimp simp: slot_bits_def default_arch_object_def pageBits_def 
               split: Structures_A.apiobject_type.splits aobject_type.splits)


lemma retype_addrs_range_subset:
  "\<lbrakk>  p \<in> set (retype_addrs ptr ty n us);
     range_cover ptr sz (obj_bits_api ty us) n \<rbrakk>
  \<Longrightarrow> {p .. p + 2 ^ obj_bits_api ty us - 1} \<subseteq> {ptr..(ptr && ~~ mask sz) + 2^sz - 1}"
  apply (clarsimp simp: retype_addrs_def ptr_add_def
              simp del: atLeastatMost_subset_iff atLeastAtMost_iff)
  apply (frule_tac x = "of_nat pa" in range_cover_cell_subset)
    apply (erule of_nat_mono_maybe[rotated])
    apply (drule range_cover.range_cover_n_less)
   apply (simp add:word_bits_def)
  apply fastforce
  done


lemma retype_addrs_obj_range_subset:
  "\<lbrakk>  p \<in> set (retype_addrs ptr ty n us);
      range_cover ptr sz (obj_bits (default_object ty us)) n;
  ty \<noteq> Untyped \<rbrakk>
  \<Longrightarrow> obj_range p (default_object ty us) \<subseteq> {ptr..(ptr && ~~ mask sz) + 2^sz - 1}"
  by(simp add: obj_range_def obj_bits_api_default_object[symmetric]
                retype_addrs_range_subset
           del: atLeastatMost_subset_iff)


lemma retype_addrs_obj_range_subset_strong:
  "\<lbrakk> p \<in> set (retype_addrs ptr ty n us);
    range_cover ptr sz (obj_bits (default_object ty us)) n;
  ty \<noteq> Untyped \<rbrakk>
   \<Longrightarrow> obj_range p (default_object ty us) \<subseteq>  {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}"
  unfolding obj_range_def

  apply (frule(1) retype_addrs_obj_range_subset)
  apply (simp add:obj_range_def)+
  apply (intro conjI impI)
  apply (erule(1) impE)
  apply clarsimp
  apply (case_tac "n = 0")
   apply (clarsimp simp:retype_addrs_def)
  proof -
    assume cover:"range_cover ptr sz (obj_bits (default_object ty us)) n"
      and  mem_p:"p \<in> set (retype_addrs ptr ty n us)"
      and  not_0:"n\<noteq> 0"
      and  tyunt:"ty\<noteq> Untyped"
    note n_less = range_cover.range_cover_n_less[OF cover]
    have unat_of_nat_m1: "unat (of_nat n - (1::word32)) < n"
      using not_0 n_less
       by (simp add:unat_of_nat_minus_1)
    have decomp:"of_nat n * 2 ^ obj_bits_api ty us = of_nat (n - 1) * 2 ^ (obj_bits (default_object ty us))
      + (2 :: word32) ^ obj_bits (default_object ty us)"
      apply (simp add:distrib_right[where b = "1::'a::len word",simplified,symmetric])
      using not_0 n_less
      apply (simp add:unat_of_nat_minus_1 obj_bits_api_def3 tyunt)
      done
    show  "p + 2 ^ obj_bits (default_object ty us) - 1 \<le> ptr + of_nat n * 2 ^ obj_bits_api ty us - 1"
      apply (subst decomp)
      apply (simp add:add.assoc[symmetric])
      apply (simp add:p_assoc_help)
      apply (rule order_trans[OF word_plus_mono_left word_plus_mono_right])
       using mem_p not_0
         apply (clarsimp simp:retype_addrs_def ptr_add_def shiftl_t2n tyunt obj_bits_api_def3)
         apply (rule word_plus_mono_right)
          apply (rule word_mult_le_mono1[OF word_of_nat_le])
          using n_less not_0
            apply (simp add:unat_of_nat_minus_1)
           apply (rule p2_gt_0[THEN iffD2])
           using cover
           apply (simp add:word_bits_def range_cover_def)
          apply (simp only: word_bits_def[symmetric])
          using not_0 n_less
          apply (clarsimp simp: unat_of_nat_minus_1)
          apply (subst unat_power_lower)
            using cover
            apply (simp add:range_cover_def)
          apply (rule nat_less_power_trans2[OF range_cover.range_cover_le_n_less(2),OF cover, folded word_bits_def])
          apply (simp add:unat_of_nat_m1 less_imp_le)
         using cover
         apply (simp add:range_cover_def word_bits_def)
        apply (rule word32_plus_mono_right_split[where sz = sz])
        using range_cover.range_cover_compare[OF cover,where p = "unat (of_nat n - (1::word32))"]
        apply (clarsimp simp:unat_of_nat_m1)
       using cover
       apply (simp add:range_cover_def word_bits_def)
      apply (rule olen_add_eqv[THEN iffD2])
      apply (subst add.commute[where a = "2^(obj_bits (default_object ty us)) - 1"])
     apply (subst p_assoc_help[symmetric])
     apply (rule is_aligned_no_overflow)
     apply (insert cover)
     apply (clarsimp simp:range_cover_def)
     apply (erule aligned_add_aligned[OF _  is_aligned_mult_triv2])
       apply (simp add:range_cover_def)+
   done
  qed


lemma retype_addrs_mem_subset_ptr_bits:
  assumes cover:"range_cover ptr sz (obj_bits_api ty us) n"
  and tynunt: "ty \<noteq> Untyped"
  and     xv: "x \<in> set (retype_addrs ptr ty n us)"
  shows "{x .. x + (2 ^ obj_bits_api ty us - 1)} \<subseteq> {ptr .. (ptr && ~~ mask sz) + (2 ^ sz - 1)}"
proof -
  have P: "obj_bits_api ty us = obj_bits (default_object ty us)"
    apply (cases ty)
      apply (simp add: obj_bits_api_def2 tynunt)+
    done
  show ?thesis
    apply (insert cover)
    using retype_addrs_obj_range_subset [OF xv _ tynunt]
    by (simp add: P obj_range_def field_simps)
qed


lemma pspace_no_overlap_retype_addrs_empty:
  assumes nptr: "pspace_no_overlap ptr sz s"
  and xv: "x \<in> set (retype_addrs ptr ty n us)"  
  and yv: "y \<notin> set (retype_addrs ptr ty n us)"
  and kov: "kheap s y = Some ko"  
  and tyv: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  and cover: "range_cover ptr sz (obj_bits_api ty us) n" 
  and oab: "obj_bits_api ty us \<le> sz"  
  shows "{x..x + (2 ^ obj_bits (default_object ty us) - 1)} \<inter> {y..y + (2 ^ obj_bits ko - 1)} = {}"
proof -
  have "{x..x + (2 ^ obj_bits (default_object ty us) - 1)} \<subseteq> {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)}"
   by (subst obj_bits_api_default_object [OF tyv, symmetric],
      rule retype_addrs_mem_subset_ptr_bits) fact+
  
  moreover have "{ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<inter> {y..y + (2 ^ obj_bits ko - 1)} = {}"
    by (subst Int_commute, rule pspace_no_overlapE) fact+
  
  ultimately show ?thesis by auto
qed


lemma valid_obj_default_object:
  assumes tyunt: "ty \<noteq> Untyped"
  and      tyct: "ty = CapTableObject \<Longrightarrow> us < word_bits - cte_level_bits \<and> 0 < us"
  shows "valid_obj ptr (default_object ty us) s"
  unfolding valid_obj_def default_object_def
  apply (cases ty)
       apply (simp add: tyunt)
      apply (simp add: valid_tcb_def default_tcb_def valid_tcb_state_def
                       tcb_cap_cases_def valid_ipc_buffer_cap_def
                       word_bits_def)
     apply (simp add: valid_ep_def default_ep_def)
    apply (simp add: valid_ntfn_def default_notification_def default_ntfn_def valid_bound_tcb_def)
   apply (frule tyct)
   apply (clarsimp simp: valid_cs_def empty_cnode_def well_formed_cnode_n_def)
   apply safe
    apply (erule ranE)
    apply (simp split: split_if_asm) 
   apply (simp add: valid_cs_size_def well_formed_cnode_n_def)
   apply safe
    apply (simp split: split_if_asm)
   apply (clarsimp split: split_if_asm)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all add: default_arch_object_def)
  done


lemma valid_arch_obj_default:
  assumes tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  shows "ArchObj ao = default_object ty us \<Longrightarrow> valid_arch_obj ao s'"
  apply (cases ty, simp_all add: default_object_def tyunt)
  apply (simp add: default_arch_object_def split: aobject_type.splits)
  done


lemma vs_lookup_trans_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  shows "vs_lookup_trans s \<subseteq> vs_lookup_trans s'" 
proof -
  have "vs_lookup1 s \<subseteq> vs_lookup1 s'"
    by (fastforce dest: ko elim: vs_lookup1_stateI2)
  thus ?thesis by (rule rtrancl_mono)
qed


(* FIXME: move to Invariants_AI *)
lemma vs_lookup_pages1_stateI2:
  assumes 1: "(r \<unrhd>1 r') s"
  assumes ko: "\<And>ko. \<lbrakk> ko_at ko (snd r) s; vs_refs_pages ko \<noteq> {} \<rbrakk> 
               \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') (snd r) s'"
  shows "(r \<unrhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup_pages1_def)


lemma vs_lookup_pages_trans_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs_pages ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  shows "vs_lookup_pages_trans s \<subseteq> vs_lookup_pages_trans s'" 
proof -
  have "vs_lookup_pages1 s \<subseteq> vs_lookup_pages1 s'"
    by (fastforce dest: ko elim: vs_lookup_pages1_stateI2)
  thus ?thesis by (rule rtrancl_mono)
qed


lemma vs_lookup_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup s \<subseteq> vs_lookup s'"
  unfolding vs_lookup_def
  apply (rule Image_mono)
   apply (rule vs_lookup_trans_sub2)
   apply (erule (1) ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done


lemma vs_lookup_pages_sub2:
  assumes ko: "\<And>ko p. \<lbrakk> ko_at ko p s; vs_refs_pages ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup_pages s \<subseteq> vs_lookup_pages s'"
  unfolding vs_lookup_pages_def
  apply (rule Image_mono)
   apply (rule vs_lookup_pages_trans_sub2)
   apply (erule (1) ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
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
  apply (drule(1) of_nat_less_pow)
  apply (drule word_plus_mono_right[OF _ is_aligned_no_overflow[unfolded p_assoc_help],rotated])
   apply simp
  apply (simp add:p_assoc_help)
  done



lemma valid_untyped_helper:
  assumes valid_c : "s \<turnstile> c" 
  and   cte_at  : "cte_wp_at (op = c) q s"
  and     tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  and   cover  : "range_cover ptr sz (obj_bits_api ty us) n"
  and   range  : "is_untyped_cap c \<Longrightarrow> usable_untyped_range c \<inter> {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api ty us)) - 1} = {}"
  and     pn   : "pspace_no_overlap ptr sz s"
  and     cn   : "caps_no_overlap ptr sz s"
  and     vp   : "valid_pspace s"
  shows "valid_cap c
           (s\<lparr>kheap := \<lambda>x. if x \<in> set (retype_addrs ptr ty n us) then Some (default_object ty us) else kheap s x\<rparr>)"
  (is "valid_cap c ?ns")
  proof -
  have obj_at_pres: "\<And>P x. obj_at P x s \<Longrightarrow> obj_at P x ?ns"
  by (clarsimp simp: obj_at_def dest: domI)
   (erule pspace_no_overlapC [OF pn _ _ cover vp])
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  have cover':"range_cover ptr sz (obj_bits (default_object ty us)) n"
    using cover tyunt
    by (clarsimp simp:obj_bits_api_def3)

  show ?thesis
  using cover valid_c range usable_range_emptyD[where cap = c] cte_at
  apply (clarsimp simp: valid_cap_def elim!: obj_at_pres
                 split: cap.splits option.splits arch_cap.splits)
      defer
     apply (fastforce elim!: obj_at_pres)
    apply (fastforce elim!: obj_at_pres)
   apply (fastforce elim!: obj_at_pres)
  apply (rename_tac word nat1 nat2)
  apply (clarsimp simp:valid_untyped_def is_cap_simps obj_at_def split:split_if_asm)
    apply (thin_tac "\<forall>x. Q x" for Q)
     apply (frule retype_addrs_obj_range_subset_strong[OF _ cover' tyunt])
     apply (frule usable_range_subseteq)
       apply (simp add:is_cap_simps)
     apply (clarsimp simp:cap_aligned_def split:split_if_asm)
      apply (frule aligned_ranges_subset_or_disjoint)
      apply (erule retype_addrs_aligned[where sz = sz])
         apply (simp add:range_cover_def)
        apply (simp add:range_cover_def word_bits_def)
       apply (simp add:range_cover_def)
      apply (clarsimp simp:obj_range_def[symmetric] obj_bits_api_def3 Int_ac tyunt
        split:split_if_asm)
     apply (elim disjE)
      apply (drule(2) subset_trans[THEN disjoint_subset2])
      apply (drule Int_absorb2)+
       apply (simp add:is_cap_simps free_index_of_def)
    apply simp
    apply (drule(1) disjoint_subset2[rotated])
    apply (simp add:Int_ac)
   apply (thin_tac "\<forall>x. Q x" for Q)
   apply (frule retype_addrs_obj_range_subset[OF _ cover' tyunt])
   apply (clarsimp simp:cap_aligned_def)
    apply (frule aligned_ranges_subset_or_disjoint)
     apply (erule retype_addrs_aligned[where sz = sz])
         apply (simp add:range_cover_def)
        apply (simp add:range_cover_def word_bits_def)
       apply (simp add:range_cover_def)
      apply (clarsimp simp:obj_range_def[symmetric] obj_bits_api_def3 Int_ac tyunt
        split:split_if_asm)
   apply (case_tac "{word..word + 2 ^ nat1 - 1} = obj_range p (default_object ty us)")
     apply simp
   apply (erule disjE)
     apply (simp add:subset_iff_psubset_eq)
     apply (simp add:subset_iff_psubset_eq[symmetric])
     apply (drule(1) psubset_subset_trans)
    apply (simp add:cte_wp_at_caps_of_state)
    apply (drule cn[unfolded caps_no_overlap_def,THEN bspec,OF ranI])
    apply simp
  apply blast+
  done
  qed

locale retype_region_proofs =
  fixes s ty us ptr sz n ps s'
   assumes   vp: "valid_pspace s"
      and    vm: "valid_mdb s"
      and   res: "caps_overlap_reserved {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api ty us)) - 1} s"
      and tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
      and  tyct: "ty = CapTableObject \<Longrightarrow> us < word_bits - cte_level_bits \<and> 0 < us"
      and   orth: "pspace_no_overlap ptr sz s"
      and  mem :  "caps_no_overlap ptr sz s"
      and cover: "range_cover ptr sz (obj_bits_api ty us) n" 
   defines "ps \<equiv> (\<lambda>x. if x \<in> set (retype_addrs ptr ty n us) then Some (default_object ty us)
                       else kheap s x)"
       and "s' \<equiv> kheap_update (\<lambda>y. ps) s"
begin
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


lemma psp_dist:
  shows         "pspace_distinct s'"
proof -
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
        apply (auto simp:range_cover_def word_bits_def)
      done
    moreover
    have "is_aligned y (obj_bits_api ty us)"
      apply (rule retype_addrs_aligned)
      apply fact+
      apply (insert cover)
      apply (auto simp:range_cover_def word_bits_def)
      done
    ultimately have
      "{x..x + (2 ^ obj_bits (default_object ty us) - 1)} \<inter> {y..y + (2 ^ obj_bits (default_object ty us) - 1)} = {}"
      using xne tyunt cover
      apply -
      apply (rule aligned_neq_into_no_overlap)
      apply (simp_all add: obj_bits_api_default_object range_cover_def word_bits_def)
      done
  } note inter = this
  moreover
  {
    fix x y ko'
    assume xne: "x \<noteq> y" and xv: "x \<in> set (retype_addrs ptr ty n us)" 
        and yv: "y \<notin> set (retype_addrs ptr ty n us)" and  "kheap s y = Some ko'"
    have "{x..x + (2 ^ obj_bits (default_object ty us) - 1)} \<inter> {y..y + (2 ^ obj_bits ko' - 1)} = {}"
      apply (rule pspace_no_overlap_retype_addrs_empty [OF orth])
      apply fact+
      apply (insert cover tyunt)
      apply (simp add:range_cover_def word_bits_def)+
      done
  }note inter' = this
  show ?thesis
    unfolding pspace_distinct_def s'_def ps_def
    apply (clarsimp split: split_if_asm option.splits
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
proof (clarsimp split: split_if_asm)
  fix x
  assume "x \<in> set (retype_addrs ptr ty n us)"
  thus "is_aligned x (obj_bits (default_object ty us))"
    apply -
    apply (drule retype_addrs_aligned)
    apply (insert cover tyunt)
      apply (fastforce simp:range_cover_def word_bits_def)+
    apply (simp add:obj_bits_api_def2 
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


lemma le_subset: "\<lbrakk>(a::('g::len) word) \<le> c\<rbrakk> \<Longrightarrow> {c..b} \<subseteq> {a..b}" by clarsimp


lemma valid_cap_pres: 
  "\<lbrakk> s \<turnstile> c; cte_wp_at (op = c) (oref,cref) s \<rbrakk> \<Longrightarrow> s' \<turnstile> c"
  using cover mem orth 
  apply (simp add:s'_def ps_def)
  apply (rule valid_untyped_helper[ OF _ _ tyunt cover _ _ _ vp ])
      apply simp+
     apply (simp add:cte_wp_at_caps_of_state)
     apply (drule res[unfolded caps_overlap_reserved_def,THEN bspec,OF ranI])
     apply simp
    apply simp+
  done


lemma valid_objs:
  "valid_objs s'"
  apply (clarsimp simp:valid_objs_def)
  apply (rule valid_pspaceE[OF vp])
  apply (clarsimp simp:valid_objs_def s'_def ps_def split:if_splits)
   apply (simp add:valid_obj_default_object[OF tyunt tyct])
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

   apply (fastforce simp: valid_tcb_state_def valid_bound_ntfn_def
                   elim!: obj_at_pres[unfolded s'_def ps_def]
                   split: Structures_A.thread_state.splits option.splits)

    apply (fastforce simp: valid_ep_def
                  elim!: obj_at_pres[unfolded s'_def ps_def]
                  split: Structures_A.endpoint.splits)
  apply (fastforce simp: valid_ntfn_def valid_bound_tcb_def
                  elim!: obj_at_pres[unfolded s'_def ps_def]
                 split: Structures_A.ntfn.splits option.splits)
  done


lemma refs_eq:
  "state_refs_of s' = state_refs_of s"
  unfolding s'_def ps_def
  apply (clarsimp intro!: ext simp: state_refs_of_def
                    simp: orthr
                   split: option.splits)
  apply (cases ty, simp_all add: tyunt default_object_def
                                 default_tcb_def default_ep_def
                                 default_notification_def default_ntfn_def)
  done


lemma cte_retype:
    "\<And>P p. \<not> P cap.NullCap \<Longrightarrow>
     cte_wp_at P p s' = cte_wp_at P p s"
  unfolding s'_def ps_def
  apply (safe elim!: cte_wp_atE)
       apply (clarsimp split: split_if_asm
                              Structures_A.apiobject_type.split_asm
                        simp: default_object_def tyunt default_tcb_def
                              empty_cnode_def cte_wp_at_cases
                       dest!: orthr
                  | simp add: tcb_cap_cases_def)+
  done


lemma iflive_s: "if_live_then_nonz_cap s" by (rule valid_pspaceE [OF vp])


lemma iflive:
  "if_live_then_nonz_cap s'"
  using iflive_s unfolding if_live_then_nonz_cap_def s'_def ps_def
  apply -
  apply (clarsimp elim!: obj_atE split: split_if_asm)
   apply (cases ty, simp_all add: default_object_def tyunt
                                  default_tcb_def default_ep_def
                                  default_notification_def default_ntfn_def)
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


lemma valid_pspace: "valid_pspace s'" using vp
  by (simp add: valid_pspace_def valid_objs psp_al psp_dist
                iflive zombies refs_eq)


(* I have the feeling I'm making this unnecessarily hard,
   but I can't put my finger on where. *)

lemma F: "\<And>x c s. (caps_of_state s x = Some c) = (cte_wp_at (op = c) x s)"
  apply (simp add: caps_of_state_cte_wp_at)
  apply (fastforce simp: cte_wp_at_def)
  done


lemma F2: "\<And>x c s. (null_filter (caps_of_state s) x = Some c)
             = (cte_wp_at (\<lambda>cap. cap \<noteq> cap.NullCap \<and> cap = c) x s)"
  apply (simp add: null_filter_def F)
  apply (fastforce simp: cte_wp_at_def)
  done


lemma F3: "\<And>x s. (None = null_filter (caps_of_state s) x)
              = (\<forall>c. \<not> cte_wp_at (\<lambda>cap. cap \<noteq> cap.NullCap \<and> cap = c) x s)"
  apply safe
   apply (simp add: F2[symmetric])
  apply (rule sym, rule ccontr, clarsimp simp: F2)
  done


lemma null_filter: "null_filter (caps_of_state s') = null_filter (caps_of_state s)"
  apply (rule ext)
  apply (case_tac "null_filter (caps_of_state s) x")
   apply (simp add: eq_commute) 
   apply (simp add: F3 cte_retype)
  apply simp
  apply (simp add: F2 cte_retype)
  done


lemma valid_cap:
  assumes cap: "s \<turnstile> cap \<and> untyped_range cap \<inter> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} = {}"
  shows "s' \<turnstile> cap"
  proof - 
  note blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
  have cover':"range_cover ptr sz (obj_bits (default_object ty us)) n"
    using cover tyunt
    by (clarsimp simp:obj_bits_api_def3)
  show ?thesis
  using cap
  apply (case_tac cap)
    unfolding valid_cap_def
    apply (simp_all add: valid_cap_def obj_at_pres cte_at_pres
                              split: option.split_asm arch_cap.split_asm
                                     option.splits)
     apply (clarsimp simp add: valid_untyped_def ps_def s'_def)
     apply (intro conjI)
       apply clarsimp
       apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
        apply (simp add:Int_ac)
       apply simp
      apply clarsimp
     apply (drule disjoint_subset [OF retype_addrs_obj_range_subset [OF _ cover' tyunt]])
      apply (simp add:Int_ac)
     apply simp
     using cover tyunt
     apply (simp add: obj_bits_api_def2 split:Structures_A.apiobject_type.splits)
     apply clarsimp+
    apply (fastforce elim!: obj_at_pres)+
  done
  qed


lemma idle_s':
  "idle_thread s' = idle_thread s"
  by (simp add: s'_def ps_def)


lemma valid_idle:
  "valid_idle s \<Longrightarrow> valid_idle s'"
  by (clarsimp simp add: valid_idle_def idle_s' refs_eq
                         pred_tcb_at_pres)


lemma arch_state [simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)


lemma irq_node [simp]:
  "interrupt_irq_node s' = interrupt_irq_node s"
  by (simp add: s'_def)


lemma valid_global_refs:
  "valid_global_refs s \<Longrightarrow> valid_global_refs s'"
  apply (simp add: valid_global_refs_def valid_refs_def global_refs_def idle_s')
  apply (simp add: cte_retype cap_range_def)
  done


lemma valid_arch_state:
  "valid_arch_state s \<Longrightarrow> valid_arch_state s'"
  by (clarsimp simp: valid_arch_state_def obj_at_pres 
                     valid_asid_table_def valid_global_pts_def)


lemma caps_retype:
  assumes nonnull: "cap \<noteq> cap.NullCap"
  and      newcap: "caps_of_state s' p = Some cap"
  shows            "caps_of_state s p = Some cap"
proof -
  from newcap have "cte_wp_at (op = cap) p s'"
    by (simp add: cte_wp_at_caps_of_state)
  hence "cte_wp_at (op = cap) p s"
    by (rule_tac subst [OF cte_retype], rule_tac nonnull, assumption)
  thus ?thesis
    by (simp add: cte_wp_at_caps_of_state)
qed


lemma unique_reply_caps:
  "unique_reply_caps (caps_of_state s) \<Longrightarrow> unique_reply_caps (caps_of_state s')"
  using caps_retype
  by (fastforce simp add: is_cap_simps unique_reply_caps_def
               simp del: split_paired_All
                  elim!: allEI)


lemma valid_reply_caps:
  "valid_reply_caps s \<Longrightarrow> valid_reply_caps s'"
  by (clarsimp simp: valid_reply_caps_def unique_reply_caps has_reply_cap_def
                     pred_tcb_at_pres cte_retype)


lemma valid_reply_masters:
  "valid_reply_masters s \<Longrightarrow> valid_reply_masters s'"
  by (clarsimp simp: valid_reply_masters_def cte_retype is_cap_simps obj_at_pres)


lemma vs_refs_default [simp]:
  "vs_refs (default_object ty us) = {}"
  by (simp add: default_object_def default_arch_object_def tyunt vs_refs_def 
                o_def pde_ref_def graph_of_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)


lemma vs_refs_pages_default [simp]:
  "vs_refs_pages (default_object ty us) = {}"
  by (simp add: default_object_def default_arch_object_def tyunt vs_refs_pages_def 
                o_def pde_ref_pages_def pte_ref_pages_def graph_of_def
           split: Structures_A.apiobject_type.splits aobject_type.splits)


lemma vs_lookup': 
  "vs_lookup s' = vs_lookup s"
  apply (rule order_antisym)
   apply (rule vs_lookup_sub2)
    apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm dest!: orthr)
  apply simp
  done


lemma vs_lookup_pages': 
  "vs_lookup_pages s' = vs_lookup_pages s"
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub2)
    apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: obj_at_def s'_def ps_def split: split_if_asm dest!: orthr)
  apply simp
  done


lemma obj_at_valid_pte:
  "\<lbrakk>valid_pte pte s; \<And>P p. obj_at P p s \<Longrightarrow> obj_at P p s'\<rbrakk> 
   \<Longrightarrow> valid_pte pte s'"
  by (cases pte, auto simp: obj_at_def)


lemma obj_at_valid_pde:
  "\<lbrakk>valid_pde pde s; \<And>P p. obj_at P p s \<Longrightarrow> obj_at P p s'\<rbrakk> 
   \<Longrightarrow> valid_pde pde s'"
  by (cases pde, auto simp: obj_at_def)


lemma valid_arch_objs':
  assumes va: "valid_arch_objs s" 
  shows "valid_arch_objs s'"
proof
  fix p ao
  assume p: "(\<exists>\<rhd> p) s'"
  assume "ko_at (ArchObj ao) p s'"
  hence "ko_at (ArchObj ao) p s \<or> ArchObj ao = default_object ty us"
    by (simp add: ps_def obj_at_def s'_def split: split_if_asm)
  moreover
  { assume "ArchObj ao = default_object ty us" with tyunt
    have "valid_arch_obj ao s'" by (rule valid_arch_obj_default)
  }
  moreover
  { assume "ko_at (ArchObj ao) p s"
    with va p
    have "valid_arch_obj ao s"
      by (auto simp: vs_lookup' elim: valid_arch_objsD)
    hence "valid_arch_obj ao s'"
      apply (cases ao, simp_all add: obj_at_pres)
       apply (erule allEI)
       apply (erule (1) obj_at_valid_pte[OF _ obj_at_pres])
      apply (erule ballEI)
      apply (erule (1) obj_at_valid_pde[OF _ obj_at_pres])
      done
  }
  ultimately
  show "valid_arch_obj ao s'" by blast
qed


end


definition
  valid_vs_lookup2 :: "(vs_ref list \<times> word32) set \<Rightarrow> word32 set \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
 "valid_vs_lookup2 lookup S caps \<equiv>
    \<forall>p ref. (ref, p) \<in> lookup \<longrightarrow>
          ref \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
         (\<exists>p' cap. caps p' = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"


lemma valid_vs_lookup_def2:
  "valid_vs_lookup s = valid_vs_lookup2
         (vs_lookup_pages s) (set (arm_global_pts (arch_state s)))
         (null_filter (caps_of_state s))"
  apply (simp add: valid_vs_lookup_def valid_vs_lookup2_def)
  apply (intro iff_allI imp_cong[OF refl] disj_cong[OF refl]
               iff_exI conj_cong[OF refl])
  apply (auto simp: null_filter_def)
  done


lemma unique_table_caps_null:
  "unique_table_caps (null_filter s)
       = unique_table_caps s"
  apply (simp add: unique_table_caps_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  done


lemma unique_table_refs_null:
  "unique_table_refs (null_filter s)
       = unique_table_refs s"
  apply (simp only: unique_table_refs_def)
  apply (intro iff_allI)
  apply (clarsimp simp: null_filter_def)
  apply (auto dest!: obj_ref_none_no_asid[rule_format]
               simp: table_cap_ref_def)
  done


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

definition
  region_in_kernel_window :: "word32 set \<Rightarrow> 'z state \<Rightarrow> bool"
where 
 "region_in_kernel_window S \<equiv>
     \<lambda>s. \<forall>x \<in> S. arm_kernel_vspace (arch_state s) x = ArmVSpaceKernelWindow"

context retype_region_proofs
begin

lemmas unique_table_caps_eq
    = arg_cong[where f=unique_table_caps, OF null_filter,
               simplified unique_table_caps_null]

lemmas unique_table_refs_eq
    = arg_cong[where f=unique_table_refs, OF null_filter,
               simplified unique_table_refs_null]

lemma valid_table_caps:
  "valid_table_caps s \<Longrightarrow> valid_table_caps s'"
  apply (simp add: valid_table_caps_def
              del: imp_disjL)
  apply (elim allEI, intro impI, simp)
  apply (frule caps_retype[rotated])
   apply clarsimp
  apply (rule obj_at_pres)
  apply simp
  done

lemma valid_arch_caps:
  "valid_arch_caps s \<Longrightarrow> valid_arch_caps s'"
  by (clarsimp simp add: valid_arch_caps_def null_filter
                         valid_vs_lookup_def2 vs_lookup_pages'
                         unique_table_caps_eq
                         unique_table_refs_eq
                         valid_table_caps)

lemma valid_arch_obj_pres:
  "valid_arch_obj ao s \<Longrightarrow> valid_arch_obj ao s'"
  apply (cases ao, simp_all)
    apply (simp add: obj_at_pres)
   apply (erule allEI)
   apply (erule (1) obj_at_valid_pte[OF _ obj_at_pres])
  apply (erule ballEI)
  apply (erule (1) obj_at_valid_pde[OF _ obj_at_pres])
  done

lemma valid_global_objs:
  "valid_global_objs s \<Longrightarrow> valid_global_objs s'"
  apply (simp add: valid_global_objs_def valid_ao_at_def)
  apply (elim conjE, intro conjI ballI)
    apply (erule exEI)
    apply (simp add: obj_at_pres valid_arch_obj_pres)
   apply (simp add: obj_at_pres)
  apply (rule exEI, erule(1) bspec)
  apply (simp add: obj_at_pres valid_arch_obj_pres)
  done

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

lemma valid_kernel_mappings:
  "valid_kernel_mappings s \<Longrightarrow> valid_kernel_mappings s'"
  apply (simp add: valid_kernel_mappings_def s'_def
                   ball_ran_eq ps_def)
  apply (simp add: default_object_def valid_kernel_mappings_if_pd_def
                   tyunt default_arch_object_def pde_ref_def
            split: Structures_A.apiobject_type.split
                   aobject_type.split)
  done

lemma valid_asid_map:
  "valid_asid_map s \<Longrightarrow> valid_asid_map s'"
  apply (clarsimp simp: valid_asid_map_def)
  apply (drule bspec, blast)
  apply (clarsimp simp: pd_at_asid_def)
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (drule obj_at_pres)
  apply (fastforce simp: vs_asid_refs_def graph_of_def 
                  intro: vs_lookupI vs_lookup1I)
  done

lemma only_idle:
  "only_idle s \<Longrightarrow> only_idle s'"
  apply (clarsimp simp: only_idle_def)
  apply (clarsimp simp: s'_def pred_tcb_at_def obj_at_def ps_def split: split_if_asm)
  apply (simp add: default_object_def tyunt split: Structures_A.apiobject_type.splits)
  apply (simp add: default_tcb_def)
  done

lemma equal_kernel_mappings:
  "equal_kernel_mappings s \<Longrightarrow>
      if ty = ArchObject PageDirectoryObj
      then equal_kernel_mappings
           (s'\<lparr>kheap := kheap s' |` (- set (retype_addrs ptr ty n us))\<rparr>)
      else equal_kernel_mappings s'"
  apply (simp add: equal_kernel_mappings_def)
  apply (intro conjI impI)
   apply (elim allEI)
   apply (simp add: obj_at_def restrict_map_def)
   apply (simp add: s'_def ps_def)
  apply (elim allEI)
  apply (simp add: obj_at_def restrict_map_def)
  apply (simp add: s'_def ps_def)
  apply (simp add: default_object_def default_arch_object_def tyunt
            split: Structures_A.apiobject_type.split
                   aobject_type.split)
  done

lemma valid_global_pd_mappings:
  "valid_global_pd_mappings s
         \<Longrightarrow> valid_global_pd_mappings s'"
  apply (erule valid_global_pd_mappings_pres)
     apply (simp | erule obj_at_pres)+
  done

lemma pspace_in_kernel_window:
  "\<lbrakk> pspace_in_kernel_window s; region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1} s \<rbrakk>
          \<Longrightarrow> pspace_in_kernel_window s'"
  apply (simp add: pspace_in_kernel_window_def s'_def ps_def)
  apply (clarsimp simp: region_in_kernel_window_def
                   del: ballI)
  apply (drule retype_addrs_mem_subset_ptr_bits[OF cover tyunt])
  apply (fastforce simp: field_simps obj_bits_api_default_object[OF tyunt])
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

lemma vms:
  "valid_machine_state s \<Longrightarrow> valid_machine_state s'"
  apply (simp add: s'_def ps_def valid_machine_state_def in_user_frame_def)
  apply (rule allI, erule_tac x=p in allE, clarsimp)
  apply (rule_tac x=sz in exI, clarsimp simp: obj_at_def orthr)
  done

lemma post_retype_invs:
  "\<lbrakk> invs s; region_in_kernel_window {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1} s \<rbrakk>
        \<Longrightarrow> post_retype_invs ty (retype_addrs ptr ty n us) s'"
  using equal_kernel_mappings
  by (clarsimp simp: invs_def post_retype_invs_def valid_state_def
                     unsafe_rep2 null_filter valid_idle
                     valid_reply_caps valid_reply_masters
                     valid_global_refs valid_arch_state
                     valid_irq_node_def obj_at_pres
                     valid_arch_caps valid_global_objs
                     valid_arch_objs' valid_irq_handlers
                     valid_mdb_rep2 mdb_and_revokable
                     valid_pspace cur_tcb only_idle
                     valid_kernel_mappings valid_asid_map
                     valid_global_pd_mappings valid_ioc vms
                     pspace_in_kernel_window
                     cap_refs_in_kernel_window valid_irq_states)

end

lemma use_retype_region_proofs':
  assumes x: "\<And>s. \<lbrakk> retype_region_proofs s ty us ptr sz n; P s \<rbrakk>
   \<Longrightarrow> Q (retype_addrs ptr ty n us) (s\<lparr>kheap :=
           \<lambda>x. if x \<in> set (retype_addrs ptr ty n us)
             then Some (default_object ty us)
             else kheap s x\<rparr>)"
  assumes y: "\<And>x s f. Q x (trans_state f s) = Q x s"
  shows
    "\<lbrakk> ty = CapTableObject \<Longrightarrow> 0 < us;
         \<And>s. P s \<longrightarrow> Q (retype_addrs ptr ty n us) s \<rbrakk> \<Longrightarrow>
    \<lbrace>\<lambda>s. valid_pspace s \<and> valid_mdb s \<and> range_cover ptr sz (obj_bits_api ty us) n 
        \<and> caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1} s
        \<and> caps_no_overlap ptr sz s \<and> pspace_no_overlap ptr sz s \<and>
        P s\<rbrace> retype_region ptr n us ty \<lbrace>Q\<rbrace>"
  apply (simp add: retype_region_def split del: split_if)
  apply (rule hoare_pre, (wp|simp add:y trans_state_update[symmetric] del: trans_state_update)+)
  apply (clarsimp simp: retype_addrs_fold 
                        foldr_upd_app_if fun_upd_def[symmetric])
  apply safe
  apply (rule x)
   apply (rule retype_region_proofs.intro, simp_all)[1]
   apply (simp add: range_cover_def obj_bits_api_def 
     slot_bits_def word_bits_def cte_level_bits_def)+
  done


lemmas use_retype_region_proofs
    = use_retype_region_proofs'[where Q="\<lambda>_. Q" and P=Q, simplified]
      for Q

lemmas retype_region_valid_pspace =
    use_retype_region_proofs[where Q=valid_pspace,
                             OF retype_region_proofs.valid_pspace,
                             simplified]

lemmas retype_region_caps_of =
    use_retype_region_proofs[
       where Q="\<lambda>s. P (null_filter (caps_of_state s))",
       OF ssubst [where P=P, OF retype_region_proofs.null_filter],
       simplified]
    for P


lemma retype_region_valid_cap:
  "\<lbrakk>ty = Structures_A.apiobject_type.CapTableObject \<Longrightarrow> 0 < us\<rbrakk>
   \<Longrightarrow> \<lbrace>(\<lambda>s. valid_pspace s \<and> caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1} s \<and>
           valid_mdb s \<and> range_cover ptr sz (obj_bits_api ty us) n \<and>
           caps_no_overlap ptr sz s \<and> pspace_no_overlap ptr sz s  \<and>
           s \<turnstile> cap) and K (untyped_range cap \<inter> {ptr..(ptr &&~~ mask sz) + 2 ^ sz - 1} = {})\<rbrace>
        retype_region ptr n us ty
      \<lbrace>\<lambda>r s. s \<turnstile> cap\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
  apply (rule use_retype_region_proofs)
    apply (erule retype_region_proofs.valid_cap)
    apply simp+
  done


lemmas retype_region_aligned =
    use_retype_region_proofs[where Q=pspace_aligned,
                             OF retype_region_proofs.psp_al,
                             simplified]


lemmas retype_region_valid_idle =
    use_retype_region_proofs[where Q=valid_idle,
                             OF retype_region_proofs.valid_idle,
                             simplified]


lemmas retype_region_valid_arch =
    use_retype_region_proofs[where Q=valid_arch_state,
                             OF retype_region_proofs.valid_arch_state,
                             simplified]


lemmas retype_region_valid_globals =
    use_retype_region_proofs[where Q=valid_global_refs,
                             OF retype_region_proofs.valid_global_refs,
                             simplified]


lemmas retype_region_valid_reply_caps =
    use_retype_region_proofs[where Q=valid_reply_caps,
                             OF retype_region_proofs.valid_reply_caps,
                             simplified]


lemmas retype_region_valid_reply_masters =
    use_retype_region_proofs[where Q=valid_reply_masters,
                             OF retype_region_proofs.valid_reply_masters,
                             simplified]


lemmas retype_region_arch_objs =
    use_retype_region_proofs[where Q=valid_arch_objs,
                             OF retype_region_proofs.valid_arch_objs',
                             simplified]


crunch irq_node[wp]: retype_region "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)


crunch interrupt_states[wp]: retype_region "\<lambda>s. P (interrupt_states s)"
  (simp: crunch_simps)


lemma invs_post_retype_invs:
  "invs s \<Longrightarrow> post_retype_invs ty refs s"
  apply (clarsimp simp: post_retype_invs_def invs_def valid_state_def)
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def
                        restrict_map_def)
  done

lemma equal_kernel_mappings_trans_state[simp]:
  "equal_kernel_mappings (trans_state f s) = equal_kernel_mappings s"
  apply (simp add: equal_kernel_mappings_def)
  done

lemma invs_trans_state[simp]:
  "invs (trans_state f s) = invs s"
  apply (simp add: invs_def valid_state_def)
  done
  
lemma post_retype_invs_trans_state[simp]:
  "post_retype_invs ty refs (trans_state f s) = post_retype_invs ty refs s"
  apply (simp add: post_retype_invs_def)
  apply (simp add: trans_state_update[symmetric] del: trans_state_update)
  done

lemma retype_region_post_retype_invs:
  "\<lbrace>invs and caps_no_overlap ptr sz and pspace_no_overlap ptr sz
      and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
      and region_in_kernel_window {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}
      and K (ty = Structures_A.CapTableObject \<longrightarrow> 0 < us)
      and K (range_cover ptr sz (obj_bits_api ty us) n) \<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. post_retype_invs ty rv\<rbrace>"
  apply (rule hoare_gen_asm)+
  apply (rule hoare_pre,
         rule use_retype_region_proofs'[where sz = sz 
      and P="invs and region_in_kernel_window {ptr .. (ptr &&~~ mask sz) + 2 ^ sz - 1}"])
      apply (rule retype_region_proofs.post_retype_invs, simp+)
   apply (simp add: invs_post_retype_invs)
   apply (clarsimp simp:invs_def valid_state_def)
  done

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


lemma subset_not_le_trans: "\<lbrakk>\<not> A \<subset> B; C \<subseteq> B\<rbrakk> \<Longrightarrow> \<not> A \<subset> C" by auto


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

lemma cte_wp_at_trans_state[simp]: "cte_wp_at P ptr (kheap_update f (trans_state f' s)) =
       cte_wp_at P ptr (kheap_update f s)"
  apply (simp add: trans_state_update[symmetric] del: trans_state_update)
  done

lemma retype_region_cte_at_other:
  assumes cover: "range_cover ptr' sz (obj_bits_api ty us) n"
  shows "\<lbrace>\<lambda>s. pspace_no_overlap ptr' sz s \<and> cte_wp_at P ptr s \<and> valid_pspace s\<rbrace> 
  retype_region ptr' n us ty \<lbrace>\<lambda>r. cte_wp_at P ptr\<rbrace>"
  unfolding retype_region_def 
  apply (simp only: foldr_upd_app_if fun_app_def K_bind_def)
  apply wp
      apply (simp only: cte_wp_at_trans_state)
      apply wp
  apply (subst retype_addrs_fold)
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_cases del: disjCI)
  apply (erule disjEI)
   apply (auto dest!: pspace_no_overlapD1[OF _ _ cover])
done


lemma retype_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at P ptr s \<and> pspace_no_overlap ptr' sz s \<and> 
       valid_pspace s \<and> range_cover ptr' sz (obj_bits_api ty us) n\<rbrace> 
  retype_region ptr' n us ty 
  \<lbrace>\<lambda>r. cte_wp_at P ptr\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_pre)
   apply (rule retype_region_cte_at_other)
   apply fastforce
  apply simp
  done


lemma pspace_no_overlap_typ_at_def:
  "pspace_no_overlap ptr bits = 
  (\<lambda>s. \<forall>T x. typ_at T x s \<longrightarrow> {x..x + (2 ^ obj_bits_type T - 1)} \<inter> {ptr..(ptr && ~~ mask bits) + (2 ^ bits - 1)} = {})"
  apply (simp add: pspace_no_overlap_def obj_at_def)
  apply (rule ext)
  apply (auto simp: obj_bits_T)
  done


lemma pspace_no_overlap_typ_at_lift:
  assumes f: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows "\<lbrace>pspace_no_overlap w b\<rbrace> f \<lbrace>\<lambda>rv. pspace_no_overlap w b\<rbrace>"
  apply (clarsimp simp: pspace_no_overlap_typ_at_def)
  apply (wp hoare_vcg_all_lift f)
  done

lemma swp_clearMemoryVM [simp]:
  "swp clearMemoryVM x = (\<lambda>_. return ())"
  by (rule ext,simp)


(* FIXME: move *)
lemma bind_assoc_reverse:
  "(do x \<leftarrow> A; _ \<leftarrow> B x; C x od) =
   (do x \<leftarrow> do x \<leftarrow> A; _ \<leftarrow> B x; return x od; C x od)"
by (simp only: bind_assoc return_bind)


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
