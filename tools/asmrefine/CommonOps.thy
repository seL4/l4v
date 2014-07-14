(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CommonOps

imports 
	"../../lib/WordLemmaBucket"
	"../../lib/CTranslationNICTA"
begin

text {* Additional constants needed to make conversion to graph lang easy *}

definition
  bvshl :: "'a :: len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
 "bvshl x y = x << (unat y)"

definition
  bvlshr :: "'a :: len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
 "bvlshr x y = x >> (unat y)"

definition
  bvashr :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where
 "bvashr x y = x >>> (unat y)"

definition
  bv_shift_amount :: "nat => 'a :: len word"
where
 "bv_shift_amount n = of_nat (min n ((2 ^ len_of TYPE('a)) - 1))"

definition
  "count_leading_zeroes z = length (takeWhile Not (to_bl z))"

definition
  "count_trailing_zeroes z = length (takeWhile Not (rev (to_bl z)))"

definition
  bv_clz :: "('a :: len) word \<Rightarrow> 'a word"
where
  "bv_clz x = of_nat (count_leading_zeroes x)"

definition
  "mem_acc mem addr = h_val mem (Ptr addr)"

definition
  "mem_upd mem addr v = heap_update (Ptr addr) v mem"

definition
 "store_word32 (addr :: word32) (w :: word32)
    = heap_update_list addr (rev (word_rsplit w))"

definition
 "load_word32 (addr :: word32) memory
    = (word_rcat (rev (heap_list memory 4 addr)) :: word32)"

definition
 "store_word8 (addr :: word32) (w :: word8) m = m (addr := w)"

definition
 "load_word8 (addr :: word32) m = (m addr :: word8)"

definition
  word_add_with_carry :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> bool
    \<Rightarrow> ('a word \<times> (bool \<times> bool))"
where
 "word_add_with_carry x y cin \<equiv>
  let cinw = if cin then 1 else 0
  in (x + y + cinw,
      unat (x + y + cinw) \<noteq> unat x + unat y + unat cinw,
      (msb x \<noteq> msb y) \<and> (msb x \<noteq> msb (x + y + cinw)))"

definition
  ptr_inverse_safe :: "('a :: mem_type) ptr \<Rightarrow> heap_typ_desc \<Rightarrow> bool"
where
  "ptr_inverse_safe p htd = (c_guard p
        \<and> (fst ` s_footprint p \<inter> fst ` dom_s htd = {}))"

definition
  all_htd_updates :: "('a :: c_type) itself \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32
        \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  "all_htd_updates (tp :: ('a :: c_type) itself) x y z
    = (if x = 0
        then typ_clear_region y (unat z)
        else if x = 1 then ptr_retyps (unat z) (Ptr y :: 'a ptr)
        else if x = 2 then typ_region_bytes y (unat z)
        else ptr_retyps (2 ^ unat z) (Ptr y :: 'a ptr))"

lemma fold_all_htd_updates:
  "ptr_retyp (p :: ('a :: c_type) ptr)
    = all_htd_updates TYPE('a) 1 (ptr_val p) 1" 
  "\<lbrakk> n < 2 ^ 32 \<rbrakk> \<Longrightarrow>
    ptr_retyps n p = all_htd_updates TYPE('a) 1 (ptr_val p) (of_nat n)" 
  "\<lbrakk> n < 2 ^ 32 \<rbrakk> \<Longrightarrow>
    ptr_retyps (2 ^ n) p = all_htd_updates TYPE('a) 3 (ptr_val p) (of_nat n)"
  "n < 2 ^ 32 \<Longrightarrow> typ_clear_region x n = all_htd_updates TYPE(word32) 0 x (of_nat n)"
  "n < 2 ^ 32 \<Longrightarrow> typ_region_bytes x n = all_htd_updates TYPE(word32) 2 x (of_nat n)"
  "(if P then (f :: heap_typ_desc \<Rightarrow> heap_typ_desc) else g) s
    = (if P then f s else g s)"
  by (simp_all add: all_htd_updates_def unat_of_nat fun_eq_iff of_nat_neq_0)

definition
  "pvalid htd (v :: ('a :: c_type) itself) x = h_t_valid htd c_guard (Ptr x :: 'a ptr)"

definition
  "palign_valid (v :: ('a :: c_type) itself) x = c_guard (Ptr x :: 'a ptr)"

definition
  "pweak_valid htd (v :: ('a :: c_type) itself) x = ptr_safe (Ptr x :: 'a ptr) htd"

definition
  "pglobal_valid htd (v :: ('a :: mem_type) itself) x = ptr_inverse_safe (Ptr x :: 'a ptr) htd"

lemma signed_div_range_check:
  assumes len: "size a > 1"
  shows
  "(sint a sdiv sint b = sint (a sdiv b))
    = (a \<noteq> (- (2 ^ (size a - 1))) \<or> b \<noteq> -1)"
proof -
  have sints: "(sint (1 :: 'a word)) = 1"
       "(sint (-1 :: 'a word)) = -1"
       "(sint (0 :: 'a word)) = 0"
    using len
    apply (simp_all add: word_size)
    done
  have abs_sint_gt_1:
    "b \<noteq> 0 \<and> b \<noteq> 1 \<and> b \<noteq> -1 \<Longrightarrow> abs (sint b) > 1"
    apply (fold word_sint.Rep_inject,
        simp only: sints abs_if split: split_if)
    apply arith
    done
  have mag: "(a \<noteq> (- (2 ^ (size a - 1))) \<or> (b \<noteq> -1 \<and> b \<noteq> 1))
    \<Longrightarrow> abs (abs (sint a) div abs (sint b)) < 2 ^ (size a - 1)"
    using word_sint.Rep_inject[where x=a and y="- (2 ^ (size a - 1))"]
          word_sint.Rep_inject[where x=b and y=1]
    apply (simp add: word_size sint_int_min sints)
    apply (simp add: nonneg_mod_div)
    apply (cases "b = 0")
     apply simp
    apply (erule impCE)
     apply (rule order_le_less_trans, rule zdiv_le_dividend, simp_all)
     apply (cut_tac x=a in sint_range')
     apply (clarsimp simp add: abs_if word_size)
    apply (cases "a = 0", simp_all)
    apply (rule order_less_le_trans, rule int_div_less_self, simp_all)
     apply (rule abs_sint_gt_1, simp)
    apply (cut_tac x=a in sint_range')
    apply (clarsimp simp add: abs_if word_size)
    done
  show ?thesis using mag len
    apply (cases "b = 1")
     apply (case_tac "size a", simp_all)[1]
     apply (case_tac nat, simp_all add: sint_word_ariths word_size)[1]
    apply (simp add: sdiv_int_def sdiv_word_def sint_sbintrunc'
                     sbintrunc_eq_in_range range_sbintrunc sgn_if)
    apply (safe, simp_all add: word_size sint_int_min)
    done
qed

end

