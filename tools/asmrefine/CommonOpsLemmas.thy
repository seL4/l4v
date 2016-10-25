(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory CommonOpsLemmas

imports
  "CommonOps"
        "../../lib/$L4V_ARCH/WordSetup"
begin

lemma fold_all_htd_updates':
  "ptr_retyp (p :: ('a :: c_type) ptr)
    = all_htd_updates TYPE('a) 1 (ptr_val p) 1"
  "(if P then (f :: heap_typ_desc \<Rightarrow> heap_typ_desc) else g) s
    = (if P then f s else g s)"
  "\<lbrakk> n < 2 ^ 32 \<rbrakk> \<Longrightarrow>
    ptr_retyps n p = all_htd_updates TYPE('a) 1 (ptr_val p) (of_nat n)"
  "\<lbrakk> n < 2 ^ 32 \<rbrakk> \<Longrightarrow>
    ptr_retyps (2 ^ n) p = all_htd_updates TYPE('a) 3 (ptr_val p) (of_nat n)"
  "n < 2 ^ 32 \<Longrightarrow> typ_clear_region x n = all_htd_updates TYPE(word32) 0 x (of_nat n)"
  "n < 2 ^ 32 \<Longrightarrow> typ_region_bytes x n = all_htd_updates TYPE(word32) 2 x (of_nat n)"
  "\<lbrakk> n < 2 ^ 32 \<rbrakk> \<Longrightarrow>
    ptr_arr_retyps n p = all_htd_updates TYPE('a) 4 (ptr_val p) (of_nat n)"
  "\<lbrakk> n < 2 ^ 32 \<rbrakk> \<Longrightarrow>
    ptr_arr_retyps (2 ^ n) p = all_htd_updates TYPE('a) 5 (ptr_val p) (of_nat n)"
  by (simp_all add: all_htd_updates_def unat_of_nat fun_eq_iff of_nat_neq_0)

lemma unat_lt2p_word32:
  "unat (w :: word32) < 2 ^ 32"
  by (rule order_less_le_trans, rule unat_lt2p, simp)

lemmas fold_all_htd_updates
    = fold_all_htd_updates' fold_all_htd_updates'(3-)[OF unat_lt2p_word32]

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
        simp only: sints abs_if split: if_split)
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

lemma ptr_add_assertion_uintD:
  "ptr_add_assertion ptr (uint (x :: ('a :: len) word)) strong htd
    \<longrightarrow> (x = 0 \<or> array_assertion ptr (if strong then unat (x + 1) else unat x) htd)"
  using unat_lt2p[where x=x]
  by (simp add: ptr_add_assertion_def uint_0_iff Word.unat_def[symmetric]
                unat_plus_if_size linorder_not_less word_size
                le_Suc_eq array_assertion_shrink_right
           del: unat_lt2p)

lemma sint_uint_sless_0_if:
  "sint x = (if x <s 0 then - uint (- x) else uint (x :: ('a :: len) word))"
  apply (simp add: word_sint_msb_eq word_sless_alt
                   word_size uint_word_ariths)
  apply (clarsimp simp: zmod_zminus1_eq_if uint_0_iff)
  done

lemma ptr_add_assertion_sintD:
  "ptr_add_assertion ptr (sint (x :: ('a :: len) word)) strong htd
    \<longrightarrow> (x = 0 \<or> (x <s 0 \<and> array_assertion (ptr +\<^sub>p sint x)
            (unat (- x)) htd)
        \<or> (x \<noteq> 0 \<and> \<not> x <s 0 \<and> array_assertion ptr (if strong then unat (x + 1) else unat x) htd))"
  using unat_lt2p[where x=x]
  apply (simp add: ptr_add_assertion_def word_sless_alt
                   sint_uint_sless_0_if[THEN arg_cong[where f="\<lambda>x. - x"]]
                   sint_uint_sless_0_if[THEN arg_cong[where f=nat]]
                   Word.unat_def[symmetric]
                   unat_plus_if_size le_Suc_eq linorder_not_less
                   word_size
           del: unat_lt2p)
  apply (simp add: array_assertion_shrink_right)
  apply (auto simp: linorder_not_less)
  done

end
