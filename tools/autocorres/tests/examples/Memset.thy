(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Memset
imports "../../AutoCorres"
begin

install_C_file "memset.c"

autocorres [
  heap_abs_syntax,
  no_heap_abs=memset,
  no_signed_word_abs=memset,
  unsigned_word_abs=memset] "memset.c"

lemma c_guard_word8_ptr [simp]:
     "c_guard (x :: word8 ptr) = (x \<noteq> NULL)"
  apply (clarsimp simp: c_guard_def ptr_aligned_def c_null_guard_def)
  apply (metis Ptr_ptr_val first_in_intvl intvl_Suc not_less_eq ptr_val.ptr_val_def)
  done

lemma to_bytes_word8 [simp]: "to_bytes (a :: word8) x = [a]"
  by (clarsimp simp: to_bytes_def typ_info_word word_rsplit_same)

lemma heap_update_list_id [simp]:
    "heap_update_list x [] = (\<lambda>x. x)"
  apply (rule ext)
  apply simp
  done

lemma heap_update_heap_update_list:
   "\<lbrakk> ptr_val p = q + (of_nat (length l)); Suc (length l) < addr_card \<rbrakk> \<Longrightarrow>
      heap_update (p :: word8 ptr) v (heap_update_list q l s) = (heap_update_list q (l @ [v]) s)"
  apply (rule ext)
  apply (clarsimp simp: heap_update_def unat_of_nat
    addr_card word_bits_def fun_upd_def)
  apply (subst heap_update_list_value, clarsimp simp: addr_card)
  apply safe
   apply (subst if_P)
    apply (fastforce intro: intvlI)
   apply (clarsimp simp: unat_of_nat word_bits_def)
  apply (subst (1 2)  heap_update_list_value,
    simp add: addr_card,
    simp add: addr_card)
  apply (case_tac "x \<in> {q..+length l}")
   apply (subst if_P, simp)
   apply (subst if_P)
    apply clarsimp
    apply (metis (full_types) intvlD intvlI less_SucI)
   apply (subst nth_append, clarsimp)
   apply (metis (hide_lams, no_types) add_diff_cancel2 intvlD le_unat_uoi less_or_eq_imp_le not_le)
  apply clarsimp
  apply (metis intvlD intvlI less_antisym)
  done

lemma (in memset) memset:
  "\<forall>s\<^sub>0. \<lbrace> \<lambda>s. s = s\<^sub>0 \<and> n < addr_card \<and> 0 \<notin> {ptr_val p ..+ n} \<rbrace>
      memset' p c n
      \<lbrace> \<lambda>rv s. s = t_hrs_'_update (hrs_mem_update (
          heap_update_list (ptr_val p) (replicate n (scast c)))) s\<^sub>0 \<rbrace>!"
proof -
  {
     fix s0
     have "\<lbrace> \<lambda>s. s = s0 \<and> n < addr_card \<and> 0 \<notin> {ptr_val p ..+ n} \<rbrace>
                memset' p c n
          \<lbrace> \<lambda>rv s. s = t_hrs_'_update (hrs_mem_update
              (heap_update_list (ptr_val p) (replicate n (scast c)))) s0 \<rbrace>!"
      apply (rule validNF_assume_pre)
      apply (unfold memset'_def)
      apply (subst whileLoop_add_inv [where M="\<lambda>((d', n'), _). n'"
                and I="\<lambda>(d', n') s.
                   n' \<le> n \<and>
                   (n' \<le> n \<longrightarrow> d' = ptr_coerce p +\<^sub>p int (n - n')) \<and>
                   (n' \<le> n \<longrightarrow> s = t_hrs_'_update
                  (hrs_mem_update (heap_update_list (ptr_val p) (replicate (n - n') (scast c)))) s0)"])
      apply wp
        apply (clarsimp simp:)
        apply (intro conjI impI)
           apply arith
          apply (clarsimp simp: ptr_add_def)
         apply (rule globals.fold_congs, simp, simp)
         apply (clarsimp simp: hrs_mem_update_def)
         apply (subst heap_update_heap_update_list)
           apply (clarsimp simp: ptr_add_def)
          apply (clarsimp)
          apply arith
         apply (metis diff_Suc_diff_eq2 diff_diff_left minus_nat.diff_0 replicate_Suc_append)
        apply (clarsimp simp: ptr_add_def)
        apply (metis (hide_lams, no_types) add_less_cancel_right add.left_neutral intvl_inter_le le0 le_add_diff_inverse of_nat_diff semiring_1_class.of_nat_0)
       apply clarsimp
      apply (clarsimp simp: hrs_mem_update_def)
      done
  }

  thus ?thesis
    by simp
qed

lemma word_rsplit_sword_0 [simplified, simp]:
  "word_rsplit (0 :: addr_bitsize signed word) = replicate (size_of TYPE(addr)) (0 :: word8)"
  apply (simp add: word_rsplit_def bin_rsplit_def Let_def)
  done

lemma word_rsplit_word_0 [simplified, simp]:
  "word_rsplit (0 :: addr_bitsize word) = replicate (size_of TYPE(addr)) (0 :: word8)"
  apply (simp add: word_rsplit_def bin_rsplit_def Let_def)
  done

lemma heap_update_zero_node [simplified]:
  "heap_update_list p (replicate (size_of TYPE(node_C)) 0) = heap_update (Ptr p) (node_C NULL 0)"
  apply (rule ext)
  apply (clarsimp simp: heap_update_def to_bytes_def)
  apply (subst packed_type_access_ti, simp)
  apply (clarsimp simp: access_ti\<^sub>0_def)
  apply (clarsimp simp: to_bytes_def to_bytes_p_def node_C_tag_def node_C_typ_tag)
  apply (subst final_pad_def)
  apply (clarsimp simp: typ_info_word size_td_lt_ti_typ_pad_combine Let_def padup_def)
  apply (clarsimp simp: ti_typ_pad_combine_def)
  apply (clarsimp simp: ti_typ_combine_def empty_typ_info_def typ_info_ptr typ_info_word)
  done

lemma (in memset) is_valid_node_C_non_NULL [simp]:
  "is_valid_node_C (lift_global_heap s) p \<Longrightarrow> 0 \<notin> {ptr_val p ..+ size_of TYPE(node_C)}"
  by (auto simp: lift_global_heap_def c_guard_def c_null_guard_def dest: simple_lift_c_guard)

lemma (in memset) zero_node:
  "\<forall>s\<^sub>0. \<lbrace> \<lambda>s. is_valid_node_C s p \<and> s = s\<^sub>0\<rbrace> zero_node' p \<lbrace> \<lambda>rv s. s = s\<^sub>0[p := (node_C NULL 0) ] \<rbrace>! "
  apply (clarsimp simp: zero_node'_def)
  apply (wp add: memset [THEN validNF_make_schematic_post, simplified])
  apply (fastforce dest: simple_lift_c_guard is_valid_node_C_non_NULL
                   simp: addr_card lift_global_heap_def heap_update_zero_node
                         memset.update_node_def typ_simple_heap_simps fun_upd_def)
  done

end
