(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Memcpy
imports
  "../../../c-parser/CTranslation"
  "../../AutoCorres"
begin

lemma byte_ptr_guarded:
    "ptr_val (x::8 word ptr) \<noteq> 0 \<Longrightarrow> c_guard x"
  unfolding c_guard_def c_null_guard_def ptr_aligned_def
  by (clarsimp simp: intvl_Suc)

(* FIXME: MOVE *)
lemma ptr_add_coerce: "ptr_val (((ptr_coerce x)::('a::{c_type}) ptr) +\<^sub>p a) = (ptr_val x) + (of_int a * of_nat (size_of TYPE('a)))"
  apply (case_tac x)
  apply (clarsimp simp: CTypesDefs.ptr_add_def)
  done

(* FIXME: MOVE *)
(* Casting a valid pointer to char* and incrementing it by a value less than
 * the size of the underlying type does not give us NULL.
 *)
lemma ptr_contained:"\<lbrakk> c_guard (x::('a::c_type) ptr); size_of TYPE('a) = sz;
                       0 \<le> i; i < int sz; (y::8 word ptr) = ptr_coerce x\<rbrakk> \<Longrightarrow> c_guard (y +\<^sub>p i)"
  apply (rule byte_ptr_guarded)
  unfolding c_guard_def c_null_guard_def ptr_add_def
  apply simp
  apply (clarsimp simp: CTypesDefs.ptr_add_def intvl_def)
  apply (erule allE [where x="nat i"])
  apply (clarsimp simp: nat_less_iff of_nat_nat)
  done

install_C_file "memcpy.c"

(* FIXME: MOVE *)
lemma squash_auxupd_id[polish]:
  "modify (t_hrs_'_update (hrs_htd_update id)) = skip"
  by (monad_eq simp: skip_def id_def hrs_htd_update_def)

autocorres "memcpy.c"

(* Dereference a pointer *)
abbreviation "deref s x \<equiv> h_val (hrs_mem (t_hrs_' s)) x"

(* char* cast *)
abbreviation "byte_cast x \<equiv> ((ptr_coerce x)::8 word ptr)"

context memcpy begin

lemma memcpy_char:
  "\<lbrace> \<lambda>s. c_guard (x::8 word ptr) \<and>
         c_guard (y::8 word ptr) \<and>
         unat sz = size_of TYPE(8 word) \<and>
         P (deref s x) \<and>
         x \<noteq> y\<rbrace>
      memcpy' (ptr_coerce y) (ptr_coerce x) sz
   \<lbrace>\<lambda> _ s. P (deref s y) \<rbrace>!"
  (* Evaluate sz *)
  apply clarsimp

  unfolding memcpy'_def
  apply (clarsimp simp:skip_def)
  apply wp

  (* Unroll the loop twice *)
  apply (subst whileLoop_unroll, wp)
     apply (subst whileLoop_unroll, wp)

  (* The remaining loop is never encountered *)
       apply (rule validNF_false_pre)
      apply wp

  (* Finally we're left with the single assignment *)
  apply (clarsimp simp:hrs_mem_update h_val_heap_update)
  apply unat_arith
 done

lemma is_aligned_add_not_aligned:
    "\<lbrakk>is_aligned (p::word32) n; \<not> is_aligned (q::word32) n\<rbrakk> \<Longrightarrow>
          \<not> is_aligned (p + q) n"
  by (metis is_aligned_addD1)

(* Possibly useful for something later *)
lemma "\<lbrakk> 2 ^ n dvd (p::nat); n > 0; i > 0; i < 2 ^ n; p + i > p; n < 32\<rbrakk> \<Longrightarrow>
          \<not> (2 ^ n dvd (p + i))"
  by (metis dvd_def dvd_reduce_multiple nat_dvd_not_less)

(* FIXME: MOVE *)
lemma word32_gr0_conv_Suc:"(m::word32) > 0 \<Longrightarrow> \<exists>n. m = n + 1"
  by (metis comm_semiring_1_class.normalizing_semiring_rules(24) zadd_diff_inverse)

(* FIXME: MOVE *)
lemma offset_not_aligned:
  "\<lbrakk> is_aligned (p::word32) n; i > 0; i < 2 ^ n; n < 32\<rbrakk>
     \<Longrightarrow> \<not> is_aligned (p + of_nat i) n"
  apply (erule is_aligned_add_not_aligned)
  unfolding is_aligned_def apply clarsimp
  apply (subst (asm) unat_of_nat_len)
   apply (metis len32 unat_less_word_bits unat_power_lower32 word_bits_conv)
  apply (metis nat_dvd_not_less)
  done

lemma of_nat_prop_exp: "n < 32 \<Longrightarrow> of_nat (2 ^ n) = 2 ^ (of_nat n)"
  by clarsimp

lemma neg_mask_add_aligned:
  "\<lbrakk> is_aligned p n; q < 2 ^ n \<rbrakk>
     \<Longrightarrow> (p + q) && ~~ mask n = p && ~~ mask n"
  by (metis is_aligned_add_helper is_aligned_neg_mask_eq)

lemma neq_imp_bytes_disjoint:
  "\<lbrakk> c_guard (x::'a::c_type ptr); c_guard y; unat j < align_of TYPE('a);
        unat i < align_of TYPE('a); x \<noteq> y; 2 ^ n = align_of TYPE('a); n < 32\<rbrakk> \<Longrightarrow>
    ptr_val x + j \<noteq> ptr_val y + i"
  apply (rule ccontr)
  apply (subgoal_tac "is_aligned (ptr_val x) n")
   apply (subgoal_tac "is_aligned (ptr_val y) n")
    apply (subgoal_tac "(ptr_val x + j && ~~ mask n) = (ptr_val y + i && ~~ mask n)")
     apply (subst (asm) neg_mask_add_aligned, simp, simp add: word_less_nat_alt)
     apply (subst (asm) neg_mask_add_aligned, simp, simp add: word_less_nat_alt)
     apply (clarsimp simp: is_aligned_neg_mask_eq)
    apply simp
   apply (clarsimp simp: c_guard_def ptr_aligned_def is_aligned_def)
  apply (clarsimp simp: c_guard_def ptr_aligned_def is_aligned_def)
  done

lemma from_bytes_eq [simp]:
  "from_bytes [x] = x"
  apply (clarsimp simp:from_bytes_def update_ti_t_def typ_info_word)
  apply (simp add:word_rcat_def)
  apply (simp add:bin_rcat_def)
  by (metis len8 word_of_int_uint word_ubin.Abs_norm)

lemma memcpy_word:
  "\<lbrace> \<lambda>s. c_guard (x::32 word ptr) \<and>
         c_guard (y::32 word ptr) \<and>
         unat sz = size_of TYPE(32 word) \<and>
         P (deref s x) \<and>
         x \<noteq> y \<rbrace>
      memcpy' (ptr_coerce y) (ptr_coerce x) sz
   \<lbrace> \<lambda>_ s. P (deref s y) \<rbrace>!"
  apply clarsimp
  unfolding memcpy'_def apply (clarsimp simp:skip_def)
  apply (rule validNF_assume_pre)
  apply (subgoal_tac "{ptr_val x ..+ unat sz} \<inter> {ptr_val y ..+ unat sz} = {}")
   apply (subst whileLoop_add_inv [where
     I="\<lambda>i s.  unat i \<le> unat sz \<and>
                (\<forall>a < i. deref s (byte_cast x +\<^sub>p uint a) = deref s (byte_cast y +\<^sub>p uint a)) \<and>
                P (deref s x)" and
     M="\<lambda>(i, s). unat sz - unat i"])
   apply (wp validNF_whileLoop_inv_measure_twosteps)
      apply clarsimp
      apply (rule conjI, unat_arith)
      apply (rule conjI, clarsimp)
       apply (case_tac "a = i")
        apply (clarsimp)
        apply (erule_tac x=i in allE)
        apply (clarsimp simp:hrs_mem_update h_val_heap_update)
        apply (subst h_val_heap_same)
            apply (rule ptr_retyp_h_t_valid)
            apply simp
           apply (rule ptr_retyp_disjoint)
            apply (rule ptr_retyp_h_t_valid)
            apply simp
           apply (clarsimp simp:ptr_add_def intvl_def CTypesDefs.ptr_add_def)
          apply simp
         apply (clarsimp simp: CTypesDefs.ptr_add_def field_of_t_simple)
         apply (drule field_of_t_simple)
         apply clarsimp
        apply simp
       apply (subgoal_tac "a < i")
        apply (clarsimp simp:hrs_mem_update)
        apply (subst h_val_heap_update_disjoint)

         (* The current goal should be obvious to unat_arith, but for some reason isn't *)
         apply (clarsimp simp:ptr_add_def intvl_def ptr_val_def disjoint_iff_not_equal)
         apply (erule_tac x="ptr_val x + a" in allE, clarsimp)
         apply (erule impE)
          apply (rule_tac x="unat a" in exI, clarsimp)
          apply unat_arith
          
         apply (erule_tac x="ptr_val y + i" and
                          P="\<lambda>ya. (\<exists>k. ya = ptr_val y + of_nat k \<and> k < 4) \<longrightarrow> ptr_val y + i \<noteq> ya" in allE, clarsimp)
         apply (erule_tac x="unat i" in allE, clarsimp)
          apply unat_arith
         apply (clarsimp simp:CTypesDefs.ptr_add_def)
        apply (subst h_val_heap_update_disjoint)
         (* Similar goal to the previous irritation, but this time Isabelle decides to play ball *)
         apply (clarsimp simp:ptr_add_def intvl_def ptr_val_def disjoint_iff_not_equal)
        apply (clarsimp simp:CTypesDefs.ptr_add_def)
       apply (clarsimp simp:CTypesDefs.ptr_add_def)
      apply unat_arith

      apply (rule conjI)
       apply (subst hrs_mem_update)+
       apply (subst h_val_heap_update_disjoint)
        apply (clarsimp simp: disjoint_iff_not_equal)
        apply (clarsimp simp:CTypesDefs.ptr_add_def intvl_def)
        apply (erule_tac x="ptr_val x + of_nat k" in allE)
        apply (erule impE)
         apply (rule_tac x="k" in exI)
         apply simp
        apply (erule_tac x="ptr_val y + i" and
                         P="\<lambda>ya. (\<exists>k. ya = ptr_val y + of_nat k \<and> k < 4) \<longrightarrow> ptr_val x + of_nat k \<noteq> ya" in allE)
        apply (erule impE)
         apply (rule_tac x="unat i" in exI)
         apply simp
         apply unat_arith
        apply simp
       apply simp

      (* Yet more tedium that unat_arith doesn't like *)
      apply (rule conjI)
       apply (rule byte_ptr_guarded,
              clarsimp simp:CTypesDefs.ptr_add_def c_guard_def c_null_guard_def intvl_def,
              (erule_tac x="unat i" in allE)+,
              clarsimp,
              unat_arith)+

     apply wp
     apply unat_arith
    apply clarsimp
    apply (subgoal_tac "deref sa x = deref sa y")
     apply clarsimp
    apply (clarsimp simp: h_val_def)[1]
    apply (rule arg_cong[where f=from_bytes])
    apply (subst numeral_eqs(3))+
    apply simp
    apply (rule_tac x=0 in allE, assumption, erule impE, unat_arith)
    apply (rule_tac x=1 in allE, assumption, erule impE, unat_arith)
    apply (rule_tac x=2 in allE, assumption, erule impE, unat_arith)
    apply (rule_tac x=3 in allE, assumption, erule impE, unat_arith)
    apply (simp add:CTypesDefs.ptr_add_def)
    apply (metis comm_semiring_1_class.normalizing_semiring_rules(24))
   apply clarsimp
   apply wp
   apply clarsimp
  apply (clarsimp simp:intvl_def disjoint_iff_not_equal)
  apply (drule_tac x=x and y=y and j="of_nat k" and i="of_nat ka" and n=2 in neq_imp_bytes_disjoint)
        apply assumption
       apply (case_tac "k = 0", clarsimp) (* insert "k > 0" *)
       apply (clarsimp simp:unat_of_nat_len)
      apply (case_tac "ka = 0", clarsimp)
      apply (clarsimp simp:unat_of_nat_len)
     apply assumption
    apply clarsimp+
  done

end

end
