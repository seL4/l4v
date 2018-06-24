(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory BinarySearch
imports "AutoCorres.AutoCorres" "../../DataStructures"
begin

external_file "binary_search.c"
install_C_file "binary_search.c"

autocorres [ts_rules = nondet, unsigned_word_abs=binary_search] "binary_search.c"

context binary_search begin

lemma uint_of_nat:
    "uint (of_nat x :: 'a::len word) = (int x) mod 2^ len_of TYPE('a)"
  apply (clarsimp simp only: uint_nat unat_of_nat)
  apply (metis of_nat_numeral semiring_1_class.of_nat_power zmod_int)
  done

lemma ptr_add_uint_of_nat [simp]:
    "p +\<^sub>p uint (of_nat x :: addr) = p +\<^sub>p int x"
  apply (subst uint_of_nat)
  apply (unfold CTypesDefs.ptr_add_def)
  apply (metis (hide_lams, no_types) uint_of_nat of_int_of_nat_eq of_int_uint)
  done

lemmas [simp] = sint_ucast_eq_uint is_up is_down


primrec
  array :: "lifted_globals \<Rightarrow> word32 ptr \<Rightarrow> word32 list \<Rightarrow> bool"
where
    "array s p [] = True"
  | "array s p (x#xs) = ((heap_w32 s p = x) \<and> (is_valid_w32 s p) \<and> array s (p +\<^sub>p 1) xs)"

definition
  "is_array s p n \<equiv> \<exists>l. array s p l \<and> length l = n"

definition
  "the_array s p n \<equiv> (THE l. length l = n \<and> array s p l)"

lemma array_unique:
    "\<lbrakk> array s p l; array s p l'; length l = length l' \<rbrakk> \<Longrightarrow> l = l'"
  apply (induct l arbitrary: l' p)
   apply clarsimp
  apply (case_tac l')
   apply clarsimp
   apply clarsimp
  done

lemma array_concat [simp]:
  "array s p (a @ b) = (array s p a \<and> array s (p +\<^sub>p int (length a)) b)"
  apply (induct a arbitrary: p)
   apply clarsimp
  apply clarsimp
  apply atomize
  apply (erule_tac x="p +\<^sub>p 1" in allE)
  apply (clarsimp simp: CTypesDefs.ptr_add_def field_simps)
  done

lemma array_is_array: "array s p a \<Longrightarrow> is_array s p (length a)"
  apply (clarsimp simp: is_array_def)
  apply force
  done

lemma array_the_array: "\<lbrakk> array s p a; length a = n \<rbrakk> \<Longrightarrow> the_array s p n = a"
  apply (simp add: the_array_def)
  apply (metis (lifting, mono_tags) array_unique the_equality)
  done

lemma length_the_array [simp]: "is_array s p n \<Longrightarrow> length (the_array s p n) = n"
  apply (induct n arbitrary: n)
   apply (clarsimp simp: is_array_def)
   apply (metis array_the_array)
  apply (clarsimp simp: is_array_def)
  done

lemma the_array_Suc:
  "\<lbrakk> is_array s p n; n > 0 \<rbrakk> \<Longrightarrow> the_array s p n = (heap_w32 s p) # (the_array s (p +\<^sub>p 1) (n - 1))"
  apply (clarsimp simp: is_array_def)
  apply (case_tac l)
   apply clarsimp
  apply clarsimp
  apply (metis One_nat_def Suc_eq_plus1 list.size(4) array.simps(2) array_the_array)
  done

lemma the_array_0 [simp]:
  "the_array s p 0 = []"
  by (metis list.size(3) array.simps(1) array_the_array)

lemma is_array_0 [simp]:
  "is_array s p 0"
  apply (clarsimp simp: is_array_def)
  done

lemma is_array_Suc:
  "\<lbrakk> is_array s p n; is_valid_w32 s (p +\<^sub>p int n) \<rbrakk> \<Longrightarrow>
      is_array s p (Suc n)"
  apply (clarsimp simp: is_array_def)
  apply (rule_tac x="l @ [heap_w32 s (p +\<^sub>p int (length l))]" in exI)
  apply clarsimp
  done

lemma array_expand: "array s p n \<Longrightarrow> array s (p +\<^sub>p 1) (tl n)"
  apply (case_tac n)
   apply clarsimp
  apply clarsimp
  done

lemma array_Ex:
  "\<lbrakk> array s p n; 0 \<le> i; i < int (length n) \<rbrakk> \<Longrightarrow> is_valid_w32 s (p +\<^sub>p i)"
  apply (induct n arbitrary: p i)
   apply clarsimp
  apply clarsimp
  apply atomize
  apply (erule_tac x="p +\<^sub>p 1" in allE)
  apply (erule_tac x="i - 1" in allE)
  apply (clarsimp simp: CTypesDefs.ptr_add_def)
  done

lemma sorted_index_lt:
  "\<lbrakk> sorted xs; unat (xs ! m) < v; n \<le> m; m < length xs \<rbrakk> \<Longrightarrow>  unat (xs ! n) < v"
  by (meson le_less_trans sorted_nth_mono unat_arith_simps(1))

lemma sorted_index_gt:
    "\<lbrakk> sorted xs; v < unat (xs ! m); m \<le> n; n < length xs \<rbrakk> \<Longrightarrow>  v < unat (xs ! n)"
  by (metis le_less_linear le_less_trans less_irrefl sorted_nth_mono word_less_nat_alt)

lemma array_access_to_list_access:
    "\<lbrakk> array s p data; n < length data \<rbrakk> \<Longrightarrow> (heap_w32 s (p +\<^sub>p int n)) = data ! n"
  apply (induct data arbitrary: n p)
   apply clarsimp
  apply (case_tac "n = 0")
   apply clarsimp
  apply atomize
  apply (erule_tac x="n - 1" in allE)
  apply (erule_tac x="p +\<^sub>p 1" in allE)
  apply (erule impE)
   apply clarsimp
  apply (erule impE)
   apply clarsimp
   apply arith
  apply (clarsimp simp: field_simps CTypesDefs.ptr_add_def)
  done

lemma binary_search_correct:
  "\<lbrace> \<lambda>s. array s arr data \<and> length data < 1000000000 \<and> n = length data \<and> sorted data \<rbrace>
           binary_search' arr n v
        \<lbrace> \<lambda>r s. r \<noteq> 0 \<longleftrightarrow> v \<in> unat ` set data \<rbrace>!"
  apply (rule validNF_assume_pre)
  apply (unfold binary_search'_def)
  apply (case_tac "n = 0")
   apply (subst whileLoop_add_inv [where I="\<lambda>(f, l, r) _. f = 0 \<and> l = 0 \<and> r = 0" and M="\<lambda>_. 0"])
   apply ((wp | clarsimp)+)[1]
  apply (subst whileLoop_add_inv [where
        I="\<lambda>(found, l, r) s. array s arr data  \<and> (r \<le> n)
                \<and> (\<forall>i. i < l \<longrightarrow> i < n \<longrightarrow> unat (data ! i) <  v)
                \<and> (\<forall>i. i \<ge> r \<longrightarrow> i < n \<longrightarrow> v < unat (data ! i))
                \<and> (found \<noteq> 0 \<longrightarrow> v \<in> unat ` set data)"
          and  M="\<lambda>((found, l, r), s). if found = 0 then 1 + (r - l) else 0" ])
  apply wp
     apply (clarsimp split del: if_split cong: if_cong
       simp: field_simps array_access_to_list_access array_Ex UINT_MAX_def)
    apply (subgoal_tac "aa \<le> ((aa + b)  div 2) \<and> ((aa + b) div 2) \<le> b")
     apply (case_tac "unat (data ! ((aa + b) div 2)) = v")
      apply (clarsimp simp: UINT_MAX_def INT_MAX_def)
     apply (case_tac "unat (data ! ((aa + b) div 2)) < v")
      apply (auto elim: sorted_index_lt simp: UINT_MAX_def INT_MAX_def cong: if_cong)[1]
     apply (subgoal_tac "unat (data ! ((aa + b) div 2)) > v")
      apply (clarsimp simp: UINT_MAX_def INT_MAX_def)
      apply (fastforce elim: sorted_index_gt)
     apply force
    apply force
   apply (clarsimp split del: if_split simp: field_simps cong: if_cong)
   apply rule
    apply clarsimp
   apply clarsimp
   apply (metis (no_types) in_set_conv_nth le_less_trans neq_iff not_less)
  apply clarsimp
  done

end

end
