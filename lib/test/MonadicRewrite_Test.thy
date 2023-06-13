(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory MonadicRewrite_Test
imports Lib.MonadicRewrite
begin

(* in order to see the way bound variables are handled with bind/bindE by various rules, show etas
   in this file *)
declare [[eta_contract=false]]

section \<open>Function definitions to use in examples\<close>

definition
  "example_k x \<equiv> gets (K x)"
definition
  "example_f \<equiv> example_k 2"

(* linear examples in normal and error monad *)

definition
  "example_add = do
     a \<leftarrow> example_f;
     b \<leftarrow> example_k a;
     c \<leftarrow> example_f;
     return (a+b+c)
   od"

definition
  "example_addE = doE
     a \<leftarrow> liftE example_f;
     b \<leftarrow> liftE (example_k a);
     c \<leftarrow> liftE example_f;
     returnOk (a+b+c)
   odE"

section \<open>Sanity checks\<close>

(* pass through entire LHS while doing nothing, should get exact same state out *)

lemma
  "monadic_rewrite True False \<top> example_add example_add"
  unfolding example_add_def
  apply monadic_rewrite_pre
   apply (rule monadic_rewrite_trans) \<comment> \<open>schematise RHS\<close>
    apply (rule monadic_rewrite_step_l)+
       apply (rule monadic_rewrite_refl)
      apply wp+
  (* the terms on both sides should be identical, including bound names *)
  apply (rule monadic_rewrite_refl)
  apply simp
  done

lemma
  "monadic_rewrite True False \<top> example_addE example_addE"
  unfolding example_addE_def
  apply monadic_rewrite_pre
   apply (rule monadic_rewrite_trans) \<comment> \<open>schematise RHS\<close>
    apply (rule monadic_rewrite_step_l)+
       apply (rule monadic_rewrite_refl)
      apply wp+
  (* the terms on both sides should be identical, including bound names *)
  apply (rule monadic_rewrite_refl)
  apply simp
  done

(* now do the same using automation (note automation needs a specific target to hit, as achieving
   nothing is considered a failure *)

lemma
  "monadic_rewrite True False \<top> example_add example_add"
  unfolding example_add_def
  apply (monadic_rewrite_l monadic_rewrite_refl[where f="return (a+b+c)" for a b c])
  (* the terms on both sides should be identical, including bound names *)
  apply (rule monadic_rewrite_refl)
  apply simp
  done

lemma
  "monadic_rewrite True False \<top> example_addE example_addE"
  unfolding example_addE_def
  apply (monadic_rewrite_l monadic_rewrite_refl[where f="returnOk (a+b+c)" for a b c])
  (* the terms on both sides should be identical, including bound names *)
  apply (rule monadic_rewrite_refl)
  apply simp
  done

section \<open>Example of rewriting with a matching rule: selecting branches of if statements\<close>

(* in this example, we know we'll always take the left branch because b will be 2 *)

definition
  "example_if = do
     a \<leftarrow> example_f;
     b \<leftarrow> example_k a;
     if (b = 2)
     then do
       c \<leftarrow> example_f;
       return (a+2+c)
     od
     else do
       c \<leftarrow> example_f;
       return (a+b+c)
     od
   od"

definition
  "example_removed_if = do
     a \<leftarrow> example_f;
     b \<leftarrow> example_k a;
     c \<leftarrow> example_f;
     return (a+2+c)
   od"

lemma example_k_wp:
  "\<lbrace>K (a = n)\<rbrace> example_k a \<lbrace>\<lambda>rv s. rv = n\<rbrace>"
  unfolding example_k_def
  by wpsimp

lemma example_f_wp_2:
  "\<lbrace>\<top>\<rbrace> example_f \<lbrace>\<lambda>rv s. rv = 2\<rbrace>"
  unfolding example_f_def
  by (wpsimp wp: example_k_wp)

lemma example_f_wp:
  "\<lbrace>K (n = 2)\<rbrace> example_f \<lbrace>\<lambda>rv s. rv = n\<rbrace>"
  unfolding example_f_def
  by (wpsimp wp: example_k_wp)

(* rewrite the if, but use succeed to show remaining wp goals *)
lemma
  "monadic_rewrite True False \<top> example_if example_removed_if"
  unfolding example_if_def example_removed_if_def
  apply (monadic_rewrite_l monadic_rewrite_if_l_True succeed)
     apply (wpsimp wp: example_k_wp)
    apply (wpsimp wp: example_f_wp_2)
  (* note: bound names are preserved *)
  apply (rule monadic_rewrite_refl)
  apply simp
  done

(* RHS version: rewrite the if, but use succeed to show remaining wp goals *)
lemma
  "monadic_rewrite True False \<top> example_removed_if example_if"
  unfolding example_if_def example_removed_if_def
  apply (monadic_rewrite_r monadic_rewrite_if_r_True succeed)
     apply (wpsimp wp: example_k_wp)
    apply (wpsimp wp: example_f_wp_2)
  (* note: bound names are preserved *)
  apply (rule monadic_rewrite_refl)
  apply simp
  done

(* rewrite the if completely automatically *)
lemma (* on left *)
  "monadic_rewrite True False \<top> example_if example_removed_if"
  unfolding example_if_def example_removed_if_def
  by (monadic_rewrite_l monadic_rewrite_if_l_True \<open>wpsimp wp: example_k_wp example_f_wp\<close>)
     (rule monadic_rewrite_refl, simp)
lemma (* on right *)
  "monadic_rewrite True False \<top> example_removed_if example_if"
  unfolding example_if_def example_removed_if_def
  by (monadic_rewrite_r monadic_rewrite_if_r_True \<open>wpsimp wp: example_k_wp example_f_wp\<close>)
     (rule monadic_rewrite_refl, simp)

(* if the required rules are already present in the environment, no need to specify a method *)
lemma (* on left *)
  "monadic_rewrite True False \<top> example_if example_removed_if"
  unfolding example_if_def example_removed_if_def
  supply example_k_wp[wp] example_f_wp[wp]
  by (monadic_rewrite_l monadic_rewrite_if_l_True)
     (rule monadic_rewrite_refl, simp)

section \<open>Symbolic execution\<close>

(* performing symbolic execution within a monadic_rewrite requires discharging no_fail/empty_fail
   conditions depending on RHS/LHS and flags *)
crunches example_k, example_f
  for inv[wp]: "P"
  and (empty_fail) empty_fail[wp]
  and (no_fail) no_fail[wp]

(* If you know the value and can prove it later: monadic_rewrite_symb_exec_l/r_known *)

lemma
  "monadic_rewrite True False \<top> example_if example_removed_if"
  unfolding example_if_def example_removed_if_def
  supply example_k_wp[wp] example_f_wp[wp]
  (* LHS: we know example_f will return 2, but will prove it later *)
  apply (monadic_rewrite_symb_exec_l_known 2)
    (* LHS: we know example_k 2 will return 2, but will prove it later *)
    (* observe that symb_exec methods attempt to discharge inv/no_/empty_fail goals in the
       background and optionally take a custom method; here we examine them with succeed *)
    apply (monadic_rewrite_symb_exec_l_known 2 succeed)
       prefer 2 apply wp (* inv *)
      prefer 2 apply wp (* empty_fail *)
     (* can simplify if condition normally *)
     apply simp
     (* we know the same return values occur on RHS, but that isn't very interesting as we won't
        normally symbolically execute if we have the same term on both sides, so let's schematise
        LHS and rewrite RHS to match it via symbolic execution *)
     apply (monadic_rewrite_pre, rule monadic_rewrite_trans[rotated])
      (* RHS: we know example_f will return 2, but will prove it later *)
      apply (monadic_rewrite_symb_exec_r_known 2)
       (* RHS: we know example_k 2 will return 2, but will prove it later *)
       apply (monadic_rewrite_symb_exec_r_known 2)
        (* done with RHS rewrite *)
        apply (rule monadic_rewrite_refl)
       (* discharge RHS obligations of returning 2 that we deferred earlier *)
       apply wpsimp+
     (* rewrite was successful, LHS = RHS *)
     apply (rule monadic_rewrite_refl)
    (* discharge LHS obligations of returning 2 that we deferred earlier *)
    apply wpsimp+
  done

(* The basic form of symbolic execution acts as one would expect: it does not specify any return
   value, discharging any obligations later *)
lemma
  "monadic_rewrite True False \<top> example_if example_removed_if"
  unfolding example_if_def example_removed_if_def
  (* let's rewrite the LHS as in previous example, but this time not knowing what the values will
     be *)
  apply monadic_rewrite_symb_exec_l+
    (* we still know we will take the first branch of the if, but we'll prove it later *)
     apply (rule_tac P="b = 2" in monadic_rewrite_gen_asm)
     (* we can simplify the if statement as usual *)
     apply simp

     (* let's rewrite RHS into new LHS now, but with normal symbolic execution *)
     apply (monadic_rewrite_pre, rule monadic_rewrite_trans[rotated])
      apply monadic_rewrite_symb_exec_r (* name collision: a \<rightarrow> aa *)
       (* the rewrite is only true if the two "a" are the same, so assume that *)
       apply (rule_tac P="aa = a" in monadic_rewrite_gen_asm, simp)
       apply monadic_rewrite_symb_exec_r
        (* done with RHS rewrite *)
        apply (rule monadic_rewrite_refl)
       (* discharge RHS obligations *)
       apply (wpsimp wp: example_f_wp)+

     (* rewrite was successful, LHS = RHS *)
     apply no_name_eta
     apply (rule monadic_rewrite_refl)
    (* clear up LHS obligations w.r.t. precondition (bit fiddly due to equalities) *)
    apply (clarsimp simp: pred_conj_def cong: conj_cong)
    apply (wpsimp wp: example_k_wp example_f_wp)+
  done

(* The "drop" form of symbolic execution is mainly used when a combination of rewrites and
   assertions results in a state-invariant operation whose results are not used, such as
   a number of getters whose results are used on branches not taken under the precondition. *)
lemma
  "monadic_rewrite True False \<top> example_if example_if"
  unfolding example_if_def
  apply (monadic_rewrite_pre, rule monadic_rewrite_trans)
    (* we artificially add operations to LHS that are irrelevant *)
    apply (repeat 10 \<open>rule monadic_rewrite_add_return\<close>)
    (* done with rewriting *)
    apply (rule monadic_rewrite_refl)
   (* we can remove added operations in one pass *)
   apply monadic_rewrite_symb_exec_l_drop+
   (* both sides equal again *)
   apply (rule monadic_rewrite_refl)
  apply simp
  done

end
