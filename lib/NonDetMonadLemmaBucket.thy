(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory NonDetMonadLemmaBucket
imports
  Lib
  Monads.Nondet_More_VCG
  Monad_Lists
  Monads.Nondet_Monad_Equations
  Monad_Commute
  Monads.Nondet_No_Fail
  Monads.Nondet_No_Throw
  CutMon
  Oblivious
  Injection_Handler
  Monads.Nondet_While_Loop_Rules_Completeness
  "Word_Lib.Distinct_Prop" (* for distinct_tuple_helper *)
  Monads.Reader_Option_VCG
begin

lemma distinct_tuple_helper:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. distinct (x # xs rv s)\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. distinct (x # (map fst (zip (xs rv s) (ys rv s))))\<rbrace>"
  apply (erule hoare_strengthen_post)
  apply (erule distinct_prefix)
  apply (simp add: map_fst_zip_prefix)
  done

lemma gets_the_validE_R_wp:
  "\<lbrace>\<lambda>s. f s \<noteq> None \<and> isRight (the (f s)) \<and> Q (theRight (the (f s))) s\<rbrace>
     gets_the f
   \<lbrace>Q\<rbrace>,-"
  apply (simp add: gets_the_def validE_R_def validE_def)
  apply (wp | wpc | simp add: assert_opt_def)+
  apply (clarsimp split: split: sum.splits)
  done

lemma return_bindE:
  "isRight v \<Longrightarrow> return v >>=E f = f (theRight v)"
  by (cases v; clarsimp simp: return_returnOk)

lemma list_case_return: (* not in Lib, because "return" is not in scope there *)
  "(case xs of [] \<Rightarrow> return v | y # ys \<Rightarrow> return (f y ys))
    = return (case xs of [] \<Rightarrow> v | y # ys \<Rightarrow> f y ys)"
  by (simp split: list.split)

(* We use isLeft, because isLeft=isl is the primitive concept; isRight=\<not>isl matches on isl. *)
lemma valid_isLeft_theRight_split:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q False rv s\<rbrace>,\<lbrace>\<lambda>e s. \<forall>v. Q True v s\<rbrace> \<Longrightarrow>
     \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. Q (isLeft rv) (theRight rv) s\<rbrace>"
  apply (simp add: validE_def)
  apply (erule hoare_strengthen_post)
  apply (simp split: sum.split_asm)
  done


(* depends on Lib.list_induct_suffix *)
lemma mapM_x_inv_wp2:
  assumes post: "\<And>s. \<lbrakk> I s; V [] s \<rbrakk> \<Longrightarrow> Q s"
  and     hr: "\<And>a as. suffix (a # as) xs \<Longrightarrow> \<lbrace>\<lambda>s. I s \<and> V (a # as) s\<rbrace> m a \<lbrace>\<lambda>r s. I s \<and> V as s\<rbrace>"
  shows   "\<lbrace>I and V xs\<rbrace> mapM_x m xs \<lbrace>\<lambda>rv. Q\<rbrace>"
proof (induct xs rule: list_induct_suffix)
  case Nil thus ?case
    apply (simp add: mapM_x_Nil)
    apply wp
    apply (clarsimp intro!: post)
    done
next
  case (Cons x xs)
  thus ?case
    apply (simp add: mapM_x_Cons)
    apply wp
     apply (wp hr)
    apply assumption
    done
qed

lemma gets_the_exs_valid_no_ofail:
  "\<lbrakk>no_ofail P h; ovalid P h Q\<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> gets_the h \<exists>\<lbrace>Q\<rbrace>"
  apply (rule exs_valid_weaken_pre)
   apply (rule gets_the_exs_valid)
  apply (fastforce simp: ovalid_def no_ofail_def)
  done

lemma put_id_return:
  "put s s = return () s"
  by (clarsimp simp: put_def return_def)

end
