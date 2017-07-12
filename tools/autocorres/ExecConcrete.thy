(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ExecConcrete
imports CorresXF
begin

definition "exec_transformed (sr :: ('s \<times> 't) set) (M :: ('t, 'r) nondet_monad) \<equiv>
    \<lambda>s. (\<Union> ((\<lambda>(r', t'). {(r, t). r = r' \<and> (t, t') \<in> sr}) ` (\<Union> (fst ` M ` {s'. (s, s') \<in> sr}))),
            True \<in> snd ` M ` {s'. (s, s') \<in> sr})"

lemma in_exec_transformed:
  "((r, s') \<in> fst (exec_transformed sr A s)) = (\<exists>t t'. (s, t) \<in> sr \<and>  (s', t') \<in> sr \<and> (r, t') \<in> fst (A t))"
  apply (clarsimp simp: exec_transformed_def)
  apply force
  done

lemma snd_exec_transformed:
  "snd (exec_transformed sr M s) = (\<exists>x. (s, x) \<in> sr \<and> snd (M x))"
  by (clarsimp simp: exec_transformed_def)

lemma exec_transformed_Id [simp]:
    "exec_transformed Id M = M"
  apply (auto simp: exec_transformed_def)
  done

lemma exec_transformed_valid_def:
    "\<lbrace> P \<rbrace> exec_transformed sr M \<lbrace> Q \<rbrace> = \<lbrace> \<lambda>s. \<exists>s'. (s', s) \<in> sr \<and> P s' \<rbrace> M \<lbrace> \<lambda>r s. \<forall>s'. (s', s) \<in> sr \<longrightarrow> Q r s' \<rbrace>"
  apply (rule iffI [rotated])
   apply (clarsimp simp: image_def split_def valid_def in_exec_transformed)
   apply force
  apply (clarsimp simp: image_def split_def valid_def exec_transformed_def)
  apply (erule allE, erule (1) impE)
  apply (case_tac "M s")
  apply (erule_tac allE, erule impE)
   by (auto intro!: exI) fastforce

lemma exec_transformed_wp [wp]:
    "\<lbrace> \<lambda>s. \<exists>s'. (s', s) \<in> sr \<and> P s' \<rbrace> M \<lbrace> \<lambda>r s. \<forall>s'. (s', s) \<in> sr \<longrightarrow> Q r s' \<rbrace> \<Longrightarrow> \<lbrace> P \<rbrace> exec_transformed sr M \<lbrace> Q \<rbrace>"
  apply (subst exec_transformed_valid_def)
  apply simp
  done

lemma exec_transformedE_wp [wp]:
  "\<lbrace> \<lambda>s. \<exists>s'. (s', s) \<in> sr \<and> P s' \<rbrace> M \<lbrace> \<lambda>r s. \<forall>s'. (s', s) \<in> sr \<longrightarrow> Q r s' \<rbrace>,\<lbrace> \<lambda>r s. \<forall>s'. (s', s) \<in> sr \<longrightarrow> E r s' \<rbrace>
      \<Longrightarrow> \<lbrace> P \<rbrace> exec_transformed sr M \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (clarsimp simp: validE_def)
  apply (rule exec_transformed_wp)
  apply (clarsimp simp: valid_def split: sum.splits)
  apply force
  done

lemma exec_transformed_no_fail [wp]:
  "no_fail (\<lambda>s. \<exists>s'. (s', s) \<in> sr \<and> P s') M \<Longrightarrow> no_fail P (exec_transformed sr M)"
  apply (clarsimp simp: no_fail_def snd_exec_transformed)
  apply force
  done

lemmas exec_transformed_wp_nf [wp] =
  validNF [OF exec_transformed_wp exec_transformed_no_fail]

lemma exec_transformed_return_wp [wp]:
    "\<lbrace> \<lambda>s. \<forall>s''. (\<exists>s'. (s, s') \<in> sr \<and> (s'', s') \<in> sr) \<longrightarrow> P a s'' \<rbrace> exec_transformed sr (return a) \<lbrace> P \<rbrace>"
  including no_pre
  apply wp
  apply clarsimp
  apply force
  done

lemma exec_transformed_returnOk_wp [wp]:
    "\<lbrace> \<lambda>s. \<forall>s''. (\<exists>s'. (s, s') \<in> sr \<and> (s'', s') \<in> sr) \<longrightarrow> P a s'' \<rbrace> exec_transformed sr (returnOk a) \<lbrace> P \<rbrace>,\<lbrace> E \<rbrace>"
  including no_pre
  apply wp
  apply clarsimp
  apply force
  done

lemma exec_transformed_fail_wp_nf [wp]:
    "\<lbrace> \<lambda>s. \<not> (\<exists>s'. (s, s') \<in> sr) \<rbrace> exec_transformed sr fail \<lbrace> P \<rbrace>!"
  apply wp
  apply (clarsimp simp: fail_def no_fail_def)
  apply force
  done

lemma exec_transformed_fail_wp [wp]:
    "\<lbrace> \<lambda>_. True \<rbrace> exec_transformed st fail \<lbrace> P \<rbrace>"
  including no_pre by wp

(*
 * Execute the given monad with a concrete state.
 *
 * In particular, we non-determinstically select a concrete state that maps
 * to the current abstract state, execute @{term M}, and then map the resulting
 * states back into the abstract universe.
 *)
definition "exec_concrete (st :: 't \<Rightarrow> 's)  (M :: ('t, 'r) nondet_monad) \<equiv>
       \<lambda>s. ({(r, t). \<exists>s' t'. s = st s' \<and> t = st t' \<and> (r, t') \<in> fst (M s')},
            \<exists>s'. s = st s' \<and> snd (M s'))"

lemma "exec_concrete st M = exec_transformed {(s, t). st t = s} M"
  apply (rule ext)
  apply (clarsimp simp: exec_concrete_def exec_transformed_def)
  apply force
  done

lemma in_exec_concrete [monad_eq]:
  "((r, s') \<in> fst (exec_concrete st A s)) = (\<exists>t t'. st t = s \<and> st t' = s' \<and> (r, t') \<in> fst (A t))"
  apply (clarsimp simp: exec_concrete_def split_def image_def)
  apply force
  done

lemma snd_exec_concrete [monad_eq]:
  "snd (exec_concrete st M s) = (\<exists>x. st x = s \<and> snd (M x))"
  by (fastforce simp: exec_concrete_def)

lemma exec_concrete_id [simp]:
    "exec_concrete id M = M"
    "exec_concrete (\<lambda>a. a) M = M"
  apply (auto simp: exec_concrete_def)
  done

lemma exec_concrete_wp [wp]:
    "\<lbrace> \<lambda>s. P (st s) \<rbrace> M \<lbrace> \<lambda>r s. Q r (st s) \<rbrace> \<Longrightarrow> \<lbrace> P \<rbrace> exec_concrete st M \<lbrace> Q \<rbrace>"
  apply (clarsimp simp: image_def split_def valid_def in_exec_concrete)
  apply force
  done

lemma exec_concreteE_wp [wp]:
  "\<lbrace> \<lambda>s. P (st s) \<rbrace> M \<lbrace> \<lambda>r s. Q r (st s) \<rbrace>,\<lbrace> \<lambda>r s. E r (st s) \<rbrace>
      \<Longrightarrow> \<lbrace> P \<rbrace> exec_concrete st M \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (clarsimp simp: validE_def)
  apply (rule exec_concrete_wp)
  apply simp
  done

lemma exec_concrete_no_fail [wp]:
  "no_fail (\<lambda>s. P (st s)) M \<Longrightarrow> no_fail P (exec_concrete st M)"
  apply (clarsimp simp: no_fail_def snd_exec_concrete)
  done

lemma exec_concrete_wp_nf [wp]:
    "\<lbrace> \<lambda>s. P (st s) \<rbrace> M \<lbrace> \<lambda>r s. Q r (st s) \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> exec_concrete st M \<lbrace> Q \<rbrace>!"
  apply rule
   apply (rule exec_concrete_wp)
   apply (erule validNF_valid)
  including no_pre
  apply wp
  apply (erule validNF_no_fail)
  done

lemma exec_concrete_return_wp [wp]:
    "\<lbrace> P a \<rbrace> exec_concrete st (return a) \<lbrace> P \<rbrace>"
  by wp

lemma exec_concrete_returnOk_wp [wp]:
    "\<lbrace> P a \<rbrace> exec_concrete st (returnOk a) \<lbrace> P \<rbrace>,\<lbrace> E \<rbrace>"
  by wp

lemma exec_concrete_return_wp_nf [wp]:
    "\<lbrace> P a \<rbrace> exec_concrete st (return a) \<lbrace> P \<rbrace>!"
  by wp

lemma exec_concrete_fail_wp_nf [wp]:
    "\<lbrace> \<lambda>s. False \<rbrace> exec_concrete st fail \<lbrace> P \<rbrace>!"
  by wp

lemma exec_concrete_fail_wp [wp]:
    "\<lbrace> \<lambda>_. True \<rbrace> exec_concrete st fail \<lbrace> P \<rbrace>"
  by wp

lemma corresXF_simple_exec_concrete:
    "corresXF_simple st (\<lambda>r s. r) P (exec_concrete st M) M"
  apply (clarsimp simp: corresXF_simple_def  image_def split_def
      snd_exec_concrete in_exec_concrete)
  apply force
  done

lemma corresXF_exec_concrete_self:
    "corresXF st (\<lambda>r s. r) (\<lambda>r s. r) P (exec_concrete st M) M"
  apply (subst corresXF_simple_corresXF [symmetric])
  apply clarsimp
  apply (rule corresXF_simple_exec_concrete)
  done

lemma corresXF_exec_concrete [intro?]:
  "corresXF id ret_xf ex_xf P A C \<Longrightarrow> corresXF st ret_xf ex_xf P (exec_concrete st A) C"
  apply (clarsimp simp: corresXF_def exec_concrete_def split: sum.splits)
  apply safe
    apply (clarsimp simp: image_def split_def)
    apply force
   apply (clarsimp simp: image_def split_def)
   apply force
  done

lemma exec_concrete_empty_fail [wp]:
  "\<lbrakk> empty_fail M; \<forall>s. \<exists>x. st x = s \<rbrakk> \<Longrightarrow> empty_fail (exec_concrete st M)"
  apply (subst empty_fail_def)
  apply (clarsimp simp: exec_concrete_def)
  apply (metis empty_failD2  surjective_pairing)
  done

(*
 * Execute the given monad in a modified state.
 *)
definition "exec_abstract st M \<equiv>
       \<lambda>s'. ({(r', t'). \<exists>t. t = st t' \<and> (r', t) \<in> fst (M (st s'))},
            \<exists>s. s = st s' \<and> snd (M (st s')))"

lemma exec_abstract_transformed:
    "exec_abstract st M = exec_transformed {(s, t). t = st s} M"
  apply (rule ext)
  apply (clarsimp simp: exec_transformed_def exec_abstract_def)
  apply blast
  done

lemma in_exec_abstract [monad_eq]:
  "((r, t) \<in> fst (exec_abstract st A s)) = (\<exists>t'. st t = t' \<and> (r, t') \<in> fst (A (st s)))"
  by (clarsimp simp: exec_abstract_def split_def image_def)

lemma snd_exec_abstract [monad_eq]:
  "snd (exec_abstract st M s) = (snd (M (st s)))"
  by (clarsimp simp: exec_abstract_def)

lemma exec_abstract_id [simp]:
    "exec_abstract id M = M"
    "exec_abstract (\<lambda>a. a) M = M"
  apply (auto simp: exec_abstract_def)
  done

lemma exec_abstract_valid_def:
    "\<lbrace> P \<rbrace> exec_abstract st M \<lbrace> Q \<rbrace> = \<lbrace> \<lambda>s. \<exists>s'. st s' = s \<and> P s' \<rbrace> M \<lbrace> \<lambda>r s. \<forall>t. st t = s \<longrightarrow> Q r t \<rbrace>"
  apply (subst exec_abstract_transformed)
  apply (subst exec_transformed_valid_def)
  apply (fastforce simp: valid_def)
  done

lemma exec_abstract_wp [wp]:
    "\<lbrakk> \<lbrace> P \<rbrace> M \<lbrace> \<lambda>r s. \<forall>t. st t = s \<longrightarrow> Q r t \<rbrace>  \<rbrakk>
              \<Longrightarrow> \<lbrace> \<lambda>s. P (st s) \<rbrace> exec_abstract st M \<lbrace> Q \<rbrace>"
  apply (subst exec_abstract_valid_def)
  apply (clarsimp simp: valid_def)
  apply force
  done

lemma exec_abstractE_wp [wp]:
    "\<lbrakk> \<lbrace> P \<rbrace> M \<lbrace> \<lambda>r s. \<forall>t. st t = s \<longrightarrow> Q r t \<rbrace>,\<lbrace> \<lambda>r s. \<forall>t. st t = s \<longrightarrow> E r t \<rbrace>  \<rbrakk>
              \<Longrightarrow> \<lbrace> \<lambda>s. P (st s) \<rbrace> exec_abstract st M \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (clarsimp simp: validE_def)
  apply (rule exec_abstract_wp)
  apply (clarsimp simp: valid_def split: sum.splits)
  apply force
  done

lemma exec_abstract_no_fail [wp]:
  "no_fail (\<lambda>s. \<exists>t. st t = s \<and> P t) M \<Longrightarrow> no_fail P (exec_abstract st M)"
  apply (clarsimp simp: no_fail_def snd_exec_abstract)
  apply force
  done

lemma exec_abstract_wp_nf [wp]:
    "\<lbrakk> \<lbrace> P \<rbrace> M \<lbrace> \<lambda>r s. \<forall>t. st t = s \<longrightarrow> Q r t \<rbrace>!  \<rbrakk>
              \<Longrightarrow> \<lbrace> \<lambda>s. P (st s) \<rbrace> exec_abstract st M \<lbrace> Q \<rbrace>!"
  apply rule
   apply (rule exec_abstract_wp)
   apply (erule validNF_valid)
  apply (rule exec_abstract_no_fail)
  apply (rule validNF_no_fail)
  apply (erule validNF_weaken_pre)
  apply force
  done

lemma exec_abstract_return_wp [wp]:
    "\<lbrace> \<lambda>s. \<forall>t. st s = st t \<longrightarrow> P a t \<rbrace> exec_abstract st (return a) \<lbrace> P \<rbrace>"
  apply wp
  apply clarsimp
  done

lemma exec_abstract_returnOk_wp [wp]:
    "\<lbrace> \<lambda>s. \<forall>t. st s = st t \<longrightarrow> P a t \<rbrace> exec_abstract st (returnOk a) \<lbrace> P \<rbrace>,\<lbrace> E \<rbrace>"
  apply wp
  apply clarsimp
  done

lemma exec_abstract_return_wp_nf [wp]:
    "\<lbrace> \<lambda>s. \<forall>t. st s = st t \<longrightarrow> P a t \<rbrace> exec_abstract st (return a) \<lbrace> P \<rbrace>!"
  apply wp
  apply clarsimp
  done

lemma exec_abstract_fail_wp_nf [wp]:
    "\<lbrace> \<lambda>s. False \<rbrace> exec_abstract st fail \<lbrace> P \<rbrace>!"
  apply wp
  apply clarsimp
  done

lemma exec_abstract_fail_wp [wp]:
    "\<lbrace> \<lambda>_. True \<rbrace> exec_abstract st fail \<lbrace> P \<rbrace>"
  by wp

lemma corresXF_simple_exec_abstract:
    "corresXF_simple st (\<lambda>r s. r) P M (exec_abstract st M)"
  apply (clarsimp simp: corresXF_simple_def  image_def split_def
      snd_exec_abstract in_exec_abstract)
  done

lemma corresXF_exec_abstract_self:
    "corresXF st (\<lambda>r s. r) (\<lambda>r s. r) P M (exec_abstract st M)"
  apply (subst corresXF_simple_corresXF [symmetric])
  apply clarsimp
  apply (rule corresXF_simple_exec_abstract)
  done

lemma corresXF_exec_abstract [intro?]:
  "corresXF st ret_xf ex_xf P A C \<Longrightarrow> corresXF id ret_xf ex_xf P (exec_abstract st A) C"
  apply (clarsimp simp: corresXF_def exec_abstract_def split: sum.splits)
  done

lemma exec_abstract_empty_fail [wp]:
  "\<lbrakk> empty_fail M; \<forall>s. \<exists>x. st x = s \<rbrakk> \<Longrightarrow> empty_fail (exec_abstract st M)"
  apply (clarsimp simp: empty_fail_def exec_abstract_def)
  apply (metis nonemptyE surjective_pairing)
  done

end
