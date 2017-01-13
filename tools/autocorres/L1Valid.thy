(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Proofs about L1.
 *)

theory L1Valid
imports L1Defs
begin

(* Weakest Precondition Proofs (WP) *)

lemma L1_skip_wp [wp]: "\<lbrace> P () \<rbrace> L1_skip \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (clarsimp simp: L1_skip_def, wp)
  done

lemma L1_modify_wp [wp]: "\<lbrace> \<lambda>s. P () (f s) \<rbrace> L1_modify f \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (clarsimp simp: L1_modify_def, wp)
  done

lemma L1_spec_wp [wp]: "\<lbrace> \<lambda>s. \<forall>t. (s, t) \<in> f \<longrightarrow> P () t \<rbrace> L1_spec f \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (unfold L1_spec_def)
  apply wp
  done

lemma L1_init_wp [wp]: "\<lbrace> \<lambda>s. \<forall>x. P () (f (\<lambda>_. x) s) \<rbrace> L1_init f \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  apply (unfold L1_init_def)
  apply (wp select_wp)
  apply fastforce
  done

(* Liveness proofs. (LP) *)

lemma L1_skip_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q () s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_skip \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_skip_def)
  apply (clarsimp simp: returnOk_def return_def validE_def valid_def)
  done

lemma L1_guard_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q () s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_guard e \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_guard_def guard_def)
  apply (clarsimp simp: returnOk_def return_def validE_def valid_def get_def bind_def fail_def)
  done

lemma L1_fail_lp: "\<lbrace>P\<rbrace> L1_fail \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_fail_def)
  done

lemma L1_throw_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> E () s \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_throw \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_throw_def)
  apply (clarsimp simp: throwError_def validE_def valid_def return_def)
  done

lemma L1_spec_lp: "\<lbrakk> \<And>s r. \<lbrakk> (s, r) \<in> e; P s \<rbrakk> \<Longrightarrow> Q () r \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_spec e \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_spec_def)
  apply (clarsimp simp: spec_def validE_def valid_def)
  done

lemma L1_modify_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> Q () (f s) \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_modify f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_modify_def)
  apply (clarsimp simp: modify_def validE_def valid_def return_def get_def put_def bind_def)
  done

lemma L1_call_lp:
  "\<lbrakk> \<And>s r. P s \<Longrightarrow> Q () (return_xf r (scope_teardown s r)) \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_call scope_setup dest_fn scope_teardown return_xf \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_call_def)
  apply (clarsimp simp: modify_def validE_def valid_def return_def
      get_def put_def bind_def bindE_def liftE_def throwError_def lift_def
      handleE_def handleE'_def fail_def split: sum.splits)
  done

lemma L1_seq_lp: "\<lbrakk>
    \<lbrace>P1\<rbrace> A \<lbrace>Q1\<rbrace>,\<lbrace>E1\<rbrace>;
    \<lbrace>P2\<rbrace> B \<lbrace>Q2\<rbrace>,\<lbrace>E2\<rbrace>;
    \<And>s. P s \<Longrightarrow> P1 s;
    \<And>s. Q1 () s \<Longrightarrow> P2 s;
    \<And>s. Q2 () s \<Longrightarrow> Q () s;
    \<And>s. E1 () s \<Longrightarrow> E () s;
    \<And>s. E2 () s \<Longrightarrow> E () s
    \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_seq A B \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_seq_def)
  apply (rule seqE [rotated])
   apply (erule validE_weaken, simp+)[1]
  apply (erule validE_weaken, simp+)[1]
  done

lemma L1_condition_lp: "
  \<lbrakk> \<lbrace>P1\<rbrace> A \<lbrace>Q1\<rbrace>,\<lbrace>E1\<rbrace>;
    \<lbrace>P2\<rbrace> B \<lbrace>Q2\<rbrace>,\<lbrace>E2\<rbrace>;
    \<And>s. P s \<Longrightarrow> P1 s;
    \<And>s. P s \<Longrightarrow> P2 s;
    \<And>s. Q1 () s \<Longrightarrow> Q () s;
    \<And>s. Q2 () s \<Longrightarrow> Q () s;
    \<And>s. E1 () s \<Longrightarrow> E () s;
    \<And>s. E2 () s \<Longrightarrow> E () s \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_condition c A B \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_condition_def)
  apply wp
    apply (erule validE_weaken, simp+)[1]
   apply (erule validE_weaken, simp+)[1]
  apply simp
  done

lemma L1_catch_lp: "
  \<lbrakk> \<lbrace>P1\<rbrace> A \<lbrace>Q1\<rbrace>,\<lbrace>E1\<rbrace>;
    \<lbrace>P2\<rbrace> B \<lbrace>Q2\<rbrace>,\<lbrace>E2\<rbrace>;
    \<And>s. P s \<Longrightarrow> P1 s;
    \<And>s. E1 () s \<Longrightarrow> P2 s;
    \<And>s. Q1 () s \<Longrightarrow> Q () s;
    \<And>s. Q2 () s \<Longrightarrow> Q () s;
    \<And>s. E2 () s \<Longrightarrow> E () s \<rbrakk> \<Longrightarrow>
  \<lbrace>P\<rbrace> L1_catch A B \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_catch_def)
  including no_pre
  apply wp
   apply (erule validE_weaken, simp+)[1]
  apply (erule validE_weaken, simp+)[1]
  done

lemma L1_init_lp: "\<lbrakk> \<And>s. P s \<Longrightarrow> \<forall>x. Q () (f (\<lambda>_. x) s) \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> L1_init f \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply wp
  apply clarsimp
  done

lemma L1_while_lp:
  assumes body_lp: "\<lbrace> P' \<rbrace> B \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>"
  and p_impl: "\<And>s. P s \<Longrightarrow> P' s"
  and q_impl: "\<And>s. Q' () s \<Longrightarrow> Q () s"
  and e_impl: "\<And>s. E' () s \<Longrightarrow> E () s"
  and inv: " \<And>s. Q' () s \<Longrightarrow> P' s"
  and inv': " \<And>s. P' s \<Longrightarrow> Q' () s"
  shows "\<lbrace> P \<rbrace> L1_while c B \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  apply (rule validE_weaken [where P'=P' and Q'=Q' and E'=E'])
     apply (clarsimp simp: L1_while_def)
     apply (rule validE_whileLoopE [where I="\<lambda>r s. P' s"])
      apply simp
      apply (rule validE_weaken [OF body_lp])
        apply (clarsimp simp: p_impl)
       apply (clarsimp simp: inv)
      apply simp
     apply (clarsimp simp: inv')
    apply (clarsimp simp: p_impl)
   apply (clarsimp simp: q_impl)
  apply (clarsimp simp: e_impl)
  done

lemma L1_recguard_lp:
  "\<lbrakk>\<lbrace>P1\<rbrace> A \<lbrace>Q1\<rbrace>, \<lbrace>E1\<rbrace>;
    \<And>s. P s \<Longrightarrow> P1 s;
    \<And>s. Q1 () s \<Longrightarrow> Q () s;
    \<And>s. E1 () s \<Longrightarrow> E () s\<rbrakk> \<Longrightarrow>
   \<lbrace>P\<rbrace> L1_recguard v A \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (clarsimp simp: L1_recguard_def)
  apply wp
   apply (erule validE_weaken)
     apply assumption
    apply simp
   apply simp
  apply simp
  done

end
