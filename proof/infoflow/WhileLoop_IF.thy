(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory WhileLoop_IF
imports
  EquivValid
  "../../lib/NonDetMonadLemmaBucket"
begin

lemma in_whileLoopD2:
  "\<lbrakk>(rt', t'') \<in> fst (whileLoop C B n t); C n t\<rbrakk> \<Longrightarrow>
    \<exists> rt t'. (rt,t') \<in> fst (B n t) \<and> (rt',t'') \<in> fst (whileLoop C B rt t')"
  apply(subst (asm) whileLoop_unroll)
  apply(simp add: condition_def)
  apply(fastforce simp: in_monad)
  done

lemma whileLoop_ev_helper:
  assumes terminate_together: "\<And> s t n. \<lbrakk>I s t; A s t; P n s; P n t\<rbrakk> \<Longrightarrow> (C n s) = (C n t)"
  assumes inv: "\<And> r. \<lbrace> P r and C r \<rbrace> B r \<lbrace> P \<rbrace>"
  assumes ev: "\<And> n. equiv_valid_inv I A (P n and C n) (B n)"
  shows
  "(rs, s') \<in> fst (whileLoop C
                          B
                         n s) \<Longrightarrow> P n s \<longrightarrow>
       (\<forall>t rt t'.
             P n t \<and> I s t \<and> A s t \<and> (rt, t') \<in> fst (whileLoop C
            B
           n t) \<longrightarrow>
             rs = rt \<and> I s' t' \<and> A s' t')"
  apply(erule whileLoop_induct)
   apply clarsimp
   apply(subgoal_tac "\<not> C r t")
    apply(clarsimp simp: whileLoop_unroll condition_def in_monad)
   apply(rule notI)
   apply(blast dest: terminate_together)
  apply clarsimp
  apply(subgoal_tac "C r t")
   apply(drule_tac t=t in in_whileLoopD2)
   apply assumption
   apply(clarify)
   apply(rename_tac rt' t'' rt t')
   apply(erule impE)
    apply(fastforce elim: use_valid[OF _ inv])
   apply(drule_tac x=t' in spec)
   apply(drule_tac x=rt' in spec)
   apply(drule_tac x=t'' in spec)
   apply(subgoal_tac "P rt t' \<and> rt = r' \<and> I s' t' \<and> A s' t'")
    apply(erule mp)
    apply fastforce
   apply(rule conjI)
    apply(fastforce intro: use_valid[OF _ inv])
   apply(insert ev)
   apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
   apply fastforce
  apply(blast dest: terminate_together)
  done

lemma whileLoop_ev:
  assumes terminate_together: "\<And> s t n. \<lbrakk>I s t; A s t; P n s; P n t\<rbrakk> \<Longrightarrow> (C n s) = (C n t)"
  assumes inv: "\<And> r. \<lbrace> P r and C r \<rbrace> B r \<lbrace> P \<rbrace>"
  assumes ev: "\<And> n. equiv_valid_inv I A (P n and C n) (B n)"
  shows
  "equiv_valid_inv I A (P n) (whileLoop C B n)"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply(rule_tac C=C in whileLoop_ev_helper[rule_format])
       apply(rule terminate_together, assumption+)
      apply(rule inv)
     apply(rule ev)
    apply assumption
   apply assumption
  apply blast
  done

record the_state = 
    h :: bool
    l :: int
    n :: int
    f1 :: int
    f2 :: int
    k :: int
    i :: int
    x :: int

definition L_equiv where
  "L_equiv s s' \<equiv> l s = l s'"

definition H_equiv where
  "H_equiv s s' \<equiv> h s = h s'"

definition H_c_equiv where
  "H_c_equiv s s' \<equiv> l s = l s' \<and> n s = n s' \<and> f1 s = f1 s' \<and> f2 s = f2 s' \<and> k s = k s' \<and> i s = i s' \<and> x s = x s'"

(* this is the program in Figure 4 from "Secure Information Flow as a Safety Problem",
   Terauchi & Aiken, SAS 2005. Automatic self-composition analysis (as a safety property) 
   can't figure out that this program is secure, because they effectively need to be able
   to infer the actual loop invariant to work out that both copies of the loop are doing
   the same thing. This happens because they can't "see" the structural similarity of
   both copies -- i.e. that they are identical. Our approach in higher order logic
   of course sees that they are identical and so the proof of security is trivial. *)
definition Prog :: "(the_state,unit) nondet_monad" where
  "Prog \<equiv> 
     do
        whileLoop (\<lambda> rv s. n s > 0) (\<lambda> rv. do
          f2 \<leftarrow> gets f2;
          modify (f1_update (\<lambda> f1. f1 + f2));
          f1 \<leftarrow> gets f1;
          modify (f2_update (\<lambda> f2. f1 - f2));
          modify (n_update (\<lambda> n. n - 1))
        od) ();
        f1 \<leftarrow> gets f1;
        k \<leftarrow> gets k;
        if (f1 > k) then modify (l_update (\<lambda>l. 1)) else modify (l_update (\<lambda>l. 0))
     od"

lemma modify_ev:
  "equiv_valid_inv I A (K (\<forall> s t. I s t \<and> A s t \<longrightarrow> I (f s) (f t) \<and> A (f s) (f t))) (modify f)"
  apply(rule equiv_valid_guard_imp)
   apply(simp add: equiv_valid_def2)
   apply(rule modify_ev2)
   prefer 2
   apply(unfold K_def, assumption)
  apply simp
  done



lemma Prog_ev:
  "equiv_valid_inv  L_equiv (H_c_equiv) \<top> Prog"
  apply(simp add: Prog_def)
  apply (wp modify_ev whileLoop_ev[where P="\<top>\<top>"] | clarsimp simp: L_equiv_def H_c_equiv_def)+
  done

(* This is Figure 9 from Terauchi & Aiken, SAS 2005. Neither standard type-based approaches
   or self-composition can see that this program is secure. The authors do some re-writing
   to bring out the fact that the update to x occurs whatever the value of h. We do
   something similar, although we do the rewriting manually. One could imagine writing
   a tactic to automate this though, assuming the tactic knows which actions read high
   state etc. *)
definition Prog2 :: "(the_state,unit) nondet_monad" where
  "Prog2 \<equiv> 
     do
        whileLoop (\<lambda> rv s. n s > 0) (\<lambda> rv. do
          f2 \<leftarrow> gets f2;
          modify (f1_update (\<lambda> f1. f1 + f2));
          f1 \<leftarrow> gets f1;
          modify (f2_update (\<lambda> f2. f1 - f2));
          modify (n_update (\<lambda> n. n - 1))
        od) ();
        h \<leftarrow> gets h;
        (if h then modify (x_update (\<lambda> x. 1)) else return ());
        (if \<not> h then modify (x_update (\<lambda> x. 1)) else return ());
        whileLoop (\<lambda> rv s. i s < f1 s) (\<lambda> rv. do
          x \<leftarrow> gets x;
          modify (l_update (\<lambda> l. l + x));
          modify (i_update (\<lambda> i. i + 1))
        od) ()
     od"

lemma equiv_valid_def2s:
  "equiv_valid_2 I A B (\<lambda> (a::unit) (b::unit). True) P P f f = equiv_valid I A B P f"
  apply(fastforce simp: equiv_valid_def2 equiv_valid_2_def)
  done

lemma Prog2_ev:
  "equiv_valid_inv  L_equiv (H_c_equiv) \<top> Prog2"
  apply(subst Prog2_def)
  apply(rule bind_ev_pre)
     apply(rule K_bind_ev)
     apply(subst equiv_valid_def2)
     apply(rule_tac W="\<top>\<top>" and Q="\<top>\<top>" in equiv_valid_rv_bind)
       apply(rule gets_evrv)
      apply (simp split: split_if add: equiv_valid_def2s)
      apply(wp whileLoop_ev[where P="\<top>\<top>"] modify_ev | clarsimp simp: L_equiv_def H_c_equiv_def)+
  done

record the_state2 =
  i :: int
  v :: int
  res :: int
  x :: int
  h :: int



(* This is the program from Figure 1(a) in "Verification Condition Generation for
   Conditional Information Flow", Amtoft & Banerjee, FMSE 2007. *)
definition Prog3 where
  "Prog3 \<equiv> do
     modify (i_update (\<lambda>i. 0));
     modify (v_update (\<lambda>i. 0));
     modify (res_update (\<lambda>i. 0));     
     whileLoop (\<lambda> rv s. i s < 7) (\<lambda>rv. do
       i \<leftarrow> gets i;
       (if odd(i) then
         do
           v \<leftarrow> gets v;
           modify (res_update (\<lambda>res. res + v));
           h \<leftarrow> gets h;
           modify (v_update (\<lambda>v. v + h))
         od
       else
         do
           x \<leftarrow> gets x;
           modify (v_update (\<lambda>v. x))
         od
       );
       modify (i_update (\<lambda>i. i + 1))
     od) ()
   od"

definition x_equiv where
  "x_equiv s s' \<equiv> x s = x s'"

definition i_equiv where
  "i_equiv s s' \<equiv> i s = i s'"

definition v_equiv where
  "v_equiv s s' \<equiv> v s = v s'"

definition res_equiv where
  "res_equiv s s' \<equiv> res s = res s'"

lemmas equivs = x_equiv_def i_equiv_def v_equiv_def res_equiv_def

lemma equiv_valid_rewrite_rels:
  "\<lbrakk>(\<And> s t. \<lbrakk>I' s t; A' s t\<rbrakk> \<Longrightarrow> I s t);
    (\<And> s t. \<lbrakk>I' s t; A' s t\<rbrakk> \<Longrightarrow> A s t);
    (\<And> s t. \<lbrakk>I s t; B s t\<rbrakk> \<Longrightarrow> I' s t);
    (\<And> s t. \<lbrakk>I s t; B s t\<rbrakk> \<Longrightarrow> B' s t)\<rbrakk> \<Longrightarrow>
   equiv_valid I A B P f \<Longrightarrow>
   equiv_valid I' A' B' P f"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply blast
  done

lemma modify_ev':
  "equiv_valid_inv I A (P and K (\<forall> s t. P s \<and> P t \<and> I s t \<and> A s t \<longrightarrow> I (f s) (f t) \<and> A (f s) (f t))) (modify f)"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad)
  done

(* Proving this is difficult in our calculus. This is because reasoning about this requires switching the equivalence relations that are being preserved at different
   points in the program. This is necessary for programs and proof/verification systems like these that focus on programs that (relatively often, compared to the size of the
   program) read High data but then don't release it. These systems can automtically adjust the equivalence relations over time because the program syntax precisely reveals
   what is being read etc. Ours cannot do so so easily because we have not much syntax to analyse due to the shallow embedding. We could craft rules for thhis particular program
   but not ones in general for every program without giving further information through e.g. annotations or such (either on the code or on the equivalence relations themselves
   through extra definitions or similar). Rather what our calculus is good at is adjusting the precondition as we go along. This is necessary for us because what data is Low at
   any point in time depends heavily on the state of the system -- e.g. a page is Low so long as the current thread has a Read cap to it (which we infer through 'pas_refined pas'
   with an appropriate Read edge in 'pas' from the current subject to the label of the page in question). Our calculus is good at reasoning about code that rarely reads High
   data (an example in seL4 is reading the state of async EPs for instance, and queued senders, where we need to resort to more complicate reasoning outside of the core
   equiv_valid calculus), but for which what is Low is heavily state-dependant, where reasoning requires tracking these kinds of preconditions as we go along.
   This kind of thing might be able to be done in a traditional self-compoisition verification framework, for instance, but not so far at the scale of seL4 AFAICT; and not with
   the kind of state-dependant definitions of what is Low and High etc. as we have in seL4. This is really where our approach sets itself apart from previous ones for this kind
   of thing. *)
lemma Prog3_ev:
  "equiv_valid x_equiv x_equiv res_equiv \<top> Prog3"
  apply(simp add: Prog3_def)
  apply(rule equiv_valid_guard_imp)
   apply(rule bind_ev_general[where B="x_equiv And i_equiv"])
     apply(rule bind_ev_general[where B="x_equiv And i_equiv And v_equiv"])
       apply(rule bind_ev_general[where B="x_equiv And i_equiv And v_equiv And res_equiv"])
         apply(rule_tac I="i_equiv And x_equiv And (\<lambda> s t. odd (i s) \<longrightarrow> v s = v t)" and A=res_equiv and B=res_equiv in equiv_valid_rewrite_rels)
             apply(fastforce simp: equivs)+
         apply(wp whileLoop_ev[where P="\<lambda> rv s. i s \<le> 7"])
           apply(fastforce simp: equivs)
          apply((wp | simp)+)[1]
         (* need to be careful how we decompose here, so we don't automatically try to
            prove equiv_valid for the gets h. *)
         apply(rule bind_ev_pre)
            apply(rule bind_ev_general[where B="x_equiv And i_equiv And (\<lambda> s t. even (i s) \<longrightarrow> v s = v t) And res_equiv" and Q="\<top>\<top>"])
              apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad equivs)
             apply(rule if_ev)
         oops         



end (* a comment *)
