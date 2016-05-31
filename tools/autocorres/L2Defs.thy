(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory L2Defs
imports CorresXF L1Defs L1Peephole MonadMono
begin

type_synonym ('s, 'a, 'e) L2_monad = "('s, 'e + 'a) nondet_monad"
definition "L2_unknown (name :: string list) \<equiv> liftE (select UNIV) :: ('s, 'a, 'e) L2_monad"
definition "L2_seq (A :: ('s, 'a, 'e) L2_monad) (B :: 'a \<Rightarrow> ('s, 'b, 'e) L2_monad) \<equiv> (A >>=E B) :: ('s, 'b, 'e) L2_monad"
definition "L2_modify m \<equiv> liftE (modify m) :: ('s, unit, 'e) L2_monad"
definition "L2_gets f (names :: string list) \<equiv> liftE (gets f) :: ('s, 'a, 'e) L2_monad"
definition "L2_condition c (A :: ('s, 'a, 'e) L2_monad) (B :: ('s, 'a, 'e) L2_monad) \<equiv> condition c A B"
definition "L2_catch (A :: ('s, 'a, 'e) L2_monad) (B :: 'e \<Rightarrow> ('s, 'a, 'ee) L2_monad) \<equiv> (A <handle2> B)"
definition "L2_while c (A :: 'a \<Rightarrow> ('s, 'a, 'e) L2_monad) i (name :: string list) \<equiv> whileLoopE c A i :: ('s, 'a, 'e) L2_monad"
definition "L2_throw x (name :: string list) \<equiv> throwError x :: ('s, 'a, 'e) L2_monad"
definition "L2_spec r \<equiv> liftE (spec r >>= (\<lambda>_. select UNIV)) :: ('s, 'a, 'e) L2_monad"
definition "L2_guard c \<equiv> (liftE (guard c)) :: ('s, unit, 'e) L2_monad"
definition "L2_fail \<equiv> fail :: ('s, 'a, 'e) L2_monad"
definition "L2_call x \<equiv> x <handle2> (\<lambda>_. fail) :: ('s, 'a, 'e) L2_monad"
definition "L2_recguard n b \<equiv> (condition (\<lambda>s. (n :: nat) = 0) fail b) :: ('s, 'a, 'e) L2_monad"

abbreviation "L2_skip \<equiv> L2_gets (\<lambda>_. ()) []"

(*
 * Temporary constructions, used internally but not emitted.
 *
 * "L2_folded_gets" is like "L2_gets", but the peephole optimiser will
 * try to eliminate the call to where it is used, eliminating it where
 * possible.  It is used for automatically generated "L2_gets" calls
 * which the user really doesn't need to know about.
 *
 * The various "call" defintions are to help generate proofs for the
 * different ways of making function calls, which are hard to unify.
 *)
definition "L2_folded_gets f names \<equiv> L2_gets f names :: ('s, 'a, 'e) L2_monad"

definition "L2_voidcall x \<equiv> L2_seq (L2_call x) (\<lambda>ret. L2_skip) :: ('s, unit, 'e) L2_monad"
definition "L2_modifycall x m \<equiv> L2_seq (L2_call x) (\<lambda>ret. L2_modify (m ret)) :: ('s, unit, 'e) L2_monad"
definition "L2_returncall x f \<equiv> L2_seq (L2_call x) (\<lambda>ret. L2_folded_gets (f ret) [''retval'']) :: ('s, 'a, 'e) L2_monad"

lemma L2_folded_gets_bind:
  "L2_seq (L2_folded_gets (\<lambda>_. x) name) f = f x"
  apply (rule ext)
  apply (monad_eq simp: L2_folded_gets_def L2_seq_def L2_gets_def)
  done

(* FIXME: we can merge these *)
lemmas L2_remove_scaffolding_1 =
  L2_folded_gets_bind [THEN eq_reflection]
  L2_returncall_def
  L2_modifycall_def
  L2_voidcall_def

lemmas L2_remove_scaffolding_2 =
  L2_remove_scaffolding_1
  L2_folded_gets_def

abbreviation (input) "L2_guarded_while G C B i n \<equiv> L2_seq (L2_guard (G i))
               (\<lambda>_. L2_while C (\<lambda>i. L2_seq (B i) (\<lambda>r. L2_seq (L2_guard (G r)) (\<lambda>_. L2_gets (\<lambda>_. r) n))) i n)"

lemmas L2_defs = L2_unknown_def L2_seq_def
    L2_modify_def L2_gets_def L2_condition_def L2_catch_def L2_while_def
    L2_throw_def L2_spec_def L2_guard_def L2_fail_def L2_folded_gets_def
    L2_voidcall_def L2_modifycall_def L2_returncall_def L2_recguard_def

(* Alternate definitions. *)
lemma L2_defs':
   "L2_unknown n \<equiv> unknownE"
   "L2_seq A' B' \<equiv> A' >>=E B'"
   "L2_modify m \<equiv> modifyE m"
   "L2_gets f n \<equiv> getsE f"
   "L2_condition c L R \<equiv> condition c L R"
   "L2_catch A B \<equiv> (A <handle2> B)"
   "L2_while c' B'' i n \<equiv> whileLoopE c' B'' i"
   "L2_throw x n \<equiv> throwError x"
   "L2_spec r \<equiv> (specE r >>=E (\<lambda>_. selectE UNIV))"
   "L2_guard c \<equiv> guardE c"
   "L2_fail \<equiv> fail"
  by (auto simp: monad_defs L2_defs bind_liftE_distrib)

definition
   L2corres :: "('s \<Rightarrow> 't) \<Rightarrow> ('s \<Rightarrow> 'r) \<Rightarrow> ('s \<Rightarrow> 'e) \<Rightarrow> ('s \<Rightarrow> bool)
       \<Rightarrow> ('t, 'e + 'r) nondet_monad \<Rightarrow> ('s, unit + unit) nondet_monad \<Rightarrow> bool"
where
  "L2corres st ret_xf ex_xf P A C
       \<equiv> corresXF st (\<lambda>_. ret_xf) (\<lambda>_. ex_xf) P A C"

(* Wrapper for calling un-translated functions. *)
definition
  "L2_call_L1 arg_xf gs ret_xf l1body
    = do cur_gs \<leftarrow> get;
        s \<leftarrow> select {s. gs s = cur_gs \<and> arg_xf s};
        (rv, s') \<leftarrow> select_f (l1body s);
        put (gs s');
        case rv of Inl _ \<Rightarrow> fail
            | Inr _ \<Rightarrow> return (Inr (ret_xf s') :: (unit + _))
    od"

lemma L2corres_L2_call_L1:
  "L2corres gs ret_xf ex_xf arg_xf
     (L2_call_L1 arg_xf gs ret_xf f) f"
  apply (clarsimp simp: L2corres_def corresXF_def L2_call_L1_def
                 split: sum.split)
  apply (clarsimp simp: snd_bind in_monad exec_get select_def)
  apply (clarsimp simp: select_f_def snd_bind put_def split: sum.split_asm)
  apply (fastforce simp: return_def)
  done

lemma L2corres_L2_call_simpl:
  "l1_f \<equiv> simpl_f \<Longrightarrow>
   L2corres gs ret_xf ex_xf arg_xf
     (L2_call_L1 arg_xf gs ret_xf simpl_f) l1_f"
  by (simp add: L2corres_L2_call_L1)

(* shouldn't be needed
lemma empty_set_exists: "(\<forall>a. a \<noteq> {}) = False"
  apply blast
  done
*)

lemma L2corres_modify_global:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> M (st s) = st (M' s) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_modify M) (L1_modify M')"
  apply (clarsimp simp: L2corres_def L2_defs L1_defs)
  apply (fold modifyE_def)
  apply (auto intro: corresXF_modify_global)
  done

lemma L2corres_modify_unknown:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_unknown name) (L1_modify M)"
  apply (clarsimp simp: L2corres_def L2_defs L1_defs)
  apply (fold selectE_def modifyE_def)
  apply (auto intro: corresXF_select_modify)
  done

lemma L2corres_spec_unknown:
  "\<lbrakk> \<And>s a. st s = st (M (a::('a \<Rightarrow> ('a::{type}))) s) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_unknown name) (L1_init M)"
  apply (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs)
  done

lemma L2corres_modify_gets:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> st s = st (M s); \<And>s. P s \<Longrightarrow> ret (M s) = f (st s) \<rbrakk> \<Longrightarrow>
         L2corres st ret ex P (L2_gets (\<lambda>s. f s) n) (L1_modify M)"
  apply (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs)
  done

lemma L2corres_gets_skip:
  "L2corres st ret ex P L2_skip L1_skip"
  by (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs)

lemma L2corres_guard:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> G' s =  G (st s) \<rbrakk> \<Longrightarrow> L2corres st return_xf exception_xf P (L2_guard G) (L1_guard G')"
  apply (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs)
  done

lemma L2corres_fail:
  "L2corres st return_xf exception_xf P L2_fail X"
  apply (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs)
  done

lemma spec_alt_def: "spec r = (\<lambda>s. (Pair () ` {s'. (s, s') \<in> r}, \<not> (\<exists>s'. (s, s') \<in> r)))"
  apply (clarsimp simp: spec_def)
  done

lemma L2corres_spec:
  "\<lbrakk> \<And>s s'. ((s, s') \<in> A') = ((st s, st s') \<in> A); surj st \<rbrakk>
    \<Longrightarrow>  L2corres st return_xf exception_xf P (L2_spec A) (L1_spec A')"
  apply (clarsimp simp: L2corres_def L2_defs L1_spec_def corresXF_def
                        liftE_def spec_alt_def return_def bind_def select_def)
  apply (clarsimp simp: image_def)
  apply (subst (asm) set_eq_UNIV)
  apply metis
  done

lemma L2corres_seq:
  "\<lbrakk> L2corres st return_xf exception_xf P A A';
     \<And>x. L2corres st return_xf' exception_xf (P' x) (B x) B';
     \<lbrace>R\<rbrace> A' \<lbrace>\<lambda>_ s. P' (return_xf s) s\<rbrace>, \<lbrace>\<lambda>_. \<top>\<rbrace>;
     \<And>s. R s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
     L2corres st return_xf' exception_xf R (L2_seq A B) (L1_seq A' B')"
  apply (unfold L2corres_def L2_seq_def L1_seq_def)
  apply (rule corresXF_guard_imp)
  apply (rule corresXF_join, assumption+)
  done

lemma L2corres_catch:
  "\<lbrakk> L2corres st V E P L L';
    \<And>x. L2corres st V E' (P' x) (R x) R';
    \<lbrace>Q\<rbrace> L' \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>_ s. P' (E s) s\<rbrace>; \<And>s. Q s \<Longrightarrow> P s \<rbrakk> \<Longrightarrow>
   L2corres st V E' Q (L2_catch L R) (L1_catch L' R')"
  apply (clarsimp simp: L2corres_def L2_catch_def L1_catch_def)
  apply (unfold handleE_def)
  apply (erule corresXF_except)
    apply assumption
   apply assumption
  apply simp
  done

lemma L2corres_throw:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> E s = A \<rbrakk> \<Longrightarrow> L2corres st V E P (L2_throw A n) (L1_throw)"
  apply (clarsimp simp: L2corres_def L2_throw_def L1_throw_def)
  apply (clarsimp simp: throwError_def return_def)
  apply (clarsimp simp: corresXF_def)
  done

lemma L2corres_cond:
  "\<lbrakk> L2corres st return_xf exception_xf P A A';
     L2corres st return_xf exception_xf P' B B';
     \<And>s. R s \<Longrightarrow> P s;
     \<And>s. R s \<Longrightarrow> P' s;
     \<And>s. R s \<Longrightarrow> c' s = c (st s) \<rbrakk> \<Longrightarrow>
     L2corres st return_xf exception_xf R (L2_condition c A B) (L1_condition c' A' B')"
  apply (unfold L2corres_def L2_condition_def L1_condition_def)
  apply (rule corresXF_cond)
    apply (erule corresXF_guard_imp, fastforce)
   apply (erule corresXF_guard_imp, fastforce)
  apply (clarsimp)
  done

lemma L2corres_inject_return:
  "\<lbrakk> L2corres st V E P L R; \<lbrace>P'\<rbrace> R \<lbrace>\<lambda>_ s. W (V s) = V' s\<rbrace>, \<lbrace> \<lambda>_. \<top> \<rbrace>; \<And>s. P' s \<Longrightarrow> P s\<rbrakk> \<Longrightarrow>
     L2corres st V' E P' (L2_seq L (\<lambda>x. L2_gets (\<lambda>_. W x) n)) R"
  apply (clarsimp simp: L2corres_def)
  apply (drule corresXF_guard_imp [where P=P'], simp)
  apply (unfold L2_seq_def L2_gets_def)
  apply (fold getsE_def)
  apply (rule corresXF_guard_imp)
  apply (erule corresXF_append_gets_abs)
  apply (erule hoare_weaken_preE)
   apply simp
  apply simp
  done

lemma L2corres_skip:
  "L2corres st return_xf exception_xf P L2_skip L1_skip"
  apply (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs)
  done

lemma L2corres_while:
  assumes body_corres: "\<And>x. L2corres st ret ex (P' x) (A x) B"
  and inv_holds: "\<lbrace>\<lambda>s. P (ret s) s \<rbrace> B \<lbrace>\<lambda>_ s. P (ret s) s \<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>"
  and cond_match: "\<And>s. P (ret s) s \<Longrightarrow> c' s = c (ret s) (st s)"
  and pred_imply: "\<And>s x. P x s \<Longrightarrow>  P' x s"
  and pred_extract: "\<And>s. P x s \<Longrightarrow>  ret s = x"
  and pred_imply2: "\<And>s. Q x s \<Longrightarrow>  P x s"
  shows "L2corres st ret ex (Q x) (L2_while c A x n) (L1_while c' B)"
  apply (clarsimp simp: L2corres_def L2_while_def L1_while_def)
  apply (rule corresXF_guard_imp)
  apply (rule corresXF_while [
         where P="\<lambda>r s. P (ret s) s" and C'=c and C="\<lambda>_. c'" and A=A and B="\<lambda>_. B"
         and ret="\<lambda>r s. ret s" and ex="\<lambda>r s. ex s" and st=st and y=x and x="()" and P'="\<lambda>r s. Q x s"])
       apply (rule corresXF_guard_imp)
        apply (rule body_corres [unfolded L2corres_def])
       apply (clarsimp simp: pred_imply)
      apply (clarsimp simp: cond_match)
     apply (rule validE_weaken [OF inv_holds], (clarsimp simp: pred_imply2)+)[1]
    apply (metis pred_extract pred_imply2)
   apply (metis pred_extract pred_imply2)
  apply simp
  done

lemma corresXF_E:
  fixes st :: "'state \<Rightarrow> 'state2"
   shows "\<lbrakk> corresXF st ret_xf ex_xf P A C; P s;
       \<lbrakk> \<not> snd (A (st s)); \<not> snd (C s) \<rbrakk> \<Longrightarrow> (r, t) \<in> fst (C s);
       \<lbrakk> \<not> snd (A (st s)); \<not> snd (C s);
              \<exists>x. r = Inl x \<and> (Inl (ex_xf x t), st t) \<in> fst (A (st s)) \<rbrakk> \<Longrightarrow> R;
       \<lbrakk> \<not> snd (A (st s)); \<not> snd (C s);
              \<exists>x. r = Inr x \<and> (Inr (ret_xf x t), st t) \<in> fst (A (st s)) \<rbrakk> \<Longrightarrow> R;
       \<lbrakk> snd (A (st s)) \<rbrakk> \<Longrightarrow> R
     \<rbrakk> \<Longrightarrow> R"
  apply atomize_elim
  apply (unfold corresXF_def)
  apply clarsimp
  apply (erule allE, erule impE, fastforce)
  apply clarsimp
  apply (erule (1) my_BallE)
  apply (clarsimp split: sum.splits)
  done

declare Ball_def [monad_eq]
declare Bex_def [monad_eq]

lemma corresXF_measure_call:
  "\<lbrakk> monad_mono C; \<And>m. corresXF st rx ex P (A m) (C m) \<rbrakk>
   \<Longrightarrow> corresXF st rx ex P (measure_call A) (measure_call C)"
  apply (unfold measure_call_def corresXF_def)
  apply (clarsimp split: prod.splits sum.splits)
  apply (fastforce dest: monad_mono_incl)
  done

lemma L2corres_returncall:
  "\<lbrakk> monad_mono dest_fn;
     \<And>m. L2corres st ret' ex' P' (Z m) (dest_fn m);
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>t s. st (return_xf t (scope_teardown s t)) = st t;
     \<And>s. st (scope_setup s) = st s;
     \<And>t s. P s \<Longrightarrow> ret (return_xf t (scope_teardown s t)) = F (ret' t) (st t) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_returncall (measure_call Z) F) (L1_call scope_setup (measure_call dest_fn) scope_teardown return_xf)"
  unfolding L1_call_def L2_returncall_def L2_call_def L2corres_def L2_defs
  apply (drule_tac A = Z and C = dest_fn in corresXF_measure_call, assumption)
  apply (rule corresXF_I)
    apply monad_eq
    apply (erule allE)
    apply (erule_tac s="scope_setup s'" in corresXF_E)
        apply simp
       apply blast
      apply clarsimp
     apply clarsimp
     apply blast
    apply clarsimp
   apply monad_eq
  apply monad_eq
  apply (rule conjI)
   apply (metis (lifting, mono_tags) corresXF_exec_fail)
  apply (metis (lifting, mono_tags) corresXF_exec_except sum.distinct(2))
  done

lemma L2corres_recursive_returncall:
  "\<lbrakk> L2corres st ret' ex' P' (Z m) (dest_fn m);
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>t s. st (return_xf t (scope_teardown s t)) = st t;
     \<And>s. st (scope_setup s) = st s;
     \<And>t s. P s \<Longrightarrow> ret (return_xf t (scope_teardown s t)) = F (ret' t) (st t) \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_returncall (Z m) F)
                          (L1_call scope_setup (dest_fn m) scope_teardown return_xf)"
  apply atomize
  unfolding L1_call_def L2_returncall_def L2_call_def L2_defs L2corres_def
  apply (rule corresXF_I)
    apply monad_eq
    apply (erule_tac s="scope_setup s'" in corresXF_E)
        apply simp
       apply assumption
      apply simp
     apply monad_eq
     apply blast
    apply simp
   apply monad_eq
  apply monad_eq
  apply (rule conjI)
   apply (simp add: corresXF_def)
  apply clarsimp
  apply (drule (1) corresXF_exec_except)
    apply force
   apply clarsimp
  apply clarsimp
  apply force
  done

lemma handleE_fail:
    "(A <handle> (\<lambda>_. fail)) = (liftE (A <catch> (\<lambda>_. fail)))"
  apply (monad_eq)
  apply force
  done

lemma handleE'_fail:
    "(A <handle2> (\<lambda>_. fail)) = (liftE (A <catch> (\<lambda>_. fail)))"
  apply (monad_eq)
  apply force
  done

lemma L2corres_modifycall:
  "\<lbrakk> monad_mono dest_fn;
     \<And>m. L2corres st ret' ex' P' (Z m) (dest_fn m);
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. P r \<Longrightarrow> F (ret' s) (st s) = st (return_xf s (scope_teardown r s));
     \<And>s. st (scope_setup s) = st s \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_modifycall (measure_call Z) F)
                          (L1_call scope_setup (measure_call dest_fn) scope_teardown return_xf)"
  apply (clarsimp simp: L1_call_def L2_call_def L2_defs L2corres_def)
  apply (clarsimp simp: liftE_bindE_handle liftE_bindE handleE'_fail handleE_fail)
  apply (drule_tac A = Z and C = dest_fn in corresXF_measure_call, assumption)
  apply (rule corresXF_I)
    apply monad_eq
    apply (erule allE)
    apply (drule (1) corresXF_exec_normal)
      apply clarsimp
     apply clarsimp
    apply clarsimp
    apply metis
   apply monad_eq
  apply monad_eq
  apply (rule conjI)
   apply (fastforce dest!: corresXF_exec_fail)
  apply (fastforce dest!: corresXF_exec_except)
  done

lemma L2corres_recursive_modifycall:
  "\<lbrakk> L2corres st ret' ex' P' (Z m) (dest_fn (m :: nat));
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. P r \<Longrightarrow> F (ret' s) (st s) = st (return_xf s (scope_teardown r s));
     \<And>s. st (scope_setup s) = st s \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_modifycall (Z m) F)
                          (L1_call scope_setup (dest_fn m) scope_teardown return_xf)"
  apply atomize
  apply (clarsimp simp: L1_call_def L2_call_def L2_defs L2corres_def)
  apply (clarsimp simp: liftE_bindE_handle liftE_bindE handleE'_fail handleE_fail)
  apply (rule corresXF_I)
    apply monad_eq
    apply (erule_tac s="scope_setup s'" in corresXF_E)
        apply simp
       apply assumption
      apply simp
     apply metis
    apply simp
   apply monad_eq
  apply monad_eq
  apply (rule conjI)
   apply (simp add: corresXF_def)
  apply (fastforce dest!: corresXF_exec_except)
  done

lemma L2corres_voidcall:
  "\<lbrakk> monad_mono dest_fn;
     \<And>m. L2corres st ret' ex' P' (Z m) (dest_fn m);
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. st (return_xf s (scope_teardown r s)) = st s;
     \<And>s. st (scope_setup s) = st s  \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_voidcall (measure_call Z))
         (L1_call scope_setup (measure_call dest_fn) scope_teardown return_xf)"
  apply (unfold L2_voidcall_def)
  apply (frule corresXF_measure_call)
   apply (subst (asm) L2corres_def, assumption)
  apply (rule_tac t = "L2_skip" and s = "L2_modify (\<lambda>s. s)" in subst)
   apply (monad_eq simp: L2_defs)
  apply (fold L2_modifycall_def L2corres_def)
  apply (fastforce elim!: L2corres_modifycall)
  done

lemma L2corres_recursive_voidcall:
  "\<lbrakk> L2corres st ret' ex' P' (Z m) (dest_fn m);
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. st (return_xf s (scope_teardown r s)) = st s;
     \<And>s. st (scope_setup s) = st s  \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_voidcall (Z m))
                          (L1_call scope_setup (dest_fn m) scope_teardown return_xf)"
  apply (unfold L2_voidcall_def)
  apply (subgoal_tac "L2_skip = L2_modify (\<lambda>s. s)")
   apply (erule ssubst)
   apply (fold L2_modifycall_def)
   apply (erule L2corres_recursive_modifycall, simp_all)[1]
  apply (monad_eq simp: L2_defs)
  done

lemma L2corres_call:
  "\<lbrakk> monad_mono dest_fn;
     \<And>m. L2corres st ret' ex' P' (Z m) (dest_fn m);
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. st (return_xf s (scope_teardown r s)) = st s;
     \<And>s r. ret (return_xf s (scope_teardown r s)) = ret' s;
     \<And>s. st (scope_setup s) = st s \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_call (measure_call Z))
                          (L1_call scope_setup (measure_call dest_fn) scope_teardown return_xf)"
  apply (clarsimp simp: L2corres_def L2_call_def L1_call_def L2_defs)
  apply (drule corresXF_measure_call, assumption)
  apply (clarsimp simp: liftE_bindE_handle liftE_bindE handleE'_fail handleE_fail)
  apply (rule corresXF_I)
    apply monad_eq
    apply (fastforce dest!: corresXF_exec_normal)
   apply monad_eq
  apply monad_eq
  apply (rule conjI)
   apply (fastforce dest!: corresXF_exec_fail)
  apply (fastforce dest!: corresXF_exec_except)
  done

lemma L2corres_recursive_call:
  "\<lbrakk> L2corres st ret' ex' P' (Z m) (dest_fn m);
     \<And>s. P s \<Longrightarrow> P' (scope_setup s);
     \<And>s r. st (return_xf s (scope_teardown r s)) = st s;
     \<And>s r. ret (return_xf s (scope_teardown r s)) = ret' s;
     \<And>s. st (scope_setup s) = st s \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_call (Z m)) (L1_call scope_setup (dest_fn m) scope_teardown return_xf)"
  apply (clarsimp simp: L2corres_def L2_call_def L1_call_def L2_defs)
  apply (clarsimp simp: liftE_bindE_handle liftE_bindE handleE'_fail handleE_fail)
  apply (rule corresXF_I)
    apply monad_eq
    apply (fastforce dest!: corresXF_exec_normal)
   apply monad_eq
  apply monad_eq
  apply (rule conjI)
   apply (fastforce dest!: corresXF_exec_fail)
  apply (fastforce dest!: corresXF_exec_except)
  done

lemma L2corres_recguard:
  "\<lbrakk> L2corres st ret ex P' B B';
     \<And>s. P s \<Longrightarrow>  P' s \<rbrakk> \<Longrightarrow>
   L2corres st ret ex P (L2_recguard x B) (L1_recguard x B')"
  apply (clarsimp simp: L2_recguard_def L1_defs)
  apply (rule L2corres_cond [unfolded L2_condition_def L1_condition_def])
      apply (rule L2corres_fail [unfolded L2_fail_def L1_fail_def])
     apply assumption
    apply assumption
   apply simp
  apply simp
  done

lemma L2_gets_bind: "\<lbrakk> \<And>s s'. V s = V s' \<rbrakk> \<Longrightarrow> L2_seq (L2_gets V n) f = f (V undefined)"
  apply (rule ext)
  apply (clarsimp simp: L2_seq_def L2_gets_def gets_def get_def return_def bindE_def)
  apply (clarsimp simp: liftE_def2 bind_def lift_def)
  apply atomize
  apply (erule_tac x=x and y=undefined in allE2)
  apply simp
  done

(* TODO: remove internal var if it is not user-visible *)
lemma L2corres_folded_gets:
  "\<lbrakk> \<And>a. L2corres st ret ex (P and (\<lambda>s. a = c (st s))) (X a) Y \<rbrakk> \<Longrightarrow>
     L2corres st ret ex P (L2_seq (L2_folded_gets c name) X) Y"
  apply atomize
  apply (clarsimp simp: L2_seq_def L2_folded_gets_def L2_gets_def bindE_def bind_def gets_def liftE_def return_def)
  apply (clarsimp simp: split_def image_def lift_def get_def pred_conj_def)
  apply (clarsimp simp: L2corres_def corresXF_def)
  done

lemma L2corres_guard_imp:
  "\<lbrakk> L2corres st ret_state ex_state Q M M'; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> L2corres st ret_state ex_state P M M'"
  apply (monad_eq simp: L2corres_def corresXF_def L1_defs L2_defs)
  done

lemma L2_recguard_cong [fundef_cong, cong]:
  "\<lbrakk> n = n'; n \<noteq> 0 \<Longrightarrow> b = b' \<rbrakk> \<Longrightarrow> L2_recguard n b = L2_recguard n' b'"
  apply (clarsimp simp: L2_recguard_def)
  done

lemma L2_call_cong [fundef_cong, cong]:
  "f = f' \<Longrightarrow> L2_call f = L2_call f'"
  by simp

lemma L2corres_recguard_0:
  "L2corres sr ret ex P (L2_recguard 0 X) Y"
  apply (clarsimp simp: L2_recguard_def)
  apply (rule L2corres_fail [unfolded L2_fail_def])
  done

lemma L2_call_liftE [simp]:
  "L2_call (liftE x) \<equiv> liftE x"
  by (monad_eq simp: L2_defs L2_call_def liftE_left liftE_liftE)

lemma L2_recguard_0 [simp]: "L2_recguard 0 x = fail"
  apply (clarsimp simp: L2_recguard_def)
  done

lemma L2_call_fail [simp]: "L2_call fail = fail"
  apply (monad_eq simp: L2_call_def)
  done

lemma L2_call_L2_gets [simp]: "L2_call (L2_gets x n) = L2_gets x n"
  apply (monad_eq simp: L2_call_def L2_gets_def)
  done

(*
 * Rules for adjusting case_prod statements after transformations.
 *
 * c.f. fix_L2_while_loop_splits_conv
 *)
lemma L2_split_fixup_1:
  "(L2_seq A (\<lambda>x. case y of (a, b) \<Rightarrow> B a b x)) =
           (case y of (a, b) \<Rightarrow> L2_seq A (\<lambda>x. B a b x))"
       by (auto simp: split_def)
lemma L2_split_fixup_2:
  "(L2_seq (case y of (a, b) \<Rightarrow> B a b) A) =
           (case y of (a, b) \<Rightarrow> L2_seq (B a b) A)"
       by (auto simp: split_def)
lemma L2_split_fixup_3:
  "(case (x, y) of (a, b) \<Rightarrow> P a b) = P x y"
       by (auto simp: split_def)
lemma L2_split_fixup_4:
  "case_prod (\<lambda>a (b :: 'a \<times> 'b). P a ) = case_prod (\<lambda>a. case_prod (\<lambda>(x :: 'a) (y :: 'b). P a ))"
       by (auto simp: split_def)
lemma L2_split_fixup_f:
  "(f (case y of (a, b) \<Rightarrow> G a b) =
           (case y of (a, b) \<Rightarrow> f (G a b)))"
       by (auto simp: split_def)
lemma L2_split_fixup_g:
  "case_prod (\<lambda>a (b :: 'a \<times> 'b). P a b) = case_prod (\<lambda>a. case_prod (\<lambda>(x :: 'a) (y :: 'b). P a (x, y)))"
       by (auto simp: split_def)

lemmas L2_split_fixups =
  L2_split_fixup_1
  L2_split_fixup_2
  L2_split_fixup_3
  L2_split_fixup_4

  L2_split_fixup_f [where f=L2_guard]
  L2_split_fixup_f [where f=L2_gets]
  L2_split_fixup_f [where f=L2_modify]

  L2_split_fixup_g [where P="\<lambda>a b. L2_gets (P a b) n" for P n]
  L2_split_fixup_g [where P="\<lambda>a b. L2_guard (P a b)" for P]
  L2_split_fixup_g [where P="\<lambda>a b. L2_modify (P a b)" for P]
  L2_split_fixup_g [where P="\<lambda>a b. L2_spec (P a b)" for P]
  L2_split_fixup_g [where P="\<lambda>a b. L2_throw (P a b) n" for P n]

  L2_split_fixup_g [where P="\<lambda>a b. L2_seq (L a b) (R a b)" for L R]
  L2_split_fixup_g [where P="\<lambda>a b. L2_while (C a b) (B a b) (I a b) n" for C B I n]
  L2_split_fixup_g [where P="\<lambda>a b. L2_unknown n" for n]
  L2_split_fixup_g [where P="\<lambda>a b. L2_catch (L a b) (R a b)" for L R]
  L2_split_fixup_g [where P="\<lambda>a b. L2_condition (C a b) (L a b) (R a b)" for C L R]
  L2_split_fixup_g [where P="\<lambda>a b. L2_call (M a b)" for M]

lemmas L2_split_fixups_congs =
  prod.case_cong

(* Peephole simplification rules for L2 programs (including HeapLift and WordAbstract). *)
named_theorems L2opt

(* L2 monad_mono rules *)
lemma L2_seq_monad_mono_step:
  "\<lbrakk> monad_mono_step f m; \<And>x. monad_mono_step (\<lambda>m. g m x) m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. L2_seq (f m) (g m)) m"
  by (simp add: L2_seq_def monad_mono_step_bindE)

lemma L2_condition_monad_mono_step:
  "\<lbrakk> monad_mono_step f m; monad_mono_step g m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. L2_condition C (f m) (g m)) m"
  by (simp add: L2_condition_def monad_mono_step_condition)

lemma L2_catch_monad_mono_step:
  "\<lbrakk> monad_mono_step f m; \<And>x. monad_mono_step (\<lambda>m. g m x) m \<rbrakk>
   \<Longrightarrow> monad_mono_step (\<lambda>m. L2_catch (f m) (g m)) m"
  by (simp add: L2_catch_def monad_mono_step_handleE')

lemma L2_while_monad_mono_step:
  "(\<And>x. monad_mono_step (\<lambda>m. B m x) m) \<Longrightarrow> monad_mono_step (\<lambda>m. L2_while C (B m) i n) m"
  by (simp add: L2_while_def monad_mono_step_whileLoopE)

lemma L2_recguard_monad_mono_step:
  "monad_mono_step f m \<Longrightarrow> monad_mono_step (\<lambda>m. L2_recguard m (f m)) m"
  by (simp add: L2_recguard_def monad_mono_step_def condition_def fail_def)

lemma L2_reccall_monad_mono_step:
  "monad_mono_step f m \<Longrightarrow> monad_mono_step (\<lambda>m. L2_call (f m)) m"
  apply (simp add: L2_call_def)
  apply (force intro: monad_mono_step_bindE monad_mono_step_const monad_mono_step_handleE')
  done

lemmas L2_monad_mono_step_rules =
  monad_mono_step_const
  L2_while_monad_mono_step
  L2_recguard_monad_mono_step
  L2_catch_monad_mono_step
  L2_seq_monad_mono_step
  L2_condition_monad_mono_step
  L2_reccall_monad_mono_step
  monad_mono_step_recguard_dec_Suc

(* Base case *)
lemma monad_mono_step_L2_recguard_0:
  "monad_mono_step (\<lambda>m. L2_recguard m (x m)) 0"
  by (monad_eq simp: monad_mono_step_def L2_recguard_def)

end
