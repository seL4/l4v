(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ExceptionRewrite
imports L1Defs L1Peephole
begin

(* The given block of code always fails. *)
definition "always_fail P A \<equiv> \<forall>s. P s \<longrightarrow> (A s = ({}, True))"

lemma always_fail_fail [simp]: "always_fail P fail"
  by (clarsimp simp: always_fail_def fail_def)

lemma bindE_alwaysfail_lhs: "\<lbrakk> always_fail \<top> L \<rbrakk> \<Longrightarrow> always_fail \<top> (L >>=E R)"
  apply (clarsimp simp: always_fail_def bindE_def bind_def throwError_def)
  done

lemma bindE_alwaysfail_rhs: "\<lbrakk> empty_fail L; no_throw \<top> L; \<And>x. always_fail \<top> (R x) \<rbrakk> \<Longrightarrow> always_fail \<top> (L >>=E R)"
  apply atomize
  apply (clarsimp simp: always_fail_def no_throw_def)
  apply (clarsimp simp: bindE_def lift_def bind_def split_def)
  apply (clarsimp simp: empty_fail_def validE_def valid_def)
  apply (erule_tac x=s in allE)+
  apply (clarsimp simp: throwError_def return_def split_def split: sum.splits)
  apply (clarsimp simp: ex_in_conv [symmetric])
  done

lemma handleE'_alwaysfail_lhs: "\<lbrakk> always_fail \<top> L \<rbrakk> \<Longrightarrow> always_fail \<top> (L <handle2> R)"
  apply (clarsimp simp: handleE'_def always_fail_def bind_def)
  done

lemma handleE'_alwaysfail_rhs: "\<lbrakk> empty_fail L; no_return \<top> L; \<And>r. always_fail \<top> (R r) \<rbrakk> \<Longrightarrow> always_fail \<top> (L <handle2> R)"
  apply atomize
  apply (clarsimp simp: always_fail_def no_return_def)
  apply (clarsimp simp: handleE'_def lift_def bind_def split_def)
  apply (clarsimp simp: empty_fail_def validE_def valid_def)
  apply (erule_tac x=s in allE)+
  apply (clarsimp simp: throwError_def return_def split_def image_constant split: sum.splits)
  apply (clarsimp simp: ex_in_conv [symmetric])
  done

lemma handleE_alwaysfail_lhs: "\<lbrakk> always_fail \<top> L \<rbrakk> \<Longrightarrow> always_fail \<top> (L <handle> R)"
  apply (unfold handleE_def)
  apply (rule handleE'_alwaysfail_lhs, auto)
  done

lemma handleE_alwaysfail_rhs: "\<lbrakk> empty_fail L; no_return \<top> L; \<And>r. always_fail \<top> (R r) \<rbrakk> \<Longrightarrow> always_fail \<top> (L <handle> R)"
  apply (unfold handleE_def)
  apply (rule handleE'_alwaysfail_rhs, auto)
  done

lemma alwaysfail_noreturn: "always_fail P A \<Longrightarrow> no_return P A"
  by (clarsimp simp: always_fail_def no_return_def validE_def valid_def split: sum.splits)

lemma alwaysfail_nothrow: "always_fail P A \<Longrightarrow> no_throw P A"
  by (clarsimp simp: always_fail_def no_throw_def validE_def valid_def split: sum.splits)

lemma empty_fail_handleE: "\<lbrakk> empty_fail L; \<And>r. empty_fail (R r) \<rbrakk> \<Longrightarrow> empty_fail (L <handle> R)"
  apply (clarsimp simp: handleE_def handleE'_def)
  apply (erule empty_fail_bind)
  apply (clarsimp simp: empty_fail_error_bits split: sum.splits)
  done

lemma no_return_bindE:
  "no_return (\<lambda>_. True) A \<Longrightarrow> (A >>=E B) = A"
  apply (rule ext)+
  apply (rule prod_eqI)
   apply (rule set_eqI)
   apply (clarsimp simp: in_bindE no_return_def validE_def valid_def)
   apply (erule_tac x=x in allE)
   apply (rule iffI)
    apply (erule disjE)
     apply clarsimp
    apply clarsimp
    apply (erule (1) my_BallE)
    apply clarsimp
   apply clarsimp
   apply (erule (1) my_BallE)
   apply (clarsimp split: sum.splits)
  apply (clarsimp simp: snd_bindE no_return_def validE_def valid_def)
  apply (erule_tac x=x in allE)
  apply force
  done

(*
 * "empty_fail" lemmas
 *)

lemma L1_skip_empty_fail [simp,L1except]: "empty_fail L1_skip"
  by (clarsimp simp: empty_fail_def L1_defs returnOk_def return_def)

lemma L1_modify_empty_fail [simp,L1except]: "empty_fail (L1_modify m)"
  by (clarsimp simp: empty_fail_def L1_defs simpler_modify_def liftE_def2)

lemma L1_guard_empty_fail [simp,L1except]: "empty_fail (L1_guard g)"
  by (metis L1_guard_def empty_fail_exception(3) guardE_def)

lemma L1_init_empty_fail [simp,L1except]: "empty_fail (L1_init v)"
  apply (clarsimp simp: empty_fail_def L1_defs returnOk_def return_def simpler_modify_def select_def)
  apply (clarsimp simp: bind_liftE_distrib [symmetric])
  apply (clarsimp simp: bind_def liftE_def return_def)
  done

lemma L1_call_empty_fail: "\<lbrakk> empty_fail b \<rbrakk> \<Longrightarrow> empty_fail (L1_call a b c d)"
  by (auto intro!: empty_fail_bindE empty_fail_handleE simp: L1_call_def empty_fail_error_bits empty_fail_get)

lemma L1_spec_empty_fail [simp,L1except]: "empty_fail (L1_spec s)"
  by (clarsimp simp: empty_fail_def L1_defs returnOk_def return_def liftE_def2 spec_def)

lemma L1_throw_empty_fail [simp,L1except]: "empty_fail L1_throw"
  by (clarsimp simp: empty_fail_def L1_defs returnOk_def return_def throwError_def)

lemma L1_fail_empty_fail [simp,L1except]: "empty_fail L1_fail"
  by (clarsimp simp: empty_fail_def L1_defs returnOk_def return_def fail_def)

lemma L1_condition_empty_fail: "\<lbrakk> empty_fail L; empty_fail R \<rbrakk> \<Longrightarrow> empty_fail (L1_condition C L R)"
  by (clarsimp simp: empty_fail_def L1_defs returnOk_def return_def split: condition_splits)

lemma L1_seq_empty_fail: "\<lbrakk> empty_fail L; empty_fail R \<rbrakk> \<Longrightarrow> empty_fail (L1_seq L R)"
  apply (clarsimp simp: L1_defs)
  apply (erule (1) empty_fail_bindE)
  done

lemma L1_catch_empty_fail: "\<lbrakk> empty_fail L; empty_fail R \<rbrakk> \<Longrightarrow> empty_fail (L1_catch L R)"
  apply (clarsimp simp: L1_defs)
  apply (erule (1) empty_fail_handleE)
  done

lemma L1_while_empty_fail: "empty_fail B \<Longrightarrow> empty_fail (L1_while C B)"
  apply (clarsimp simp: L1_while_def)
  apply (rule empty_fail_whileLoopE)
  apply simp
  done

(*
 * no_throw lemmas.
 *)

lemma L1_skip_nothrow [simp,L1except]: "no_throw \<top> L1_skip"
  by (clarsimp simp: L1_defs)

lemma L1_modify_nothrow [simp,L1except]: "no_throw \<top> (L1_modify m)"
  by (clarsimp simp: L1_defs)

lemma L1_guard_nothrow [simp,L1except]: "no_throw \<top> (L1_guard g)"
  by (clarsimp simp: L1_defs)

lemma L1_call_nothrow [simp,L1except]: "no_throw \<top> (L1_call x y z q)"
  apply (clarsimp simp: L1_call_def L1_defs)
  apply (subst no_throw_bindE_simple | simp add: no_throw_handleE_simple)+
  done

lemma L1_init_nothrow [simp,L1except]: "no_throw \<top> (L1_init a)"
  by (rule no_throw_L1_init)

lemma L1_spec_nothrow [simp,L1except]: "no_throw \<top> (L1_spec a)"
  by (clarsimp simp: L1_defs)

lemma L1_fail_nothrow [simp,L1except]: "no_throw \<top> L1_fail"
  by (clarsimp simp: L1_defs)

lemma L1_while_nothrow: "no_throw \<top> B \<Longrightarrow> no_throw \<top> (L1_while C B)"
  apply (clarsimp simp: L1_while_def)
  apply (clarsimp simp: no_throw_def)
  apply (rule validE_whileLoopE [where I="\<lambda>_ _. True"])
    apply simp
   apply (erule validE_weaken, simp+)
  done

lemma L1_catch_nothrow_lhs: "\<lbrakk> no_throw \<top> L \<rbrakk> \<Longrightarrow> no_throw \<top> (L1_catch L R)"
  apply (clarsimp simp: L1_defs no_return_def no_throw_def)
  apply (erule handleE_wp [rotated])
  apply simp
  done

lemma L1_catch_nothrow_rhs: "\<lbrakk> no_throw \<top> R \<rbrakk> \<Longrightarrow> no_throw \<top> (L1_catch L R)"
  apply (clarsimp simp: L1_defs no_return_def no_throw_def)
  apply (rule handleE_wp, assumption)
  apply (rule hoareE_TrueI)
  done

lemma L1_seq_nothrow: "\<lbrakk> no_throw \<top> L; no_throw \<top> R \<rbrakk> \<Longrightarrow> no_throw \<top> (L1_seq L R)"
  apply (clarsimp simp: L1_defs)
  apply (erule (1) no_throw_bindE_simple)
  done

lemma L1_condition_nothrow: "\<lbrakk> no_throw \<top> L; no_throw \<top> R \<rbrakk> \<Longrightarrow> no_throw \<top> (L1_condition C L R)"
  apply (clarsimp simp: L1_condition_def condition_def)
  apply (clarsimp simp: no_throw_def)
  apply (clarsimp simp: valid_def validE_def)
  done

(*
 * no_return lemmas
 *)

lemma L1_throw_noreturn [simp,L1except]: "no_return \<top> L1_throw"
  apply (clarsimp simp: L1_defs no_return_def)
  apply wp
  done

lemma L1_fail_noreturn [simp,L1except]: "no_return \<top> L1_fail"
  apply (clarsimp simp: L1_defs no_return_def)
  done

lemma L1_seq_noreturn_lhs: "no_return \<top> L \<Longrightarrow> no_return \<top> (L1_seq L R)"
  apply (clarsimp simp: L1_defs no_return_def)
  including no_pre
  apply wp
  apply clarsimp
  done

lemma L1_seq_noreturn_rhs: "\<lbrakk> no_return \<top> R \<rbrakk> \<Longrightarrow> no_return \<top> (L1_seq L R)"
  apply (clarsimp simp: L1_defs no_return_def no_throw_def)
  apply (rule seqE [where B="\<lambda>_ _. True"])
   apply (rule hoareE_TrueI)
  apply simp
  done

lemma L1_catch_noreturn: "\<lbrakk> no_return \<top> L; no_return \<top> R \<rbrakk> \<Longrightarrow> no_return \<top> (L1_catch L R)"
  apply (clarsimp simp: L1_defs)
  apply (clarsimp simp: no_return_def)
  apply (rule handleE_wp, assumption)
  apply simp
  done

lemma L1_condition_noreturn: "\<lbrakk> no_return \<top> L; no_return \<top> R \<rbrakk> \<Longrightarrow> no_return \<top> (L1_condition C L R)"
  by (clarsimp simp: L1_defs no_return_def validE_def valid_def split: condition_splits)

(*
 * always_fail lemmas
 *)

lemma L1_fail_alwaysfail [simp,L1except]: "always_fail \<top> L1_fail"
  by (clarsimp simp: L1_defs)

lemma L1_seq_alwaysfail_lhs: "\<lbrakk> always_fail \<top> L \<rbrakk> \<Longrightarrow> always_fail \<top> (L1_seq L R)"
  by (auto intro!: bindE_alwaysfail_lhs simp: L1_defs)

lemma L1_seq_alwaysfail_rhs: "\<lbrakk> empty_fail L; no_throw \<top> L; always_fail \<top> R \<rbrakk> \<Longrightarrow> always_fail \<top> (L1_seq L R)"
  by (auto intro!: bindE_alwaysfail_rhs simp: L1_defs)

lemma L1_catch_alwaysfail_lhs: "\<lbrakk> always_fail \<top> L \<rbrakk> \<Longrightarrow> always_fail \<top> (L1_catch L R)"
  by (auto intro!: handleE_alwaysfail_lhs simp: L1_defs)

lemma L1_catch_alwaysfail_rhs: "\<lbrakk> empty_fail L; no_return \<top> L; always_fail \<top> R \<rbrakk> \<Longrightarrow> always_fail \<top> (L1_catch L R)"
  by (auto intro!: handleE_alwaysfail_rhs simp: L1_defs)

lemma L1_condition_alwaysfail: "\<lbrakk> always_fail \<top> L; always_fail \<top> R \<rbrakk> \<Longrightarrow> always_fail \<top> (L1_condition C L R)"
  by (clarsimp simp: L1_defs always_fail_def split: condition_splits)

(*
 * Rewrite rules.
 *)

lemma L1_catch_nothrow [L1except]:
  "no_throw \<top> A \<Longrightarrow> L1_catch A E = A"
  by (metis L1_catch_def no_throw_handleE)

lemma L1_seq_noreturn [L1except]:
  "no_return \<top> A \<Longrightarrow> L1_seq A B = A"
  apply (clarsimp simp: L1_defs)
  apply (metis no_return_bindE)
  done

lemma L1_catch_throw [L1except]:
  "L1_catch L1_throw E = E"
  apply (clarsimp simp: L1_defs)
  apply (clarsimp simp: throwError_def handleE_def handleE'_def)
  done

lemma anything_to_L1_fail [L1except]:
  "always_fail \<top> A \<Longrightarrow> A = L1_fail"
  apply (clarsimp simp: always_fail_def L1_fail_def fail_def)
  apply (rule ext)
  apply force
  done

(*
lemma L1_seq_fail [L1except]:
  "\<lbrakk> empty_fail L; no_throw \<top> L; always_fail \<top> R \<rbrakk> \<Longrightarrow> L1_seq L R = L1_fail"
  apply (subst (2) anything_to_L1_fail)
   apply (rule L1_seq_alwaysfail_rhs)
     apply auto
  done
*)

lemma L1_catch_L1_seq_nothrow [L1except]:
  "\<lbrakk> no_throw \<top> A \<rbrakk> \<Longrightarrow> L1_catch (L1_seq A B) C = L1_seq A (L1_catch B C)"
  apply (unfold L1_defs)
  apply (subst bindE_handleE_join [symmetric])
   apply simp
  apply simp
  done

lemma L1_catch_simple_seq [L1except]:
  "L1_catch (L1_seq L1_skip B) E = (L1_seq L1_skip (L1_catch B E))"
  "L1_catch (L1_seq L1_fail B) E = (L1_seq L1_fail (L1_catch B E))"
  "L1_catch (L1_seq (L1_modify m) B) E = (L1_seq (L1_modify m) (L1_catch B E))"
  "L1_catch (L1_seq (L1_spec s) B) E = (L1_seq (L1_spec s) (L1_catch B E))"
  "L1_catch (L1_seq (L1_guard g) B) E = (L1_seq (L1_guard g) (L1_catch B E))"
  "L1_catch (L1_seq (L1_init i) B) E = (L1_seq (L1_init i) (L1_catch B E))"
  "L1_catch (L1_seq (L1_call a b c d) B) E = (L1_seq (L1_call a b c d) (L1_catch B E))"
  apply (subst L1_catch_seq_join | clarsimp simp: L1_defs L1_call_nothrow | rule no_throw_bindE_simple)+
  done

lemma L1_catch_single [L1except]:
  "L1_catch (L1_skip) E = L1_skip"
  "L1_catch (L1_fail) E =  L1_fail"
  "L1_catch (L1_modify m) E = L1_modify m"
  "L1_catch (L1_spec s) E = L1_spec s"
  "L1_catch (L1_guard g) E = L1_guard g"
  "L1_catch (L1_init i) E = L1_init i"
  "L1_catch (L1_call a b c d) E = L1_call a b c d"
  apply (subst L1_catch_nothrow | clarsimp simp: L1_defs L1_call_nothrow | rule no_throw_bindE_simple)+
  done

lemma L1_catch_single_while [L1except]:
  "\<lbrakk> no_throw \<top> B \<rbrakk> \<Longrightarrow> L1_catch (L1_while C B) E = L1_while C B"
  by (metis L1_catch_def L1_while_nothrow handleE_def no_throw_handleE')

lemma L1_catch_seq_while [L1except]:
  "\<lbrakk> no_throw \<top> B \<rbrakk> \<Longrightarrow> L1_catch (L1_seq (L1_while C B) X) E = L1_seq (L1_while C B) (L1_catch X E)"
  apply (rule L1_catch_seq_join [symmetric])
  apply (clarsimp simp: L1_defs)
  apply (rule whileLoopE_nothrow)
  apply simp
  done

lemma L1_catch_single_cond [L1except]:
  "L1_catch (L1_condition C L R) E = L1_condition C (L1_catch L E) (L1_catch R E)"
  apply (rule ext)+
  apply (monad_eq simp: L1_defs Bex_def Ball_def)
  apply blast
  done

(* Exponential: can only apply in certain circumstances. *)
lemma L1_catch_cond_seq:
  "L1_catch (L1_seq (L1_condition C L R) B) E = L1_condition C (L1_catch (L1_seq L B) E) (L1_catch (L1_seq R B) E)"
  apply (subst L1_condition_distrib)
  apply (rule L1_catch_single_cond)
  done

(* This exciting lemma lets up break up a L1_catch into two parts in
 * the exciting circumstance that "E" never returns. *)
lemma L1_catch_seq_cond_noreturn_ex:
  "\<lbrakk> no_return \<top> E \<rbrakk> \<Longrightarrow> (L1_catch (L1_seq (L1_condition c A B) C) E) = (L1_seq (L1_catch (L1_condition c A B) E) (L1_catch C E))"
  apply (clarsimp simp: L1_defs)
  apply (monad_eq simp: no_return_def valid_def validE_def Ball_def
      Bex_def unit_Inl_or_Inr split:sum.splits)
  apply (safe, (metis Inr_not_Inl)+)
  done

lemmas L1_catch_seq_cond_nothrow = L1_catch_L1_seq_nothrow [OF L1_condition_nothrow]

end
