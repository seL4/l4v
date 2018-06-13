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
 * More theories and lemmas related to the non-deterministic monad library.
 *)

theory NonDetMonadEx
imports
  "Word_Lib.WordSetup"
  "Lib.NonDetMonadLemmaBucket"
  "Lib.OptionMonadND"
begin

(*
 * Definitions.
 *)

(* Fail unless the given state obeys the given condition. *)
abbreviation "guard \<equiv> state_assert"

lemma guard_def:
    "guard P = (\<lambda>s. (if P s then {((), s)} else {}, \<not> P s))"
  apply (monad_eq simp: state_assert_def Bex_def)
  done

abbreviation "spec \<equiv> state_select"
lemmas spec_def = state_select_def

(* Fail unless the given state obeys the given condition. *)
definition
  guardE :: "('s \<Rightarrow> bool) \<Rightarrow> ('s, 'e + unit) nondet_monad"
where
  "guardE P \<equiv> (liftE (guard P))"

(* Shorthand definitions. *)
definition "unknown \<equiv> select UNIV"
definition "selectE S = liftE (select S)"
definition "unknownE \<equiv> selectE UNIV"
definition "skip \<equiv> return ()"
definition "skipE \<equiv> returnOk ()"
definition "modifyE m = liftE (modify m)"
definition "specE r \<equiv> liftE (spec r)"
definition "getsE g \<equiv> liftE (gets g)"

lemmas monad_defs = unknown_def unknownE_def selectE_def skip_def
    skipE_def modifyE_def specE_def getsE_def guardE_def

lemmas [monad_eq] = monad_defs

lemma in_spec [monad_eq]:
    "(r', s') \<in> fst (spec R s) = ((s, s') \<in> R)"
  by (clarsimp simp: spec_def image_def)

lemma snd_spec [monad_eq]:
    "snd (spec R s) = (\<not> (\<exists>s'. (s, s') \<in> R))"
  by (clarsimp simp: spec_def)


(*
 * Theorems
 *)

lemma guardE_wp [wp]: "\<lbrace> \<lambda>s. f s \<longrightarrow> P () s \<rbrace> guardE f \<lbrace> P \<rbrace>,\<lbrace> Q \<rbrace>"
  apply (unfold guardE_def)
  apply wp
  done

lemma modifyE_wp_nf [wp]:
    "\<lbrace> \<lambda>s. P () (m s) \<rbrace> modifyE m \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>!"
  by (monad_eq simp: modifyE_def validE_NF_def valid_def no_fail_def)

lemma modifyE_wp [wp]:
    "\<lbrace> \<lambda>s. P () (m s) \<rbrace> modifyE m \<lbrace> P \<rbrace>, \<lbrace> Q \<rbrace>"
  by (monad_eq simp: modifyE_def validE_NF_def valid_def no_fail_def)

lemma when_wp_nf [wp]:
  "\<lbrakk> P \<Longrightarrow> \<lbrace> Q \<rbrace> f \<lbrace> R \<rbrace>! \<rbrakk>
           \<Longrightarrow> \<lbrace> if P then Q else R () \<rbrace> when P f \<lbrace> R \<rbrace>!"
  by (monad_eq simp: validNF_def valid_def no_fail_def)

lemmas [wp] = hoare_whenE_wp

lemma gets_the_wp_nf [wp]:
  "\<lbrace>\<lambda>s. (f s \<noteq> None) \<and> Q (the (f s)) s\<rbrace> gets_the f \<lbrace>Q\<rbrace>!"
  by (monad_eq simp: gets_the_def validNF_def valid_def no_fail_def
            assert_opt_def split: option.splits)

lemma getsE_wp_nf [wp]:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> getsE f \<lbrace> P \<rbrace>,\<lbrace> E \<rbrace>!"
  by (monad_eq simp: getsE_def validE_NF_def validE_def
                 valid_def no_fail_def split: sum.splits)

lemma getsE_wp [wp]:
  "\<lbrace>\<lambda>s. P (f s) s\<rbrace> getsE f \<lbrace> P \<rbrace>,\<lbrace> E \<rbrace>"
  by (monad_eq simp: getsE_def validE_def valid_def split: sum.splits)

lemma validE_NF_K_bind [wp]:
  "\<lbrace> P \<rbrace> x \<lbrace> Q \<rbrace>, \<lbrace> E \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> K_bind x f \<lbrace> Q \<rbrace>, \<lbrace> E \<rbrace>!"
  by simp

lemma empty_fail_skip [simp]: "empty_fail skip"
  apply (clarsimp simp: empty_fail_def skip_def return_def)
  done

lemma empty_fail_exception [simp]:
  "empty_fail (modifyE m)"
  "empty_fail skipE"
  "empty_fail (guardE G)"
  "empty_fail (returnOk r)"
  "empty_fail (getsE g)"
  apply (auto simp add: skipE_def modifyE_def returnOk_def guardE_def getsE_def)
  done

lemma simple_nothrow [simp]:
  "no_throw \<top> skipE"
  "no_throw \<top> (modifyE m)"
  "no_throw \<top> (guardE g)"
  "no_throw \<top> (specE a)"
  "no_throw \<top> (getsE v)"
  "no_throw \<top> fail"
  apply (auto simp: skipE_def modifyE_def guardE_def specE_def getsE_def)
  done

lemma simple_bindE_fail [simp]:
  "(guardE X >>=E (\<lambda>_. fail)) = fail"
  "(modifyE M >>=E (\<lambda>_. fail)) = fail"
  "(returnOk X >>=E (\<lambda>_. fail)) = fail"
  "(getsE X >>=E (\<lambda>_. fail)) = fail"
  "(skipE >>=E (\<lambda>_. fail)) = fail"
  "handleE fail x = fail"
  apply (auto intro!: bindE_fail_propagates simp: handleE_def handleE'_def)
  done

lemma skip_wp [wp]: "\<lbrace> P () \<rbrace> skip \<lbrace> P \<rbrace>"
  apply (clarsimp simp: skip_def valid_def return_def)
  done

lemma skip_nf [wp]: "\<lbrace> P () \<rbrace> skip \<lbrace> P \<rbrace>!"
  apply (monad_eq simp: validNF_def valid_def no_fail_def skip_def)
  done

declare valid_case_prod [wp]
declare validE_case_prod [wp]

lemma getsE_to_returnOk [simp]: "getsE (\<lambda>s. v) = returnOk v"
  apply (monad_eq simp: getsE_def)
  done

lemma guard_conj_split:
  "guard (\<lambda>s. P s \<and> Q s) = (guard P >>= (\<lambda>_. guard Q))"
  apply (monad_eq simp: Bex_def)
  done

lemma validNF_assume_pre:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>! \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!"
    by (metis hoare_assume_pre no_fail_assume_pre validNF_def)

lemma liftE_condition_distrib: "liftE (condition C L R) = condition C (liftE L) (liftE R)"
  apply monad_eq
  apply force
  done

lemma condition_gets:
  "condition C (gets P) (gets Q) = gets (\<lambda>s. if C s then P s else Q s)"
  apply (monad_eq)
  done

lemma if_distrib_conj: "(if P then (A \<and> B) else (A \<and> C)) = (A \<and> (if P then B else C))"
  apply clarsimp
  done

lemma if_distrib_disj: "(if P then (A \<or> B) else (A \<or> C)) = (A \<or> (if P then B else C))"
  apply clarsimp
  done

lemma if_distrib_disj': "(if P then (B \<or> A) else (C \<or> A)) = (A \<or> (if P then B else C))"
  apply clarsimp
  apply blast
  done

lemma whileLoop_fail:
    "(whileLoop C (\<lambda>_. fail) i) = (guard (\<lambda>s. \<not> C i s) >>= (\<lambda>_. return i))"
  apply (subst whileLoop_unroll)
  apply (monad_eq)
  done

lemma whileLoopE_fail:
    "(whileLoopE C (\<lambda>_. fail) i) = (guardE (\<lambda>s. \<not> C i s) >>= (\<lambda>_. returnOk i))"
  apply (subst whileLoopE_unroll)
  apply (monad_eq simp: guardE_def)
  done

lemma oreturn_exec [simp]:
    "oreturn a s = Some a"
  by (clarsimp simp: oreturn_def)

lemma ogets_exec [simp]:
    "ogets a s = Some (a s)"
  by (clarsimp simp: ogets_def)

lemma ofail_exec [simp]:
    "ofail s = None"
  by (clarsimp simp: ofail_def)

lemma oguard_failed [simp]:
    "(oguard G s = None) = (\<not> G s)"
  by (clarsimp simp: oguard_def)

lemma oguard_passed [simp]:
    "(oguard G s = Some v) = (G s)"
  by (clarsimp simp: oguard_def)

lemma owhile_fail:
    "(owhile C (\<lambda>_. ofail) i) = (oguard (\<lambda>s. \<not> C i s) |>> (\<lambda>_. oreturn i))"
  apply (rule ext)
  apply (subst owhile_unroll)
  apply (clarsimp simp: obind_def ocondition_def split: option.splits)
  done

lemma liftE_left: "x >>= (\<lambda>a. liftE (y a)) \<equiv> liftE (x >>= y)"
  by (simp add: bind_liftE_distrib liftE_bindE)

lemma liftE_liftE: "liftE x >>=E (\<lambda>a. liftE (y a)) \<equiv> liftE (x >>= y)"
  by (simp add: bind_liftE_distrib)

lemma liftE_gets_fail: "liftE (gets M) >>=E (\<lambda>_. fail) = fail"
  by (metis gets_bind_ign liftE_bindE)


lemma gets_the_to_return:
   "X s = Some v \<Longrightarrow> gets_the X s = return v s"
  by (clarsimp simp: gets_the_def exec_gets)

lemma owhile_to_fold:
  assumes p_increments: "\<And>r. P (Q r) = (P r + 1 :: 'a::len word)"
  shows "owhile (\<lambda>r s. P r < x) (\<lambda>r. oreturn (Q r)) i =
      oreturn (if P i \<le> x then fold (\<lambda>i. Q) [unat (P i)..<unat x] i else i)"
    (is "?LHS = oreturn (?RHS x)")
  apply (rule ext)
  apply (case_tac "P i \<le> x")
   apply simp
   apply (rule_tac s=xa in owhile_rule [where I="\<lambda>r s. P i \<le> P r \<and> P r \<le> x \<and> r = ?RHS (P r)"
        and M="measure (\<lambda>r. unat x - unat (P r))"])
        apply clarsimp
       apply clarsimp
      apply clarsimp
      apply (clarsimp simp: p_increments)
      apply (subst unatSuc2)
       apply (metis less_is_non_zero_p1)
      apply unat_arith
     apply (clarsimp simp: p_increments)
     apply (subst unat_Suc2)
      apply clarsimp
     apply clarsimp
     apply unat_arith
    apply (clarsimp simp: oreturn_def)
   apply (clarsimp simp: oreturn_def)
  apply simp
  apply (subst owhile_unroll)
  apply (subst ocondition_False)
   apply simp
  apply simp
  done

lemma whileLoop_to_fold:
  assumes p_increments: "\<And>r. P (Q r) = (P r + 1 :: 'a::len word)"
  shows "(whileLoop (\<lambda>r s. P r < x)
           (\<lambda>r. return (Q r))
           i s) = return (if P i \<le> x then fold (\<lambda>i r. (Q r)) [unat (P i) ..< unat x] i else i) s"
    (is "?LHS s = return (?RHS x) s")
  apply (subst OptionMonadND.gets_the_return [symmetric])
  apply (subst gets_the_whileLoop)
  apply (rule gets_the_to_return)
  apply (subst owhile_to_fold)
   apply (rule p_increments)
  apply (clarsimp simp: oreturn_def)
  done

lemma guard_True_bind [simp]:
    "(guard (\<lambda>_. True) >>= M) = M ()"
  by (monad_eq simp: guard_def)

lemma validNF_guardE [wp]:
  "\<lbrace> \<lambda>s. P () s \<and> G s  \<rbrace> guardE G \<lbrace> P \<rbrace>,\<lbrace> E \<rbrace>!"
  apply rule
   apply wp
   apply simp
  apply (monad_eq simp: no_fail_def guardE_def)
  done

(* FIXME: move *)
lemma validNF_when [wp]:
  "\<lbrace> P \<rbrace> B \<lbrace> Q \<rbrace>! \<Longrightarrow> \<lbrace> \<lambda>s. if C then P s else Q () s \<rbrace> when C B \<lbrace> Q \<rbrace>!"
  by (monad_eq simp: validNF_alt_def when_def split: sum.splits prod.splits)

(* FIXME: move *)
lemma validNF_unknown [wp]:
  "\<lbrace> \<lambda>s. \<forall>x. Q x s \<rbrace> unknown \<lbrace> Q \<rbrace>!"
  by (monad_eq simp: unknown_def validNF_alt_def)

(* FIXME: move *)
lemma validNF_gets_the [wp]:
  "\<lbrace> \<lambda>s. \<exists>x. M s = Some x \<and> Q x s  \<rbrace> gets_the M \<lbrace> Q \<rbrace>!"
  by (monad_eq simp: gets_the_def validNF_alt_def Ball_def split: option.splits)

(* FIXME: move *)


(* Forms of whileLoop and whileLoopE that work well with the
 * "monad_eq" ruleset. *)

definition
  whileLoopME
where
 "whileLoopME C R F \<equiv>
    whileLoop C (\<lambda>r s. ({(r', s'). R (r, s) (r', s')}, F (r, s)))"

definition
  whileLoopE_ME
where
 "whileLoopE_ME C R F \<equiv>
    whileLoopE C (\<lambda>r s. ({(r', s'). R (r, s) (r', s')}, F (r, s)))"

lemma in_whileLoop_monad_eq [monad_eq]:
  "((r', s') \<in> fst (whileLoop C B r s)) =
      ((r', s') \<in> fst (whileLoopME C
        (\<lambda>(r, s) (r', s'). (r', s') \<in> fst (B r s))
        (\<lambda>(r, s). snd (B r s)) r s))"
  by (clarsimp simp: whileLoopME_def)

lemma snd_whileLoop_monad_eq [monad_eq]:
  "(snd (whileLoop C B r s)) =
      (snd (whileLoopME C
        (\<lambda>(r, s) (r', s'). (r', s') \<in> fst (B r s))
        (\<lambda>(r, s). snd (B r s)) r s))"
  by (clarsimp simp: whileLoopME_def)

lemma in_whileLoopE_monad_eq [monad_eq]:
  "((r', s') \<in> fst (whileLoopE C B r s)) =
      ((r', s') \<in> fst (whileLoopE_ME C
        (\<lambda>(r, s) (r', s'). (r', s') \<in> fst (B r s))
        (\<lambda>(r, s). snd (B r s)) r s))"
  by (clarsimp simp: whileLoopE_ME_def)

lemma snd_whileLoopE_monad_eq [monad_eq]:
  "(snd (whileLoopE C B r s)) =
      (snd (whileLoopE_ME C
        (\<lambda>(r, s) (r', s'). (r', s') \<in> fst (B r s))
        (\<lambda>(r, s). snd (B r s)) r s))"
  by (clarsimp simp: whileLoopE_ME_def)

lemma in_fst_case_prod [monad_eq]: "((r, s) \<in> fst ((case z of (x, y) \<Rightarrow> B x y) s'))
          = ((r, s) \<in> fst (B (fst z) (snd z) s'))"
  by (clarsimp simp: split_def)

lemma snd_case_prod [monad_eq]: "(snd ((case z of (x, y) \<Rightarrow> B x y) s'))
          = (snd (B (fst z) (snd z) s'))"
  by (clarsimp simp: split_def)

lemma validE_K_bind [wp]:
    "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace> \<Longrightarrow> \<lbrace> P \<rbrace> (K_bind f) x \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  by simp

lemma validE_whenE [wp]:
    "\<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace> \<Longrightarrow> \<lbrace> \<lambda>s. if c then P s else Q () s \<rbrace> whenE c f \<lbrace> Q \<rbrace>,\<lbrace> E \<rbrace>"
  by (clarsimp simp: whenE_def validE_def valid_def
        returnOk_def return_def split: sum.splits)

end
