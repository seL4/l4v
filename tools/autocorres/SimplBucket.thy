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
 * Random lemmas relating to the SIMPL language.
 *)

theory SimplBucket
imports "../c-parser/CTranslation"
begin

lemma Normal_resultE:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>c, s\<rangle> \<Rightarrow> Normal t'; \<And>t. \<lbrakk> \<Gamma> \<turnstile> \<langle>c, Normal t\<rangle> \<Rightarrow> Normal t'; s = Normal t\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (metis noAbrupt_startD noFault_startD noStuck_startD xstate.exhaust)

(* The final state of a While loop will not have the condition. *)
lemma exec_While_final_cond':
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>b, s\<rangle> \<Rightarrow> s'; b = While C B; s = Normal v; s' = Normal x \<rbrakk> \<Longrightarrow> x \<notin> C"
  apply (induct arbitrary: v x rule: exec.induct)
  apply simp_all
  apply (atomize, clarsimp)
  apply (erule exec_elim_cases, auto)
  done

lemma exec_While_final_cond:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>While C B, s\<rangle> \<Rightarrow> Normal s'\<rbrakk> \<Longrightarrow> s' \<notin> C"
  apply (erule Normal_resultE)
  apply (erule exec_While_final_cond', auto)
  done

(*
 * If an invariant is held over a while loop, it will still hold when
 * the loop is complete.
 *)
lemma exec_While_final_inv':
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>b, s\<rangle> \<Rightarrow> s'; b = While C B; s = Normal v; s' = Normal x; I v; \<And>s s'. \<lbrakk> I s; \<Gamma> \<turnstile> \<langle>B, Normal s\<rangle> \<Rightarrow> Normal s' \<rbrakk> \<Longrightarrow> I s' \<rbrakk> \<Longrightarrow> I x"
  apply atomize
  apply (induct arbitrary: v x rule: exec.induct)
  (* We avoid using the simplifier here, because of looping. *)
  apply (clarify | (atomize, erule Normal_resultE, metis))+
  done

lemma exec_While_final_inv:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>While C B, Normal s\<rangle> \<Rightarrow> Normal s'; I s; \<And>s s'. \<lbrakk> I s; \<Gamma> \<turnstile> \<langle>B, Normal s\<rangle> \<Rightarrow> Normal s' \<rbrakk> \<Longrightarrow> I s' \<rbrakk> \<Longrightarrow> I s'"
  apply (erule exec_While_final_inv', auto)
  done

(* Determine if the given SIMPL fragment may throw an exception. *)
primrec
  exceptions_thrown :: "('a, 'p, 'e) com \<Rightarrow> bool"
where
    "exceptions_thrown Skip = False"
  | "exceptions_thrown (Seq a b) = (exceptions_thrown a \<or> exceptions_thrown b)"
  | "exceptions_thrown (Basic a) = False"
  | "exceptions_thrown (Spec a) = False"
  | "exceptions_thrown (Cond a b c) = (exceptions_thrown b \<or> exceptions_thrown c)"
  | "exceptions_thrown (Catch a b) = (exceptions_thrown a \<and> exceptions_thrown b)"
  | "exceptions_thrown (While a b) = exceptions_thrown b"
  | "exceptions_thrown Throw = True"
  | "exceptions_thrown (Call p) = True"
  | "exceptions_thrown (Guard f g a) = exceptions_thrown a"
  | "exceptions_thrown (DynCom a) = (\<exists>s. exceptions_thrown (a s))"

(* May the given stack of exception handlers throw an exception? *)
primrec
  exceptions_unresolved :: "('a, 'p, 'e) com list \<Rightarrow> bool"
where
    "exceptions_unresolved [] = True"
  | "exceptions_unresolved (x#xs) = (exceptions_thrown x \<and> exceptions_unresolved xs)"

(* If code can't throw an exception, it won't result in abrupt termination. *)
lemma exceptions_thrown_not_abrupt:
  "\<lbrakk> \<Gamma> \<turnstile> \<langle>p, s\<rangle> \<Rightarrow> s'; \<not> exceptions_thrown p; \<not> isAbr s \<rbrakk> \<Longrightarrow> \<not> isAbr s'"
  apply (induct rule: exec.induct, auto)
  done

end
