(*
 * Copyright 2019, Data61
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Guess_ExI
imports
  Eisbach_Methods
  Apply_Debug
begin

(*
This file contains the experimental methods guess_exI and guess_spec. Each, as the name suggests,
attempts to guess an instantiation for their respective rules. It does so by looking
for a matching premise for the quantifying binder, checking that
this could be the only match for safety.
*)

method abs_used for P = (match (P) in "\<lambda>s. ?P" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)

method in_conj for P Q = (
      match (Q) in "P" \<Rightarrow> \<open>-\<close>
    | match (Q) in "\<lambda>y. A y \<and> B y"  for A B  \<Rightarrow>
            \<open> match (A) in "(Q' :: 'b)" for Q' \<Rightarrow> \<open>match (B) in "(Q'' :: 'b)"  for Q'' \<Rightarrow>
             \<open> in_conj P Q' | in_conj P Q''\<close>\<close>\<close>
    )

method guess_exI =
    (require_determ \<open>(match conclusion in "\<exists>x. Q x" for Q \<Rightarrow>
                            \<open>match premises in "P y" for P y \<Rightarrow>
                             \<open>abs_used P, in_conj P Q, rule exI[where x=y]\<close>\<close>)\<close>)

lemma fun_uncurry:
  "(P \<longrightarrow> Q \<longrightarrow> R) \<longleftrightarrow> (P \<and> Q) \<longrightarrow> R"
  by auto

method guess_spec_inner for P uses I =
    ((match I in "\<forall>x. C x \<longrightarrow> _ x" for C \<Rightarrow> \<open>in_conj P C\<close> ))

method guess_spec =
    (require_determ \<open>(match premises in I:"\<forall>x. _ x \<longrightarrow> _ x" \<Rightarrow>
                            \<open>match premises in "P y" for P y \<Rightarrow>
                            \<open>abs_used P, guess_spec_inner P I:I[simplified fun_uncurry],
                                         insert I, drule spec[where x=y]\<close>\<close>)\<close>)

text \<open>Tests and examples\<close>
experiment begin

 lemma
    assumes Q: "Q x"
    shows  "P x \<Longrightarrow> \<forall>x. Q x \<longrightarrow> P x \<longrightarrow> R  \<Longrightarrow> R"
    by (guess_spec, blast intro: Q)

  (* Conflicting premises are checked *)
  lemma
    assumes Q: "Q x"
    shows "\<lbrakk> P x; P y \<rbrakk> \<Longrightarrow>  \<forall>x. Q x \<longrightarrow> P x \<longrightarrow> R \<Longrightarrow> R"
    apply (fails \<open>guess_spec\<close>)
    by (blast intro: Q)

  (* Conflicts between different conjuncts are checked *)
  lemma
    assumes Q: "Q x"
    shows "\<lbrakk> P x; Q y \<rbrakk> \<Longrightarrow> \<forall>x. Q x \<longrightarrow> P x \<longrightarrow> R \<Longrightarrow> R"
    apply (fails \<open>guess_spec\<close>)
    by (blast intro: Q)
end

text \<open>Tests and examples\<close>
experiment begin
  lemma "P x \<Longrightarrow> \<exists>x. P x"
    by guess_exI

  lemma
    assumes Q: "Q x"
    shows "P x \<Longrightarrow> \<exists>x. Q x \<and> P x"
    apply guess_exI
    by (blast intro: Q)

  (* Conflicting premises are checked *)
  lemma
    assumes Q: "Q x"
    shows "\<lbrakk> P x; P y \<rbrakk> \<Longrightarrow> \<exists>x. Q x \<and> P x"
    apply (fails \<open>guess_exI\<close>)
    by (blast intro: Q)

  (* Conflicts between different conjuncts are checked *)
  lemma
    assumes Q: "Q x"
    shows "\<lbrakk> P x; Q y \<rbrakk> \<Longrightarrow> \<exists>x. Q x \<and> P x"
    apply (fails \<open>guess_exI\<close>)
    by (blast intro: Q)
end

end