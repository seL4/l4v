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
begin

(* This file contains the experimental method guess_exI, which, as the name suggests,
attempts to guess an instantiation for an existential in the goal. It does so by looking
for a matching premise for one of the conjuncts inside the existential binder, checking that
this could be the only match for safety. *)

method abs_used for P = (match (P) in "\<lambda>s. ?P" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)

method find_prem for Q = (
      match (Q) in "\<lambda>v. y = v" for y \<Rightarrow>
            \<open>rule exI[where x=y]\<close>
    | match (Q) in "\<lambda>v. v = y" for y \<Rightarrow>
            \<open>rule exI[where x=y]\<close>
    | match (Q) in "\<lambda>v. (P v :: bool)" for P \<Rightarrow>
            \<open>match premises in "P y" (multi) for y \<Rightarrow>
                   \<open>abs_used P, rule exI[where x=y]\<close>\<close>
    | match (Q) in "\<lambda>y. A y \<longrightarrow> B y" for A B  \<Rightarrow>
            \<open> match (A) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close>
            | match (B) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close> \<close>
    | match (Q) in "\<lambda>y. A y \<and> B y" for A B  \<Rightarrow>
            \<open> match (A) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close>
            | match (B) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close> \<close>
    )

method guess_exI =
    (require_determ \<open>(match conclusion in "\<exists>x. Q x" for Q \<Rightarrow>
                            \<open>find_prem Q\<close>)\<close>)

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

  (* NB: conflicts between different conjuncts are currently not checked *)
  lemma
    assumes Q: "Q x"
    shows "\<lbrakk> P x; Q y \<rbrakk> \<Longrightarrow> \<exists>x. Q x \<and> P x"
    apply guess_exI
    oops
end

end