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
imports HOL.HOL "HOL-Eisbach.Eisbach"
begin

(* This file contains the experimental method guess_exI, which, as the name suggests,
attempts to guess an instantiation for an existential in the goal. It does so by looking
for a matching premise for one of the conjuncts inside the existential binder, checking that
this could be the only match for safety. *)

ML {*

local

fun disj x y = (if x then true else y)

fun can_match t t' = can Thm.match (t',t)

fun obind f x = (case x of NONE => NONE | (SOME v) => f v)

in

fun duplicate_prems ctxt (t : term) st =
  let val prems = Drule.cprems_of st
      val cterm = t |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt
      val match_exists = fold (disj) (map (cterm |> can_match) prems) false
  in (if match_exists then no_tac else all_tac) st
  end


fun determ_method (method : Method.method) thms st =
  let
    val alternatives_exist = is_some (method thms st |> Seq.filter_results
                                                     |> Seq.pull
                                                     |> obind (Seq.pull o snd))

  in (if alternatives_exist then Method.fail else method) (thms) st
end

fun duplicate_prems_method term ctxt = SIMPLE_METHOD (duplicate_prems ctxt term)

fun determ_method' text ctxt = determ_method (Method.evaluate_runtime text ctxt)
end

*}

method_setup determ = {*
  (Method.text_closure) >> determ_method'
*}

method_setup in_prems = {*
  (Args.term_pattern) >> duplicate_prems_method
*}

method abs_used for P = (match (P) in "\<lambda>s. ?P" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)

method find_prem for Q =  (match (Q) in "\<lambda>v. y = v" for y \<Rightarrow>
                                  \<open>rule exI[where x=y]\<close>                                   |
                           match (Q) in "\<lambda>v. v = y" for y \<Rightarrow>
                                  \<open>rule exI[where x=y]\<close>                                   |
                           match (Q) in "\<lambda>v. (P v :: bool)" for P \<Rightarrow>
                                  \<open>match premises in "P y" (multi) for y \<Rightarrow>
                                   \<open>abs_used P, rule exI[where x=y]\<close>\<close> |
                           match (Q) in "\<lambda>y. A y \<longrightarrow> B y" for A B  \<Rightarrow>
                                 \<open>match (A) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close> |
                                  match (B) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close>\<close>        |
                           match (Q) in "\<lambda>y. A y \<and> B y" for A B  \<Rightarrow>
                                 \<open>match (A) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close> |
                                  match (B) in "(P :: 'a)" for P \<Rightarrow> \<open>find_prem P\<close> \<close>)

method guess_exI = (determ \<open>(match conclusion in "\<exists>x. Q x" for Q \<Rightarrow>
                            \<open>find_prem Q\<close>)\<close>)

end
