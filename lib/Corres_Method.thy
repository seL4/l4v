(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Corres_Method
imports Corres_Cases ExtraCorres
begin

(* A proof method for automating simple steps in corres proofs.

   While the method might solve some corres proofs completely, the purpose is to make simple
   things more automatic, remove boilerplate, and to leave a proof state in which the user can make
   more progress. The goal is not to provide full automation or deeper search.

   The main idea is to repeatedly try to apply terminal [corres] rules after splitting off the head
   of a bind/bindE statement on both sides of a corres goal. The method provides options for less
   safe rules such as moving asserts to guards etc when the user knows that this is safe to do in
   a particular instance.

   See description at corres' method below for all parameters and options.
*)

section \<open>Goal predicates\<close>

(* Succeed if the conclusion is a corres goal and also not purely schematic *)
method is_corres = succeeds \<open>rule corres_inst\<close>, fails \<open>rule TrueI\<close>

lemma no_fail_triv: "no_fail P f \<Longrightarrow> no_fail P f" .
lemmas hoare_trivs = hoare_triv hoare_trivE hoare_trivE_R hoare_trivR_R no_fail_triv

(* Succeed if the conclusion is a wp/no_fail goal and also not purely schematic*)
method is_wp = succeeds \<open>rule hoare_trivs\<close>, fails \<open>rule TrueI\<close>

lemmas hoare_post_False = hoare_pre_cont[where P="\<lambda>_. \<bottom>"]
lemmas hoareE_post_False = hoare_FalseE[where Q="\<lambda>_. \<bottom>" and E="\<lambda>_. \<bottom>"]

(* Succeed if the conclusion has a schematic post condition (assuming a wp goal). *)
method is_hoare_schematic_post =
  (* If the post condition matches both \<top> and \<bottom>, it must be schematic *)
  succeeds \<open>wp_pre, rule hoare_post_False hoareE_post_False\<close>,
  succeeds \<open>wp_pre, rule wp_post_taut wp_post_tautE\<close>

section \<open>Main corres method\<close>

named_theorems corres_splits
method corres_split declares corres_splits = no_name_eta, rule corres_splits

(* This method is called on non-corres, non-wp side conditions after a corres rule has been
   applied. At that point, there should be no schematic variables in those side condition goals.
   Despite that, we are still careful with simp etc here, in case the user does provide a corres
   rule that generates a schematic in those side condition goals. *)
method corres_cleanup methods m uses simp simp_del split split_del cong intro =
  #break "corres_cleanup",
  ( m
  | assumption
  | rule refl TrueI
  | clarsimp simp del: corres_no_simp simp_del simp: simp split: split split del: split_del
             cong: cong intro!: intro
  (* enables passing in conjI for terminal goals: *)
  | (rule intro;
     corres_cleanup m simp: simp simp_del: simp_del split: split split_del: split_del
                      cong: cong intro: intro))

(* Apply a single corres rule and attempt to solve non-corres and non-wp side conditions.
   We don't expect any wp side conditions, but check anyway for safety. If the rule is declared
   as terminal rule, all side conditions must be solved and no corres or wp side conditions are
   allowed. If the rule is declared as a regular corres rule, unsolved side conditions as well as
   corres and wp side conditions will be left over unchanged. *)
method corres_rule
  methods m uses simp simp_del split split_del cong intro declares corres corres_term =
  determ \<open>solves \<open>((rule corres_term | corres_rrel_pre, rule corres_term);
                   solves \<open>corres_cleanup m simp: simp simp_del: simp_del split: split
                                            split_del: split_del cong: cong\<close>)\<close>
          | (rule corres | corres_rrel_pre, rule corres);
            ((fails \<open>is_corres\<close>, fails \<open>is_wp\<close>,
              solves \<open>corres_cleanup m simp: simp simp_del: simp_del split: split
                                       split_del: split_del cong: cong\<close>)?)\<close>

(* For normalisation of corres terms, e.g. liftE *)
named_theorems corres_simp

(* The main method:

   After preliminaries such as wpfix and corres_pre, repeatedly try to either solve the goal
   outright or split off the head from a bind/bindE statement and apply a corres rule (only
   split when a corres rule applies). If none of these works, try a corres rule from the "fallback"
   argument. (These are for things like moving asserts to a guard, which we only want to do if no
   other corres rule applies).

   Attempt to solve side conditions with the corres_cleanup method. The cleanup method uses the
   simp and term_simp arguments.

   Attempt simp on the head corres goal without rewriting guards or return relation when
   none of these make progress (to process things such as liftM). Does not use the term_simp
   argument.

   Attempt clarsimp on the head side condition and final implications. Does not use the term_simp
   argument.

   Attempt wpsimp+ when the head goal is a wp goal (usually present when all corres goals have been
   solved). Fail if we somehow ended up with a schematic post condition despite all safety measures.
*)
method corres'
  methods m
  uses simp term_simp simp_del split split_del cong intro wp wp_del fallback
  declares corres corres_term corres_splits =
  (((* debug breakpoint *)
    #break "corres",
    (* introduce schematic guards if they don't exist *)
    corres_pre0
    (* fix up schematic guards if they contain constructor parameters *)
    | wpfix
    (* apply a single corres rule if possible *)
    | corres_rule m simp: term_simp simp simp_del: simp_del split_del: split_del split: split
                    cong: cong corres: corres corres_term: corres_term
    (* only split if we can apply a single corres rule afterwards *)
    | corres_split corres_splits: corres_splits,
      corres_rule m simp: simp term_simp simp_del: simp_del split_del: split_del split: split
                    cong: cong corres: corres corres_term: corres_term
    (* apply potentially unsafe fallback rules if any are provided *)
    | corres_rule m simp: simp term_simp simp_del: simp_del split_del: split_del split: split
                    cong: cong corres: fallback
    (* simplify head corres goal, e.g. for things like liftM unfolding if the user provides such
       a rule as "simp". Not clarsimp, because clarsimp will still perform hypsubst on assumptions
       and might through that rewrite guards *)
    | succeeds \<open>is_corres\<close>,
      simp (no_asm_use) cong: corres_weaker_cong cong split: split split del: if_split split_del
                        add: simp corres_simp del: corres_no_simp simp_del
    (* simplify any remaining side condition head goal (non-corres, non-wp). This is either a side
       condition that was not solved by corres_cleanup, or it is one of the two terminal implication
       goals. It is very likely that the method will stop after this and not have solved the goal,
       but it also very likely that the first thing we want to do for such a goal is clarsimp. That
       means, overall we might solve a few more goals, and not be detrimental to interactive proof
       either. *)
    | fails \<open>is_corres\<close>, fails \<open>is_wp\<close>,
      clarsimp cong: cong simp del: simp_del simp: simp split del: if_split split_del split: split
               intro!: intro
    (* if (and only if) we get to the state where all corres goals and side conditions are solved,
       attempt to solve all wp goals that were generated in order. We are not using then_all_new_fwd
       here, because we should only start solving wp goals once *all* corres goals are solved --
       otherwise the goal will still have schematic post conditions. Fail if there is a
       free schematic postcondition despite all these measures.
       *)
    | succeeds \<open>is_wp\<close>, fails \<open>is_hoare_schematic_post\<close>,
      (wpsimp wp: wp wp_del: wp_del simp: simp simp_del: simp_del split: split split_del: split_del
              cong: cong)+
   )+)[1]

(* Instance of the corres' method with default cleanup tactic. We provide "fail" as default to let
   the other cleanup tactis run. "succeed" would stop without progress (useful for debugging). *)
method corres
  uses simp term_simp simp_del split split_del cong intro wp wp_del fallback
  declares corres corres_term corres_splits =
  corres' \<open>fail\<close> simp: simp term_simp: term_simp simp_del: simp_del split: split
                 split_del: split_del cong: cong intro: intro wp: wp wp_del: wp_del
                 fallback: fallback
                 corres: corres corres_term: corres_term corres_splits: corres_splits


section \<open>Corres rule setup\<close>

lemmas [corres_splits] =
  corres_split
  corres_splitEE

lemmas corres_split_liftE_bindE [corres_splits] =
  corres_splitEE[OF corres_liftE_rel_sum[THEN iffD2], simplified]

(* corres_term are rules that are safe when all side conditions can be solved immediately -- they
   might have guards like \<top> that are too weak in general, but if the goal can be solved with
   that weak guard, the rule is safe. This enables us to solve trivial cases without adding
   unsafe rules to the [corres] set. *)
lemmas [corres_term] =
  corres_return_eq_same corres_gets_trivial select_corres_eq
  corres_underlying_assert_assert

lemmas corres_returnOk_eq_same[corres_term] = corres_returnOkTT[of "(=)"]
lemmas corres_throwError_eq_same[corres_term] = corres_throwErrorTT[of "(=)"]

lemma corres_get_trivial[corres_term]:
  "corres_underlying sr nf nf' (\<lambda>s s'. (s,s') \<in> sr) \<top> \<top> get get"
  by simp

lemmas corres_underlying_stateAssert_stateAssert_trivial[corres_term] =
  corres_underlying_stateAssert_stateAssert[where P=\<top> and P'=\<top>, simplified]

lemma corres_modify_tivial[corres_term]:
  "(\<And>s s'. (s, s') \<in> sr \<Longrightarrow> (f s, g s') \<in> sr) \<Longrightarrow>
   corres_underlying sr nf nf' dc \<top> \<top> (modify f) (modify g)"
  by (simp add: corres_modify)

(* Regular corres rules are rules where we expect side conditions to be solvable once the rule
   matches, but those side conditions might be too hard for automation, so they must be safe to
   leave over for later manual proof. *)
lemmas [corres] =
  corres_underlying_fail_fail
  corres_fail
  corres_assert
  whenE_throwError_corres (* match this before corres_whenE *)
  corres_whenE
  corres_when

  (* not in corres_split, because head is usually not solvable by single rule: *)
  corres_split_handle
  corres_split_catch
  corres_if2

(* Transform corres terms when no other rules match: *)
lemmas [corres_simp] =
  liftE_bindE
  unless_when
  unlessE_whenE

end