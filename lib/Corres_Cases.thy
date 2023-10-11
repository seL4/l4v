(*
 * Copyright 2023, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Corres_Cases
imports Corres_UL
begin

text \<open>
  This file defines the following main methods for safe data type case distinctions on
  corres/corres_underlying predicates.

  \<^item> corres_cases_left: case distinction on abstract monad
  \<^item> corres_cases_right: case distinction on concrete monad
  \<^item> corres_cases: try corres_cases_left, then corres_cases_right
  \<^item> corres_cases_both: simultaneous (quadratic) case distinction on both sides, with safe
                       elimination of trivially contradictory cases.

  The first 3 methods take no arguments, corres_cases_both takes an optional simp argument to,
  for example, unfold relations that synchronise cases between the abstract and concrete side.

  The case distinctions work if the entire monad is a "case" statement, or if the monad is a
  @{const bind} or @{const bindE} term with a "case" statement in the head position.

  There is an existing method for case distinctions (@{method wpc}), but this method is not
  flexible enough for @{term corres}: consider the goal
  @{text "\<And>x. corres r (?G x) ?G' (case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) m"} -- if we perform
  case distinction on @{term x}, then we can transform @{text "?G x"} into
  @{text "\<lambda>x s. (x = None \<longrightarrow> ?Q1 x s) \<and> (\<forall>y. x = Some y \<longrightarrow> ?Q2 x y s)"},
  but we cannot do the same with @{text "?G'"}, because @{text "?G'"} does not depend on @{text x}.
  The best we can do is @{text "?G' = \<lambda>s. ?A s \<and> ?B s"}, which so far seems to be good enough
  in our manual proofs.

  The @{method wpc} method will try to treat both preconditions uniformly and fail on @{text "?G'"}.
  Extending @{method wpc} to deal with guards in a non-uniform way would be possible, but would make
  setup for new constants even more messy than it already is. Instead we re-use the general idea
  here (in Eisbach instead of ML), and leave the @{method wpc} setup clean for other uses.
\<close>

section \<open>Helper functions and definitions\<close>

(* The following three definitions are originally by Dan Matichuck from the Eisbach
   CorresK_Method example *)

(* Retrieve a split rule for a target term that is expected to be a case statement. *)
ML \<open>
fun get_split_rule ctxt target =
let
  val (hdTarget, args) = strip_comb (Envir.eta_contract target)
  val (constNm, _) = dest_Const hdTarget
  val constNm_fds = String.fields (fn c => c = #".") constNm

  val _ = if String.isPrefix "case_" (List.last constNm_fds) then ()
          else raise TERM ("Not a case statement", [target])

  val typeNm = (String.concatWith "." o rev o tl o rev) constNm_fds
  val split = Proof_Context.get_thm ctxt (typeNm ^ ".split")
  val vars = Term.add_vars (Thm.prop_of split) []

  val datatype_name = List.nth (rev constNm_fds, 1)

  fun T_is_datatype (Type (nm, _)) = (Long_Name.base_name nm = Long_Name.base_name datatype_name)
    | T_is_datatype _ = false

  val datatype_var =
    case find_first (fn ((_, _), T') => T_is_datatype T') vars of
      SOME (ix, _) => ix
    | NONE => error ("Couldn't find datatype in thm: " ^ datatype_name)

  val split' = Drule.infer_instantiate ctxt
                                       [(datatype_var, Thm.cterm_of ctxt (List.last args))] split

in SOME split' end
handle TERM _ => NONE;
\<close>

(* The above function as an attribute. The term argument is expected to be a case statement. *)
attribute_setup get_split_rule = \<open>Args.term >>
  (fn t => Thm.rule_attribute [] (fn context => fn _ =>
      case get_split_rule (Context.proof_of context) t of
        SOME thm => thm
      | NONE => Drule.free_dummy_thm))\<close>

(* Apply a split rule to a goal. Example usage:

   apply_split f "\<lambda>f. corres_underlying sr nf nf' r P P' f f'"

   The first (free) f is expected to be a case statement and is used to extract the split rule.
   The second term is expected to take this f as a parameter and provide the term context of the
   case statement in the goal so the split rule is applied to the correct occurrence of the case
   statement.
*)
method apply_split for f :: 'a and R :: "'a \<Rightarrow> bool" =
    (match [[get_split_rule f]] in U: "(?x :: bool) = ?y" \<Rightarrow>
      \<open>match U[THEN iffD2] in U': "\<And>H. ?A \<Longrightarrow> H (?z :: 'c)" \<Rightarrow>
        \<open>match (R) in "R' :: 'c \<Rightarrow> bool" for R' \<Rightarrow>
          \<open>rule U'[where H=R']\<close>\<close>\<close>)

context
begin

(* This predicate provides an abstraction for guard/precondition terms for transformations
   on those guards.

   P and P' are the abstract and concrete preconditions before the transformation
   Q and Q' are the abstract and concrete preconditions after the transformation

   R is the predicate to be transformed.
*)
private definition corres_case_helper ::
  "(('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool)) \<Rightarrow> (('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool)) \<Rightarrow> bool \<Rightarrow> bool" where
  "corres_case_helper \<equiv> \<lambda>(P, P') (Q, Q') R. (\<forall>s. P s \<longrightarrow> Q s) \<longrightarrow>  (\<forall>s. P' s \<longrightarrow> Q' s) \<longrightarrow> R"


(* The following lemmas enable us to lift preconditions of corres_case_helper over conjunction,
   universal quantifiers, and implication. Note that there are strong versions for forall/implies
   where both guards are treated uniformly, and weak versions, where forall/implies is dropped
   in one guard, but not the other.

   The collection of the lemmas below is used to process the term R in corres_case_helper and
   create appropriately lifted guard/preconditions during that procedure. The names and general
   idea are from the WPC theory.
*)

private lemma corres_case_helperI:
  "corres_case_helper (P, P') (P, P') R \<Longrightarrow> R"
  by (simp add: corres_case_helper_def)

private lemma corres_case_conj_process:
  "\<lbrakk> corres_case_helper (P, P') (A, A') R; corres_case_helper (P, P') (B, B') S \<rbrakk>
   \<Longrightarrow> corres_case_helper (P, P') (\<lambda>s. A s \<and> B s, \<lambda>s. A' s \<and> B' s) (R \<and> S)"
  by (clarsimp simp add: corres_case_helper_def)

private lemma corres_case_all_process:
  "\<lbrakk> \<And>x. corres_case_helper (P, P') (Q x, Q' x) (R x) \<rbrakk>
   \<Longrightarrow> corres_case_helper (P, P') (\<lambda>s. \<forall>x. Q x s, \<lambda>s. \<forall>x. Q' x s) (\<forall>x. R x)"
  by (clarsimp simp: corres_case_helper_def subset_iff)

private lemma corres_case_all_process_weak:
  "\<lbrakk> \<And>x. corres_case_helper (P, P') (Q x, Q') (R x) \<rbrakk>
   \<Longrightarrow> corres_case_helper (P, P') (\<lambda>s. \<forall>x. Q x s, Q') (\<forall>x. R x)"
  by (clarsimp simp: corres_case_helper_def subset_iff)

private lemma corres_case_imp_process:
  "\<lbrakk> S \<Longrightarrow> corres_case_helper (P, P') (Q, Q') R \<rbrakk>
   \<Longrightarrow> corres_case_helper (P, P') (\<lambda>s. S \<longrightarrow> Q s, \<lambda>s. S \<longrightarrow> Q' s) (S \<longrightarrow> R)"
  by (clarsimp simp add: corres_case_helper_def subset_iff)

private lemma corres_case_imp_process_weak:
  "\<lbrakk> S \<Longrightarrow> corres_case_helper (P, P') (Q, Q') R \<rbrakk>
   \<Longrightarrow> corres_case_helper (P, P') (\<lambda>s. S \<longrightarrow> Q s, Q') (S \<longrightarrow> R)"
  by (clarsimp simp add: corres_case_helper_def subset_iff)

private lemmas corres_case_process =
  corres_case_conj_process corres_case_all_process corres_case_imp_process

private lemmas corres_case_process_weak =
  corres_case_conj_process corres_case_all_process_weak corres_case_imp_process_weak

(* Turn goals of the form

   (\<forall>y. x = SomeConstr y \<longrightarrow> corres (?P x) P' (SomeConstr y) g) \<and>
   (\<forall>y. x = OtherConstr y \<longrightarrow> corres (?P x) P' (OtherConstr y) g) \<and>
   ...

   into multiple goals of the form

   \<And>y. x = SomeConstr y \<Longrightarrow> corres (?P1 x y) ?P'1 (SomeConstr y) g)
   \<And>y. x = OtherConstr y \<Longrightarrow> corres (?P2 x y) ?P'2 (OtherConstr y) g)

   with instantiations

   ?P x = \<lambda>s. (\<forall>y. x = SomeConstr y \<longrightarrow> ?P1 x y s) \<and> (\<forall>y. x = OtherConstr y \<longrightarrow> ?P2 x y s)
   ?P' = \<lambda>s. ?P'1 s \<and> ?P'2 s

   We do this by first transforming the goal into a corres_case_helper goal, and then applying
   the corresponding lifting rules. We first try to get both sides (?P and ?P') to have
   quantifiers and implications to get a stronger statement, and fall back to the weaker \<and> for ?P'
   shown above when that doesn't work (e.g. because ?P' might not depend on x).

   When all lifting rules have applied, we transform the goal back into a corres goal using the
   provided helper rule (e.g. corres_case_helper_corres_left below).
*)
private method corres_cases_body uses helper =
  determ \<open>rule corres_case_helperI, repeat_new \<open>rule corres_case_process\<close>; rule helper
          | rule corres_case_helperI, repeat_new \<open>rule corres_case_process_weak\<close>; rule helper\<close>


(* Instances of corres_case_helper for left and right side of the corres predicate.
   These lemmas bind the corres guards to the corres_case_helper guards. *)
private lemma corres_case_helper_corres_left:
  "corres_underlying sr nf nf' r Q Q' f f' \<Longrightarrow>
    corres_case_helper (P, P') (Q, Q') (corres_underlying sr nf nf' r P P' f f')"
  by (auto simp: corres_case_helper_def elim!: corres_guard_imp)

private lemma corres_case_helper_corres_right:
  "corres_underlying sr nf nf' r Q' Q f f' \<Longrightarrow>
    corres_case_helper (P, P') (Q, Q') (corres_underlying sr nf nf' r P' P f f')"
  by (auto simp: corres_case_helper_def elim!: corres_guard_imp)


section \<open>Main method definitions\<close>

(* Case distinction on abstract side *)
method corres_cases_left =
  determ \<open>
    corres_pre,
    (match conclusion in
      "corres_underlying sr nf nf' r P P' (f >>= g) f'" for sr nf nf' r P P' f g f'
         \<Rightarrow> \<open>apply_split f "\<lambda>f. corres_underlying sr nf nf' r P P' (f >>= g) f'"\<close>
     \<bar> "corres_underlying sr nf nf' r P P' (f >>=E g) f'" for sr nf nf' r P P' f g f'
         \<Rightarrow> \<open>apply_split f "\<lambda>f. corres_underlying sr nf nf' r P P' (f >>=E g) f'"\<close>
     \<bar>  "corres_underlying sr nf nf' r P P' f f'" for sr nf nf' r P P' f f'
         \<Rightarrow> \<open>apply_split f "\<lambda>f. corres_underlying sr nf nf' r P P' f f'"\<close>),
    corres_cases_body helper: corres_case_helper_corres_left\<close>

(* case distinction on concrete side *)
method corres_cases_right =
  determ \<open>
    corres_pre,
    (match conclusion in
      "corres_underlying sr nf nf' r P P' f (f' >>= g)" for sr nf nf' r P P' f g f'
         \<Rightarrow> \<open>apply_split f' "\<lambda>f'. corres_underlying sr nf nf' r P P' f (f' >>= g)"\<close>
     \<bar> "corres_underlying sr nf nf' r P P' f (f' >>=E g)" for sr nf nf' r P P' f g f'
         \<Rightarrow> \<open>apply_split f' "\<lambda>f'. corres_underlying sr nf nf' r P P' f (f' >>=E g)"\<close>
     \<bar>  "corres_underlying sr nf nf' r P P' f f'" for sr nf nf' r P P' f f'
         \<Rightarrow> \<open>apply_split f' "\<lambda>f'. corres_underlying sr nf nf' r P P' f f'"\<close>),
     corres_cases_body helper: corres_case_helper_corres_right\<close>

(* single case distinction on either left or right, whichever works first *)
method corres_cases = corres_cases_left | corres_cases_right

(* Case distinction on abstract and concrete side with quadractic blowup, but attempt to solve
   contradictory side conditions by simp. Cases that are solved by simp will produce \<top> as guard
   so that no free schematics are introduced into later goals. *)
method corres_cases_both uses simp =
  (* corres_pre first, so that the ";" later only refers to corres goals, not the final implications *)
  determ \<open>
    corres_pre,
    (corres_cases_left; corres_cases_right;
     (solves \<open>rule corres_inst[where P=\<top> and P'=\<top>], simp add: simp\<close>)?)\<close>

end


section \<open>Examples and tests\<close>

experiment
begin

(* abstract side *)
lemma "corres_underlying srel nf nf' rrel (G x) G' (case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) m"
  (* produces strong (forall, implies) guard conditions in the final implications for both sides *)
  apply corres_cases
  oops

schematic_goal
  "\<And>x. corres_underlying srel nf nf' rrel (?G x) ?G' (case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) m"
  (* produces weak (just ?A \<and> ?B) guard conditions for concrete side, because ?G' does not
     depend on "x", on which we do the case distinction *)
  apply corres_cases
  oops

(* abstract side, with bind *)
lemma "corres_underlying srel nf nf' rrel G G' ((case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) >>= g) m"
  apply corres_cases
  oops

(* abstract side, with bindE *)
lemma "corres_underlying srel nf nf' rrel G G' ((case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) >>=E g) m"
  apply corres_cases
  oops

(* concrete side: *)
lemma "corres_underlying srel nf nf' rrel G G' m (case x of None \<Rightarrow> a | Some y \<Rightarrow> b y)"
  apply corres_cases
  oops

schematic_goal
  "\<And>x. corres_underlying srel nf nf' rrel ?G (?G' x) m (case x of None \<Rightarrow> a | Some y \<Rightarrow> b y)"
  apply corres_cases
  oops

lemma "corres_underlying srel nf nf' rrel G G' m ((case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) >>= g)"
  apply corres_cases
  oops

lemma "corres_underlying srel nf nf' rrel G G' m ((case x of None \<Rightarrow> a | Some y \<Rightarrow> b y) >>=E g)"
  apply corres_cases
  oops

(* both sides: *)
lemma "corres_underlying srel nf nf' rrel G G' (case x of None \<Rightarrow> a | Some y \<Rightarrow> b)
                                               (case x of None \<Rightarrow> a' | Some y \<Rightarrow> b' y)"
  (* two cases remain (both None, both Some); eliminated cases have guard \<top> in final implication *)
  apply corres_cases_both
  oops

schematic_goal
  "\<And>x y. corres_underlying srel nf nf' rrel (?G x) (?G' y) (case x of None \<Rightarrow> a | Some y \<Rightarrow> b)
                                                           (case y of None \<Rightarrow> a' | Some y \<Rightarrow> b' y)"
  (* 4 cases remain, because none are contradictory *)
  apply corres_cases_both
  oops

(* some example relation between abstract and concrete values *)
definition
  "none_rel x y \<equiv> (x = None) = (y = None)"

lemma
  "none_rel x y \<Longrightarrow>
   corres_underlying srel nf nf' rrel G G' (case x of None \<Rightarrow> a | Some y \<Rightarrow> b)
                                            (case y of None \<Rightarrow> a' | Some y \<Rightarrow> b' y)"
  (* two cases remain, none_rel is untouched in the cases that remain, but unfolded in the
     ones that were eliminated *)
  apply (corres_cases_both simp: none_rel_def)
  oops

end

end