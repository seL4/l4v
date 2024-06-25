(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WPC
imports "WP_Pre"
keywords "wpc_setup" :: thy_decl
begin

(* Case splitting method producing independent guards (preconditions) for each case in a
   datatype case split. The current setup can handle judgements such as valid, corres, or ccorres
   with up to two independent predicate guards and one independent set-type guard. Unneeded guards
   can be ignored in setup.

   The helper predicate unifies the treatment of guards in the proof method. The P guards will be
   transformed into Q guards in each branch of the case. The R is the judgement (valid, corres, etc).

   The helper predicate encodes that the judgement supports a standard guard weakening rule,
   from which rules for conjunction-lifting and forall-lifting follow below. These are then used
   by the tactic to generate assumptions of the form "\<forall>y. x = SomeConstructor y \<longrightarrow> P y".

   If more or other types of guards are needed, add them to the helper predicate and re-prove the
   processing rules below. *)
definition wpc_helper ::
  "('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> 'c set \<Rightarrow> ('a \<Rightarrow> bool) \<times> ('b \<Rightarrow> bool) \<times> 'c set \<Rightarrow> bool \<Rightarrow> bool"
  where
  "wpc_helper \<equiv> \<lambda>(P, P', P'') (Q, Q', Q'') R.
                  (\<forall>s. P s \<longrightarrow> Q s) \<and> (\<forall>s. P' s \<longrightarrow> Q' s) \<and> P'' \<subseteq> Q'' \<longrightarrow> R"

lemma wpc_conj_process:
  "\<lbrakk> wpc_helper (P, P', P'') (A, A', A'') C; wpc_helper (P, P', P'') (B, B', B'') D \<rbrakk>
   \<Longrightarrow> wpc_helper (P, P', P'') (\<lambda>s. A s \<and> B s, \<lambda>s. A' s \<and> B' s, A'' \<inter> B'') (C \<and> D)"
  by (clarsimp simp add: wpc_helper_def)

lemma wpc_all_process:
  "\<lbrakk> \<And>x. wpc_helper (P, P', P'') (Q x, Q' x, Q'' x) (R x) \<rbrakk>
   \<Longrightarrow> wpc_helper (P, P', P'') (\<lambda>s. \<forall>x. Q x s, \<lambda>s. \<forall>x. Q' x s, {s. \<forall>x. s \<in> Q'' x}) (\<forall>x. R x)"
  by (clarsimp simp: wpc_helper_def subset_iff)

lemma wpc_all_process_very_weak:
  "\<lbrakk> \<And>x. wpc_helper (P, P', P'') (Q, Q', Q'') (R x) \<rbrakk>
   \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') (\<forall>x. R x)"
  by (clarsimp simp: wpc_helper_def)

lemma wpc_imp_process:
  "\<lbrakk> Q \<Longrightarrow> wpc_helper (P, P', P'') (R, R', R'') S \<rbrakk>
   \<Longrightarrow> wpc_helper (P, P', P'') (\<lambda>s. Q \<longrightarrow> R s, \<lambda>s. Q \<longrightarrow> R' s, {s. Q \<longrightarrow> s \<in> R''}) (Q \<longrightarrow> S)"
  by (clarsimp simp add: wpc_helper_def subset_iff)

lemma wpc_imp_process_weak:
  "\<lbrakk> wpc_helper (P, P', P'') (R, R', R'') S \<rbrakk> \<Longrightarrow> wpc_helper (P, P', P'') (R, R', R'') (Q \<longrightarrow> S)"
  by (clarsimp simp add: wpc_helper_def)

lemmas wpc_processors       = wpc_conj_process wpc_all_process wpc_imp_process
lemmas wpc_weak_processors  = wpc_conj_process wpc_all_process wpc_imp_process_weak
lemmas wpc_vweak_processors = wpc_conj_process wpc_all_process_very_weak wpc_imp_process_weak

lemma wpc_helperI:
  "wpc_helper (P, P', P'') (P, P', P'') Q \<Longrightarrow> Q"
  by (simp add: wpc_helper_def)

lemma wpc_foo: "\<lbrakk> undefined x; False \<rbrakk> \<Longrightarrow> P x"
  by simp

ML \<open>
signature WPC = sig
  exception WPCFailed of string * term list * thm list;

  val foo_thm: thm;
  val iffd2_thm: thm;
  val wpc_helperI: thm;

  val instantiate_concl_pred: Proof.context -> cterm -> thm -> thm;

  val detect_term: Proof.context -> int -> thm -> cterm -> (cterm * term) list;
  val detect_terms: Proof.context -> (term -> cterm -> thm -> int -> tactic) -> int -> tactic;

  val split_term: thm list -> Proof.context -> term -> cterm -> thm -> int -> tactic;

  val wp_cases_tac: thm list -> Proof.context -> int -> tactic;
  val wp_debug_tac: thm list -> Proof.context -> int -> tactic;
  val wp_cases_method: thm list -> (Proof.context -> Method.method) context_parser;

end;

structure WPCPredicateAndFinals = Theory_Data
(struct
    type T = (cterm * thm) list
    val empty = []
    fun merge (xs, ys) =
        (* Order of predicates is important, so we can't reorder *)
        let val tms = map (Thm.term_of o fst) xs
            fun inxs x = exists (fn y => x aconv y) tms
            val ys' = filter (not o inxs o Thm.term_of o fst) ys
        in
            xs @ ys'
        end
end);

structure WeakestPreCases : WPC =
struct

exception WPCFailed of string * term list * thm list;

val iffd2_thm = @{thm "iffD2"};
val wpc_helperI = @{thm "wpc_helperI"};
val foo_thm = @{thm "wpc_foo"};

(* it looks like cterm_instantiate would do the job better,
   but this handles the case where ?'a must be instantiated
   to ?'a \<times> ?'b *)
fun instantiate_concl_pred ctxt pred thm =
let
  val get_concl_pred  = (fst o strip_comb o HOLogic.dest_Trueprop o Thm.concl_of);
  val get_concl_predC = (Thm.cterm_of ctxt o get_concl_pred);

  val get_pred_tvar   = domain_type o Thm.typ_of o Thm.ctyp_of_cterm;
  val thm_pred        = get_concl_predC thm;
  val thm_pred_tvar   = Term.dest_TVar (get_pred_tvar thm_pred);
  val pred_tvar       = Thm.ctyp_of ctxt (get_pred_tvar pred);

  val thm2            = Thm.instantiate (TVars.make [(thm_pred_tvar, pred_tvar)], Vars.empty) thm;

  val thm2_pred       = Term.dest_Var (get_concl_pred thm2);
in
  Thm.instantiate (TVars.empty, Vars.make [(thm2_pred, pred)]) thm2
end;

fun detect_term ctxt n thm tm =
let
  val foo_thm_tm   = instantiate_concl_pred ctxt tm foo_thm;
  val matches      = resolve_tac ctxt [foo_thm_tm] n thm;
  val outcomes     = Seq.list_of matches;
  val get_goalterm = (HOLogic.dest_Trueprop o Logic.strip_assums_concl
                       o Envir.beta_eta_contract o hd o Thm.prems_of);
  val get_argument = hd o snd o strip_comb;
in
  map (pair tm o get_argument o get_goalterm) outcomes
end;

fun detect_terms ctxt tactic2 n thm =
let
  val pfs           = WPCPredicateAndFinals.get (Proof_Context.theory_of ctxt);
  val detects       = map (fn (tm, rl) => (detect_term ctxt n thm tm, rl)) pfs;
  val detects2      = filter (not o null o fst) detects;
  val ((pred, arg), fin)   = case detects2 of
                                [] => raise WPCFailed ("detect_terms: no match", [], [thm])
                               | ((d3, fin) :: _) => (hd d3, fin)
in
  tactic2 arg pred fin n thm
end;

(* give each rule in the list one possible resolution outcome *)
fun resolve_each_once_tac ctxt thms i
    = fold (curry (op APPEND'))
        (map (DETERM oo resolve_tac ctxt o single) thms)
        (K no_tac) i

fun resolve_single_tac ctxt rules n thm =
  case Seq.chop 2 (resolve_each_once_tac ctxt rules n thm)
  of ([], _) => raise WPCFailed
                        ("resolve_single_tac: no rules could apply",
                         [], thm :: rules)
   | (_ :: _ :: _, _) => raise WPCFailed
                        ("resolve_single_tac: multiple rules applied",
                         [], thm :: rules)
   | ([x], _) => Seq.single x;

fun split_term processors ctxt target pred fin =
let
  val hdTarget      = head_of target;
  val (constNm, _)  = dest_Const hdTarget handle TERM (_, tms)
                       => raise WPCFailed ("split_term: couldn't dest_Const", tms, []);
  val split = case (Ctr_Sugar.ctr_sugar_of_case ctxt constNm) of
      SOME sugar => #split sugar
    | _ => raise WPCFailed ("split_term: not a case", [hdTarget], []);
  val subst         = split RS iffd2_thm;
  val subst2        = instantiate_concl_pred ctxt pred subst;
in
  resolve_tac ctxt [subst2]
  THEN' resolve_tac ctxt [wpc_helperI]
  THEN' (REPEAT_ALL_NEW (resolve_tac ctxt processors) THEN_ALL_NEW resolve_single_tac ctxt [fin])
end;

(* n.b. need to concretise the lazy sequence via a list to ensure exceptions
  have been raised already and catch them *)
fun wp_cases_tac processors ctxt n thm =
  detect_terms ctxt (split_term processors ctxt) n thm
      |> Seq.list_of |> Seq.of_list
    handle WPCFailed _ => no_tac thm;

fun wp_debug_tac processors ctxt n thm =
  detect_terms ctxt (split_term processors ctxt) n thm
      |> Seq.list_of |> Seq.of_list
    handle WPCFailed e => (warning (@{make_string} (WPCFailed e)); no_tac thm);

fun wp_cases_method processors = Scan.succeed (fn ctxt =>
  Method.SIMPLE_METHOD' (wp_cases_tac processors ctxt));

local structure P = Parse and K = Keyword in

fun add_wpc tm thm lthy = let
  val ctxt = Local_Theory.target_of lthy
  val tm' = (Syntax.read_term ctxt tm) |> Thm.cterm_of ctxt o Logic.varify_global
  val thm' = Proof_Context.get_thm ctxt thm
in
  Local_Theory.background_theory (WPCPredicateAndFinals.map (fn xs => (tm', thm') :: xs)) lthy
end;

val _ =
    Outer_Syntax.command
        @{command_keyword "wpc_setup"}
        "Add new WPC term and helper rule"
        (P.term -- P.name >> (fn (tm, thm) => Toplevel.local_theory NONE NONE (add_wpc tm thm)))

end;
end;
\<close>

ML \<open>
val wp_cases_tactic_weak   = WeakestPreCases.wp_cases_tac @{thms wpc_weak_processors};
val wp_cases_method_strong = WeakestPreCases.wp_cases_method @{thms wpc_processors};
val wp_cases_method_weak   = WeakestPreCases.wp_cases_method @{thms wpc_weak_processors};
val wp_cases_method_vweak  = WeakestPreCases.wp_cases_method @{thms wpc_vweak_processors};
\<close>

(* Main proof methods: *)
method_setup wpc0 = \<open>wp_cases_method_strong\<close>
  "case splitter for weakest-precondition proofs"

method_setup wpcw0 = \<open>wp_cases_method_weak\<close>
  "weak-form case splitter for weakest-precondition proofs"

(* Instances specifically for wp (introducing schematic guards automatically): *)
method wpc = (wp_pre, wpc0)
method wpcw = (wp_pre, wpcw0)

(* Test and example *)
experiment
begin

(* Assume some kind of judgement wpc_test with a precondition P of type set and a
   precondition Q of type 'a \<Rightarrow> bool: *)
definition wpc_test :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> bool" where
  "wpc_test P Q R S \<equiv> (R `` P) \<subseteq> S"

(* Weakening rule to introduce schematics for the two guards *)
lemma wpc_test_weaken:
  "\<lbrakk> wpc_test Q X' R S; P \<subseteq> Q; \<And>s. X s \<Longrightarrow> X' s \<rbrakk> \<Longrightarrow> wpc_test P X R S"
  by (simp add: wpc_test_def, blast)

(* Setup rule, establishes connection between wpc_helper and judgment wpc_test. The precondition has
   the judgement with transformed (Q) guards, the conclusion has the helper predicate with the
   judgement applied to the original (P) guards. The guard arguments of wpc_helper must be in the
   form below (no arguments or patterns) for the method to work properly.

   Note that this example ignores the first predicate guard P, and only uses P'/P''. Use/leave out
   guards as needed. *)
lemma wpc_helper_validF:
  "wpc_test Q'' Q' R S \<Longrightarrow> wpc_helper (P, P', P'') (Q, Q', Q'') (wpc_test P'' P' R S)"
  by (simp add: wpc_test_def wpc_helper_def) blast

(* Set up the proof method for wpc_test. First parameter is a function that takes the argument
   position on which the case split happens (here R) and returns the judgement. Second parameter
   is the setup rule. *)
wpc_setup "\<lambda>R. wpc_test P X R S" wpc_helper_validF

(* Demo for weak form (wpcw), produces a separate guard for each branch, no implications. *)
lemma case_options_weak_wp:
  "\<lbrakk> wpc_test P X R S; \<And>x. wpc_test P' X' (R' x) S \<rbrakk>
    \<Longrightarrow> wpc_test (P \<inter> P') (\<lambda>s. X s \<and> X' s) (case opt of None \<Rightarrow> R | Some x \<Rightarrow> R' x) S"
  apply (rule wpc_test_weaken)
    apply wpcw
     apply assumption
    apply assumption
   apply simp
  apply simp
  done

(* Demo for strong form (wpc), produces a separate guard for each branch with implications. *)
lemma
  "\<lbrakk> wpc_test P X R S; \<And>x. wpc_test (P' x) (X' x) (R' x) S \<rbrakk>
    \<Longrightarrow> wpc_test (P \<inter> {s. \<forall>x. opt = Some x \<longrightarrow> s \<in> P' x})
                 (\<lambda>s. X s \<and> (\<forall>x. X' x s))
                 (case opt of None \<Rightarrow> R | Some x \<Rightarrow> R' x) S"
  apply (rule wpc_test_weaken)
    apply wpc
     apply assumption
    apply assumption
   apply fastforce
  apply clarsimp
  done

end

end
