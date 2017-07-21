(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WPC
imports "WP_Pre"
keywords "wpc_setup" :: thy_decl

begin

definition
  wpc_helper :: "(('a \<Rightarrow> bool) \<times> 'b set)
                 \<Rightarrow> (('a \<Rightarrow> bool) \<times> 'b set) \<Rightarrow> bool \<Rightarrow> bool" where
 "wpc_helper \<equiv> \<lambda>(P, P') (Q, Q') R. ((\<forall>s. P s \<longrightarrow> Q s) \<and> P' \<subseteq> Q') \<longrightarrow> R"

lemma wpc_conj_process:
  "\<lbrakk> wpc_helper (P, P') (A, A') C; wpc_helper (P, P') (B, B') D \<rbrakk>
       \<Longrightarrow> wpc_helper (P, P') (\<lambda>s. A s \<and> B s, A' \<inter> B') (C \<and> D)"
  by (clarsimp simp add: wpc_helper_def)

lemma wpc_all_process:
  "\<lbrakk> \<And>x. wpc_helper (P, P') (Q x, Q' x) (R x) \<rbrakk>
       \<Longrightarrow> wpc_helper (P, P') (\<lambda>s. \<forall>x. Q x s, {s. \<forall>x. s \<in> Q' x}) (\<forall>x. R x)"
  by (clarsimp simp: wpc_helper_def subset_iff)

lemma wpc_all_process_very_weak:
  "\<lbrakk> \<And>x. wpc_helper (P, P') (Q, Q') (R x) \<rbrakk> \<Longrightarrow> wpc_helper (P, P') (Q, Q') (\<forall>x. R x)"
  by (clarsimp simp: wpc_helper_def)

lemma wpc_imp_process:
  "\<lbrakk> Q \<Longrightarrow> wpc_helper (P, P') (R, R') S \<rbrakk>
        \<Longrightarrow> wpc_helper (P, P') (\<lambda>s. Q \<longrightarrow> R s, {s. Q \<longrightarrow> s \<in> R'}) (Q \<longrightarrow> S)"
  by (clarsimp simp add: wpc_helper_def subset_iff)

lemma wpc_imp_process_weak:
  "\<lbrakk> wpc_helper (P, P') (R, R') S \<rbrakk> \<Longrightarrow> wpc_helper (P, P') (R, R') (Q \<longrightarrow> S)"
  by (clarsimp simp add: wpc_helper_def)

lemmas wpc_processors
  = wpc_conj_process wpc_all_process wpc_imp_process
lemmas wpc_weak_processors
  = wpc_conj_process wpc_all_process wpc_imp_process_weak
lemmas wpc_vweak_processors
  = wpc_conj_process wpc_all_process_very_weak wpc_imp_process_weak

lemma wpc_helperI:
  "wpc_helper (P, P') (P, P') Q \<Longrightarrow> Q"
  by (simp add: wpc_helper_def)

lemma wpc_foo: "\<lbrakk> undefined x; False \<rbrakk> \<Longrightarrow> P x"
  by simp

lemma foo:
  assumes foo_elim: "\<And>P Q h. \<lbrakk> foo Q h; \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> foo P h"
  shows
  "\<lbrakk> \<And>x. foo (Q x) (f x); foo R g \<rbrakk> \<Longrightarrow>
      foo (\<lambda>s. (\<forall>x. Q x s) \<and> (y = None \<longrightarrow> R s))
         (case y of Some x \<Rightarrow> f x | None \<Rightarrow> g)"
  by (auto split: option.split intro: foo_elim)

ML {*

signature WPC = sig
  exception WPCFailed of string * term list * thm list;

  val foo_thm: thm;
  val iffd2_thm: thm;
  val wpc_helperI: thm;

  val instantiate_concl_pred: Proof.context -> cterm -> thm -> thm;

  val detect_term: Proof.context -> thm -> cterm -> (cterm * term) list;
  val detect_terms: Proof.context -> (term -> cterm -> thm -> tactic) -> tactic;

  val split_term: thm list -> Proof.context -> term -> cterm -> thm -> tactic;

  val wp_cases_tac: thm list -> Proof.context -> tactic;
  val wp_debug_tac: thm list -> Proof.context -> tactic;
  val wp_cases_method: thm list -> (Proof.context -> Method.method) context_parser;

end;

structure WPCPredicateAndFinals = Theory_Data
(struct
    type T = (cterm * thm) list
    val empty = []
    val extend = I
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

  val thm2            = Thm.instantiate ([(thm_pred_tvar, pred_tvar)], []) thm;

  val thm2_pred       = Term.dest_Var (get_concl_pred thm2);
in
  Thm.instantiate ([], [(thm2_pred, pred)]) thm2
end;

fun detect_term ctxt thm tm =
let
  val foo_thm_tm   = instantiate_concl_pred ctxt tm foo_thm;
  val matches      = resolve_tac ctxt [foo_thm_tm] 1 thm;
  val outcomes     = Seq.list_of matches;
  val get_goalterm = (HOLogic.dest_Trueprop o Logic.strip_assums_concl
                       o Envir.beta_eta_contract o hd o Thm.prems_of);
  val get_argument = hd o snd o strip_comb;
in
  map (pair tm o get_argument o get_goalterm) outcomes
end;

fun detect_terms ctxt tactic2 thm =
let
  val pfs           = WPCPredicateAndFinals.get (Proof_Context.theory_of ctxt);
  val detects       = map (fn (tm, rl) => (detect_term ctxt thm tm, rl)) pfs;
  val detects2      = filter (not o null o fst) detects;
  val ((pred, arg), fin)   = case detects2 of
                                [] => raise WPCFailed ("detect_terms: no match", [], [thm])
                               | ((d3, fin) :: _) => (hd d3, fin)
in
  tactic2 arg pred fin thm
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

fun split_term processors ctxt target pred fin t =
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
 ((resolve_tac ctxt [subst2] 1)
    THEN
  (resolve_tac ctxt [wpc_helperI] 1)
    THEN
  (REPEAT_ALL_NEW (resolve_tac ctxt processors)
     THEN_ALL_NEW
   resolve_single_tac ctxt [fin]) 1
 ) t
end;

(* n.b. need to concretise the lazy sequence via a list to ensure exceptions
  have been raised already and catch them *)
fun wp_cases_tac processors ctxt thm =
  detect_terms ctxt (split_term processors ctxt) thm
      |> Seq.list_of |> Seq.of_list
    handle WPCFailed _ => no_tac thm;

fun wp_debug_tac processors ctxt thm =
  detect_terms ctxt (split_term processors ctxt) thm
      |> Seq.list_of |> Seq.of_list
    handle WPCFailed e => (warning (@{make_string} (WPCFailed e)); no_tac thm);

fun wp_cases_method processors = Scan.succeed (fn ctxt =>
  Method.SIMPLE_METHOD (wp_cases_tac processors ctxt));

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
        "Add wpc stuff"
        (P.term -- P.name >> (fn (tm, thm) => Toplevel.local_theory NONE NONE (add_wpc tm thm)))

end;
end;

*}

ML {*

val wp_cases_tactic_weak = WeakestPreCases.wp_cases_tac @{thms wpc_weak_processors};
val wp_cases_method_strong = WeakestPreCases.wp_cases_method @{thms wpc_processors};
val wp_cases_method_weak   = WeakestPreCases.wp_cases_method @{thms wpc_weak_processors};
val wp_cases_method_vweak  = WeakestPreCases.wp_cases_method @{thms wpc_vweak_processors};

*}

method_setup wpc0 = {* wp_cases_method_strong *}
  "case splitter for weakest-precondition proofs"

method_setup wpcw0 = {* wp_cases_method_weak *}
  "weak-form case splitter for weakest-precondition proofs"

method wpc = (wp_pre, wpc0)
method wpcw = (wp_pre, wpcw0)

definition
  wpc_test :: "'a set \<Rightarrow> ('a \<times> 'b) set \<Rightarrow> 'b set \<Rightarrow> bool"
  where
 "wpc_test P R S \<equiv> (R `` P) \<subseteq> S"

lemma wpc_test_weaken:
  "\<lbrakk> wpc_test Q R S; P \<subseteq> Q \<rbrakk> \<Longrightarrow> wpc_test P R S"
  by (simp add: wpc_test_def, blast)

lemma wpc_helper_validF:
  "wpc_test Q' R S \<Longrightarrow> wpc_helper (P, P') (Q, Q') (wpc_test P' R S)"
  by (simp add: wpc_test_def wpc_helper_def, blast)

setup {*

let
  val tm  = Thm.cterm_of @{context} (Logic.varify_global @{term "\<lambda>R. wpc_test P R S"});
  val thm = @{thm wpc_helper_validF};
in
  WPCPredicateAndFinals.map (fn xs => (tm, thm) :: xs)
end;

*}

lemma set_conj_Int_simp:
  "{s \<in> S. P s} = S \<inter> {s. P s}"
  by auto

lemma case_options_weak_wp:
  "\<lbrakk> wpc_test P R S; \<And>x. wpc_test P' (R' x) S \<rbrakk>
    \<Longrightarrow> wpc_test (P \<inter> P') (case opt of None \<Rightarrow> R | Some x \<Rightarrow> R' x) S"
  apply (rule wpc_test_weaken)
   apply wpcw
    apply assumption
   apply assumption
  apply simp
  done


end
