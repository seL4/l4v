(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Corres_Method
imports Corres_UL SpecValid_R
begin

(*TODO move this *)

method_setup repeat_new =
 \<open>Method.text_closure >> (fn m => fn ctxt => fn facts =>
   let
     fun tac i st' =
       Goal.restrict i 1 st'
       |> method_evaluate m ctxt facts
       |> Seq.map (Goal.unrestrict i)

   in SIMPLE_METHOD (SUBGOAL (fn (_,i) => REPEAT_ALL_NEW tac i) 1) facts end)
\<close>

chapter \<open>Corres Methods\<close>

section \<open>Boilerplate\<close>

context begin

private definition "my_true \<equiv> True"

private lemma my_true: "my_true" by (simp add: my_true_def)

method no_schematic_concl = (fails \<open>rule my_true\<close>)

end

definition
  "corres_underlyingK sr nf nf' F r Q Q' f g \<equiv>
    F \<longrightarrow> corres_underlying sr nf nf' r Q Q' f g"

lemma corresK_name_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; P' s'; F; (s, s') \<in> sr \<rbrakk>
                 \<Longrightarrow> corres_underlyingK sr nf nf' F r ((=) s) ((=) s') f g \<rbrakk>
        \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' f g"
  apply (clarsimp simp add: corres_underlyingK_def)
  apply (rule corres_name_pre)
  apply blast
  done

lemma corresK_assume_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; P' s'; F; (s, s') \<in> sr \<rbrakk>
                 \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' f g \<rbrakk>
        \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' f g"
  apply (clarsimp simp add: corres_underlyingK_def)
  apply (rule corres_assume_pre)
  apply blast
  done

lemma corresK_drop_any_guard:
  "corres_underlying sr nf nf' r Q Q' f g \<Longrightarrow> corres_underlyingK sr nf nf' F r Q Q' f g"
  by (simp add: corres_underlyingK_def)

lemma corresK_assume_guard:
  "(F \<Longrightarrow> corres_underlying sr nf nf' r Q Q' f g) \<Longrightarrow> corres_underlyingK sr nf nf' F r Q Q' f g"
  by (simp add: corres_underlyingK_def)

lemma corresK_unlift:
  "corres_underlyingK sr nf nf' F r Q Q' f g \<Longrightarrow> (F \<Longrightarrow> corres_underlying sr nf nf' r Q Q' f g)"
  by (simp add: corres_underlyingK_def)

lemma corresK_lift:
  "corres_underlying sr nf nf' r Q Q' f g \<Longrightarrow> corres_underlyingK sr nf nf' F r Q Q' f g"
  by (simp add: corres_underlyingK_def)

lemma corresK_lift_rule:
  "corres_underlying sr nf nf' r Q Q' f g \<longrightarrow> corres_underlying sra nfa nfa' ra Qa Qa' fa ga
  \<Longrightarrow> corres_underlyingK sr nf nf' F r Q Q' f g \<longrightarrow> corres_underlyingK sra nfa nfa' F ra Qa Qa' fa ga"
  by (simp add: corres_underlyingK_def)

lemmas corresK_drop = corresK_drop_any_guard[where F=True]

context begin

lemma corresK_start:
  assumes x: "corres_underlyingK sr nf nf' F r Q Q' f g"
  assumes y: "\<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> F \<and> Q s \<and> Q' s'"
  shows      "corres_underlying sr nf nf' r P P' f g"
  using x by (auto simp: y corres_underlying_def corres_underlyingK_def)

lemma corresK_weaken:
  assumes x: "corres_underlyingK sr nf nf' F' r Q Q' f g"
  assumes y: "\<And>s s'. \<lbrakk> P s; P' s'; F; (s, s') \<in> sr \<rbrakk> \<Longrightarrow> F' \<and> Q s \<and> Q' s'"
  shows      "corres_underlyingK sr nf nf' F r P P' f g"
  using x by (auto simp: y corres_underlying_def corres_underlyingK_def)

private lemma corres_trivial:
  "False \<Longrightarrow> corres_underlying sr nf nf' r P P' f f'"
  by simp

method check_corres =
  (succeeds \<open>rule corres_trivial\<close>, fails \<open>rule TrueI\<close>)

private lemma corresK_trivial:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' f f'"
  by simp

(* Ensure we don't apply calculational rules if either function is schematic *)

private definition "dummy_fun \<equiv> undefined"

private lemma corresK_dummy_left:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' dummy_fun f'"
  by simp

private lemma corresK_dummy_right:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' f dummy_fun"
  by simp

method check_corresK =
  (succeeds \<open>rule corresK_trivial\<close>, fails \<open>rule corresK_dummy_left corresK_dummy_right\<close>)

private definition "my_false s \<equiv> False"

private
  lemma corres_my_falseE: "my_false x \<Longrightarrow> P" by (simp add: my_false_def)

method no_schematic_prems = (fails \<open>erule corres_my_falseE\<close>)

private lemma hoare_pre: "\<lbrace>my_false\<rbrace> f \<lbrace>Q\<rbrace>" by (simp add: valid_def my_false_def)
private lemma hoareE_pre: "\<lbrace>my_false\<rbrace> f \<lbrace>Q\<rbrace>,\<lbrace>Q'\<rbrace>" by (simp add: validE_def valid_def my_false_def)
private lemma hoare_E_E_pre: "\<lbrace>my_false\<rbrace> f -,\<lbrace>Q\<rbrace>" by (simp add: validE_E_def validE_def valid_def my_false_def)
private lemma hoare_E_R_pre: "\<lbrace>my_false\<rbrace> f \<lbrace>Q\<rbrace>,-" by (simp add: validE_R_def validE_def valid_def my_false_def)

private lemmas hoare_pres = hoare_pre hoare_pre hoare_E_E_pre hoare_E_R_pre

method schematic_hoare_pre = (succeeds \<open>rule hoare_pres\<close>)

private
  lemma corres_my_false: "corres_underlying sr nf nf' r my_false P f f'"
                         "corres_underlying sr nf nf' r P' my_false f f'"
  by (auto simp add: my_false_def[abs_def] corres_underlying_def)

private
  lemma corresK_my_false: "corres_underlyingK sr nf nf' F r my_false P f f'"
                         "corres_underlyingK sr nf nf' F r P' my_false f f'"
  by (auto simp add: corres_my_false  corres_underlyingK_def)


method corres_raw_pre =
  (check_corres, (fails \<open>rule corres_my_false\<close>, rule corresK_start)?)

lemma corresK_weaken_states:
  "corres_underlyingK sr nf nf' F r Q Q' f g \<Longrightarrow>
    corres_underlyingK sr nf nf' (F \<and> (\<forall>s s'. P s \<longrightarrow> P' s' \<longrightarrow> (s, s') \<in> sr \<longrightarrow> Q s \<and> Q' s'))
     r P P' f g"
  apply (erule corresK_weaken)
  apply simp
  done

private lemma
  corresK_my_falseF:
  "corres_underlyingK sr nf nf' (my_false undefined) r P P' f f'"
  by (simp add: corres_underlyingK_def my_false_def)

method corresK_pre =
  (check_corresK,
    (fails \<open>rule corresK_my_false\<close>,
      ((succeeds \<open>rule corresK_my_falseF\<close>, rule corresK_weaken_states) |
       rule corresK_weaken)))

method corres_pre = (corres_raw_pre | corresK_pre)?

lemma corresK_weakenK:
  "corres_underlyingK sr nf nf' F' r P P' f f' \<Longrightarrow> (F \<Longrightarrow> F') \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' f f'"
  by (simp add: corres_underlyingK_def)

(* Special corres rules which should only be applied when the return value relation is
   concrete, to avoid bare schematics. *)

named_theorems corres_concrete_r and corres_concrete_rER

private lemma corres_r_False:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' F (\<lambda>_. my_false) P P' f f'"
  by simp

private lemma corres_r_FalseE:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' F ((\<lambda>_. my_false) \<oplus> r) P P' f f'"
  by simp

private lemma corres_r_FalseE':
  "False \<Longrightarrow> corres_underlyingK sr nf nf' F (r \<oplus> (\<lambda>_. my_false)) P P' f f'"
  by simp

method corres_concrete_r declares corres_concrete_r corres_concrete_rER =
  (fails \<open>rule corres_r_False corres_r_FalseE corres_r_FalseE'\<close>, determ \<open>rule corres_concrete_r\<close>)
 | (fails \<open>rule corres_r_FalseE\<close>, determ \<open>rule corres_concrete_rER\<close>)


end


section \<open>Corresc - Corres over case statements\<close>

text
 \<open>Based on wpc, corresc examines the split rule for top-level case statements on the left
  and right hand sides, propagating backwards the stateless and left/right preconditions.\<close>

ML \<open>

fun get_split_rule ctxt target =
let
  val (hdTarget,args) = strip_comb (Envir.eta_contract target)
  val (constNm, _)  = dest_Const hdTarget
  val constNm_fds   = (String.fields (fn c => c = #".") constNm)

  val _ = if String.isPrefix "case_" (List.last constNm_fds) then ()
          else raise TERM ("Not a case statement",[target])

  val typeNm        = (String.concatWith "." o rev o tl o rev) constNm_fds;
  val split         = Proof_Context.get_thm ctxt (typeNm ^ ".split");
  val vars = Term.add_vars (Thm.prop_of split) []

  val datatype_name = List.nth (rev constNm_fds,1)

  fun T_is_datatype (Type (nm,_)) = (Long_Name.base_name nm) = (Long_Name.base_name datatype_name)
    | T_is_datatype _ = false

  val datatype_var =
    case (find_first (fn ((_,_),T') => (T_is_datatype T')) vars) of
      SOME (ix,_) => ix
    | NONE => error ("Couldn't find datatype in thm: " ^ datatype_name)

  val split' = Drule.infer_instantiate ctxt
    [(datatype_var, Thm.cterm_of ctxt (List.last args))] split

in
   SOME split' end
   handle TERM _ => NONE;
\<close>

attribute_setup get_split_rule = \<open>Args.term >>
  (fn t => Thm.rule_attribute [] (fn context => fn _ =>
      case (get_split_rule (Context.proof_of context) t) of
        SOME thm => thm
      | NONE => Drule.free_dummy_thm))\<close>

method apply_split for f :: 'a and R :: "'a \<Rightarrow> bool"=
    (match [[get_split_rule f]] in U: "(?x :: bool) = ?y" \<Rightarrow>
      \<open>match U[THEN iffD2] in U': "\<And>H. ?A \<Longrightarrow> H (?z :: 'c)" \<Rightarrow>
        \<open>match (R) in "R' :: 'c \<Rightarrow> bool" for R' \<Rightarrow>
          \<open>rule U'[where H=R']\<close>\<close>\<close>)

definition
  wpc2_helper :: "(('a \<Rightarrow> bool) \<times> 'b set)
                 \<Rightarrow> (('a \<Rightarrow> bool) \<times> 'b set) \<Rightarrow> (('a \<Rightarrow> bool) \<times> 'b set)
                 \<Rightarrow> (('a \<Rightarrow> bool) \<times> 'b set) \<Rightarrow> bool \<Rightarrow> bool" where
 "wpc2_helper \<equiv> \<lambda>(P, P') (Q, Q') (PP, PP') (QQ,QQ') R.
    ((\<forall>s. P s \<longrightarrow> Q s) \<and> P' \<subseteq> Q') \<longrightarrow> ((\<forall>s. PP s \<longrightarrow> QQ s) \<and> PP' \<subseteq> QQ') \<longrightarrow> R"

definition
  "wpc2_protect B Q \<equiv> (Q :: bool)"

lemma wpc2_helperI:
  "wpc2_helper (P, P') (P, P') (PP, PP') (PP, PP') Q \<Longrightarrow> Q"
  by (simp add: wpc2_helper_def)

lemma wpc2_conj_process:
  "\<lbrakk> wpc2_helper (P, P') (A, A') (PP, PP') (AA, AA') C; wpc2_helper (P, P') (B, B') (PP, PP') (BB, BB') D \<rbrakk>
       \<Longrightarrow> wpc2_helper (P, P') (\<lambda>s. A s \<and> B s, A' \<inter> B') (PP, PP') (\<lambda>s. AA s \<and> BB s, AA' \<inter> BB') (C \<and> D)"
  by (clarsimp simp add: wpc2_helper_def)

lemma wpc2_all_process:
  "\<lbrakk> \<And>x. wpc2_helper (P, P') (Q x, Q' x) (PP, PP') (QQ x, QQ' x) (R x) \<rbrakk>
       \<Longrightarrow> wpc2_helper (P, P') (\<lambda>s. \<forall>x. Q x s, {s. \<forall>x. s \<in> Q' x}) (PP, PP') (\<lambda>s. \<forall>x. QQ x s, {s. \<forall>x. s \<in> QQ' x}) (\<forall>x. R x)"
  by (clarsimp simp: wpc2_helper_def subset_iff)

lemma wpc2_imp_process:
  "\<lbrakk> wpc2_protect B Q \<Longrightarrow> wpc2_helper (P, P') (R, R') (PP, PP') (RR, RR') S \<rbrakk>
        \<Longrightarrow> wpc2_helper (P, P') (\<lambda>s. Q \<longrightarrow> R s, {s. Q \<longrightarrow> s \<in> R'}) (PP, PP') (\<lambda>s. Q \<longrightarrow> RR s, {s. Q \<longrightarrow> s \<in> RR'}) (Q \<longrightarrow> S)"
  by (clarsimp simp add: wpc2_helper_def subset_iff wpc2_protect_def)



text \<open>
 Generate quadratic blowup of the case statements on either side of refinement.
 Attempt to discharge resulting contradictions.
\<close>


method corresc_body for B :: bool uses helper =
  determ \<open>(rule wpc2_helperI,
    repeat_new \<open>rule wpc2_conj_process wpc2_all_process wpc2_imp_process[where B=B]\<close> ; (rule helper))\<close>

lemma wpc2_helper_corres_left:
  "corres_underlyingK sr nf nf' QQ r Q A f f' \<Longrightarrow>
    wpc2_helper (P, P') (Q, Q') (\<lambda>_. PP,PP') (\<lambda>_. QQ,QQ') (corres_underlyingK sr nf nf' PP r P A f f')"
  by (clarsimp simp: wpc2_helper_def  corres_underlyingK_def elim!: corres_guard_imp)

method corresc_left_raw =
  determ \<open>(match conclusion in "corres_underlyingK sr nf nf' F r P P' f f'" for sr nf nf' F r P P' f f'
    \<Rightarrow> \<open>apply_split f "\<lambda>f. corres_underlyingK sr nf nf' F r P P' f f'"\<close>,
        corresc_body False helper: wpc2_helper_corres_left)\<close>

lemma wpc2_helper_corres_right:
  "corres_underlyingK sr nf nf' QQ r A Q f f' \<Longrightarrow>
    wpc2_helper (P, P') (Q, Q') (\<lambda>_. PP,PP') (\<lambda>_. QQ,QQ') (corres_underlyingK sr nf nf' PP r A P f f')"
  by (clarsimp simp: wpc2_helper_def corres_underlyingK_def elim!: corres_guard_imp)

method corresc_right_raw =
  determ \<open>(match conclusion in "corres_underlyingK sr nf nf' F r P P' f f'" for sr nf nf' F r P P' f f'
    \<Rightarrow> \<open>apply_split f' "\<lambda>f'. corres_underlyingK sr nf nf' F r P P' f f'"\<close>,
        corresc_body True helper: wpc2_helper_corres_right)\<close>

definition
  "corres_protect r = (r :: bool)"

lemma corres_protect_conj_elim[simp]:
  "corres_protect (a \<and> b) = (corres_protect a \<and> corres_protect b)"
  by (simp add: corres_protect_def)

lemma wpc2_corres_protect:
  "wpc2_protect B Q \<Longrightarrow> corres_protect Q"
  by (simp add: wpc2_protect_def corres_protect_def)

method corresc_left = (corresc_left_raw; (drule wpc2_corres_protect[where B=False]))
method corresc_right = (corresc_right_raw; (drule wpc2_corres_protect[where B=True]))

named_theorems corresc_simp

declare wpc2_protect_def[corresc_simp]
declare corres_protect_def[corresc_simp]

lemma corresK_false_guard_instantiate:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' True r P P' f f'"
  by (simp add: corres_underlyingK_def)

lemma
  wpc_contr_helper:
  "wpc2_protect False (A = B) \<Longrightarrow> wpc2_protect True (A = C) \<Longrightarrow> B \<noteq> C \<Longrightarrow> P"
  by (auto simp: wpc2_protect_def)

method corresc declares corresc_simp =
  (check_corresK, corresc_left_raw; corresc_right_raw;
    ((solves \<open>rule corresK_false_guard_instantiate,
     determ \<open>(erule (1) wpc_contr_helper)?\<close>, simp add: corresc_simp\<close>)
    | (drule wpc2_corres_protect[where B=False], drule wpc2_corres_protect[where B=True])))[1]

section \<open>Corres_rv\<close>

text \<open>Corres_rv is used to propagate backwards the stateless precondition (F) from corres_underlyingK.
  It's main purpose is to defer the decision of where each condition should go: either continue
  through the stateless precondition, or be pushed into the left/right side as a hoare triple.\<close>


(*Don't unfold the definition. Use corres_rv method or associated rules. *)
definition corres_rv :: "bool \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool)
           \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('t, 'b) nondet_monad \<Rightarrow>
            ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "corres_rv F r P P' f f' Q \<equiv>
   F \<longrightarrow> (\<forall>s s'. P s \<longrightarrow> P' s' \<longrightarrow>
    (\<forall>sa rv. (rv, sa) \<in> fst (f s) \<longrightarrow> (\<forall>sa' rv'. (rv', sa') \<in> fst (f' s') \<longrightarrow> r rv rv' \<longrightarrow> Q rv rv')))"

(*Don't unfold the definition. Use corres_rv method or associated rules. *)
definition "corres_rvE_R F r P P' f f' Q \<equiv>
  corres_rv F (\<lambda>_ _. True) P P' f f'
    (\<lambda>rvE rvE'. case (rvE,rvE') of (Inr rv, Inr rv') \<Rightarrow> r rv rv' \<longrightarrow> Q rv rv' | _ \<Rightarrow> True)"

lemma corres_rvD:
  "corres_rv F r P P' f f' Q \<Longrightarrow>
   F \<Longrightarrow> P s \<Longrightarrow> P' s' \<Longrightarrow> (rv,sa) \<in> fst (f s) \<Longrightarrow>
      (rv',sa') \<in> fst (f' s') \<Longrightarrow> r rv rv' \<Longrightarrow> Q rv rv'"
  by (auto simp add: corres_rv_def)

lemma corres_rvE_RD:
  "corres_rvE_R F r P P' f f' Q \<Longrightarrow>
   F \<Longrightarrow> P s \<Longrightarrow> P' s' \<Longrightarrow> (Inr rv,sa) \<in> fst (f s) \<Longrightarrow>
      (Inr rv',sa') \<in> fst (f' s') \<Longrightarrow> r rv rv' \<Longrightarrow> Q rv rv'"
  by (auto simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

lemma corres_rv_prove:
  "(\<And>s s' sa sa' rv rv'. F \<Longrightarrow>
    (rv,sa) \<in> fst (f s) \<Longrightarrow> (rv',sa') \<in> fst (f' s') \<Longrightarrow> P s \<Longrightarrow> P' s' \<Longrightarrow> r rv rv' \<Longrightarrow> Q rv rv') \<Longrightarrow>
    corres_rv F r P P' f f' Q"
  by (auto simp add: corres_rv_def)

lemma corres_rvE_R_prove:
  "(\<And>s s' sa sa' rv rv'. F \<Longrightarrow>
    (Inr rv,sa) \<in> fst (f s) \<Longrightarrow> (Inr rv',sa') \<in> fst (f' s') \<Longrightarrow> P s \<Longrightarrow> P' s' \<Longrightarrow> r rv rv' \<Longrightarrow> Q rv rv') \<Longrightarrow>
    corres_rvE_R F r P P' f f' Q"
  by (auto simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

lemma corres_rv_wp_left:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>rv'. r rv rv' \<longrightarrow> Q rv rv'\<rbrace> \<Longrightarrow> corres_rv True r P \<top> f f' Q"
  by (fastforce simp add: corres_rv_def valid_def)

lemma corres_rvE_R_wp_left:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>rv'. r rv rv' \<longrightarrow> Q rv rv'\<rbrace>, - \<Longrightarrow> corres_rvE_R True r P \<top> f f' Q"
  apply (simp add: corres_rvE_R_def validE_def validE_R_def)
  apply (rule corres_rv_wp_left)
  apply (erule hoare_strengthen_post)
  apply (auto split: sum.splits)
  done

lemma corres_rv_wp_right:
  "\<lbrace>P'\<rbrace> f' \<lbrace>\<lambda>rv' s. \<forall>rv. r rv rv' \<longrightarrow> Q rv rv'\<rbrace> \<Longrightarrow> corres_rv True r \<top> P' f f' Q"
  by (fastforce simp add: corres_rv_def valid_def)

lemma corres_rvE_R_wp_right:
  "\<lbrace>P'\<rbrace> f' \<lbrace>\<lambda>rv' s. \<forall>rv. r rv rv' \<longrightarrow> Q rv rv'\<rbrace>, - \<Longrightarrow> corres_rvE_R True r \<top> P' f f' Q"
  apply (simp add: corres_rvE_R_def validE_def validE_R_def)
  apply (rule corres_rv_wp_right)
  apply (erule hoare_strengthen_post)
  apply (auto split: sum.splits)
  done

lemma corres_rv_weaken:
  "(\<And>rv rv'. Q rv rv' \<Longrightarrow> Q' rv rv') \<Longrightarrow> corres_rv F r P P' f f' Q \<Longrightarrow> corres_rv F r P P' f f' Q'"
  by (auto simp add: corres_rv_def)

lemma corres_rvE_R_weaken:
  "(\<And>rv rv'. Q rv rv' \<Longrightarrow> Q' rv rv') \<Longrightarrow> corres_rvE_R F r P P' f f' Q \<Longrightarrow> corres_rvE_R F r P P' f f' Q'"
  by (auto simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

lemma corres_rv_defer_no_args:
  "corres_rv (\<forall>rv rv'. r rv rv' \<longrightarrow> F) r (\<lambda>_. True) (\<lambda>_. True) f f' (\<lambda>_ _. F)"
  by (auto simp add: corres_rv_def)

lemma corres_rvE_R_defer_no_args:
  "corres_rvE_R (\<forall>rv rv'. r rv rv' \<longrightarrow> F) r (\<lambda>_. True) (\<lambda>_. True) f f' (\<lambda>_ _. F)"
  by (auto simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

(*UNSAFE*)
lemma corres_rv_defer:
  "corres_rv (\<forall>rv rv'. r rv rv' \<longrightarrow> Q rv rv') r (\<lambda>_. True) (\<lambda>_. True) f f' Q"
  by (auto simp add: corres_rv_def)

(*UNSAFE*)
lemma corres_rvE_R_defer:
  "corres_rvE_R (\<forall>rv rv'. r rv rv' \<longrightarrow> Q rv rv') r (\<lambda>_. True) (\<lambda>_. True) f f' Q"
  by (auto simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

lemmas corres_rv_proveT =
  corres_rv_prove[where P=\<top> and P'=\<top> and F=True, simplified]

lemmas corres_rvE_R_proveT =
  corres_rvE_R_prove[where P=\<top> and P'=\<top> and F=True,simplified]

lemma corres_rv_conj_lift:
  "corres_rv F r P PP f g Q \<Longrightarrow> corres_rv F' r P' PP' f g Q' \<Longrightarrow>
    corres_rv (F \<and> F') r (\<lambda>s. P s \<and> P' s) (\<lambda>s'. PP s' \<and> PP' s') f g (\<lambda>rv rv'. Q rv rv' \<and> Q' rv rv')"
   by (clarsimp simp add: corres_rv_def)

lemma corres_rvE_R_conj_lift:
  "corres_rvE_R F r P PP f g Q \<Longrightarrow> corres_rvE_R F' r P' PP' f g Q' \<Longrightarrow>
    corres_rvE_R (F \<and> F') r (\<lambda>s. P s \<and> P' s) (\<lambda>s'. PP s' \<and> PP' s') f g (\<lambda>rv rv'. Q rv rv' \<and> Q' rv rv')"
   by (auto simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

subsection \<open>Corres_rv method\<close>

text \<open>This method propagate corres_rv obligations into each precondition according to the following
heuristic:
 For each conjunct in the obligation:

   1) Try to solve trivially (to handle schematic conditions)
   2) If it does not depend on function return values, propagate it as a stateless precondition
   3) If either side is a corres_noop (used by symbolic execution), propagate as hoare triple
      for other side.
   4) If it can be phrased entirely with variables accessible to the left side, propagate it as
      a left hoare triple.
   5) As in 3) but on the right.

 Fail if any of 1-5 are unsuccessful for any conjunct.

In the case where corres_rv fails, the user will need to intervene, either
by specifying where to defer the obligation or solving the goal in-place.
\<close>

definition "corres_noop = return undefined"

context begin

private lemma corres_rv_defer_left:
  "corres_rv F r (\<lambda>_. \<forall>rv rv'. Q rv rv') P' f f' Q"
  by (simp add: corres_rv_def)

private lemma corres_rvE_R_defer_left:
  "corres_rvE_R F r (\<lambda>_. \<forall>rv rv'. Q rv rv') P' f f' Q"
  by (simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

private lemma corres_rv_defer_right:
  "corres_rv F r P (\<lambda>_. \<forall>rv rv'. Q rv rv') f f' Q"
  by (simp add: corres_rv_def)

private lemma corres_rvE_R_defer_right:
  "corres_rvE_R F r P (\<lambda>_. \<forall>rv rv'. Q rv rv') f f' Q"
  by (simp add: corres_rv_def corres_rvE_R_def split: sum.splits)

lemmas corres_rv_proves =
  corres_rv_proveT corres_rvE_R_proveT

(* Try to handle cases where corres_rv obligations have been left schematic *)
lemmas corres_rv_trivials =
  corres_rv_proves[where Q="\<lambda>_ _. True", OF TrueI]
  corres_rv_proves[where Q="\<lambda>rv rv'. F rv rv' \<longrightarrow> True" for F, # \<open>simp\<close>]
  corres_rv_proves[where Q=r and r=r for r, # \<open>simp\<close>]

lemmas corres_rv_defers =
  corres_rv_defer_no_args corres_rvE_R_defer_no_args

lemmas corres_rv_wp_lefts =
  corres_rv_wp_left corres_rvE_R_wp_left

lemmas corres_rv_wp_rights =
  corres_rv_wp_right corres_rvE_R_wp_right

lemmas corres_rv_noops =
  corres_rv_wp_lefts[where f'=corres_noop] corres_rv_wp_rights[where f=corres_noop]

lemmas corres_rv_lifts' =
  corres_rv_conj_lift corres_rvE_R_conj_lift

lemmas corres_rv_lifts =
  corres_rv_lifts'
  corres_rv_lifts'[where P="\<lambda>_. True" and P'="\<lambda>_. True" and f="corres_noop", simplified]
  corres_rv_lifts'[where PP="\<lambda>_. True" and PP'="\<lambda>_. True" and g="corres_noop", simplified]

lemmas corres_rv_prove_simple =
  corres_rv_proveT[# \<open>thin_tac _, thin_tac _\<close>, simplified]

method corres_rv =
  (((repeat_new \<open>rule corres_rv_trivials corres_rv_lifts\<close>)?);
    ((rule corres_rv_trivials corres_rv_defers corres_rv_noops |
     (succeeds \<open>rule corres_rv_defer_left corres_rvE_R_defer_left\<close>,
      rule corres_rv_wp_lefts) |
     (succeeds \<open>rule corres_rv_defer_right corres_rvE_R_defer_right\<close>,
      rule corres_rv_wp_rights))))

end


section \<open>CorresK Split rules\<close>

text \<open>
 The corresK split allows preconditions to be propagated backward via the extra stateless precondition
 (here given as @{term F}. The head function is propagated backward directly, while the tail
 is propagated via corres_rv. Using the corres_rv method, this condition is then decomposed and
 pushed into the stateless, left, and right preconditions as appropriate.

 The return value relation is now almost never needed directly, and so it is wrapped in corres_protect
 to prevent it from being used during simplification.
 \<close>

lemma corresK_split:
  assumes x: "corres_underlyingK sr nf nf' F r' P P' a c"
  assumes y: "\<And>rv rv'. corres_protect (r' rv rv') \<Longrightarrow> corres_underlyingK sr nf nf' (F' rv rv') r (R rv) (R' rv') (b rv) (d rv')"
  assumes c: "corres_rv F'' r' PP PP' a c F'"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>"
  shows      "corres_underlyingK sr nf nf' (F \<and> F'') r (PP and P and Q) (PP' and P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  apply (clarsimp simp: corres_underlying_def corres_underlyingK_def bind_def)
  apply (rule conjI)
   apply (frule (3) x[simplified corres_underlyingK_def, rule_format, THEN corres_underlyingD],simp)
   apply clarsimp
   apply (drule(1) bspec,clarsimp)
   apply (drule (5) corres_rvD[OF c])
   apply (rule_tac x="(ac,bc)" in bexI,clarsimp)
    apply (frule_tac s'=baa in y[simplified corres_underlyingK_def corres_protect_def, rule_format, THEN corres_underlyingD])
          apply assumption+
       apply (erule(1) use_valid[OF _ z(1)])
      apply (erule(1) use_valid[OF _ z(2)])
     apply fastforce
    apply clarsimp
    apply (drule(1) bspec,clarsimp)
   apply simp
  apply (frule (3) x[simplified corres_underlyingK_def, rule_format, THEN corres_underlyingD],simp)
  apply clarsimp
  apply (drule(1) bspec,clarsimp)
  apply (drule (5) corres_rvD[OF c])
  apply (frule_tac s'=baa in y[simplified corres_underlyingK_def corres_protect_def, rule_format, THEN corres_underlyingD])
        apply simp+
     apply (erule(1) use_valid[OF _ z(1)])
    apply (erule(1) use_valid[OF _ z(2)])
   apply fastforce
  apply clarsimp
  done

section \<open>Corres_inst\<close>

text \<open>Handles rare in-place subgoals generated by corres rules which need to be solved immediately
      in order to instantiate a schematic.
      We peek into the generated return-value relation to see if we can solve the instantiation.
\<close>

definition "corres_inst_eq x y \<equiv> x = y"

lemma corres_inst_eqI[wp]: "corres_inst_eq x x" by (simp add: corres_inst_eq_def)

lemma corres_inst_test: "False \<Longrightarrow> corres_inst_eq x y" by simp

method corres_inst =
  (succeeds \<open>rule corres_inst_test\<close>, fails \<open>rule TrueI\<close>,
    (rule corres_inst_eqI |
      (clarsimp simp: corres_protect_def split del: if_split, rule corres_inst_eqI)
     | (clarsimp simp: corres_protect_def split del: if_split,
         fastforce intro!: corres_inst_eqI)))[1]

section \<open>Corres Method\<close>

text \<open>Handles structured decomposition of corres goals\<close>

named_theorems
  corres_splits and (* rules that, one applied, must
                        eventually yield a successful corres or corresK rule application*)
  corres_simp_del and (* bad simp rules that break everything *)
  corres and (* solving terminal corres subgoals *)
  corresK (* calculational rules that are phrased as corresK rules *)

context begin

lemma corres_fold_dc:
  "corres_underlyingK sr nf nf' F dc P P' f f' \<Longrightarrow> corres_underlyingK sr nf nf' F (\<lambda>_ _. True) P P' f f'"
  by (simp add: dc_def[abs_def])

private method corres_fold_dc =
  (match conclusion in
    "corres_underlyingK _ _ _ _ (\<lambda>_ _. True) _ _ _ _" \<Rightarrow> \<open>rule corres_fold_dc\<close>)

section \<open>Corres_apply method\<close>

text \<open>This is a private method that performs an in-place rewrite of corres rules into
 corresK rules. This is primarily for backwards-compatibility with the existing corres proofs.
 Works by trying to apply a corres rule, then folding the resulting subgoal state into a single
 conjunct and atomizing it, then propagating the result into the stateless precondition.
\<close>

private definition "guard_collect (F :: bool) \<equiv> F"
private definition "maybe_guard F \<equiv> True"

private lemma corresK_assume_guard_guarded:
  "(guard_collect F \<Longrightarrow> corres_underlying sr nf nf' r Q Q' f g) \<Longrightarrow>
    maybe_guard F \<Longrightarrow> corres_underlyingK sr nf nf' F r Q Q' f g"
  by (simp add: corres_underlyingK_def guard_collect_def)

private lemma guard_collect: "guard_collect F \<Longrightarrow> F"
  by (simp add: guard_collect_def)

private lemma has_guard: "maybe_guard F" by (simp add: maybe_guard_def)
private lemma no_guard: "maybe_guard True" by (simp add: maybe_guard_def)

private method corres_apply =
  (rule corresK_assume_guard_guarded,
    (determ \<open>rule corres\<close>, safe_fold_subgoals)[1],
     #break "corres_apply",
   ((focus_concl \<open>(atomize (full))?\<close>, erule guard_collect, rule has_guard) | rule no_guard))[1]

private method corres_alternate = corres_inst | corres_rv



method corres_once declares corres_splits corres corresK corresc_simp =
  (no_schematic_concl,
   (corres_alternate |
     (corres_fold_dc?,
     (corres_pre,
      #break "corres",
      ( (check_corresK, determ \<open>rule corresK\<close>)
      | corres_apply
      | corres_concrete_r
      | corresc
      | (rule corres_splits, corres_once)
      )))))


method corres declares corres_splits corres corresK corresc_simp =
  (corres_once+)[1]

text \<open>Unconditionally try applying split rules. Useful for determining why corres is not applying
 in a given proof.\<close>

method corres_unsafe_split declares corres_splits corres corresK corresc_simp =
  ((rule corres_splits | corres_pre | corres_once)+)[1]

end

lemmas [corres_splits] =
  corresK_split

lemma corresK_when [corres_splits]:
  "\<lbrakk>corres_protect G \<Longrightarrow> corres_protect G' \<Longrightarrow> corres_underlyingK sr nf nf' F dc P P' a c\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf nf' ((G = G') \<and> F) dc ((\<lambda>x. G \<longrightarrow> P x)) (\<lambda>x. G' \<longrightarrow> P' x) (when G a) (when G' c)"
  apply (simp add: corres_underlying_def corres_underlyingK_def corres_protect_def)
  apply (cases "G = G'"; cases G; simp)
  by (clarsimp simp: return_def)

lemma corresK_return_trivial:
  "corres_underlyingK sr nf nf' True dc (\<lambda>_. True) (\<lambda>_. True) (return ()) (return ())"
  by (simp add: corres_underlyingK_def)

lemma corresK_return_eq:
  "corres_underlyingK sr nf nf' True (=) (\<lambda>_. True) (\<lambda>_. True) (return x) (return x)"
  by (simp add: corres_underlyingK_def)

lemma corres_lift_to_K:
  "corres_underlying sra nfa nf'a ra Pa P'a fa f'a \<longrightarrow> corres_underlying sr nf nf' r P P' f f' \<Longrightarrow>
    corres_underlyingK sra nfa nf'a F ra Pa P'a fa f'a \<longrightarrow> corres_underlyingK sr nf nf' F r P P' f f'"
  by (simp add: corres_underlyingK_def)

lemmas [THEN iffD2, atomized, THEN corresK_lift_rule, rule_format, simplified o_def, corres_splits] =
  corres_liftE_rel_sum
  corres_liftM_simp
  corres_liftM2_simp


lemmas [corresK] =
  corresK_return_trivial
  corresK_return_eq

lemma corresK_subst_left: "g = f \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' g f'" by simp

lemma corresK_subst_right: "g' = f' \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
  corres_underlyingK sr nf nf' F r P P' f g'" by simp

lemmas corresK_fun_app_left[corres_splits] = corresK_subst_left[OF fun_app_def[THEN meta_eq_to_obj_eq]]
lemmas corresK_fun_app_right[corres_splits] = corresK_subst_right[OF fun_app_def[THEN meta_eq_to_obj_eq]]

lemmas corresK_Let_left[corres_splits] = corresK_subst_left[OF Let_def[THEN meta_eq_to_obj_eq]]
lemmas corresK_Let_right[corres_splits] = corresK_subst_right[OF Let_def[THEN meta_eq_to_obj_eq]]

lemmas corresK_return_bind_left[corres_splits] = corresK_subst_left[OF return_bind]
lemmas corresK_return_bind_right[corres_splits] = corresK_subst_right[OF return_bind]

lemmas corresK_liftE_bindE_left[corres_splits] = corresK_subst_left[OF liftE_bindE]
lemmas corresK_liftE_bindE_right[corres_splits] = corresK_subst_right[OF liftE_bindE]

lemmas corresK_K_bind_left[corres_splits] =
  corresK_subst_left[where g="K_bind f rv" and f="f" for f rv, # \<open>simp\<close>]

lemmas corresK_K_bind_right[corres_splits] =
  corresK_subst_right[where g'="K_bind f' rv" and f'="f'" for f' rv, # \<open>simp\<close>]


section \<open>Corres Search - find symbolic execution path that allows a given rule to be applied\<close>

lemma corresK_if [corres_splits]:
  "\<lbrakk>(corres_protect G \<Longrightarrow> corres_protect G' \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' a c);
    (corres_protect (\<not>G) \<Longrightarrow> corres_protect (\<not>G') \<Longrightarrow> corres_underlyingK sr nf nf' F' r Q Q' b d)\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf nf' ((G = G') \<and> (G \<longrightarrow> F) \<and> (\<not>G \<longrightarrow> F')) r (if G then P else Q) (if G' then P' else Q') (if G then a else b)
      (if G' then c else d)"
    by (simp add: corres_underlying_def corres_underlyingK_def corres_protect_def)

lemma corresK_if_rev:
  "\<lbrakk>(corres_protect (\<not> G) \<Longrightarrow> corres_protect G' \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' a c);
    (corres_protect G \<Longrightarrow> corres_protect (\<not>G') \<Longrightarrow> corres_underlyingK sr nf nf' F' r Q Q' b d)\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf nf' ((\<not> G = G') \<and> (\<not>G \<longrightarrow> F) \<and> (G \<longrightarrow> F')) r (if G then Q else P) (if G' then P' else Q') (if G then b else a)
      (if G' then c else d)"
    by (simp add: corres_underlying_def corres_underlyingK_def corres_protect_def)



named_theorems corres_symb_exec_ls and corres_symb_exec_rs

lemma corresK_symb_exec_l_search[corres_symb_exec_ls]:
  fixes x :: "'b \<Rightarrow> 'a \<Rightarrow> ('d \<times> 'a) set \<times> bool"
  notes [simp] = corres_noop_def
  shows
  "\<lbrakk>\<And>s. \<lbrace>PP s\<rbrace> m \<lbrace>\<lambda>_. (=) s\<rbrace>; \<And>rv. corres_underlyingK sr nf True (F rv) r (Q rv) P' (x rv) y;
   corres_rv F' dc RR (\<lambda>_. True) m (corres_noop) (\<lambda>rv _. F rv);
   empty_fail m; no_fail P m; \<lbrace>R\<rbrace> m \<lbrace>Q\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf True F' r (RR and P and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP s' s)) P' (m >>= x) y"
  apply (clarsimp simp add: corres_underlyingK_def)
  apply (rule corres_name_pre)
  apply (clarsimp simp: corres_underlying_def corres_underlyingK_def
                        bind_def valid_def empty_fail_def no_fail_def)
  apply (drule_tac x=a in meta_spec)+
  apply (drule_tac x=a in spec)+
  apply (drule mp, assumption)+
  apply (clarsimp simp: not_empty_eq)
  apply (drule corres_rvD; (assumption | simp add: return_def)?)
  apply (drule_tac x="(aa,ba)" in bspec,simp)+
  apply clarsimp
  apply (drule_tac x=aa in meta_spec)
  apply clarsimp
  apply (drule_tac x="(ba,b)" in bspec,simp)
  apply clarsimp
  apply (drule mp, fastforce)
  apply clarsimp
  apply (drule_tac x="(a,bb)" in bspec,simp)
  apply clarsimp
  apply (rule_tac x="(aa,ba)" in bexI)
   apply (clarsimp)
   apply (rule_tac x="(ab,bc)" in bexI)
    apply (clarsimp)+
  done


lemmas corresK_symb_exec_liftME_l_search[corres_symb_exec_ls] =
  corresK_symb_exec_l_search[where 'd="'x + 'y", folded liftE_bindE]

lemma corresK_symb_exec_r_search[corres_symb_exec_rs]:
  fixes y :: "'b \<Rightarrow> 'a \<Rightarrow> ('e \<times> 'a) set \<times> bool"
  assumes X: "\<And>s. \<lbrace>PP' s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes corres: "\<And>rv. corres_underlyingK sr nf nf' (F rv) r P (Q' rv) x (y rv)"
  assumes Y: "corres_rv F' dc (\<lambda>_. True) RR (corres_noop) m (\<lambda>_ rv'. F rv')"
  assumes nf: "nf' \<Longrightarrow> no_fail P' m"
  assumes Z: "\<lbrace>R\<rbrace> m \<lbrace>Q'\<rbrace>"
  notes [simp] = corres_noop_def
  shows
  "corres_underlyingK sr nf nf' F' r P (RR and P' and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP' s' s)) x (m >>= y)"
  apply (insert corres)
  apply (simp add: corres_underlyingK_def)
  apply (rule impI)
  apply (rule corres_name_pre)
  apply (clarsimp simp: corres_underlying_def corres_underlyingK_def
                        bind_def valid_def empty_fail_def no_fail_def)
  apply (intro impI conjI ballI)
    apply clarsimp
    apply (frule(1) use_valid[OF _ X])
    apply (drule corres_rvD[OF Y]; (assumption | simp add: return_def)?)
    apply (frule(1) use_valid[OF _ Z])
    apply (drule_tac x=aa in meta_spec)
    apply clarsimp
    apply (drule_tac x="(a, ba)" in bspec,simp)
    apply (clarsimp)
    apply (drule(1) bspec)
    apply clarsimp
   apply clarsimp
   apply (frule(1) use_valid[OF _ X])
   apply (drule corres_rvD[OF Y]; (assumption | simp add: return_def)?)
   apply (frule(1) use_valid[OF _ Z])
   apply fastforce
  apply (rule no_failD[OF nf],simp+)
  done

lemmas corresK_symb_exec_liftME_r_search[corres_symb_exec_rs] =
  corresK_symb_exec_r_search[where 'e="'x + 'y", folded liftE_bindE]

context begin

private method corres_search_wp = solves \<open>((wp | wpc | simp)+)[1]\<close>

text \<open>
  Depth-first search via symbolic execution of both left and right hand
  sides, handling case statements and
  potentially mismatched if statements. The find_goal
  method handles searching each branch of case or if statements, while
  we rely on backtracking to guess the order of left/right executions.

  According to the above rules, a symbolic execution step can be taken
  when the function can be shown to not modify the state. Questions
  of wellformedness (i.e. empty_fail or no_fail) are deferred to the user
  after the search concludes.
\<close>


private method corres_search_frame methods m uses search =
   (#break "corres_search",
    ((corres?, corres_once corres: search corresK:search)
    | (corresc, find_goal \<open>m\<close>)[1]
    | (rule corresK_if, find_goal \<open>m\<close>)[1]
    | (rule corresK_if_rev, find_goal \<open>m\<close>)[1]
    | (rule corres_symb_exec_ls, corres_search_wp, m)
    | (rule corres_symb_exec_rs, corres_search_wp, m)))

text \<open>
   Set up local context where we make sure we don't know how to
   corres our given rule. The search is finished when we can only
   make corres progress once we add our rule back in
\<close>

method corres_search uses search
  declares corres corres_symb_exec_ls corres_symb_exec_rs =
  (corres_pre,
   use search[corres del] search[corresK del] search[corres_splits del] in
     \<open>use in \<open>corres_search_frame \<open>corres_search search: search\<close> search: search\<close>\<close>)[1]

end

chapter \<open>Misc Helper Lemmas\<close>


lemma corresK_assert[corresK]:
  "corres_underlyingK sr nf nf' ((nf' \<longrightarrow> Q) \<and> P) dc \<top> \<top> (assert P) (assert Q)"
  by (auto simp add: corres_underlyingK_def corres_underlying_def return_def assert_def fail_def)

lemma corres_stateAssert_implied_frame:
  assumes A: "\<forall>s s'. (s, s') \<in> sr \<longrightarrow> F' \<longrightarrow> P' s \<longrightarrow> Q' s' \<longrightarrow> A s'"
  assumes C: "\<And>x. corres_underlyingK sr nf nf' F r P Q f (g x)"
  shows
  "corres_underlyingK sr nf nf' (F \<and> F') r (P and P') (Q and Q') f (stateAssert A [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (corres_search search: C[THEN corresK_unlift])
  apply (wp corres_rv_defer | simp add: A)+
  done

lemma corresK_return [corres_concrete_r]:
  "corres_underlyingK sr nf nf' (r a b) r \<top> \<top> (return a) (return b)"
  by (simp add: corres_underlyingK_def)

lemma corres_throwError_str [corres_concrete_rER]:
  "corres_underlyingK sr nf nf' (r (Inl a) (Inl b)) r \<top> \<top> (throwError a) (throwError b)"
 by (simp add: corres_underlyingK_def)+

section \<open>Error Monad\<close>



lemma corresK_splitE [corres_splits]:
  assumes x: "corres_underlyingK sr nf nf' F (f \<oplus> r') P P' a c"
  assumes y: "\<And>rv rv'. corres_protect (r' rv rv') \<Longrightarrow> corres_underlyingK sr nf nf' (F' rv rv') (f \<oplus> r) (R rv) (R' rv') (b rv) (d rv')"
  assumes c: "corres_rvE_R F'' r' PP PP' a c F'"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>, -" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>, -"
  shows      "corres_underlyingK sr nf nf' (F \<and> F'') (f \<oplus> r) (PP and P and Q) (PP' and P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  unfolding bindE_def
  apply (rule corresK_weakenK)
  apply (rule corresK_split[OF x, where F'="\<lambda>rv rv'. case (rv,rv') of (Inr rva, Inr rva') \<Rightarrow> F' rva rva' | _ \<Rightarrow> True"])
  apply (simp add: corres_protect_def)
    prefer 2
    apply simp
    apply (rule corres_rv_prove[where F=F''])
    apply (case_tac rv; case_tac rv'; simp)
    apply (rule corres_rvE_RD[OF c]; assumption)
    apply (case_tac rv; case_tac rv'; simp)
     apply (simp add: corres_underlyingK_def corres_protect_def)
    apply (rule corresK_weaken)
     apply (rule y)
    apply (simp add: corres_protect_def)
    apply (subst conj_assoc[symmetric])
    apply (rule conjI)
     apply (rule conjI)
      apply (subgoal_tac "(case (Inr b) of (Inr b) \<Rightarrow> R b s
                        | _ \<Rightarrow> True)"; assumption?)
      apply (subgoal_tac "(case (Inr ba) of (Inr ba) \<Rightarrow> R' ba s'
                        | _ \<Rightarrow> True)"; assumption?)
      apply clarsimp+
   apply (insert z)
  by ((fastforce simp: valid_def validE_def validE_R_def split: sum.splits)+)

lemma corresK_returnOk [corres_concrete_r]:
  "corres_underlyingK sr nf nf' (r (Inr a) (Inr b)) r \<top> \<top> (returnOk a) (returnOk b)"
  by (simp add: returnOk_def corres_underlyingK_def)

lemma corres_assertE_str[corresK]:
  "corres_underlyingK sr nf nf' ((nf' \<longrightarrow> Q) \<and> P) (f \<oplus> dc) \<top> \<top> (assertE P) (assertE Q)"
  by (auto simp add: corres_underlying_def corres_underlyingK_def returnOk_def return_def assertE_def fail_def)

lemmas corres_symb_exec_whenE_l_search[corres_symb_exec_ls] =
  corresK_symb_exec_l_search[where 'd="'x + 'y", folded liftE_bindE]

lemmas corres_returnOk_liftEs
  [folded returnOk_liftE, THEN iffD2, atomized, THEN corresK_lift_rule, rule_format, corresK] =
  corres_liftE_rel_sum[where m="return x" for x]
  corres_liftE_rel_sum[where m'="return x" for x]


(* Failure *)

lemma corresK_fail[corresK]:
  "corres_underlyingK sr nf True False r P P' f fail"
  by (simp add: corres_underlyingK_def)

lemma corresK_fail_no_fail'[corresK]:
  "corres_underlyingK sr nf False True (\<lambda>_ _. False) (\<lambda>_. True) (\<lambda>_. True) f fail"
  apply (simp add: corres_underlyingK_def)
  by (fastforce intro!: corres_fail)

section \<open>Correswp\<close>

text
  \<open>This method wraps up wp and wpc to ensure that they don't accidentally generate schematic
   assumptions when handling hoare triples that emerge from corres proofs.
   This is partially due to wp not being smart enough to avoid applying certain wp_comb rules
   when the precondition is schematic, and arises when the schematic precondition doesn't have
   access to some meta-variables in the postcondition.

   To solve this, instead of meta-implication in the wp_comb rules we use corres_inst_eq, which
   can only be solved by reflexivity. In most cases these comb rules are either never applied or
   solved trivially. If users manually apply corres_rv rules to create postconditions with
   inaccessible meta-variables (@{method corres_rv} will never do this), then these rules will
   be used. Since @{method corres_inst} has access to the protected return-value relation, it has a chance
   to unify the generated precondition with the original schematic one.\<close>

named_theorems correswp_wp_comb and correswp_wp_comb_del

lemma corres_inst_eq_imp:
  "corres_inst_eq A B \<Longrightarrow> A \<longrightarrow> B" by (simp add: corres_inst_eq_def)

lemmas corres_hoare_pre = hoare_pre[# \<open>-\<close> \<open>atomize (full), rule allI, rule corres_inst_eq_imp\<close>]

method correswp uses wp =
  (determ \<open>
     (fails \<open>schematic_hoare_pre\<close>, (wp add: wp | wpc))
   | (schematic_hoare_pre,
        (use correswp_wp_comb [wp_comb]
             correswp_wp_comb_del[wp_comb del]
             hoare_pre[wp_pre del]
             corres_hoare_pre[wp_pre]
        in
      \<open>use in \<open>wp add: wp | wpc\<close>\<close>))\<close>)

lemmas [correswp_wp_comb_del] =
  hoare_vcg_precond_imp
  hoare_vcg_precond_impE
  hoare_vcg_precond_impE_R

lemma corres_inst_conj_lift[correswp_wp_comb]:
  "\<lbrakk>\<lbrace>R\<rbrace> f \<lbrace>Q\<rbrace>; \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>; \<And>s. corres_inst_eq (R s) (P s)\<rbrakk> \<Longrightarrow>
       \<lbrace>\<lambda>s. P s \<and> P' s\<rbrace> f \<lbrace>\<lambda>rv s. Q rv s \<and> Q' rv s\<rbrace>"
  by (rule hoare_vcg_conj_lift; simp add: valid_def corres_inst_eq_def)

lemmas [correswp_wp_comb] =
  correswp_wp_comb_del[# \<open>-\<close> \<open>atomize (full), rule allI, rule corres_inst_eq_imp\<close>]
  valid_validE_R
  hoare_vcg_R_conj[OF valid_validE_R]
  hoare_vcg_E_elim[OF valid_validE_E]
  hoare_vcg_E_conj[OF valid_validE_E]
  validE_validE_R
  hoare_vcg_R_conj
  hoare_vcg_E_elim
  hoare_vcg_E_conj
  hoare_vcg_conj_lift

declare hoare_post_comb_imp_conj[correswp_wp_comb_del]

section \<open>Corressimp\<close>
text \<open>Combines corres, wp and clarsimp\<close>

text
\<open>If clarsimp solves a terminal subgoal, its preconditions are left uninstantiated. We can
try to catch this by first attempting a trivial instantiation before invoking clarsimp, but
only keeping the result if clarsimp solves the goal,\<close>

lemmas hoare_True_inst =
  hoare_pre[where P="\<lambda>_. True", of "\<lambda>_. True", # \<open>-\<close> \<open>simp\<close>]
  asm_rl[of "\<lbrace>\<lambda>_. True\<rbrace> f \<lbrace>E\<rbrace>,\<lbrace>R\<rbrace>" for f E R]

lemmas corres_rv_True_inst =
  asm_rl[of "corres_rv True r (\<lambda>_. True) (\<lambda>_. True) f f' Q" for r f f' Q]
  asm_rl[of "corres_rvE_R True r (\<lambda>_. True) (\<lambda>_. True) f f' Q" for r f f' Q]

lemmas corresK_True_inst =
  asm_rl[of "corres_underlyingK sr nf nf' True dc (\<lambda>_. True) (\<lambda>_. True) f g" for sr nf nf' f g]
  asm_rl[of "corres_underlyingK sr nf nf' True r (\<lambda>_. True) (\<lambda>_. True) f g" for sr nf nf' r f g]
  asm_rl[of "corres_underlying sr nf nf' dc (\<lambda>_. True) (\<lambda>_. True) f g" for sr nf nf' f g]
  asm_rl[of "corres_underlying sr nf nf' r (\<lambda>_. True) (\<lambda>_. True) f g" for sr nf nf' r f g]

lemmas calculus_True_insts = hoare_True_inst corres_rv_True_inst corresK_True_inst

method corressimp uses simp cong search wp
  declares corres corresK corres_splits corresc_simp =
  ((no_schematic_concl,
    (corres corresc_simp: simp
    | correswp wp: wp
    | (rule calculus_True_insts, solves \<open>clarsimp cong: cong simp: simp corres_protect_def\<close>)
    | clarsimp cong: cong simp: simp simp del: corres_simp_del split del: if_split
    | (match search in _ \<Rightarrow> \<open>corres_search search: search\<close>)))+)[1]

declare corres_return[corres_simp_del]

section \<open>Normalize corres rule into corresK rule\<close>

lemma corresK_convert:
  "A \<longrightarrow> corres_underlying sr nf nf' r P Q f f' \<Longrightarrow>
   corres_underlyingK sr nf nf' A r P Q f f'"
  by (auto simp add: corres_underlyingK_def)

method corresK_convert = (((drule uncurry)+)?, drule corresK_convert corresK_drop)

section \<open>Lifting corres results into wp proofs\<close>

definition
  "ex_abs_underlying sr P s' \<equiv> \<exists>s. (s,s') \<in> sr \<and> P s"

lemma ex_absI[intro!]:
  "(s, s') \<in> sr \<Longrightarrow> P s \<Longrightarrow> ex_abs_underlying sr P s'"
  by (auto simp add: ex_abs_underlying_def)

lemma use_corresK':
  "corres_underlyingK sr False nf' F r PP PP' f f' \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<Longrightarrow>
    \<lbrace>K F and PP' and ex_abs_underlying sr (PP and P)\<rbrace> f' \<lbrace>\<lambda>rv' s'. \<exists>rv. r rv rv' \<and> ex_abs_underlying sr (Q rv) s'\<rbrace>"
  by (fastforce simp: corres_underlying_def corres_underlyingK_def valid_def ex_abs_underlying_def)

lemma use_corresK [wp]:
  "corres_underlyingK sr False nf' F r PP PP' f f' \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>rv'. r rv rv' \<longrightarrow> Q rv' s\<rbrace> \<Longrightarrow>
    \<lbrace>K F and PP' and ex_abs_underlying sr (PP and P)\<rbrace> f' \<lbrace>\<lambda>rv'. ex_abs_underlying sr (Q rv')\<rbrace>"
 apply (fastforce simp: corres_underlying_def corres_underlyingK_def valid_def ex_abs_underlying_def)
 done

lemma hoare_add_post':
  "\<lbrakk>\<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>; \<lbrace>P''\<rbrace> f \<lbrace>\<lambda>rv s. Q' rv s \<longrightarrow> Q rv s\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>P' and P''\<rbrace> f \<lbrace>Q\<rbrace>"
  by (fastforce simp add: valid_def)

lemma use_corresK_frame:
  assumes corres: "corres_underlyingK sr False nf' F r PP P' f f'"
  assumes frame: "(\<forall>s s' rv rv'. (s,s') \<in> sr \<longrightarrow> r rv rv' \<longrightarrow> Q rv s \<longrightarrow> Q' rv' s' \<longrightarrow> QQ' rv' s')"
  assumes valid: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  assumes valid': "\<lbrace>PP'\<rbrace> f' \<lbrace>Q'\<rbrace>"
  shows "\<lbrace>K F and P' and PP' and ex_abs_underlying sr (PP and P)\<rbrace> f' \<lbrace>QQ'\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_add_post'[OF valid'])
   apply (rule hoare_strengthen_post)
    apply (rule use_corresK'[OF corres valid])
   apply (insert frame)[1]
   apply (clarsimp simp: ex_abs_underlying_def)
  apply clarsimp
  done

lemma use_corresK_frame_E_R:
  assumes corres: "corres_underlyingK sr False nf' F (lf \<oplus> r) PP P' f f'"
  assumes frame: "(\<forall>s s' rv rv'. (s,s') \<in> sr \<longrightarrow> r rv rv' \<longrightarrow> Q rv s \<longrightarrow> Q' rv' s' \<longrightarrow> QQ' rv' s')"
  assumes valid: "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>, -"
  assumes valid': "\<lbrace>PP'\<rbrace> f' \<lbrace>Q'\<rbrace>, -"
  shows "\<lbrace>K F and P' and PP' and ex_abs_underlying sr (PP and P)\<rbrace> f' \<lbrace>QQ'\<rbrace>, -"
  apply (simp only: validE_R_def validE_def)
  apply (rule use_corresK_frame[OF corres _ valid[simplified validE_R_def validE_def] valid'[simplified validE_R_def validE_def]])
  by (auto simp: frame split: sum.splits)

lemma K_True: "K True = (\<lambda>_. True)" by simp
lemma True_And: "((\<lambda>_. True) and P) = P" by simp

method use_corres uses frame =
  (corresK_convert?, drule use_corresK_frame use_corresK_frame_E_R, rule frame,
    (solves \<open>wp\<close> | defer_tac), (solves \<open>wp\<close> | defer_tac), (simp only: True_And K_True)?)

experiment
  fixes sr nf' r P P' f f' F G Q Q' QQ' PP PP' g g'
  assumes f_corres[corres]: "G \<Longrightarrow> F \<Longrightarrow> corres_underlying sr False True r P P' f f'" and
          g_corres[corres]: "corres_underlying sr False True dc \<top> \<top> g g'" and
          wpl [wp]: "\<lbrace>PP\<rbrace> f \<lbrace>Q\<rbrace>" and wpr [wp]: "\<lbrace>PP'\<rbrace> f' \<lbrace>Q'\<rbrace>"
                  and [wp]: "\<lbrace>P\<rbrace> g \<lbrace>\<lambda>_. P\<rbrace>" "\<lbrace>PP\<rbrace> g \<lbrace>\<lambda>_. PP\<rbrace>" "\<lbrace>P'\<rbrace> g' \<lbrace>\<lambda>_. P'\<rbrace>" "\<lbrace>PP'\<rbrace> g' \<lbrace>\<lambda>_. PP'\<rbrace>" and
          frameA: "\<forall>s s' rv rv'. (s,s') \<in> sr \<longrightarrow> r rv rv' \<longrightarrow> Q rv s \<longrightarrow> Q' rv' s' \<longrightarrow> QQ' rv' s'"
  begin

  lemmas f_Q' = f_corres[atomized, @\<open>use_corres frame: frameA\<close>]

  lemma "G \<Longrightarrow> F \<Longrightarrow> corres_underlying sr False True dc (P and PP) (P' and PP')
    (g >>= (K (f >>= K (assert True)))) (g' >>= (K (f' >>= (\<lambda>rv'. (stateAssert (QQ' rv') [])))))"
  apply (simp only: stateAssert_def K_def)
  apply corres
  apply (corres_search search: corresK_assert)
  apply corres_rv
  apply (correswp | simp)+
  apply corres_rv
  apply (correswp wp: f_Q' | simp)+
  apply corressimp+
  by auto

end

section \<open>Corres Argument lifting\<close>

text \<open>Used for rewriting corres rules with syntactically equivalent arguments\<close>

lemma lift_args_corres:
  "corres_underlying sr nf nf' r (P x) (P' x) (f x) (f' x) \<Longrightarrow> x = x' \<Longrightarrow>
   corres_underlying sr nf nf' r (P x) (P' x') (f x) (f' x')" by simp

method lift_corres_args =
  (match premises in
    H[thin]:"corres_underlying _ _ _ _ (P x) (P' x) (f x) (f' x)" (cut 5) for P P' f f' x \<Rightarrow>
      \<open>match (f) in "\<lambda>_. g" for g \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow>
        \<open>match (f') in "\<lambda>_. g'" for g' \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow>
          \<open>cut_tac lift_args_corres[where f=f and f'=f' and P=P and P'=P', OF H]\<close>\<close>\<close>)+

(* Use calculational rules. Don't unfold the definition! *)
lemmas corres_rv_def_I_know_what_I'm_doing = corres_rv_def
lemmas corres_rvE_R_def_I_know_what_I'm_doing = corres_rvE_R_def

hide_fact corres_rv_def
hide_fact corres_rvE_R_def

end
