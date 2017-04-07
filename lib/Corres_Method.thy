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

lemma corres_name_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; P' s'; (s, s') \<in> sr \<rbrakk>
                 \<Longrightarrow> corres_underlying sr nf nf' r (op = s) (op = s') f g \<rbrakk>
        \<Longrightarrow> corres_underlying sr nf nf' r P P' f g"
  apply (simp add: corres_underlying_def split_def
                   Ball_def)
  apply blast
  done

definition
  "corres_underlyingK sr nf nf' F r Q Q' f g \<equiv>
    F \<longrightarrow> corres_underlying sr nf nf' r Q Q' f g"

lemma corresK_name_pre:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; P' s'; F; (s, s') \<in> sr \<rbrakk>
                 \<Longrightarrow> corres_underlyingK sr nf nf' F r (op = s) (op = s') f g \<rbrakk>
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

method check_corres = (succeeds \<open>rule corres_trivial\<close>, fails \<open>rule TrueI\<close>)

private lemma corresK_trivial:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' f f'"
  by simp

method check_corresK = (succeeds \<open>rule corresK_trivial\<close>, fails \<open>rule TrueI\<close>)

private definition "my_false s \<equiv> False"

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

method corresK_pre =
  (check_corresK, (fails \<open>rule corresK_my_false\<close>, rule corresK_weaken)?)

method corres_pre = (corres_raw_pre | corresK_pre)

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


(*
named_theorems corres_concrete_P

private lemma corres_both_False:
  "corres_underlyingK sr nf nf' F r my_false my_false f f'"
  by (auto simp add: my_false_def[abs_def] corres_underlying_def corres_underlyingK_def)

method corres_concrete_P declares corres_concrete_P =
  ((rule corresK_unlift)?,
    fails \<open>rule corres_both_False\<close>, determ \<open>rule corres_concrete_P\<close>)
*)

end


section \<open>Corresc - Corres over case statements\<close>

ML {*

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
*}

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
  "\<lbrakk> Q \<Longrightarrow> wpc2_helper (P, P') (R, R') (PP, PP') (RR, RR') S \<rbrakk>
        \<Longrightarrow> wpc2_helper (P, P') (\<lambda>s. Q \<longrightarrow> R s, {s. Q \<longrightarrow> s \<in> R'}) (PP, PP') (\<lambda>s. Q \<longrightarrow> RR s, {s. Q \<longrightarrow> s \<in> RR'}) (Q \<longrightarrow> S)"
  by (clarsimp simp add: wpc2_helper_def subset_iff)

lemmas wpc2_processors
  = wpc2_conj_process wpc2_all_process wpc2_imp_process

lemma
  wpc_contr_helper:
  "A = B \<Longrightarrow> A = C \<Longrightarrow> B \<noteq> C \<Longrightarrow> P"
  by blast

text \<open>
 Generate quadratic blowup of the case statements on either side of refinement.
 Attempt to discharge resulting contradictions.
\<close>


method corresc_body uses helper =
  determ \<open>(rule wpc2_helperI, repeat_new \<open>rule wpc2_processors\<close> ; (rule helper))\<close>

lemma wpc2_helper_corres_left:
  "corres_underlyingK sr nf nf' QQ r Q A f f' \<Longrightarrow>
    wpc2_helper (P, P') (Q, Q') (\<lambda>_. PP,PP') (\<lambda>_. QQ,QQ') (corres_underlyingK sr nf nf' PP r P A f f')"
  by (clarsimp simp: wpc2_helper_def  corres_underlyingK_def elim!: corres_guard_imp)

method corresc_left =
  determ \<open>(match conclusion in "corres_underlyingK sr nf nf' F r P P' f f'" for sr nf nf' F r P P' f f'
    \<Rightarrow> \<open>apply_split f "\<lambda>f. corres_underlyingK sr nf nf' F r P P' f f'"\<close>,
        corresc_body helper: wpc2_helper_corres_left)\<close>

lemma wpc2_helper_corres_right:
  "corres_underlyingK sr nf nf' QQ r A Q f f' \<Longrightarrow>
    wpc2_helper (P, P') (Q, Q') (\<lambda>_. PP,PP') (\<lambda>_. QQ,QQ') (corres_underlyingK sr nf nf' PP r A P f f')"
  by (clarsimp simp: wpc2_helper_def corres_underlyingK_def elim!: corres_guard_imp)

method corresc_right =
  determ \<open>(match conclusion in "corres_underlyingK sr nf nf' F r P P' f f'" for sr nf nf' F r P P' f f'
    \<Rightarrow> \<open>apply_split f' "\<lambda>f'. corres_underlyingK sr nf nf' F r P P' f f'"\<close>,
        corresc_body helper: wpc2_helper_corres_right)\<close>

named_theorems corresc_simp

lemma corresK_false_guard_instantiate:
  "False \<Longrightarrow> corres_underlyingK sr nf nf' True r P P' f f'"
  by (simp add: corres_underlyingK_def)

method corresc declares corresc_simp =
  (check_corresK, corresc_left; corresc_right;
    (solves \<open>rule corresK_false_guard_instantiate,
      (simp add: corresc_simp)?, (erule (1) wpc_contr_helper, simp add: corresc_simp)?\<close>)?)[1]


section \<open>Alternative split rules\<close>

text \<open>
 These split rules provide much greater information about what is happening on each side
 of the refinement.
 \<close>

definition corres_rv ::"(('s \<times> 't) set) \<Rightarrow>
                        ('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('t \<Rightarrow> bool)
           \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('t, 'b) nondet_monad \<Rightarrow> bool"
  where
  "corres_rv sr r P P' f f' \<equiv>
   \<forall>(s,s') \<in> sr. P s \<longrightarrow> P' s' \<longrightarrow>
    (\<forall>sa rv. (rv, sa) \<in> fst (f s) \<longrightarrow> (\<forall>sa' rv'. (rv', sa') \<in> fst (f' s') \<longrightarrow> (sa,sa') \<in> sr \<longrightarrow> r rv rv'))"

lemma corres_rvD:
  "corres_rv sr r P P' f f' \<Longrightarrow>
   (s,s') \<in> sr \<Longrightarrow> P s \<Longrightarrow> P' s' \<Longrightarrow> (rv,sa) \<in> fst (f s) \<Longrightarrow>
      (rv',sa') \<in> fst (f' s') \<Longrightarrow> (sa,sa') \<in> sr \<Longrightarrow> r rv rv'"
  by (auto simp add: corres_rv_def)

(* Working with corres_rv is not immediately intuitive, but most of the time it just goes away.
   Might need more rules if complex goals show up. *)

lemma corres_rv_prove:
  "(\<And>s s' sa sa' rv rv'. (s,s') \<in> sr \<Longrightarrow> (sa,sa') \<in> sr \<Longrightarrow>
    (rv,sa) \<in> fst (f s) \<Longrightarrow> (rv',sa') \<in> fst (f' s') \<Longrightarrow> P s \<Longrightarrow> P' s' \<Longrightarrow> r rv rv') \<Longrightarrow>
    corres_rv sr r P P' f f'"
  by (auto simp add: corres_rv_def)

lemmas corres_rv_proveT = corres_rv_prove[where P=\<top> and P'=\<top>,simplified]

lemmas corres_rv_trivial[intro!, wp] = corres_rv_prove[where r="\<lambda>_ _. True" and P=\<top> and P'=\<top>, OF TrueI]

lemma corres_rv_defer_left:
  "corres_rv sr r (\<lambda>s. \<forall>rv rv'. r rv rv') \<top> f f'"
  by (auto simp add: corres_rv_def)

lemma corres_rv_wp_left:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>rv'. r rv rv'\<rbrace> \<Longrightarrow> corres_rv sr r P \<top> f f'"
  by (fastforce simp add: corres_rv_def valid_def)

lemma corres_rv_defer_right:
  "corres_rv sr r \<top> (\<lambda>s. \<forall>rv rv'. r rv rv') f f'"
  by (auto simp add: corres_rv_def)

lemma corres_rv_wp_right:
  "\<lbrace>P'\<rbrace> f' \<lbrace>\<lambda>rv' s. \<forall>rv. r rv rv'\<rbrace> \<Longrightarrow> corres_rv sr r \<top> P' f f'"
  by (fastforce simp add: corres_rv_def valid_def)

lemma corres_rv_weaken:
  "(\<And>rv rv'. r rv rv' \<Longrightarrow> r' rv rv') \<Longrightarrow> corres_rv sr r P P' f f' \<Longrightarrow> corres_rv sr r' P P' f f'"
  by (auto simp add: corres_rv_def)

lemma corresK_split:
  assumes x: "corres_underlyingK sr nf nf' F r' P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlyingK sr nf nf' (F' rv rv') r (R rv) (R' rv') (b rv) (d rv')"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>"
  assumes c: "corres_rv sr (\<lambda>rv rv'. r' rv rv' \<longrightarrow> F' rv rv') PP PP' a c"
  shows      "corres_underlyingK sr nf nf' F r (PP and P and Q) (PP' and P' and Q') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  apply (clarsimp simp: corres_underlying_def corres_underlyingK_def bind_def)
  apply (rule conjI)
   apply (frule (3) x[simplified corres_underlyingK_def, rule_format, THEN corres_underlyingD],simp)
   apply clarsimp
   apply (drule(1) bspec,clarsimp)
   apply (insert c;simp?)
   apply (drule(6) corres_rvD)
   apply (rule_tac x="(ac,bc)" in bexI,clarsimp)
    apply (frule_tac s'=baa in y[simplified corres_underlyingK_def, rule_format, THEN corres_underlyingD])
          apply assumption+
       apply (erule(1) use_valid[OF _ z(1)])
      apply (erule(1) use_valid[OF _ z(2)])
     apply fastforce
    apply clarsimp
    apply (drule(1) bspec,clarsimp)
   apply simp
  apply clarsimp
  apply (frule (3) x[simplified corres_underlyingK_def, rule_format, THEN corres_underlyingD],simp)
  apply clarsimp
  apply (drule(1) bspec,clarsimp)
  apply (insert c;simp?)
  apply (drule(6) corres_rvD)
  apply (frule_tac s'=baa in y[simplified corres_underlyingK_def, rule_format, THEN corres_underlyingD])
        apply simp+
     apply (erule(1) use_valid[OF _ z(1)])
    apply (erule(1) use_valid[OF _ z(2)])
   apply fastforce
  apply clarsimp
  done

section \<open>Corres Method\<close>

text \<open>Handles structured decomposition of corres goals\<close>

named_theorems
  corres_splits and
  corres_simp and (* conservative simplification rules applied when no progress can be made *)
  corres_simp_del and (* bad simp rules that break everything *)
  corres and (* solving terminal corres subgoals *)
  corresK (* calculational rules that are phrased as corresK rules *)

context begin

text \<open>Testing for schematic goal state\<close>

lemma corres_fold_dc:
  "corres_underlyingK sr nf nf' F dc P P' f f' \<Longrightarrow> corres_underlyingK sr nf nf' F (\<lambda>_ _. True) P P' f f'"
  by (simp add: dc_def[abs_def])

private method corres_fold_dc =
  (match conclusion in
    "corres_underlyingK _ _ _ _ (\<lambda>_ _. True) _ _ _ _" \<Rightarrow> \<open>rule corres_fold_dc\<close>)

private attribute_setup no_simps =
  \<open>Scan.succeed (Thm.declaration_attribute (fn _ => Context.mapping I (put_simpset HOL_basic_ss)))\<close>

(* method corres_simp declares corres_simp =
  (use [[no_simps, simproc unit_eq]] in \<open>simp add: corres_simp\<close>) *)

method corres_simp declares corres_simp = (simp only: corres_simp)

(* Lift corres_underlying rules into corres_underlyingK rules in-place *)

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
  (rule corresK_assume_guard_guarded, (determ \<open>rule corres\<close>, safe_fold_subgoals)[1],
     #break "corres_apply",
   ((focus_concl \<open>(atomize (full))?\<close>, erule guard_collect, rule has_guard) | rule no_guard))[1]

method corres_once declares corres_splits corres corresK corres_simp corresc_simp =
   (corres_fold_dc?,
   (corres_pre,
    #break "corres",
    ( (check_corresK, determ \<open>rule corresK\<close>)
    | corres_apply
    | corres_concrete_r
    | corresc
    | (rule corres_splits, corres_once)
    | (corres_simp, corres_once)
    )))


method corres declares corres_splits corres corresK corres_simp corresc_simp =
  (corres_once+)[1]

end

lemmas [corres_splits] =
  corresK_split

lemma corresK_when:
  "\<lbrakk>G \<Longrightarrow> G' \<Longrightarrow> corres_underlyingK sr nf nf' F dc P P' a c\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf nf' ((G = G') \<and> F) dc ((\<lambda>x. G \<longrightarrow> P x)) (\<lambda>x. G' \<longrightarrow> P' x) (when G a) (when G' c)"
  apply (simp add: corres_underlying_def corres_underlyingK_def)
  apply (cases "G = G'"; cases G; simp)
  by (clarsimp simp: return_def)

lemma corresK_return_trivial:
  "corres_underlyingK sr nf nf' True dc (\<lambda>_. True) (\<lambda>_. True) (return ()) (return ())"
  by (simp add: corres_underlyingK_def)

lemma corresK_return_eq:
  "corres_underlyingK sr nf nf' True (op =) (\<lambda>_. True) (\<lambda>_. True) (return x) (return x)"
  by (simp add: corres_underlyingK_def)

lemma corres_lift_to_K:
  "corres_underlying sra nfa nf'a ra Pa P'a fa f'a \<longrightarrow> corres_underlying sr nf nf' r P P' f f' \<Longrightarrow>
    corres_underlyingK sra nfa nf'a F ra Pa P'a fa f'a \<longrightarrow> corres_underlyingK sr nf nf' F r P P' f f'"
  by (simp add: corres_underlyingK_def)

lemmas corresK_liftM =
  corres_liftM2_simp[THEN iffD2,atomized, THEN corres_lift_to_K, rule_format]



lemmas [corresK] =
  corresK_when
  corresK_liftM
  corresK_return_trivial
  corresK_return_eq

lemmas [corres_simp] =
  fun_app_def comp_apply option.inject K_bind_def return_bind
  Let_def liftE_bindE



section \<open>Corres Search - find symbolic execution path that allows a given rule to be applied\<close>

lemma corresK_if:
  "\<lbrakk>(G \<Longrightarrow> G' \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' a c); (\<not>G \<Longrightarrow> \<not>G' \<Longrightarrow> corres_underlyingK sr nf nf' F' r Q Q' b d)\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf nf' ((G = G') \<and> (G \<longrightarrow> F) \<and> (\<not>G \<longrightarrow> F')) r (if G then P else Q) (if G' then P' else Q') (if G then a else b)
      (if G' then c else d)"
    by (simp add: corres_underlying_def corres_underlyingK_def)

lemma corresK_if_rev:
  "\<lbrakk>(\<not> G \<Longrightarrow> G' \<Longrightarrow> corres_underlyingK sr nf nf' F r P P' a c); (G \<Longrightarrow> \<not>G' \<Longrightarrow> corres_underlyingK sr nf nf' F' r Q Q' b d)\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf nf' ((\<not> G = G') \<and> (\<not>G \<longrightarrow> F) \<and> (G \<longrightarrow> F')) r (if G then Q else P) (if G' then P' else Q') (if G then b else a)
      (if G' then c else d)"
    by (simp add: corres_underlying_def corres_underlyingK_def)



named_theorems corres_symb_exec_ls and corres_symb_exec_rs

lemma corresK_symb_exec_l_search[corres_symb_exec_ls]:
  fixes x :: "'b \<Rightarrow> 'a \<Rightarrow> ('d \<times> 'a) set \<times> bool"
  shows
  "\<lbrakk>\<And>s. \<lbrace>PP s\<rbrace> m \<lbrace>\<lambda>_. op = s\<rbrace>; \<And>rv. corres_underlyingK sr nf True (F rv) r (Q rv) P' (x rv) y;
   empty_fail m; no_fail P m; \<lbrace>R\<rbrace> m \<lbrace>Q\<rbrace>; \<lbrace>RR\<rbrace> m \<lbrace>\<lambda>rv s. F rv\<rbrace>\<rbrakk>
\<Longrightarrow> corres_underlyingK sr nf True True r (RR and P and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP s' s)) P' (m >>= x) y"
  apply (simp add: corres_underlyingK_def)
  apply (rule corres_name_pre)
  apply (clarsimp simp: corres_underlying_def corres_underlyingK_def
                        bind_def valid_def empty_fail_def no_fail_def)
  apply (drule_tac x=a in meta_spec)+
  apply (drule_tac x=a in spec)+
  apply (drule mp, assumption)+
  apply (clarsimp simp: not_empty_eq)
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
  assumes X: "\<And>s. \<lbrace>PP' s\<rbrace> m \<lbrace>\<lambda>r. op = s\<rbrace>"
  assumes corres: "\<And>rv. corres_underlyingK sr nf nf' (F rv) r P (Q' rv) x (y rv)"
  assumes nf: "nf' \<Longrightarrow> no_fail P' m"
  assumes Z: "\<lbrace>R\<rbrace> m \<lbrace>Q'\<rbrace>"
  assumes Y: "\<lbrace>RR\<rbrace> m \<lbrace>\<lambda>rv s. F rv\<rbrace>"
  shows
  "corres_underlyingK sr nf nf' True r P (RR and P' and R and (\<lambda>s. \<forall>s'. s = s' \<longrightarrow> PP' s' s)) x (m >>= y)"
  apply (insert corres)
  apply (simp add: corres_underlyingK_def)
  apply (rule corres_name_pre)
  apply (clarsimp simp: corres_underlying_def corres_underlyingK_def
                        bind_def valid_def empty_fail_def no_fail_def)
  apply (intro impI conjI ballI)
    apply clarsimp
    apply (frule(1) use_valid[OF _ X])
    apply (frule(1) use_valid[OF _ Y])
    apply (frule(1) use_valid[OF _ Z])
    apply simp
    apply (drule_tac x=aa in meta_spec)
    apply clarsimp
    apply (drule_tac x="(a, ba)" in bspec,simp)
    apply (clarsimp)
    apply (drule(1) bspec)
    apply clarsimp
   apply clarsimp
   apply (frule(1) use_valid[OF _ X])
   apply (frule(1) use_valid[OF _ Y])
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
  declares corres corres_simp corres_symb_exec_ls corres_symb_exec_rs =
  (corres_pre,
   use search[corres del] search[corresK del] in
     \<open>use in \<open>corres_search_frame \<open>corres_search search: search\<close> search: search\<close>\<close>)[1]

end

chapter \<open>Misc Helper Lemmas\<close>


lemma corresK_assert[corresK]:
  "corres_underlyingK sr nf nf' ((nf' \<longrightarrow> Q) \<and> P) dc \<top> \<top> (assert P) (assert Q)"
  by (auto simp add: corres_underlyingK_def corres_underlying_def return_def assert_def fail_def)

lemma corres_stateAssert_implied_frame:
  assumes A: "\<forall>s s'. (s, s') \<in> sr \<longrightarrow> P' s \<longrightarrow> Q' s' \<longrightarrow> A s'"
  assumes C: "\<And>x. corres_underlyingK sr nf nf' F r P Q f (g x)"
  shows
  "corres_underlyingK sr nf nf' F r (P and P') (Q and Q') f (stateAssert A [] >>= g)"
  apply (clarsimp simp: bind_assoc stateAssert_def)
  apply (corres_search search: C[THEN corresK_unlift])
  by (wp | simp add: A)+

lemma corresK_return [corres_concrete_r]:
  "corres_underlyingK sr nf nf' (r a b) r \<top> \<top> (return a) (return b)"
  by (simp add: corres_underlyingK_def)

lemma corres_K_bind [corresK]:
  "corres_underlyingK sr nf nf' F r P P' f f' \<Longrightarrow>
   corres_underlyingK sr nf nf' F r P P' f (K_bind f' a)"
  by simp

chapter \<open>Extra Stuff (Stale)\<close>

section \<open>Named state rules\<close>

text \<open>This forms the bases of the a similar framework for spec_valid (i.e. induction proofs)\<close>

definition
  "with_state P s \<equiv> \<lambda>s'. s = s' \<and> P s"


lemma corres_name_state:
  assumes "\<And>s s'. (s,s') \<in> sr \<Longrightarrow> corres_underlying sr nf nf' r (with_state P s) (with_state P' s') f f'"
  shows
  "corres_underlying sr nf nf' r P P' f f'"
  apply (insert assms)
  apply (simp add: corres_underlying_def with_state_def)
  by (fastforce split: prod.splits prod.split_asm)

lemma corres_name_state_pre:
  assumes "corres_underlying sr nf nf' r (with_state Q s) (with_state Q' s') f f'"
          "\<And>s. P s \<Longrightarrow> Q s" "\<And>s'. P' s' \<Longrightarrow> Q' s'"
  shows
  "corres_underlying sr nf nf' r (with_state P s) (with_state P' s') f f'"
  apply (insert assms)
  apply (simp add: corres_underlying_def with_state_def)
  by (fastforce split: prod.splits prod.split_asm)

lemma corres_drop_state:
  assumes "corres_underlying sr nf nf' r P P' f f'"
  shows "corres_underlying sr nf nf' r (with_state P s) (with_state P' s') f f'"
  apply (rule corres_guard_imp)
  apply (rule assms)
  by (auto simp add: with_state_def)


lemma corres_split_named:
  assumes x: "(s, s') \<in> sr \<Longrightarrow> corres_underlying sr nf nf' r' (with_state P s) (with_state P' s') a c"
  assumes y: "\<And>ss ss' rv rv'. r' rv rv' \<Longrightarrow> (rv,ss) \<in> fst (a s) \<Longrightarrow> (rv',ss') \<in> fst (c s') \<Longrightarrow>
  (ss,ss') \<in> sr \<Longrightarrow>
  corres_underlying sr nf nf' r (with_state (R rv' rv) ss) (with_state (R' rv rv') ss') (b rv) (d rv')"
  assumes    "(s,s') \<in> sr \<Longrightarrow> Q' s' \<Longrightarrow> s \<turnstile> \<lbrace>Q\<rbrace> a \<lbrace>\<lambda>r s. (\<exists>s'' r''. r' r r'' \<and> (s,s'') \<in> sr \<and> (r'',s'') \<in> fst (c s')) \<longrightarrow> (\<forall>r''. r' r r'' \<longrightarrow>  R r'' r s)\<rbrace>"
             "(s,s') \<in> sr \<Longrightarrow> Q s \<Longrightarrow> s' \<turnstile> \<lbrace>Q'\<rbrace> c \<lbrace>\<lambda>r s'. \<forall>x. r' x r \<longrightarrow> (\<exists>s. (s,s') \<in> sr) \<longrightarrow> R' x r s'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (with_state (P and Q) s) (with_state (P' and Q') s') (a >>= (\<lambda>rv. b rv)) (c >>= (\<lambda>rv'. d rv'))"
  using assms
  apply -
  apply (clarsimp simp: corres_underlying_def bind_def with_state_def)
  apply (clarsimp simp: Bex_def Ball_def valid_def spec_valid_def)
  by meson

section \<open>Error Monad\<close>

lemmas [THEN iffD2, atomized, THEN corresK_lift_rule, rule_format, corresK] =
  corres_liftE_rel_sum
  corres_liftM2_simp
  corres_liftM_simp

lemma corres_splitEE_str [corres_splits]:
  assumes x: "corres_underlyingK sr nf nf' F (f \<oplus> r') P P' a c"
  assumes y: "\<And>rv rv'. r' rv rv' \<Longrightarrow> corres_underlyingK sr nf nf' (F' rv rv') (f \<oplus> r) (R rv) (R' rv') (b rv) (d rv')"
  assumes z: "\<lbrace>Q\<rbrace> a \<lbrace>R\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>" "\<lbrace>Q'\<rbrace> c \<lbrace>R'\<rbrace>, \<lbrace>\<lambda>_ _. True\<rbrace>"
  assumes c: "corres_rv sr (\<lambda>rv rv'. (case (rv,rv') of (Inr rva, Inr rva') \<Rightarrow> r' rva rva' \<longrightarrow> F' rva rva' | _ \<Rightarrow> True)) PP PP' a c"
  shows      "corres_underlyingK sr nf nf' F (f \<oplus> r) (PP and P and Q) (PP' and P' and Q') (a >>=E (\<lambda>rv. b rv)) (c >>=E (\<lambda>rv'. d rv'))"
  apply (simp add: bindE_def)
  apply (rule corresK_split[OF x, where F'="\<lambda>rv rv'. case (rv,rv') of (Inr rva, Inr rva') \<Rightarrow> F' rva rva' | _ \<Rightarrow> True"])
    prefer 4
    apply (rule corres_rv_weaken[OF _ c])
    apply (case_tac rv; case_tac rv'; simp)
    apply simp
    apply (case_tac rv; case_tac rv'; simp)
     apply (simp add: corres_underlyingK_def)
    apply (rule corresK_weaken)
     apply (rule y)
    apply simp
    apply (subst conj_assoc[symmetric])
    apply (rule conjI)
     apply (rule conjI)
      apply (subgoal_tac "(case (Inr b) of (Inr b) \<Rightarrow> R b s
                        | _ \<Rightarrow> True)"; assumption?)
      apply (subgoal_tac "(case (Inr ba) of (Inr ba) \<Rightarrow> R' ba s'
                        | _ \<Rightarrow> True)"; assumption?)
      apply clarsimp+
   apply (insert z)
  by ((fastforce simp: valid_def validE_def split: sum.splits)+)

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


(* Wrap it up in a big hammer. Small optimization to avoid searching when no fact is given. *)


method corressimp uses simp cong search wp
  declares corres corresK corres_splits corres_simp corresc_simp =
  ((corres corresc_simp: simp
    | use hoare_vcg_precond_imp[wp_comb del] hoare_vcg_precond_imp[wp_pre del] in
      \<open>use in \<open>wp add: wp\<close>\<close>
    | wpc | clarsimp cong: cong simp: simp simp del: corres_simp_del split del: if_split
    | rule corres_rv_trivial |
      (match search in _ \<Rightarrow> \<open>corres_search search: search\<close>))+)[1]

declare corres_return[corres_simp_del]

end
