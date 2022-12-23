(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory WPEx
imports
  NonDetMonadVCG
  Strengthen
begin

(* Only the wps method and wps_tac are left of this experiment: *)
text \<open>WPEx - the WP Extension Experiment\<close>

definition mresults :: "('s, 'a) nondet_monad \<Rightarrow> ('a \<times> 's \<times> 's) set" where
 "mresults f = {(rv, s', s). (rv, s') \<in> fst (f s)}"

definition assert_value_exported ::
  "'x \<times> 's \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('x \<Rightarrow> ('s, 'a) nondet_monad)" where
  "assert_value_exported x f y \<equiv> do s \<leftarrow> get; if x = (y, s) then f else fail od"

lemma in_mresults_export:
  "(rv, s', s) \<in> mresults (assert_value_exported (rv', s'') f rv'')
      = ((rv, s', s) \<in> mresults f \<and> rv' = rv'' \<and> s'' = s)"
  by (simp add: assert_value_exported_def mresults_def in_monad)

lemma in_mresults_bind:
  "(rv, s', s) \<in> mresults (a >>= b)
       = (\<exists>rv' s''. (rv, s', s'') \<in> mresults (b rv') \<and> (rv', s'', s) \<in> mresults a)"
  by (auto simp: mresults_def bind_def elim: rev_bexI)

lemma mresults_export_bindD:
  "(rv, s', s) \<in> mresults (a >>= assert_value_exported (rv', s'') b) \<Longrightarrow> (rv, s', s'') \<in> mresults b"
  "(rv, s', s) \<in> mresults (a >>= assert_value_exported (rv', s'') b) \<Longrightarrow> (rv', s'', s) \<in> mresults a"
  by (simp_all add: in_mresults_export in_mresults_bind)

definition wpex_name_for_id :: "'a \<Rightarrow> 'a" where
  "wpex_name_for_id = id"

lemma use_valid_mresults:
  "\<lbrakk> (rv, s', s) \<in> mresults f; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> P s \<longrightarrow> Q rv s'"
  by (auto simp: mresults_def valid_def)

lemma valid_strengthen_with_mresults:
  "\<lbrakk> \<And>s rv s'. \<lbrakk> (rv, s', s) \<in> mresults f; wpex_name_for_id (Q' s rv s') \<rbrakk> \<Longrightarrow> Q rv s';
     \<And>prev_s. \<lbrace>P prev_s\<rbrace> f \<lbrace>Q' prev_s\<rbrace> \<rbrakk>
   \<Longrightarrow> \<lbrace>\<lambda>s. P s s\<rbrace> f \<lbrace>Q\<rbrace>"
  by (clarsimp simp: valid_def mresults_def wpex_name_for_id_def) blast

lemma wpex_name_for_idE: "wpex_name_for_id P \<Longrightarrow> P"
  by (simp add: wpex_name_for_id_def)

ML \<open>

fun dest_mresults_tac t = Seq.of_list ([t] RL @{thms mresults_export_bindD});

(* take a rule of conclusion p --> q and decide whether to use it
   as an introduction rule or if of form ?P x --> ?P y to use it
   as y = x *)
fun get_rule_uses ctxt rule = let
    val (p, q) = (Thm.concl_of #> Envir.beta_eta_contract #> HOLogic.dest_Trueprop
                    #> HOLogic.dest_imp) rule;
    fun mk_eqthm v (n, (x, _)) = let
        val (_, tp) = dest_Var v;
        val (argtps, tp') = strip_type tp;
        val _ = if (tp' = @{typ bool}) then ()
                else error "get_rule_uses: range type <> bool";
        val ct = Thm.cterm_of ctxt;
        val eq = HOLogic.eq_const (nth argtps (n - 1))
                    $ Bound (length argtps - n) $ x;
        val v' = fold_rev Term.abs (map (pair "x") argtps) eq;
      in rule
        |> Thm.instantiate (TVars.empty, Vars.make [(Term.dest_Var v, ct v')])
        |> simplify (put_simpset HOL_ss ctxt)
      end;
  in case (strip_comb p, strip_comb q) of
      ((v as Var _, args), (v' as Var _, args')) =>
        if v = v' andalso length args = length args'
        then (map (mk_eqthm v) ((1 upto length args) ~~ (args ~~ args')), [])
        else ([], [])
    | (_, (Var _, _)) => ([], [])
    | _ => ([], [rule])
  end;

fun get_wp_simps_strgs ctxt rules asms = let
    val wp_rules = rules @ (WeakestPre.debug_get ctxt |> #rules |> WeakestPre.dest_rules);
    val wp_rules' = filter (null o Thm.prems_of) wp_rules;
    val asms' = maps (Seq.list_of o REPEAT dest_mresults_tac) asms;
    val uses = asms' RL [@{thm use_valid_mresults}];
    val wp_rules'' = wp_rules' RL uses;
  in
    apply2 flat (map_split (get_rule_uses ctxt) wp_rules'')
  end;

fun postcond_ss ctxt = ctxt
    |> put_simpset HOL_basic_ss
    |> (fn ctxt => ctxt addsimps @{thms pred_conj_def})
    |> simpset_of

fun wp_default_ss ctxt = ctxt
    |> put_simpset HOL_ss
    |> Splitter.del_split @{thm if_split}
    |> simpset_of

fun wps_tac ctxt rules =
let
  (* avoid duplicate simp rule etc warnings: *)
  val ctxt = Context_Position.set_visible false ctxt
in
  resolve_tac ctxt [@{thm valid_strengthen_with_mresults}]
  THEN' (safe_simp_tac (put_simpset (postcond_ss ctxt) ctxt))
  THEN' Subgoal.FOCUS (fn focus => let
      val ctxt = #context focus;
      val (simps, _) = get_wp_simps_strgs ctxt rules (#prems focus);
    in CHANGED (simp_tac (put_simpset (wp_default_ss ctxt) ctxt addsimps simps) 1) end) ctxt
  THEN' eresolve_tac ctxt [@{thm wpex_name_for_idE}]
end

val wps_method = Attrib.thms >> curry
  (fn (ts, ctxt) => Method.SIMPLE_METHOD' (wps_tac ctxt ts));

\<close>

method_setup wps = \<open>wps_method\<close> "experimental wp simp method"

experiment
begin

lemma "\<lbrace>P\<rbrace> do v \<leftarrow> return (Suc 0); return (Suc (Suc 0)) od \<lbrace>(=)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_seq_ext)+
    apply (wps | rule hoare_vcg_prop)+
  oops

end

end
