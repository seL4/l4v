(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WPEx
imports
  "../NonDetMonadVCG"
  "../Strengthen"
begin

text \<open>WPEx - the WP Extension Experiment\<close>

definition
  mresults :: "('s, 'a) nondet_monad \<Rightarrow> ('a \<times> 's \<times> 's) set"
where
 "mresults f = {(rv, s', s). (rv, s') \<in> fst (f s)}"

definition
  assert_value_exported :: "'x \<times> 's \<Rightarrow> ('s, 'a) nondet_monad \<Rightarrow> ('x \<Rightarrow> ('s, 'a) nondet_monad)"
where
 "assert_value_exported x f y \<equiv>
    do s \<leftarrow> get; if x = (y, s) then f else fail od"

syntax
  "_assert_bind" :: "['a, 'b] => dobind" ("_ =<= _")

translations
  "do v =<= a; e od" == "a >>= CONST assert_value_exported v e"
  "doE v =<= a; e odE" == "a >>=E CONST assert_value_exported v e"

lemma in_mresults_export:
  "(rv, s', s) \<in> mresults (assert_value_exported (rv', s'') f rv'')
      = ((rv, s', s) \<in> mresults f \<and> rv' = rv'' \<and> s'' = s)"
  by (simp add: assert_value_exported_def mresults_def in_monad)

lemma in_mresults_bind:
  "(rv, s', s) \<in> mresults (a >>= b)
       = (\<exists>rv' s''. (rv, s', s'') \<in> mresults (b rv') \<and> (rv', s'', s) \<in> mresults a)"
  apply (simp add: mresults_def bind_def)
  apply (auto elim: rev_bexI)
  done

lemma mresults_export_bindD:
  "(rv, s', s) \<in> mresults (a >>= assert_value_exported (rv', s'') b)
       \<Longrightarrow> (rv, s', s'') \<in> mresults b"
  "(rv, s', s) \<in> mresults (a >>= assert_value_exported (rv', s'') b)
       \<Longrightarrow> (rv', s'', s) \<in> mresults a"
  by (simp_all add: in_mresults_export in_mresults_bind)

definition "wpex_name_for_id = id"

definition "wpex_name_for_id_prop p \<equiv> (p :: prop)"

lemma wpex_name_for_id_propI:
  "PROP p \<Longrightarrow> PROP wpex_name_for_id_prop p"
  by (simp add: wpex_name_for_id_prop_def)

lemma wpex_name_for_id_propE:
  "PROP wpex_name_for_id_prop p \<Longrightarrow> PROP p"
  by (simp add:  wpex_name_for_id_prop_def)

lemma del_asm_rule:
  "\<lbrakk> PROP P; PROP Q \<rbrakk> \<Longrightarrow> PROP Q"
  by assumption

ML \<open>

val p_prop_var = Term.dest_Var (Logic.varify_global @{term "P :: prop"});

fun del_asm_tac asm =
  eresolve0_tac [(Thm.instantiate ([], [(p_prop_var, asm)]) @{thm del_asm_rule})];

fun subgoal_asm_as_thm tac =
  Subgoal.FOCUS_PARAMS (fn focus => SUBGOAL (fn (t, _) => let
    val asms = Logic.strip_assums_hyp t;
    val ctxt = #context focus;
    fun asm_tac asm = (Subgoal.FOCUS_PREMS (fn focus => let
        fun is_asm asm' = asm aconv (Thm.concl_of asm');
        val (asm' :: _) = filter is_asm (#prems focus);
      in tac asm' end) (#context focus)
        THEN_ALL_NEW del_asm_tac (Thm.cterm_of ctxt asm)) 1;
  in
    FIRST (map asm_tac asms)
  end) 1);

exception SAME;

fun eta_flat (Abs (name, tp, (Abs a)))
        = eta_flat (Abs (name, tp, eta_flat (Abs a)))
  | eta_flat (Abs (_, _, t $ Bound 0))
        = if member (=) (loose_bnos t) 0 then raise SAME
          else subst_bound (Bound 0, t)
  | eta_flat (Abs (name, tp, t $ Abs a))
        = eta_flat (Abs (name, tp, t $ eta_flat (Abs a)))
  | eta_flat _ = raise SAME;

fun const_spine t = case strip_comb t of
    (Const c, xs) => SOME (c, xs)
  | (Abs v, []) => (const_spine (eta_flat (Abs v)) handle SAME => NONE)
  | (Abs _, (_ :: _)) => error "const_spine: term not beta expanded"
  | _ => NONE;

fun build_annotate' t wr ps = case (const_spine t, wr) of
    (SOME (bd as ("NonDetMonad.bind", _), [a, b]),
     "WPEx.mresults") => let
           val (a', ps') = build_annotate' a "WPEx.mresults" ps;
         in case const_spine b of
             SOME (ass as ("WPEx.assert_value_exported", _), [rvs, c])
                 => let
                      val (c', ps'') = build_annotate' c "WPEx.mresults" ps'
                    in (Const bd $ a' $ (Const ass $ rvs $ c'), ps'') end
          | _ => let
                  val tp  = fastype_of (Const bd);
                  val btp = domain_type (range_type tp);
                  val rtp = domain_type btp;
                  val stp = domain_type (range_type btp);
                  val mtp = range_type (range_type btp);
                  val ass = Const ("WPEx.assert_value_exported",
                                   HOLogic.mk_prodT (rtp, stp) -->
                                    (stp --> mtp) --> rtp --> stp --> mtp);
                  val rv  = Bound (length ps');
                  val s   = Bound (length ps' + 1);
                  val rvs = HOLogic.pair_const rtp stp $ rv $ s;
                  val b'  = betapply (b, Bound (length ps'));
                  val borings = ["x", "y", "rv"];
                  val rvnms = case b of
                      Abs (rvnm, _, _) =>
                          if member (=) borings rvnm then []
                          else [(rvnm, rvnm ^ "_st")]
                    | _ => [];
                  val cnms = case const_spine a' of
                      SOME ((cnm, _), _) => let
                          val cnm' = List.last (space_explode "." cnm);
                        in [(cnm' ^ "_rv", cnm' ^ "_st")] end
                    | _ => [];
                  val nms = hd (rvnms @ cnms @ [("rv", "s")]);
                  val ps'' = ps' @ [(fst nms, rtp), (snd nms, stp)];
                  val (b'', ps''') = build_annotate' b' "WPEx.mresults" ps'';
               in (Const bd $ a' $ (ass $ rvs $ b''), ps''') end
         end
  | _ => (t, ps);

fun build_annotate asm =
  case const_spine (HOLogic.dest_Trueprop (Envir.beta_norm asm)) of
    SOME (memb as ("Set.member", _), [x, st]) => (case const_spine st of
        SOME (mres as ("WPEx.mresults", _), [m]) => let
              val (m', ps) = build_annotate' m "WPEx.mresults" [];
              val _ = if null ps then raise SAME else ();
              val t = Const memb $ x $ (Const mres $ m');
              fun mk_exists ((s, tp), tm) = HOLogic.exists_const tp $ Abs (s, tp, tm);
            in HOLogic.mk_Trueprop (Library.foldr mk_exists (rev ps, t)) end
      | _ => raise SAME) | _ => raise SAME;


val put_Lib_simpset =  put_simpset (Simplifier.simpset_of (Proof_Context.init_global @{theory Lib}))


fun in_mresults_ctxt ctxt = ctxt
    |> put_Lib_simpset
    |> (fn ctxt => ctxt addsimps [@{thm in_mresults_export}, @{thm in_mresults_bind}])
    |> Splitter.del_split @{thm if_split}

fun prove_qad ctxt term tac = Goal.prove ctxt [] [] term
  (K (if Config.get ctxt quick_and_dirty andalso false
      then ALLGOALS (Skip_Proof.cheat_tac ctxt)
      else tac));

fun preannotate_ss ctxt = ctxt
  |> put_simpset HOL_basic_ss
  |> (fn ctxt => ctxt addsimps [@{thm K_bind_def}])
  |> simpset_of

fun in_mresults_ss ctxt = ctxt
  |> put_Lib_simpset
  |> (fn ctxt => ctxt addsimps [@{thm in_mresults_export}, @{thm in_mresults_bind}])
  |> Splitter.del_split @{thm if_split}
  |> simpset_of


val in_mresults_cs = Classical.claset_of (Proof_Context.init_global @{theory Lib});

fun annotate_tac ctxt asm = let
    val asm' = simplify (put_simpset (preannotate_ss ctxt) ctxt) asm;
    val annotated = build_annotate (Thm.concl_of asm');
    val ctxt' = Classical.put_claset in_mresults_cs (put_simpset (in_mresults_ss ctxt) ctxt)
    val thm = prove_qad ctxt (Logic.mk_implies (Thm.concl_of asm', annotated))
                   (auto_tac ctxt'
                    THEN ALLGOALS (TRY o blast_tac ctxt'));
  in
    cut_facts_tac [asm' RS thm] 1
  end
  handle SAME => no_tac;

fun annotate_goal_tac ctxt
  = REPEAT_DETERM1 (subgoal_asm_as_thm (annotate_tac ctxt) ctxt 1
       ORELSE (eresolve_tac ctxt [exE] 1));

val annotate_method =
  Scan.succeed (fn ctxt => Method.SIMPLE_METHOD (annotate_goal_tac ctxt))
    : (Proof.context -> Method.method) context_parser;

\<close>

method_setup annotate = \<open>annotate_method\<close> "tries to annotate"

lemma use_valid_mresults:
  "\<lbrakk> (rv, s', s) \<in> mresults f; \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> P s \<longrightarrow> Q rv s'"
  by (auto simp: mresults_def valid_def)

lemma mresults_validI:
  "\<lbrakk> \<And>rv s' s. (rv, s', s) \<in> mresults f \<Longrightarrow> P s \<longrightarrow> Q rv s' \<rbrakk>
        \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (auto simp: mresults_def valid_def)

ML \<open>

val use_valid_mresults = @{thm use_valid_mresults};

val mresults_export_bindD = @{thms mresults_export_bindD};

fun dest_mresults_tac t = Seq.of_list ([t] RL mresults_export_bindD);

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
        |> Thm.instantiate ([], [(Term.dest_Var v, ct v')])
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
    val uses = asms' RL [use_valid_mresults];
    val wp_rules'' = wp_rules' RL uses;
  in
    apply2 flat (map_split (get_rule_uses ctxt) wp_rules'')
  end;

fun tac_with_wp_simps_strgs ctxt rules tac =
  subgoal_asm_as_thm (fn asm => let
    val (simps, strgs) = get_wp_simps_strgs ctxt rules [asm]
  in
    cut_facts_tac [asm] 1 THEN tac (simps, strgs)
  end) ctxt;

val mresults_validI = @{thm mresults_validI};

fun postcond_ss ctxt = ctxt
    |> put_simpset HOL_basic_ss
    |> (fn ctxt => ctxt addsimps [@{thm pred_conj_def}])
    |> simpset_of

fun wp_default_ss ctxt = ctxt
    |> put_simpset HOL_ss
    |> Splitter.del_split @{thm if_split}
    |> simpset_of

fun raise_tac s = all_tac THEN (fn _ => error s);

fun wpx_tac ctxt rules
  = TRY (resolve_tac ctxt [mresults_validI] 1)
    THEN (full_simp_tac (put_simpset (postcond_ss ctxt) ctxt) 1)
    THEN TRY (annotate_goal_tac ctxt)
    THEN tac_with_wp_simps_strgs ctxt rules (fn (simps, strgs) =>
      REPEAT_DETERM1
        (CHANGED (full_simp_tac (put_simpset (wp_default_ss ctxt) ctxt addsimps simps) 1)
          ORELSE Strengthen.default_strengthen ctxt strgs 1)
    ) 1;

val wpx_method = Attrib.thms >> curry (fn (ts, ctxt) =>
  Method.SIMPLE_METHOD (wpx_tac ctxt ts));

\<close>

method_setup wpx = \<open>wpx_method\<close> "experimental wp method"

lemma foo:
  "(rv, s', s) \<in> mresults (do x \<leftarrow> get; y \<leftarrow> get; put (x + y :: nat); return () od)
        \<Longrightarrow> s' = s + s"
  apply annotate
  apply wpx
  done

lemma foo2:
  "(rv, s', s) \<in> mresults (do x \<leftarrow> get; y \<leftarrow> get; put (if z = Suc 0 then x + y else x + y + z); return () od)
        \<Longrightarrow> s' = s + s + (if z = Suc 0 then 0 else z)"
  apply wpx
  apply simp
  done

text \<open>Have played around with it, the issues are:
  1: Need to deal with non-linear code, known issue.
  2: Using fastforce in annotate isn't cutting the mustard, need to automate better.
     Probably half the issue is that there are too many simp rules available.
  3: Related to (2), there's the question of whether you can simplify code enough
     once it's been annotated. This may re-raise the specter of annotation on demand.
  4: It's hard to tell whether it's worked or not.
  5: Structural rules don't really work - rules that want to transform the whole
     postcondition once we get up to a particular point. Related to 4, it's hard to
     say where that point is hit.
  6: Performance problems with getting the set of available rules.
\<close>

lemma valid_strengthen_with_mresults:
  "\<lbrakk> \<And>s rv s'. \<lbrakk> (rv, s', s) \<in> mresults f;
           wpex_name_for_id (Q' s rv s') \<rbrakk> \<Longrightarrow> Q rv s';
       \<And>prev_s. \<lbrace>P prev_s\<rbrace> f \<lbrace>Q' prev_s\<rbrace> \<rbrakk>
     \<Longrightarrow> \<lbrace>\<lambda>s. P s s\<rbrace> f \<lbrace>Q\<rbrace>"
  apply atomize
  apply (clarsimp simp: valid_def mresults_def wpex_name_for_id_def)
  apply blast
  done

lemma wpex_name_for_idE: "wpex_name_for_id P \<Longrightarrow> P"
  by (simp add: wpex_name_for_id_def)

ML \<open>

val valid_strengthen_with_mresults = @{thm valid_strengthen_with_mresults};
val wpex_name_for_idE = @{thm wpex_name_for_idE};

fun wps_tac ctxt rules =
let
  (* avoid duplicate simp rule etc warnings: *)
  val ctxt = Context_Position.set_visible false ctxt
in
  resolve_tac ctxt [valid_strengthen_with_mresults] 1
  THEN (safe_simp_tac (put_simpset (postcond_ss ctxt) ctxt) 1)
  THEN Subgoal.FOCUS (fn focus => let
      val ctxt = #context focus;
      val (simps, _) = get_wp_simps_strgs ctxt rules (#prems focus);
    in CHANGED (simp_tac (put_simpset (wp_default_ss ctxt) ctxt addsimps simps) 1) end) ctxt 1
  THEN eresolve_tac ctxt [wpex_name_for_idE] 1
end

val wps_method = Attrib.thms >> curry
  (fn (ts, ctxt) => Method.SIMPLE_METHOD (wps_tac ctxt ts));

\<close>

method_setup wps = \<open>wps_method\<close> "experimental wp simp method"

lemma foo3:
  "\<lbrace>P\<rbrace> do v \<leftarrow> return (Suc 0); return (Suc (Suc 0)) od \<lbrace>(=)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_seq_ext)+
    apply (wps | rule hoare_vcg_prop)+
  oops

end
