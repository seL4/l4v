(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory AutoCorresModifiesProofs
imports
  "CBaseRefine.L4VerifiedLinks"
  "CLib.SIMPL_Lemmas"
begin

text \<open>
  Generate modifies specs, i.e. specifications of which globals fields
  may potentially be modified by each function.

  It turns out that ac_corres is not strong enough to automagically
  transfer C-parser's modifies theorems across to the AutoCorres functions.
  This is because the modifies specs are unconditional, whereas our
  ac_corres theorems have preconditions on the initial states.

  In other words, the modifies spec is a syntactic property of a function
  rather than a semantic one. Fortunately, this also makes it straightforward
  to prove them from scratch over our newly-generated functions.
\<close>

section \<open>Rules for modifies proof method\<close>

text \<open>
  Transferring modifies rules for un-translated functions.
  These functions are defined to be equivalent to their SIMPL specs
  (via L1_call_simpl), so the limitations of ac_corres do not apply.
\<close>
lemma autocorres_modifies_transfer:
  notes bind_wp[wp]
  fixes \<Gamma> globals f' f_'proc modifies_eqn P xf
  assumes f'_def: "f' \<equiv> AC_call_L1 P globals xf (L1_call_simpl check_termination \<Gamma> f_'proc)"
  assumes f_modifies: "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call f_'proc {t. modifies_eqn (globals t) (globals \<sigma>)}"
  shows "\<lbrace> \<lambda>s. s = \<sigma> \<rbrace> f' \<lbrace> \<lambda>_ s. modifies_eqn s \<sigma> \<rbrace>"
  apply (clarsimp simp: f'_def AC_call_L1_def L2_call_L1_def L1_call_simpl_def)
  apply (simp add: liftM_def bind_assoc)
  apply wpsimp
  apply (clarsimp simp: in_monad select_def split: xstate.splits)
  by (case_tac xa; clarsimp dest!: exec_normal[OF singletonI _ f_modifies[rule_format]])

text \<open>
  A monadic Hoare triple for a modifies spec looks like
    "\<lbrace>\<lambda>s. s = \<sigma>\<rbrace> prog \<lbrace>\<lambda>s. \<exists>x1 x2... s = \<sigma>\<lparr>field1 := x1, ...\<rparr>\<rbrace>"
  where (fieldk, xk) are the possibly-modified fields.
  To prove it, we rewrite the precondition to an invariant:
     \<lbrace>\<lambda>s. \<exists>x1 x2... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace> prog \<lbrace>\<lambda>_ s. \<exists>x1 x2... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace>
  Then we carry the invariant through each statement of the program.
\<close>

text \<open>
  Adapter for apply rules to an invariant goal.
  We allow "I" and "I'" to be different (in our modifies proof, "I"
  will have \<exists>-quantified vars lifted out).
\<close>
lemma valid_inv_weaken:
  "\<lbrakk> valid P f (\<lambda>_. R); \<And>s. I s \<Longrightarrow> P s; \<And>s. R s \<Longrightarrow> I' s \<rbrakk> \<Longrightarrow> valid I f (\<lambda>_. I')"
  by (fastforce simp: valid_def)

text \<open>
  Our function modifies rules have a schematic precond,
  so this rule avoids weakening the invariant when applying those rules
  and ending up with an underspecified P.
\<close>
lemma valid_inv_weaken':
  "\<lbrakk> valid I f (\<lambda>_. Q); \<And>s. Q s \<Longrightarrow> I' s \<rbrakk> \<Longrightarrow> valid I f (\<lambda>_. I')"
  by (rule valid_inv_weaken)

text \<open>
  Used by modifies_initial_tac to instantiate a schematic precondition
  to an invariant.
\<close>
lemma valid_invI:
  "valid I f (\<lambda>_. I) \<Longrightarrow> valid I f (\<lambda>_. I)"
  by -

text \<open>For rewriting foralls in premises.\<close>
lemma All_to_all:
  "Trueprop (\<forall>x. P x) \<equiv> (\<And>x. P x)"
  by presburger

subsection \<open>Hoare rules for state invariants\<close>
named_theorems valid_inv

lemmas [valid_inv] =
  fail_inv
  gets_inv
  return_inv
  hoare_K_bind

lemma when_inv[valid_inv]:
  "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> \<lbrace>I\<rbrace> when c f \<lbrace>\<lambda>_. I\<rbrace>"
  apply wp
   apply auto
  done

lemma bind_inv[valid_inv]:
  "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> (\<And>x. \<lbrace>I\<rbrace> g x \<lbrace>\<lambda>_. I\<rbrace>) \<Longrightarrow> \<lbrace>I\<rbrace> f >>= g \<lbrace>\<lambda>_. I\<rbrace>"
  apply (wp; assumption)
  done

lemma guard_inv[valid_inv]:
  "\<lbrace>I\<rbrace> guard G \<lbrace>\<lambda>_. I\<rbrace>"
  by (fastforce simp: valid_def)

lemma modify_inv[valid_inv]:
  "(\<And>s. I s \<Longrightarrow> I (f s)) \<Longrightarrow> \<lbrace>I\<rbrace> modify f \<lbrace>\<lambda>_. I\<rbrace>"
  apply wp
  by simp

lemma skip_inv[valid_inv]:
  "\<lbrace>I\<rbrace> skip \<lbrace>\<lambda>_. I\<rbrace>"
  by (rule skip_wp)

lemma select_inv[valid_inv]:
  "\<lbrace>I\<rbrace> select f \<lbrace>\<lambda>_. I\<rbrace>"
  by (rule hoare_weaken_pre, rule select_wp, blast)

lemma condition_inv[valid_inv]:
  "\<lbrace>I\<rbrace> t \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> \<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> \<lbrace>I\<rbrace> condition c t f\<lbrace>\<lambda>_. I\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (rule condition_wp)
    apply auto
  done

lemma whileLoop_inv[valid_inv]:
  "\<lbrakk>\<And>r. \<lbrace>I\<rbrace> b r \<lbrace>\<lambda>_. I\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> whileLoop c b r \<lbrace>\<lambda>_. I\<rbrace>"
  apply (rule whileLoop_wp)
   apply (blast intro: hoare_weaken_pre)
  apply assumption
  done

lemma valid_case_prod_inv[valid_inv]:
  "(\<And>x y. \<lbrace>I\<rbrace> f x y \<lbrace>\<lambda>_. I\<rbrace>) \<Longrightarrow> \<lbrace>I\<rbrace> case v of (x, y) \<Rightarrow> f x y \<lbrace>\<lambda>_. I\<rbrace>"
  apply wp
  apply auto
  done

lemma unknown_inv[valid_inv]:
  "\<lbrace>I\<rbrace> unknown \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold unknown_def)
  apply (rule select_inv)
  done

lemma throwError_inv[valid_inv]:
  "\<lbrace>I\<rbrace> throwError e \<lbrace>\<lambda>_. I\<rbrace>"
  by wp

lemma catch_inv[valid_inv]:
  "\<lbrakk> \<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace>; \<And>e. \<lbrace>I\<rbrace> h e \<lbrace>\<lambda>_. I\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> catch f h \<lbrace>\<lambda>_. I\<rbrace>"
  apply wpsimp
    apply assumption
   apply (simp add: validE_def)
  by assumption

lemma whileLoopE_inv[valid_inv]:
  "(\<And>r. \<lbrace>I\<rbrace> b r \<lbrace>\<lambda>_. I\<rbrace>) \<Longrightarrow> \<lbrace>I\<rbrace> whileLoopE c b r \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold whileLoopE_def)
  apply (rule whileLoop_inv)
  apply (auto simp: lift_def split: sum.splits intro: throwError_inv)
  done

lemma bindE_inv[valid_inv]:
  "\<lbrakk> \<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace>; \<And>x. \<lbrace>I\<rbrace> g x \<lbrace>\<lambda>_. I\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> f >>=E g \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold bindE_def)
  apply (rule bind_inv)
  apply (auto simp: lift_def split: sum.splits intro: throwError_inv)
  done

lemma returnOk_inv[valid_inv]:
  "\<lbrace>I\<rbrace> returnOk x \<lbrace>\<lambda>_. I\<rbrace>"
  apply (simp add: returnOk_def)
  done

lemma liftE_inv[valid_inv]:
  "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> \<lbrace>I\<rbrace> liftE f \<lbrace>\<lambda>_. I\<rbrace>"
  by wp

lemma getsE_inv[valid_inv]:
  "\<lbrace>I\<rbrace> getsE f \<lbrace>\<lambda>r. I\<rbrace>"
  apply (unfold getsE_def)
  apply (blast intro: liftE_inv gets_inv)
  done

lemma skipE_inv[valid_inv]:
  "\<lbrace>I\<rbrace> skipE \<lbrace>\<lambda>r. I\<rbrace>"
  apply (unfold skipE_def)
  apply (blast intro: liftE_inv returnOk_inv)
  done

lemma modifyE_inv[valid_inv]:
  "(\<And>s. I s \<Longrightarrow> I (f s)) \<Longrightarrow> \<lbrace>I\<rbrace> modifyE f \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold modifyE_def)
  apply (blast intro: liftE_inv modify_inv)
  done

lemma guardE_inv[valid_inv]:
  "\<lbrace>I\<rbrace> guardE G \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold guardE_def)
  apply (blast intro: liftE_inv guard_inv)
  done

lemma whenE_inv[valid_inv]:
  "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> \<lbrace>I\<rbrace> whenE c f \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold whenE_def)
  apply (auto intro: returnOk_inv)
  done

lemma unless_inv[valid_inv]:
  "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> \<lbrace>I\<rbrace> unless c f \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold unless_def)
  by (rule when_inv)

lemma unlessE_inv[valid_inv]:
  "\<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace> \<Longrightarrow> \<lbrace>I\<rbrace> unlessE c f \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold unlessE_def)
  by (auto intro: returnOk_inv)

lemma handleE'_inv[valid_inv]:
  "\<lbrakk> \<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace>; \<And>e. \<lbrace>I\<rbrace> h e \<lbrace>\<lambda>_. I\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> handleE' f h \<lbrace>\<lambda>_. I\<rbrace>"
  by (fastforce simp: handleE'_def intro: return_inv bind_inv split: sum.splits)

lemma handleE_inv[valid_inv]:
  "\<lbrakk> \<lbrace>I\<rbrace> f \<lbrace>\<lambda>_. I\<rbrace>; \<And>e. \<lbrace>I\<rbrace> h e \<lbrace>\<lambda>_. I\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> handleE f h \<lbrace>\<lambda>_. I\<rbrace>"
  apply (unfold handleE_def)
  by (rule handleE'_inv)

text \<open>@{term measure_call} appears in AutoCorres-generated calls to recursive functions.\<close>
lemma measure_call_inv[valid_inv]:
  "\<lbrakk>\<And>m. \<lbrace>I\<rbrace> f m \<lbrace>\<lambda>_. I\<rbrace>\<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> measure_call f \<lbrace>\<lambda>_. I\<rbrace>"
  by (fastforce simp: measure_call_def valid_def)

text \<open>
  Recursion base case for AutoCorres-generated specs.
  NB: we don't make this valid_inv because it conflicts with bind_inv.
      Instead we apply it manually.
\<close>
lemma modifies_recursive_0: "\<lbrace>I\<rbrace> do guard (\<lambda>_. (0 :: nat) < 0); f od \<lbrace>\<lambda>_. I\<rbrace>"
  by simp

text \<open>These rules are currently sufficient for all the kernel code.\<close>
thm valid_inv


section \<open>Modifies proof procedure\<close>
text \<open>
  The most important assumptions are currently:
  - skip_heap_abs is set; we don't deal with lifted_globals
  - all functions are translated to the nondet_monad
  - we assume a specific format of modifies rule from the C-parser
    (see comment for gen_modifies_prop)
  - function_name_prefix="" and function_name_suffix="'" as per default
    (FIXME: get these from function_info once it's been fixed)

  The top-level procedure gets all kernel functions in topological order,
  then does the modifies proofs for each function (or recursive function group).
  The "scope" option should be supported (TODO: but not yet tested) and
  in that case the C-parser modifies rules will be transferred directly.
\<close>

ML \<open>
structure AutoCorresModifiesProofs = struct

(* Translate a term, top-down, stopping once a conversion has been applied.
 * trans is an assoc-list of terms to translate.
 * Bound vars in trans are interpreted relative to outside t. *)
fun translate_term trans t = case assoc (trans, t) of SOME t' => t' | NONE =>
      case t of f $ x => translate_term trans f $ translate_term trans x
              | Abs (v, vT, b) => Abs (v, vT, translate_term (map (apply2 (incr_boundvars 1)) trans) b)
              | _ => t;

(* Remove "Hoare.meq" and "Hoare.mex" scaffolding from SIMPL modifies specs *)
fun modifies_simp ctxt =
  Conv.fconv_rule
    (Raw_Simplifier.rewrite ctxt true
      @{thms meq_def[THEN eq_reflection] mex_def[THEN eq_reflection]});

fun modifies_simp_term ctxt =
  Raw_Simplifier.rewrite_term (Proof_Context.theory_of ctxt)
    @{thms meq_def[THEN eq_reflection] mex_def[THEN eq_reflection]} [];

(* Translate c-parser's "modifies" specs of the form
 *   \<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call f_'proc {t. mex x1... meq (globals t) ((globals s)\<lparr>f1 := x1...\<rparr>)}
 * to specs on the AutoCorres-generated monad
 *   \<lbrace>\<lambda>s. s = \<sigma>\<rbrace> f' \<lbrace>\<lambda>_ s. \<exists>x1... \<sigma> = s\<lparr>f1 := x1...\<rparr>\<rbrace>
 *
 * This involves:
 *  - talking about the "globals" state instead of "globals myvars"
 *  - removing "meq" and "mex" which are unnecessary for our proof method
 *    and have buggy syntax translations
 *  - using the monadic hoare predicate
 *
 * Returns tuple of (state var, function arg vars, measure var, prop).
 * The returned vars are Free in the prop; the measure var is NONE for non-recursive functions.
 *)
fun gen_modifies_prop ctxt
      (fn_info: FunctionInfo.function_info Symtab.table)
      (prog_info: ProgramInfo.prog_info) f_name c_prop = let
  val f_info = the (Symtab.lookup fn_info f_name);
  val globals_type = #globals_type prog_info;
  val globals_term = #globals_getter prog_info;
  val ac_ret_type = #return_type f_info;
  val state0_var = Free ("\<sigma>", globals_type);

  val @{term_pat "Trueprop (\<forall>\<sigma>. _\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call ?f_'proc {t. ?c_modifies_eqn})"} = c_prop;
  (* Bound 0 = s, Bound 1 = \<sigma> in c_prop *)
  val modifies_eqn = c_modifies_eqn |> translate_term
                       [(globals_term $ Bound 0, Bound 0), (globals_term $ Bound 1, state0_var)];
  val modifies_postcond = Abs (Name.uu_, ac_ret_type, Abs ("s", globals_type, modifies_eqn))
                          |> modifies_simp_term ctxt;
  val arg_vars = map Free (#args f_info);
  val measure_var = if FunctionInfo.is_function_recursive f_info
                    (* will not clash with arg_vars as C identifiers do not contain primes *)
                    then SOME (Free ("measure'", @{typ nat})) else NONE;
  val f_const = #const f_info
  val f_call = betapplys (f_const, (case measure_var of SOME v => [v] | NONE => []) @ arg_vars);
  val modifies_prop = @{mk_term "Trueprop (\<lbrace>\<lambda>s. s = ?state\<rbrace> ?call \<lbrace>?postcond\<rbrace>)" (state, call, postcond)}
                         (state0_var, f_call, modifies_postcond);
  in (state0_var, arg_vars, measure_var, modifies_prop) end;

(* Solve invariant goals of the form
 *   \<And>s. (\<exists>x1 x2... s = \<sigma>\<lparr>field1 := x1, field2 := x2, ...\<rparr>) \<Longrightarrow>
 *       (\<exists>x1 x2... f s = \<sigma>\<lparr>field1 := x1, field2 := x2, ...\<rparr>)
 * where f is some update function (usually id, but for modify statements
 * it is the modifying function).
 * We assume that s is all-quantified and \<sigma> is free. *)
fun modifies_invariant_tac quiet_fail ctxt n st = if Thm.nprems_of st = 0 then no_tac st else let
  val globals_typ = Syntax.read_typ ctxt "globals";
  val globals_cases = Proof_Context.get_thm ctxt "globals.cases";
  val globals_splits = hd (Proof_Context.get_thms ctxt "globals.splits");

  (* The fastest way (so far) is manually splitting s and \<sigma>, then simplifying.
   * The Isar analogue would be
   *   elim exE, case_tac "s", case_tac "\<sigma>", simp
   *)

  (* \<sigma> is free, so obtaining the split rule is straightforward *)
  val sigma_free = Free ("\<sigma>", globals_typ);
  val case_sigma = Drule.infer_instantiate' ctxt [SOME (Thm.cterm_of ctxt sigma_free)] globals_cases;

  (* However, s is bound and accessing it requires some awkward contortions *)
  (* globals.splits is an equation that looks like
   *   (\<And>r. ?P r) \<equiv> (\<And>fields... ?P {fields})
   * We walk down the current goal and apply globals.splits to the quantifier for the correct s.
   * The correct s would be the one that appears in our invariant assumption of the form
   *   s = \<sigma>\<lparr>updates...\<rparr>
   * (We removed the preceding \<exists>'s using exE beforehand.) *)
  fun split_s_tac st = let
    val subgoal = Logic.get_goal (Thm.prop_of st) n;
    val prems = Logic.strip_assums_hyp subgoal;
    val env = Term.strip_all_vars subgoal |> map snd |> rev;
    fun find @{term_pat "Trueprop (?s = _)"} =
          (case s of Bound s_idx => if fastype_of1 (env, s) = globals_typ then [s_idx] else []
                   | _ => [])
      | find _ = []
    val s_idx = case maps find prems of
                    [] => raise THM ("modifies_invariant_tac: failed to find invariant assumption", n, [st])
                  | idx::_ => idx;
    fun split_conv idx (Const ("Pure.all", _) $ Abs (_, _, body)) ct =
            if idx > s_idx then Conv.forall_conv (fn _ => split_conv (idx - 1) body) ctxt ct else let
              val (_, cP) = Thm.dest_comb ct
              val inst = Drule.infer_instantiate' ctxt [SOME cP] globals_splits
              (*val _ = @{trace} (cP, inst, case Thm.prop_of inst of @{term_pat "?x \<equiv> _"} => x, Thm.term_of ct);*)
              in inst end
      | split_conv _ _ ct = Conv.no_conv ct; (* shouldn't happen *)
    in Conv.gconv_rule (split_conv (length env - 1) subgoal) n st |> Seq.single end
    handle e as THM _ => if quiet_fail then no_tac st else Exn.reraise e;

  (* avoid contextual rules, like split_pair_Ex, that lead simp down the garden path *)
  val globals_record_simps = maps (Proof_Context.get_thms ctxt) ["globals.ext_inject", "globals.update_convs"];
  in st |>
      (DETERM (REPEAT (eresolve_tac ctxt @{thms exE} n)) THEN
       split_s_tac THEN
       resolve_tac ctxt [case_sigma] n THEN
       SOLVES (asm_full_simp_tac (put_simpset HOL_ss ctxt addsimps globals_record_simps) n))
  end

(* Convert initial modifies goal of the form
 *   \<lbrace>\<lambda>s. s = \<sigma>\<rbrace> prog \<lbrace>\<lambda>_ s. \<exists>x1... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace>
 * to one where the modifies is expressed as an invariant:
 *   \<lbrace>\<lambda>s. \<exists>x1... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace> prog \<lbrace>\<lambda>_ s. \<exists>x1... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace>
 *)
fun modifies_initial_tac ctxt n =
  resolve_tac ctxt @{thms hoare_weaken_pre} n THEN
  resolve_tac ctxt @{thms valid_invI} n;

(* Incremental nets. (Why isn't this standard??) *)
type incr_net = (int * thm) Net.net * int;
fun build_incr_net rls = (Tactic.build_net rls, length rls);
fun add_to_incr_net th (net, sz) =
  (Net.insert_term (K false) (Thm.concl_of th, (sz + 1, th)) net, sz + 1); (* guessed from tactic.ML *)
fun net_of (n: incr_net) = fst n;

(* Apply a callee's modifies rule to its call site.
 * The current goal should be expressed as an invariant:
 *   \<lbrace>\<lambda>s. \<exists>x1... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace> f args... \<lbrace>\<lambda>_ s. \<exists>x1... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace>
 * We assume that callee_modifies contains the correct modifies rule
 * and is unique (no backtracking).
 *)
fun modifies_call_tac (callee_modifies: incr_net) ctxt n = DETERM (
  (* We move the existentials out of the precondition:
     \<And>x1... \<lbrace>\<lambda>s. s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace> f args... \<lbrace>\<lambda>_ s. \<exists>x1... s = \<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace> *)
  REPEAT (resolve_tac ctxt @{thms hoare_ex_pre} n) THEN
  resolve_tac ctxt @{thms valid_inv_weaken'} n THEN
  (* Then we can apply the modifies rule, which looks like:
     \<lbrace>\<lambda>s. s = ?\<sigma>\<rbrace> f ?args... \<lbrace>\<lambda>_ s. \<exists>x1... s = ?\<sigma>\<lparr>field1 := x1, ...\<rparr> \<rbrace> *)
  DETERM (resolve_from_net_tac ctxt (net_of callee_modifies) n) THEN
  modifies_invariant_tac true ctxt n);

(* VCG for trivial state invariants, such as globals modifies specs.
 * Takes vcg rules from "valid_inv". *)
val valid_invN = Context.theory_name { long=true } @{theory} ^ ".valid_inv"
fun modifies_vcg_tac leaf_tac ctxt n = let
  val vcg_rules = Named_Theorems.get ctxt valid_invN |> Tactic.build_net;
  fun vcg n st = Seq.make (fn () => let
        (* do not backtrack once we have matched vcg_rules *)
        val st' = DETERM (resolve_from_net_tac ctxt vcg_rules n) st;
        in Seq.pull ((case Seq.pull st' of
                          NONE => leaf_tac ctxt n
                        | SOME _ => (K (K st') THEN_ALL_NEW vcg) n) st) end);
  in vcg n end;

(* Specify and prove modifies for one (non-recursive) function. *)
fun do_modifies_one ctxt fn_info (prog_info: ProgramInfo.prog_info) callee_modifies f_name = let
  val c_modifies_prop = Thm.prop_of (Proof_Context.get_thm ctxt (f_name ^ "_modifies"));
  val (state0_var, arg_vars, measure_var, ac_modifies_prop) =
        gen_modifies_prop ctxt fn_info prog_info f_name c_modifies_prop;
  val _ = if isSome measure_var then error ("do_modifies_one bug: got recursive function " ^ f_name) else ();
  val f_def = the (Symtab.lookup fn_info f_name) |> #definition;
  fun leaf_tac ctxt n = FIRST [modifies_call_tac callee_modifies ctxt n, modifies_invariant_tac true ctxt n,
                               print_tac ctxt ("do_modifies_one failed (goal " ^ string_of_int n ^ ")")];
  val thm = Goal.prove ctxt (map (fn (Free (v, _)) => v) (state0_var :: arg_vars)) [] ac_modifies_prop
              (K (NO_CONTEXT_TACTIC ctxt (Method.unfold [f_def] ctxt []) THEN
                  modifies_initial_tac ctxt 1 THEN
                  modifies_vcg_tac leaf_tac ctxt 1 THEN
                  leaf_tac ctxt 1));
in thm end;

(* Make a list of conjunctions. *)
fun mk_conj_list [] = @{term "HOL.True"}
  | mk_conj_list [x] = x
  | mk_conj_list (x::xs) = HOLogic.mk_conj (x, (mk_conj_list xs))

(* Specify and prove modifies for a recursive function group. *)
fun do_modifies_recursive ctxt fn_info (prog_info: ProgramInfo.prog_info) (callee_modifies: incr_net) f_names = let
  (* Collect information *)
  val c_modifies_props = map (fn f_name => Thm.prop_of (Proof_Context.get_thm ctxt (f_name ^ "_modifies"))) f_names;
  val modifies_props =
    map2 (gen_modifies_prop ctxt fn_info prog_info) f_names c_modifies_props;
  val f_defs = map (fn f_name => the (Symtab.lookup fn_info f_name) |> #definition) f_names;

  fun free_name (Free (v, _)) = v;

  (*
   * We do the proof in three parts.
   *
   * First, we prove modifies on the base case (measure' = 0) for each function.
   * This is trivially handled by @{thm modifies_recursive_0}.
   *)
  val base_case_props =
    map (fn (state0_var, arg_vars, SOME measure_var, prop) =>
      (state0_var, arg_vars, subst_free [(measure_var, @{term "0 :: nat"})] prop))
      modifies_props;
  val base_case_leaf_tac = modifies_invariant_tac true;
  val base_case_thms =
    map2 (fn (state0_var, arg_vars, prop) => fn f_def =>
            Goal.prove ctxt (map free_name (state0_var :: arg_vars)) [] prop
              (K (EqSubst.eqsubst_tac ctxt [0] [f_def] 1 THEN
                  modifies_initial_tac ctxt 1 THEN
                  resolve_tac ctxt @{thms modifies_recursive_0} 1 THEN
                  base_case_leaf_tac ctxt 1)))
         base_case_props f_defs;

  (*
   * Next, we prove the induction step "measure'" \<rightarrow> "Suc measure'".
   * We create an induction hypothesis for each function, quantifying
   * over its variables:
   *   \<And>\<sigma> arg1 arg2... \<lbrace>\<lambda>s. s = \<sigma>\<rbrace> f measure' arg1 arg2... \<lbrace>\<lambda>s. \<exists>x1... s = \<sigma>\<lparr>f1 := x1...\<rparr>\<rbrace>
   * Then, we can perform the VCG-based proof as usual, using these
   * hypotheses in modifies_call_tac.
   *)
  val inductive_hyps =
    map (fn (state0_var, arg_vars, SOME measure_var, prop) =>
           fold Logic.all (state0_var :: arg_vars) prop)
        modifies_props;
  val inductive_props =
    map (fn (state0_var, arg_vars, SOME measure_var, prop) =>
           (state0_var, arg_vars, measure_var, subst_free [(measure_var, @{term "Suc"} $ measure_var)] prop))
        modifies_props;
  val inductive_thms =
    map2 (fn (state0_var, arg_vars, measure_var, prop) => fn f_def =>
            Goal.prove ctxt (map free_name (state0_var :: measure_var :: arg_vars)) inductive_hyps prop
              (fn {context, prems} => let
                  val callee_modifies' = fold add_to_incr_net prems callee_modifies;
                  fun inductive_leaf_tac ctxt n =
                    FIRST [modifies_call_tac callee_modifies' ctxt n, modifies_invariant_tac true ctxt n];
                  in EqSubst.eqsubst_tac ctxt [0] [f_def] 1 THEN
                     (* AutoCorres specifies recursive calls to use "measure - 1",
                      * which in our case becomes "Suc measure - 1". Simplify to "measure". *)
                     NO_CONTEXT_TACTIC ctxt (Method.unfold @{thms diff_Suc_1} ctxt []) THEN
                     modifies_initial_tac ctxt 1 THEN
                     modifies_vcg_tac inductive_leaf_tac ctxt 1 THEN
                     inductive_leaf_tac ctxt 1 end))
         inductive_props f_defs

  (*
   * Third, we create a combined modifies prop
   *   (\<forall>\<sigma> arg1... \<lbrace>\<lambda>s. s = \<sigma>\<rbrace> f1 measure' arg1... \<lbrace>...\<rbrace>) \<and>
   *   (\<forall>\<sigma> arg1... \<lbrace>\<lambda>s. s = \<sigma>\<rbrace> f2 measure' arg1... \<lbrace>...\<rbrace>) \<and> ...
   * and apply induction on measure', solving the subgoals using the
   * theorems from before.
   * Note that we quantify over args because arg names may clash between functions.
   *
   * We pre-proved the induction steps separately for convenience
   * (e.g. so we can access the hypotheses as facts instead of premises).
   *)
  fun hd_of_equal [x] = x
    | hd_of_equal (x::xs) = if forall (fn x' => x = x') xs then x else
                              raise TERM ("do_modifies_group bug: unequal terms", xs);
  val (measure_var, final_props) =
    modifies_props
    |> map (fn (state0_var, arg_vars, SOME measure_var, prop) =>
              (measure_var,
               fold (fn Free (v, T) => fn P => HOLogic.mk_all (v, T, P))
                    (state0_var :: arg_vars) (HOLogic.dest_Trueprop prop)))
    |> (fn xs => let
          val props = map snd xs;
          val measure_var = map fst xs |> hd_of_equal;
          in (measure_var, props) end);
  val combined_prop = HOLogic.mk_Trueprop (mk_conj_list final_props);

  fun intro_tac ctxt rls n = TRY ((resolve_tac ctxt rls THEN_ALL_NEW intro_tac ctxt rls) n);
  fun elim_tac ctxt rls n = TRY ((eresolve_tac ctxt rls THEN_ALL_NEW elim_tac ctxt rls) n);

  (*fun maybe_print_tac msg ctxt = print_tac ctxt msg;*)
  fun maybe_print_tac msg ctxt = all_tac;
  (*val _ = @{trace} ("inductive thms", inductive_thms);*)

  val combined_thm =
    Goal.prove ctxt [free_name measure_var] [] combined_prop
      (K (Induct.induct_tac ctxt
            false (* simplifier *)
            [[SOME (NONE, (measure_var, false))]] (* variables *)
            [] (* arbitrary: *)
            [] (* ??? *)
            (SOME @{thms nat.induct}) (* induct rule *)
            [] (* extra thms *)
            1
            THEN
          maybe_print_tac "base case" ctxt THEN
          (* base case *)
          SOLVES (
            (((DETERM o intro_tac ctxt @{thms conjI allI})
              THEN' K (maybe_print_tac "base case'" ctxt))
             THEN_ALL_NEW resolve_tac ctxt base_case_thms) 1
          ) THEN
          maybe_print_tac "inductive case" ctxt THEN
          (* recursive case *)
          SOLVE (
            (((DETERM o (intro_tac ctxt @{thms conjI allI} THEN_ALL_NEW
                         elim_tac ctxt @{thms conjE}) THEN_ALL_NEW
                         (fn n => Conv.gconv_rule
                                    (Raw_Simplifier.rewrite ctxt true @{thms All_to_all}) n
                                  #> Seq.succeed))
              THEN' K (maybe_print_tac "inductive case'" ctxt))
             THEN_ALL_NEW (resolve_tac ctxt inductive_thms THEN_ALL_NEW Method.assm_tac ctxt)) 1
          )));

  (* Finally, we extract theorems for individual functions. *)
  val final_thms =
    HOLogic.conj_elims combined_thm
    |> map (fn thm =>
        thm
        |> Thm.equal_elim (Raw_Simplifier.rewrite ctxt true @{thms All_to_all} (Thm.cprop_of thm))
        |> Thm.forall_elim_vars 0);
  in final_thms end;

(* Prove and store modifies rules for one function or recursive function group. *)
fun prove_modifies
      (fn_info: FunctionInfo.function_info Symtab.table)
      (prog_info: ProgramInfo.prog_info)
      (callee_modifies: incr_net)
      (results: thm Symtab.table)
      (f_names: string list)
      (thm_names: string list)
      ctxt
      : (thm list * Proof.context) option = let
    val f_infos = map (the o Symtab.lookup fn_info) f_names;
    val maybe_thms =
        if length f_names = 1 andalso #is_simpl_wrapper (hd f_infos)
        then let
          val f_name = hd f_names;
          val _ = tracing (f_name ^ " is un-translated; transferring C-parser's modifies rule directly");
          val f_def = the (Symtab.lookup fn_info f_name) |> #definition;
          val orig_modifies = Proof_Context.get_thm ctxt (f_name ^ "_modifies");
          val transfer_thm = @{thm autocorres_modifies_transfer};
          val thm = transfer_thm OF [f_def, orig_modifies];
          in SOME [modifies_simp ctxt thm] end
        else let
          val callees = map (FunctionInfo.all_callees o the o Symtab.lookup fn_info) f_names
                        |> Symset.union_sets |> Symset.dest;
          val missing_callees = callees |> filter_out (fn callee =>
                Symtab.defined results callee orelse member (=) f_names callee);
          in if not (null missing_callees)
             then (warning ("Can't prove modifies; depends on functions without modifies proofs: " ^
                            commas missing_callees);
                   NONE)
             else if length f_names = 1
                  then SOME ([do_modifies_one ctxt fn_info prog_info callee_modifies (hd f_names)])
                  else SOME (do_modifies_recursive ctxt fn_info prog_info callee_modifies f_names) end;
    in case maybe_thms of
           SOME thms => let
             val (_, ctxt) = Local_Theory.notes (map2 (fn thm_name => fn thm =>
                               ((Binding.name thm_name, []), [([thm], [])])) thm_names thms) ctxt;
             in SOME (thms, ctxt) end
         | NONE => NONE
    end;

fun define_modifies_group fn_info prog_info f_names (acc as (callee_modifies, results, ctxt)) =
    (tracing ("Doing modifies proof for: " ^ commas f_names);
     case f_names |> filter (fn f_name =>
            not (isSome (try (Proof_Context.get_thm ctxt) (f_name ^ "_modifies")))) of
         [] =>
           (case prove_modifies fn_info prog_info
                   callee_modifies results f_names
                   (map (fn f_name => f_name ^ "'_modifies") f_names) ctxt of
                NONE => acc
              | SOME (thms, ctxt') => (fold add_to_incr_net thms callee_modifies,
                                       fold Symtab.update_new (f_names ~~ thms) results, ctxt'))
       | missing =>
           (warning ("Can't do proof because C-parser modifies rules are missing for: " ^ commas missing);
                     acc));

(*
 * This is the top-level wrapper that generates modifies rules for the most
 * recently translated set of functions from a given C file.
 *)
fun new_modifies_rules filename ctxt = let
    val all_fn_info = Symtab.lookup (AutoCorresFunctionInfo.get (Proof_Context.theory_of ctxt)) filename |> the;
    val ts_info = FunctionInfo.Phasetab.lookup all_fn_info FunctionInfo.TS |> the;
    val prog_info = ProgramInfo.get_prog_info ctxt filename;
    (* Assume that the user has already generated and named modifies rules
     * for previously-translated callees. *)
    val existing_modifies =
          Symtab.dest ts_info
          |> List.mapPartial (fn (fn_name, fn_def) =>
               try (fn _ => (fn_name, Proof_Context.get_thm ctxt (fn_name ^ "'_modifies"))) ())
          |> Symtab.make;
    (* We will do modifies proofs for these functions *)
    val pending_fn_info =
          Symtab.dest ts_info
          |> List.mapPartial (fn (f, info) =>
               if Symtab.defined existing_modifies f then NONE else SOME (f, info))
          |> Symtab.make;
    val (call_graph, _) = FunctionInfo.calc_call_graph pending_fn_info;
    val (callee_modifies, results, ctxt') =
          fold (define_modifies_group ts_info prog_info)
               (#topo_sorted_functions call_graph |> map Symset.dest)
               (build_incr_net (Symtab.dest existing_modifies |> map snd),
                existing_modifies, ctxt)
in ctxt' end

end;
\<close>

end
