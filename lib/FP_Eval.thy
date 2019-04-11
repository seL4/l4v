(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory FP_Eval
imports
  HOL.HOL
  "ml-helpers/TermPatternAntiquote"
begin

text \<open>
  FP_Eval: efficient evaluator for functional programs.

  The algorithm is similar to @{method simp}, but streamlined somewhat.
  Poorly-scaling simplifier features are omitted, e.g.:
  conditional rules, eta normalisation, rewriting under lambdas, etc.

  See FP_Eval_Tests for examples and tests. Currently, only
  ML conversions and tactics are provided.

  Features:
    \<bullet> Low overhead (usually lower than @{method simp})
    \<bullet> Applicative-order evaluation to WHNF (doesn't rewrite under lambdas)
    \<bullet> Manual specification of rewrite rules, no global context
    \<bullet> Cong rules supported for controlling evaluation (if, let, case, etc.)
    \<bullet> Finer control than simp: explicit skeletons, debugging callbacks,
       perf counters (see signature for FP_Eval.eval')

  Major TODOs:
    \<bullet> Preprocess rewrite rules for speed
    \<bullet> Optimize eval_rec more
    \<bullet> Support for simprocs (ideally with static checks)
    \<bullet> Simple tactical and Isar method wrappers
    \<bullet> Automatic ruleset builders
    \<bullet> Static analysis for rules:
      \<bullet> Confluence, termination
      \<bullet> Completeness
      \<bullet> Running time?
    \<bullet> Dynamic analysis e.g. unused rules

  Work in progress.
\<close>

locale FP_Eval begin
lemma bool_prop_eq_True:
  "Trueprop P \<equiv> (P \<equiv> True)"
  by (simp add: atomize_eq)

lemma bool_prop_eq_False:
  "Trueprop (\<not>P) \<equiv> (P \<equiv> False)"
  by (simp add: atomize_eq)
end

ML \<open>
structure FP_Eval = struct

(*** Utils ***)

(* O(1) version of thm RS @{thm eq_reflection} *)
fun then_eq_reflection thm = let
  val (x, y) = Thm.dest_binop (Thm.dest_arg (Thm.cprop_of thm));
  val cT = Thm.ctyp_of_cterm x;
  val rule = @{thm eq_reflection} |> Thm.instantiate' [SOME cT] [SOME x, SOME y];
  in Thm.implies_elim rule thm end;

fun bool_conv_True thm =
      Thm.instantiate ([], [((("P", 0), @{typ bool}),
                             Thm.dest_arg (Thm.cprop_of thm))])
                      @{thm FP_Eval.bool_prop_eq_True}
      |> (fn conv => Thm.equal_elim conv thm);

fun bool_conv_False thm =
      Thm.instantiate ([], [((("P", 0), @{typ bool}),
                             Thm.dest_arg (Thm.dest_arg (Thm.cprop_of thm)))])
                      @{thm FP_Eval.bool_prop_eq_False}
      |> (fn conv => Thm.equal_elim conv thm);

(* Emulate simp's conversion of non-equational rules to "P \<equiv> True", etc. *)
fun maybe_convert_eqn thm =
      (* HACK: special case to transform @{thm refl} to "(HOL.eq ?t ?t) \<equiv> True",
               as the default result of "?t \<equiv> ?t" isn't what we want *)
      if Thm.eq_thm_prop (thm, @{thm refl}) then SOME (bool_conv_True thm) else
      (case Thm.prop_of thm of
           @{term_pat "Trueprop (_ = _)"} =>
             SOME (then_eq_reflection thm)
         | @{term_pat "Trueprop (\<not> _)"} =>
             SOME (bool_conv_False thm)
         | @{term_pat "_ \<equiv> _"} => SOME thm
         | @{term_pat "Trueprop _"} =>
             SOME (bool_conv_True thm)
         | _ => NONE);

(* FIXME: turn into Config.
   NB: low-level eval' ignores this global setting *)
(* 0: none; 1: summary details; 2+: everything *)
val trace = Unsynchronized.ref 0;


(*** Data structures ***)

(* TODOs:
     - cond rules?
     - simprocs?
     - skeleton optimisation?
*)
type eqns_for_const =
  int * (* arity of const (we require it to be equal in all rules) *)
  (int list * thm) option * (* possible cong rule skeleton (list of which args to evaluate) *)
  thm Net.net; (* eval equations *)
(* NB: the cong thm is never actually used; it only tells
       fp_eval how to perform the rewriting. *)

(* Main fp_eval context *)
type rules = eqns_for_const Symtab.table;

(* For completeness, though make_rules is preferred *)
val empty_rules : rules = Symtab.empty;


(*** Data structure operations ***)

(* Must be simple Pure.eq equations *)
val net_from_eqns : thm list -> thm Net.net = fn eqns =>
      let fun lift_eqn eqn = (case Thm.prop_of eqn of
                                  @{term_pat "_ \<equiv> _"} => eqn
                                | _ => raise THM ("net_from_eqns: not a simple equation", 0, [eqn]));
           val eqns' = map lift_eqn eqns;
           fun insert eqn = Net.insert_term (K false) (Thm.term_of (Thm.lhs_of eqn), eqn);
      in fold_rev insert eqns' Net.empty end;

(* Must be a simple Pure.eq equation, or convertible to one *)
fun add_eqn raw_eqn : rules -> rules =
  let val eqn = case maybe_convert_eqn raw_eqn of
                    NONE => raise THM ("add_eqn: can't use this as equation", 0, [raw_eqn])
                  | SOME eqn => eqn;
      val eqn_lhs = Thm.term_of (Thm.lhs_of eqn);
      val (cname, args) = case strip_comb eqn_lhs of
                            (* This should be OK because Const names are qualified *)
                              (Const (cname, _), args) => (cname, args)
                            | (Free (cname, _), args) => (cname, args)
                            | _ => raise THM ("add_eqn: head of LHS is not a constant", 0, [eqn]);
      val arity = length args;
      val empty_entry = (cname, (arity, NONE, Net.empty));
      fun update_entry (arity', cong, net) =
            if arity <> arity'
            then raise THM ("add_eqn: arity mismatch for " ^ cname ^
                            " (existing=" ^ string_of_int arity' ^
                            ", new=" ^ string_of_int arity ^ ")", 0, [raw_eqn])
            else (arity, cong, Net.insert_term (K false) (eqn_lhs, eqn) net);
  in Symtab.map_default empty_entry update_entry end

(* Helper for add_cong. cong_thm must be a weak cong rule of the form

    "\<lbrakk> ?x_i = ?y_i;
       ?x_j = ?y_j \<rbrakk> \<Longrightarrow>
     my_const ?x_1 ?x_2 ... ?x_i ... = my_const ?x_1 ... ?y_i ..."

   Returns indices of ?x_i in the LHS of the conclusion.
 *)
fun process_cong cong_thm : string * int * int list =
  let fun die msg terms = raise TERM ("add_cong: " ^ msg, terms @ [Thm.prop_of cong_thm]);
      (* LHS vars in premises tell us which order to use for rewriting *)
      fun dest_prem (Const (@{const_name Pure.eq}, _) $ Var (vl, _) $ Var (vr, _)) = (vl, vr)
        | dest_prem (@{const Trueprop} $
                        (Const (@{const_name HOL.eq}, _) $ Var (vl, _) $ Var (vr, _))) = (vl, vr)
        | dest_prem t = die "premise not a simple equality" [t];
      val prem_pairs = Logic.strip_imp_prems (Thm.prop_of cong_thm)
                       |> map dest_prem;
      (* check concl and get LHS argument list *)
      val (concl_lhs, concl_rhs) =
        case Logic.strip_imp_concl (Thm.prop_of cong_thm) of
            @{term_pat "?lhs \<equiv> ?rhs"} => (lhs, rhs)
          | @{term_pat "Trueprop (?lhs = ?rhs)"} => (lhs, rhs)
          | concl => die "concl not a simple equality" [concl];
      val (cname, arg_pairs) = case apply2 strip_comb (concl_lhs, concl_rhs) of
              ((head as Const (cname, _), args1), (head' as Const (cname', _), args2)) =>
                if cname <> cname'
                  then die "different consts" [head, head']
                else if length args1 <> length args2
                  then die "different arities" [concl_lhs, concl_rhs]
                else if not (forall is_Var (args1 @ args2))
                  then die "args not schematic vars" [concl_lhs, concl_rhs]
                else (cname, map (apply2 (dest_Var #> fst)) (args1 ~~ args2))
            | _ => die "equation heads are not constants" [concl_lhs, concl_rhs];
      (* for each prem LHS, find its argument position in the concl *)
      fun prem_index var = case find_index (fn v => v = var) (map fst arg_pairs) of
                              ~1 => die "var in prems but not conclusion" [Var (var, dummyT)]
                            | n => n;
      val prem_indices = map prem_index (map fst prem_pairs);
      (* ensure no duplicates, otherwise fp_eval would do multiple evaluations *)
      val _ = case duplicates (op=) prem_indices of
                  [] => ()
                | (n::_) => die "var appears twice in prems" [Var (fst (nth prem_pairs n), dummyT)];
      (* TODO: we could do even more checking here, but most other errors would
               cause fp_eval to fail-fast *)
      val const_arity = length arg_pairs;
  in (cname, const_arity, prem_indices) end;

fun add_cong cong_thm : rules -> rules =
  let val (cname, arity, cong_spec) = process_cong cong_thm;
      val empty_entry = (cname, (arity, NONE, Net.empty));
      fun update_entry (arity', opt_cong, net) =
            if arity <> arity'
            then raise THM ("add_cong: arity mismatch for " ^ cname ^
                            " (existing=" ^ string_of_int arity' ^
                            ", new=" ^ string_of_int arity ^ ")", 0, [cong_thm])
            else case opt_cong of
                      NONE => (arity, SOME (cong_spec, cong_thm), net)
                    | SOME (cong_spec', cong_thm') =>
                        if cong_spec = cong_spec'
                        then (warning ("add_cong: adding duplicate for " ^ cname);
                              (arity, opt_cong, net))
                        else raise THM ("add_cong: different cong rule already exists for " ^ cname,
                                        0, [cong_thm', cong_thm]);
  in Symtab.map_default empty_entry update_entry end;

(* Simple builder *)
fun make_rules eqns congs = fold_rev add_eqn eqns (fold add_cong congs empty_rules);

fun merge_rules (r1, r2) =
  let fun merge_const cname (r as (arity, cong, net), r' as (arity', cong', net')) =
        if pointer_eq (r, r') then r else
        let val _ = if arity = arity' then () else
                      error ("merge_rules: different arity for " ^ cname ^ ": " ^
                             string_of_int arity ^ ", " ^ string_of_int arity');
            val cong'' = case (cong, cong') of
                            (NONE, NONE) => NONE
                          | (SOME _, NONE) => cong
                          | (NONE, SOME _) => cong'
                          | (SOME (_, thm), SOME (_, thm')) =>
                              if Thm.eq_thm_prop (thm, thm') then cong else
                                raise THM ("merge_rules: different cong rules for " ^ cname, 0,
                                           [thm, thm']);
        in (arity, cong'', Net.merge Thm.eq_thm_prop (net, net')) end;
  in if pointer_eq (r1, r2) then r1 else
       Symtab.join merge_const (r1, r2)
  end;

fun dest_rules rules =
      let val const_rules = Symtab.dest rules |> map snd;
          val eqnss = map (fn (_, _, net) => Net.content net) const_rules;
          val congs = map_filter (fn (_, cong, _) => Option.map snd cong) const_rules;
      in (List.concat eqnss, congs) end;


(*** Evaluator ***)

(* Skeleton terms track which subterms have already been fully
   evaluated and can be skipped. This follows the same method as
   Raw_Simplifier.bottomc. *)
val skel0 = Bound 0; (* always descend and rewrite *)
val skel_skip = Var (("", 0), dummyT); (* always skip *)

(* Full interface *)
fun eval' (ctxt: Proof.context)
          (debug_trace: int -> (unit -> string) -> unit) (* debug callback: level, message *)
          (breakpoint: cterm -> bool) (* if true, stop rewriting and return *)
          (eval_under_var: bool) (* if true, expand partially applied funcs under Var skeletons *)
          (rules: rules)
          (ct0: cterm, ct0_skel: term)
          (* eqn, final skeleton, perf counters *)
          : (thm * term) * (string * int) list = let
      (* Performance counters *)
      val counter_eval_rec    = Unsynchronized.ref 0;
      val counter_try_rewr    = Unsynchronized.ref 0;
      val counter_rewrite1    = Unsynchronized.ref 0;
      val counter_rewrites    = Unsynchronized.ref 0;
      val counter_rewr_skel   = Unsynchronized.ref 0;
      val counter_beta_redc   = Unsynchronized.ref 0;
      val counter_transitive  = Unsynchronized.ref 0;
      val counter_combination = Unsynchronized.ref 0;
      val counter_dest_comb   = Unsynchronized.ref 0;
      val counter_congs       = Unsynchronized.ref 0;
      fun increment c = (c := !c + 1);

      (* Debug output *)
      val print_term = Syntax.string_of_term ctxt;
      val print_cterm = print_term o Thm.term_of;
      fun print_maybe_thm t = Option.getOpt (Option.map (print_term o Thm.prop_of) t, "<none>");

      (* Utils *)
      fun my_transitive t1 t2 =
            (increment counter_transitive;
             Thm.transitive t1 t2);
      fun my_combination t1 t2 =
            (increment counter_combination;
             Thm.combination t1 t2);

      fun transitive1 NONE NONE = NONE
        | transitive1 (t1 as SOME _) NONE = t1
        | transitive1 NONE (t2 as SOME _) = t2
        | transitive1 (SOME t1) (SOME t2) = SOME (my_transitive t1 t2);

      fun maybe_rewr_result NONE ct = ct
        | maybe_rewr_result (SOME rewr) _ = Thm.rhs_of rewr;

      fun maybe_eqn (SOME eqn) _ = eqn
        | maybe_eqn _ ct = Thm.reflexive ct;

      fun combination1 _ NONE _ NONE = NONE
        | combination1 cf cf_rewr cx cx_rewr =
            SOME (my_combination (maybe_eqn cf_rewr cf) (maybe_eqn cx_rewr cx));

      (* strip_comb; invent skeleton to same depth if required *)
      val strip_comb_skel = let
            fun strip (f $ x, fK $ xK, ts) = strip (f, fK, (x, xK)::ts)
              | strip (f $ x, skel as Var _, ts) =
                  (* if a sub-comb is normalized, expand it for matching purposes,
                     but don't expand children *)
                  if eval_under_var then strip (f, skel, (x, skel)::ts)
                  else (f $ x, skel, ts)
              (* skeleton doesn't match; be conservative and expand all *)
              | strip (f $ x, _, ts) = strip (f, skel0, (x, skel0)::ts)
              | strip (f, fK, ts) = (f, fK, ts) (* finish *);
            in fn (t, skel) => strip (t, skel, []) end;

      (* strip_comb for cterms *)
      val strip_ccomb : cterm -> int -> cterm * cterm list = let
            fun strip ts t n = if n = 0 then (t, ts) else
                  case Thm.term_of t of
                      _ $ _ => let val (f, x) = Thm.dest_comb t;
                                   (* yes, even dest_comb is nontrivial *)
                                   val _ = increment counter_dest_comb;
                               in strip (x::ts) f (n-1) end
                    | _ => (t, ts);
            in strip [] end;

      (* find the first matching eqn and use it *)
      fun rewrite1 _  [] = NONE
        | rewrite1 ct (eqn::eqns) = let
            val _ = increment counter_rewrite1;
            in
              SOME (Thm.instantiate (Thm.first_order_match (Thm.lhs_of eqn, ct)) eqn, eqn)
              |> tap (fn _ => increment counter_rewrites)
              handle Pattern.MATCH => rewrite1 ct eqns
            end;

      (* Apply rewrite step to skeleton.
         FIXME: traverses whole RHS. If the RHS is large and the rest of the
                evaluation ignores most of it, then this is wasted work.
                Either preprocess eqn or somehow update skel lazily *)
      fun rewrite_skel eqn skel =
        let val _ = debug_trace 2 (fn () => "rewrite_skel: " ^ print_maybe_thm (SOME eqn) ^ " on " ^ print_term skel);
            (* FIXME: may be wrong wrt. first_order_match--eta conversions? *)
            fun match (Var (v, _)) t = Vartab.map_default (v, t) I
              | match (pf $ px) (f $ x) = match pf f #> match px x
              | match (pf $ px) (t as Var _) = match pf t #> match px t
              | match (Abs (_, _, pt)) (Abs (_, _, t)) = match pt t
              | match (Abs (_, _, pt)) (t as Var _) = match pt t
              | match _ _ = I;
            val inst = match (Thm.term_of (Thm.lhs_of eqn)) skel Vartab.empty;
            fun subst (t as Var (v, _)) = Option.getOpt (Vartab.lookup inst v, t)
              | subst t = t;
            (* Consts in the RHS that don't appear in our rewrite rules, are also normalised *)
            fun norm_consts (t as Var _) = t
              | norm_consts (t as Bound _) = t
              | norm_consts (Abs (v, T, t)) = Abs (v, T, norm_consts t)
              | norm_consts (t as Const (cname, _)) =
                  if Symtab.defined rules cname then t else Var ((cname, 0), dummyT)
              | norm_consts (t as Free (cname, _)) =
                  if Symtab.defined rules cname then t else Var ((cname, 0), dummyT)
              | norm_consts (f $ x) =
                  let val f' = norm_consts f;
                      val x' = norm_consts x;
                  in case (f', x') of
                          (Var _, Var _) => f'
                        | _ => f' $ x'
                  end;
        in map_aterms subst (Thm.term_of (Thm.rhs_of eqn))
           |> tap (fn t' => counter_rewr_skel := !counter_rewr_skel + size_of_term t')
           |> norm_consts
           |> tap (fn t' => debug_trace 2 (fn () => "rewrite_skel:   ==> " ^ print_term t')) end;

      fun apply_skel (f as Var _) (Var _) = f
        | apply_skel (f as Abs _) x = betapply (f, x)
        | apply_skel f x = f $ x;

      (* Main structure.
         We just rewrite all combinations inside-out, and ignore everything else.
         Special cases:
          - Combinations may have no arguments; this expands a single Const or Free.
          - A combination may have more args than the arity of its head, e.g.
            "If c t f x y z ...". In this case, we rewrite "If c t f" only,
            then recurse on the new combination.
          - If the head is a lambda abs, its arity is considered to be the number of
            bound vars; they are evaluated first and then beta redc is performed.
       *)
      val reached_breakpoint = Unsynchronized.ref false;
      fun eval_rec (ct, skel) =
        ((if !reached_breakpoint then () else reached_breakpoint := breakpoint ct);
         if !reached_breakpoint
         then (debug_trace 1 (fn () => "eval_rec: triggered breakpoint on: " ^ print_cterm ct);
               (NONE, skel))
         else
          (increment counter_eval_rec;
           debug_trace 2 (fn () => "eval_rec: " ^ print_cterm ct ^ " (skel: " ^ print_term skel ^ ")");
            case skel of
                Var _ => (NONE, skel)
              | Abs _ => (NONE, skel)
              | _ => let
                val (head, head_skel, args) = strip_comb_skel (Thm.term_of ct, skel);
                val (chead, cargs) = strip_ccomb ct (length args);
                (* rules for head, if any *)
                val maybe_head_rules =
                      case head of
                          Const (cname, _) => Symtab.lookup rules cname
                        | Free (cname, _) => Symtab.lookup rules cname
                        | _ => NONE;

                val beta_depth = let
                      fun f (Abs (_, _, t)) = 1 + f t
                        | f _ = 0;
                      in Int.min (length args, f head) end;

                (* Emulating call by value. First, we find the equation arity of the head.
                   We evaluate a number of args up to the arity, except if the head has a
                   cong specification, we follow the cong spec. *)
                val (eval_args, effective_arity) =
                      case maybe_head_rules of
                          SOME (arity, maybe_cong, _) =>
                            if length args < arity
                            then (List.tabulate (length args, I), length args)
                            else (case maybe_cong of
                                      NONE => (List.tabulate (arity, I), arity)
                                    | SOME (indices, cong_thm) =>
                                        (increment counter_congs;
                                         debug_trace 2 (fn () => "eval_rec:   will use cong skeleton: " ^ print_maybe_thm (SOME cong_thm));
                                         (indices, arity)))
                          (* If head has no equations, just evaluate all arguments. *)
                        | NONE => let val d = if beta_depth = 0 then length args else beta_depth;
                                  in (List.tabulate (d, I), d) end;
                val skip_args = subtract op= eval_args (List.tabulate (length args, I));

                (* evaluate args *)
                fun eval_arg i = (i, (nth cargs i, eval_rec (nth cargs i, snd (nth args i))));
                fun skip_arg i = (i, (nth cargs i, (NONE, snd (nth args i))));
                val arg_convs = map eval_arg eval_args @ map skip_arg skip_args
                                |> sort (int_ord o apply2 fst) |> map snd;

                (* substitute results up to arity of head *)
                (* TODO: avoid unnecessary cterm ops? *)
                fun recombine beta_redc =
                      fold (fn (arg, (arg_conv, arg_skel)) => fn (f, (f_conv, f_skel)) =>
                              let val comb_thm = combination1 f f_conv arg arg_conv;
                                  val result = maybe_rewr_result comb_thm (Thm.apply f arg);
                              (* respect breakpoint, if set *)
                              in case (if not beta_redc orelse !reached_breakpoint then Bound 0
                                       else Thm.term_of f) of
                                      Abs _ => let
                                        val _ = debug_trace 2 (fn () =>
                                                  "eval_rec:   beta redc: " ^ print_cterm result);
                                        val _ = increment counter_beta_redc;
                                        val beta_thm = Thm.beta_conversion false result;
                                        (* f_skel must be Abs, for apply_skel to do what we want *)
                                        val f_skel' = case f_skel of Abs _ => f_skel
                                                                   | _ => Thm.term_of f;
                                        in (Thm.rhs_of beta_thm,
                                            (transitive1 comb_thm (SOME beta_thm),
                                             apply_skel f_skel' arg_skel)) end
                                    | _ => (result, (comb_thm, apply_skel f_skel arg_skel))
                              end);

                val (ct', (arg_conv, skel')) =
                       recombine true
                           (take effective_arity arg_convs)
                           (chead, (NONE, head_skel));

                (* Now rewrite the application of head to args *)
                val _ = debug_trace 2 (fn () => "eval_rec:   head is " ^ print_term head ^
                                                ", (effective) arity " ^ string_of_int effective_arity);
                in case maybe_head_rules of (* TODO: refactor the following *)
                      NONE =>
                        if beta_depth = 0
                        then let (* No equation and not Abs head, so mark as normalised.
                                    We also know effective_arity = length args, so arg_convs
                                    is complete *)
                                 val _ = @{assert} (effective_arity = length args);
                                 val skel'' = case head of Abs _ => skel' | _ =>
                                                fold (fn x => fn f => apply_skel f x)
                                                     (map (snd o snd) arg_convs) skel_skip;
                                 in (arg_conv, skel'') end
                        else let (* Add remaining args and continue rewriting *)
                                 val (ct'', (conv'', skel'')) =
                                       recombine false
                                           (drop effective_arity arg_convs)
                                           (maybe_rewr_result arg_conv ct', (arg_conv, skel'));
                                 val (final_conv, final_skel) = eval_rec (ct'', skel'');
                             in (transitive1 conv'' final_conv, final_skel) end
                    | SOME (arity, _, net) =>
                        if effective_arity < arity then (arg_conv, skel') else
                        let val rewr_result =
                              if !reached_breakpoint then NONE else
                                (debug_trace 2 (fn () => "eval_rec:   now rewrite head from: " ^ print_cterm ct');
                                 rewrite1 ct' (Net.match_term net (Thm.term_of ct')));
                        in case rewr_result of
                              NONE =>
                                (* No equations; add remaining args and mark head as normalised *)
                                let val (_, (conv'', _)) =
                                          recombine false
                                              (drop effective_arity arg_convs)
                                              (ct', (arg_conv, skel'));
                                    val skel'' = fold (fn x => fn f => apply_skel f x)
                                                      (map (snd o snd) arg_convs) skel_skip;
                                in (conv'', skel'') end
                            | SOME (conv, rule) =>
                                let val _ = debug_trace 2 (fn () => "eval: "
                                              ^ print_maybe_thm (SOME conv) ^ "\n  using: "
                                              ^ print_maybe_thm (SOME rule));
                                    val _ = increment counter_try_rewr;
                                    val rhs_skel = rewrite_skel rule skel';
                                    val conv' = case arg_conv of NONE => conv
                                                               | SOME t => my_transitive t conv;
                                    val _ = debug_trace 2 (fn () =>
                                                "eval_rec:   after rewrite: " ^ print_maybe_thm (SOME conv'));
                                    (* Add remaining args and continue rewriting *)
                                    val (ct'', (conv'', skel'')) =
                                          recombine false
                                              (drop effective_arity arg_convs)
                                              (Thm.rhs_of conv', (SOME conv', rhs_skel));
                                    val (final_conv, final_skel) = eval_rec (ct'', skel'');
                                in (transitive1 conv'' final_conv, final_skel) end
                        end
                end
                |> tap (fn (conv, skel) => debug_trace 2 (fn () =>
                         "result: " ^ print_maybe_thm (SOME (maybe_eqn conv ct)) ^ "\n  skel: " ^ print_term skel))
          ));

      (* Final result *)
      val (ct_rewr, final_skel) = eval_rec (ct0, ct0_skel);
      val counters = [
            ("eval_rec",    !counter_eval_rec),
            ("try_rewr",    !counter_try_rewr),
            ("rewrite1",    !counter_rewrite1),
            ("rewrites",    !counter_rewrites),
            ("rewr_skel",   !counter_rewr_skel),
            ("beta_redc",   !counter_beta_redc),
            ("transitive",  !counter_transitive),
            ("combination", !counter_combination),
            ("dest_comb",   !counter_dest_comb),
            ("congs",       !counter_congs)
            ];
  in ((maybe_eqn ct_rewr ct0, final_skel), counters) end;


(* Simplified interface with common defaults *)
fun eval (ctxt: Proof.context)
         (rules: rules)
         : (cterm * term) -> ((thm * term) * (string * int) list) =
  let fun debug_trace level msg = if level <= !trace then tracing (msg ()) else ();
      fun breakpoint _ = false;
      val eval_under_var = false;
  in eval' ctxt debug_trace breakpoint eval_under_var rules end;

(* Even simpler interface; uses default skel *)
fun eval_conv ctxt rules: conv =
  rpair skel0 #> eval ctxt rules #> fst #> fst;

(* FIXME: eval doesn't rewrite under binders, we should add some forall_conv here *)
fun eval_tac ctxt rules n: tactic =
  Conv.gconv_rule (eval_conv ctxt rules) n
  #> Seq.succeed;

end;
\<close>

text \<open>See FP_Eval_Tests for explanation\<close>
lemma (in FP_Eval) let_weak_cong':
  "a = b \<Longrightarrow> Let a t = Let b t"
  by simp

end