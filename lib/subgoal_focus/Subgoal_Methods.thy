(*  Title:      Subgoal_Methods.thy
    Author:     Daniel Matichuk, NICTA/UNSW

Methods for managing subgoals collectively.
*)

(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Subgoal_Methods
imports Main
begin
ML \<open>
signature SUBGOAL_METHODS =
sig
  val fold_subgoals: Proof.context -> bool -> thm -> thm
  val unfold_subgoals_tac: Proof.context -> tactic
  val distinct_subgoals: Proof.context -> thm -> thm
end;

structure Subgoal_Methods: SUBGOAL_METHODS =
struct

fun max_common_prefix eq (ls :: lss) =
      let
        val ls' = tag_list 0 ls;
        fun all_prefix (i,a) =
          forall (fn ls' => if length ls' > i then eq (a, nth ls' i) else false) lss
        val ls'' = take_prefix all_prefix ls'
      in map snd ls'' end
  | max_common_prefix _ [] = [];

fun push_outer_params ctxt th =
  let
    val ctxt' = ctxt
      |> Simplifier.empty_simpset
      |> Simplifier.add_simp Drule.norm_hhf_eq;
  in
    Conv.fconv_rule
      (Raw_Simplifier.rewrite_cterm (true, false, false) (K (K NONE)) ctxt') th
  end;

fun fix_schematics ctxt raw_st =
  let
    val ((schematic_types, [st']), ctxt1) = Variable.importT [raw_st] ctxt;
    val ((_, inst), ctxt2) =
      Variable.import_inst true [Thm.prop_of st'] ctxt1;

    val schematic_terms = map (apsnd (Thm.cterm_of ctxt2)) inst;
    val schematics = (schematic_types, schematic_terms);

  in (Thm.instantiate schematics st', ctxt2) end

val strip_params = Term.strip_all_vars;
val strip_prems = Logic.strip_imp_prems o Term.strip_all_body;
val strip_concl = Logic.strip_imp_concl o Term.strip_all_body;



fun fold_subgoals ctxt prefix raw_st =
  if Thm.nprems_of raw_st < 2 then raw_st
  else
    let
      val (st, inner_ctxt) = fix_schematics ctxt raw_st;

      val subgoals = Thm.prems_of st;
      val paramss = map strip_params subgoals;
      val common_params = max_common_prefix (eq_snd (op =)) paramss;

      fun strip_shift subgoal =
        let
          val params = strip_params subgoal;
          val diff = length common_params - length params;
          val prems = strip_prems subgoal;
        in map (Term.incr_boundvars diff) prems end;

      val premss = map (strip_shift) subgoals;

      val common_prems = max_common_prefix (op aconv) premss;

      val common_params = if prefix then common_params else [];
      val common_prems = if prefix then common_prems else [];

      fun mk_concl subgoal =
        let
          val params = Term.strip_all_vars subgoal;
          val local_params = drop (length common_params) params;
          val prems = strip_prems subgoal;
          val local_prems = drop (length common_prems) prems;
          val concl = strip_concl subgoal;
        in Logic.list_all (local_params, Logic.list_implies (local_prems, concl)) end;

      val goal =
        Logic.list_all (common_params,
          (Logic.list_implies (common_prems,Logic.mk_conjunction_list (map mk_concl subgoals))));

      val chyp = Thm.cterm_of inner_ctxt goal;

      val (common_params',inner_ctxt') =
        Variable.add_fixes (map fst common_params) inner_ctxt
        |>> map2 (fn (_, T) => fn x => Thm.cterm_of inner_ctxt (Free (x, T))) common_params;

      fun try_dest rule =
        try (fn () => (@{thm conjunctionD1} OF [rule], @{thm conjunctionD2} OF [rule])) ();

      fun solve_headgoal rule =
        let
          val rule' = rule
            |> Drule.forall_intr_list common_params'
            |> push_outer_params inner_ctxt';
        in
          (fn st => Thm.implies_elim st rule')
        end;

      fun solve_subgoals rule' st =
        (case try_dest rule' of
          SOME (this, rest) => solve_subgoals rest (solve_headgoal this st)
        | NONE => solve_headgoal rule' st);

      val rule = Drule.forall_elim_list common_params' (Thm.assume chyp);
    in
      st
      |> push_outer_params inner_ctxt
      |> solve_subgoals rule
      |> Thm.implies_intr chyp
      |> singleton (Variable.export inner_ctxt' ctxt)
    end;

fun distinct_subgoals ctxt raw_st =
  let
    val (st, inner_ctxt) = fix_schematics ctxt raw_st;
    val subgoals = Drule.cprems_of st;
    val atomize = Conv.fconv_rule (Object_Logic.atomize_prems inner_ctxt);

    val rules =
      map (atomize o Raw_Simplifier.norm_hhf inner_ctxt o Thm.assume) subgoals
      |> sort (int_ord o apply2 Thm.nprems_of);

    val st' = st
      |> ALLGOALS (fn i =>
        Object_Logic.atomize_prems_tac inner_ctxt i THEN solve_tac inner_ctxt rules i)
      |> Seq.hd;

    val subgoals' = subgoals
      |> inter (op aconvc) (Thm.chyps_of st')
      |> distinct (op aconvc);
  in
    Drule.implies_intr_list subgoals' st'
    |> singleton (Variable.export inner_ctxt ctxt)
  end;

(* Variant of filter_prems_tac that recovers premise order *)
fun filter_prems_tac' ctxt pred =
  let
    fun Then NONE tac = SOME tac
      | Then (SOME tac) tac' = SOME (tac THEN' tac');
    fun thins H (tac, n, i) =
      (if pred H then (tac, n + 1, i)
       else (Then tac (rotate_tac n THEN' eresolve_tac ctxt [thin_rl]), 0, i + n));
  in
    SUBGOAL (fn (goal, i) =>
      let val Hs = Logic.strip_assums_hyp goal in
        (case fold thins Hs (NONE, 0, 0) of
          (NONE, _, _) => no_tac
        | (SOME tac, _, n) => tac i THEN rotate_tac (~ n) i)
      end)
  end;

fun trim_prems_tac ctxt rules =
let
  fun matches (prem,rule) =
  let
    val ((_,prem'),ctxt') = Variable.focus NONE prem ctxt;
    val rule_prop = Thm.prop_of rule;
  in Unify.matches_list (Context.Proof ctxt') [rule_prop] [prem'] end;

in filter_prems_tac' ctxt (not o member matches rules) end;

val adhoc_conjunction_tac = REPEAT_ALL_NEW
  (SUBGOAL (fn (goal, i) =>
    if can Logic.dest_conjunction (Logic.strip_imp_concl goal)
    then resolve0_tac [Conjunction.conjunctionI] i
    else no_tac));

fun unfold_subgoals_tac ctxt =
  TRY (adhoc_conjunction_tac 1)
  THEN (PRIMITIVE (Raw_Simplifier.norm_hhf ctxt));

val _ =
  Theory.setup
   (Method.setup @{binding fold_subgoals}
      (Scan.lift (Args.mode "prefix") >> (fn prefix => fn ctxt =>
         SIMPLE_METHOD (PRIMITIVE (fold_subgoals ctxt prefix))))
      "lift all subgoals over common premises/params" #>
    Method.setup @{binding unfold_subgoals}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD (unfold_subgoals_tac ctxt)))
      "recover subgoals after folding" #>
    Method.setup @{binding distinct_subgoals}
      (Scan.succeed (fn ctxt => SIMPLE_METHOD (PRIMITIVE (distinct_subgoals ctxt))))
     "trim all subgoals to be (logically) distinct" #>
    Method.setup @{binding trim}
      (Attrib.thms >> (fn thms => fn ctxt =>
         SIMPLE_METHOD (HEADGOAL (trim_prems_tac ctxt thms))))
     "trim all premises that match the given rules");

end;
\<close>

end
