(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)
(*
 * Optimise L2 fragments of code by using facts learnt earlier in the fragments
 * to simplify code afterwards.
 *)

structure L2Opt =
struct

(*
 * Map the given simpset to tweak it for L2Opt.
 *
 * If "use_ugly_rules" is enabled, we will use rules that are useful for
 * discharging proofs, but make the output ugly.
 *)
fun map_opt_simpset use_ugly_rules =
    Simplifier.add_cong @{thm if_cong}
    #> Simplifier.add_cong @{thm split_cong}
    #> Simplifier.add_cong @{thm HOL.conj_cong}
    #> (if use_ugly_rules then
          (fn ctxt => ctxt addsimps [@{thm split_def}])
        else
           I)

(*
 * Solve a goal of the form:
 *
 *   simp_expr P A ?X
 *
 * This is done by simplifying "A" while assuming "P", and unifying the result
 * (usually instantiating "X") in the process.
 *)
val simp_expr_thm =
    @{lemma "(simp_expr P G G == simp_expr P G G') ==> simp_expr P G G'" by (clarsimp simp: simp_expr_def)}
fun solve_simp_expr_tac ctxt =
  Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
  (fn thm =>
    case Drule.cprems_of thm of
      [] => (no_tac thm)
    | (goal::_) =>
      (case Thm.term_of goal of
        (_ $ (Const (@{const_name "simp_expr"}, _) $ P $ L $ _)) =>
        let
          val goal = @{mk_term "simp_expr ?P ?L ?L" (P, L)} (P, L)
              |> Thm.cterm_of ctxt
          val simplified = Simplifier.asm_full_rewrite (map_opt_simpset false ctxt) goal

          (* Ensure that all schematics have been resolved. *)
          val schematic_remains = Term.exists_subterm Term.is_Var (Thm.prop_of simplified)
        in
          if schematic_remains then
            (resolve_tac ctxt @{thms simp_expr_triv} 1) thm
          else
            ((resolve_tac ctxt [simp_expr_thm] 1) THEN (resolve_tac ctxt [simplified] 1)) thm
        end
      | _ => no_tac thm)
    )) ctxt

(*
 * Solve a goal of the forms:
 *
 *   simp_expr P A B
 *
 * where both "A" and "B" are constants (i.e., not schematics).
 *)
fun solve_simp_expr_const_tac ctxt thm =
  if (Term.exists_subterm Term.is_Var (Thm.term_of (Thm.cprem_of thm 1))) then
    no_tac thm
  else
    SOLVES (
      (resolve_tac ctxt @{thms simp_expr_solve_constant} 1)
      THEN (Clasimp.clarsimp_tac (map_opt_simpset true ctxt) 1)) thm

(*
 * Given a theorem of the form:
 *
 *   monad_equiv P L R Q E
 *
 * simplify "P", possibly trimming parts of it that are too large.
 *
 * The idea here is to avoid exponential blow-up by trimming off terms that get
 * too large.
 *)
fun simp_monad_equiv_pre_tac ctxt =
  Subgoal.FOCUS_PARAMS (fn {context = ctxt, ...} =>
  (fn thm =>
    case Thm.term_of (Thm.cprem_of thm 1) of
      Const (@{const_name Trueprop}, _) $
        (Const (@{const_name monad_equiv}, _) $ P $ _ $ _ $ _ $ _) =>
        let
          (* If P is schematic, we could end up with flex-flex pairs that Isabelle refuses to solve.
           * Our monad_equiv rules should never allow this to happen. *)
          val _ = if not (exists_subterm is_Var P) then () else
                    raise CTERM ("autocorres: bad schematic in monad_equiv_pre", [Thm.cprem_of thm 1])
          (* Perform basic simplification of the term. *)
          val simp_thm = Simplifier.asm_full_rewrite (map_opt_simpset false ctxt) (Thm.cterm_of ctxt P)
        in
          (resolve_tac ctxt [@{thm monad_equiv_weaken_pre''} OF [simp_thm]] 1
            ORELSE (fn t => raise (CTERM ("autocorres: monad_equiv_pre failed to prove goal", [Thm.cprem_of t 1])))) thm
        end
    | _ =>
        all_tac thm
    )) ctxt

(*
 * Recursively simplify a monadic expression, using information gleaned from
 * earlier in the program to simplify parts of the program further down.
 *)
fun monad_equiv ctxt ct =
let
  (* Mark context as being "invisible" to reduce warnings being printed. *)
  val ctxt = Context_Position.set_visible false ctxt

  (* Generate our top-level "monad_equiv" goal. *)
  val goal = @{mk_term "?L == ?R" (L)} (Thm.term_of ct)
    |> Thm.cterm_of ctxt
    |> Goal.init
    |> Utils.apply_tac "Creating object-level equality." (resolve_tac ctxt @{thms eq_reflection} 1)
    |> Utils.apply_tac "Creating 'monad_equiv' goal." (resolve_tac ctxt @{thms monad_equiv_eq} 1)

  (* Print a diagnostic if this branch fails. *)
  val num_failures = ref 0
  fun print_failure_tac t =
    if (false andalso !num_failures < 5) then
      (num_failures := !num_failures + 1; (print_tac ctxt "Branch failed" THEN no_tac) t)
    else
      (no_tac t)

  (* Fetch theorms used in the simplification process. *)
  val thms = Utils.get_rules ctxt @{named_theorems L2flow}

  (* Tactic to blindly apply simplification rules. *)
  fun solve_goal_tac _ =
    (simp_monad_equiv_pre_tac ctxt 1)
    THEN DETERM (
      SOLVES
      ((solve_simp_expr_const_tac ctxt)
      ORELSE
      ((solve_simp_expr_tac ctxt 1)
      ORELSE
      ((resolve_tac ctxt thms THEN_ALL_NEW solve_goal_tac) 1
      ORELSE
      ((print_failure_tac))))))

  (* Apply the rules. *)
  val thm =
    Utils.apply_tac "Simplifying L2" (solve_goal_tac 1) goal
    |> Goal.finish ctxt
in
  thm
end

(*
 * A simproc implementing the "L2_gets_bind" rule. The rule, unfortunately, has
 * the ability to cause exponential growth in the spec size in some cases;
 * thus, we can only selectively apply it in cases where this doesn't happen.
 *
 * In particular, we propagate a "gets" into its usage if it is used at most once.
 *
 * Or, if the user asks for "no_opt", we only erase the "gets" if it is never used.
 * (Even with "no optimisation", we still want to get rid of control flow variables
 * emitted by c-parser. Hopefully the user won't mind if their own unused variables
 * also disappear.)
 *)
val l2_gets_bind_thm = mk_meta_eq @{thm L2_gets_bind}
fun l2_gets_bind_simproc' ctxt cterm =
let
  fun is_simple (_ $ Abs (_, _, Bound _)) = true
    | is_simple (_ $ Abs (_, _, Free _)) = true
    | is_simple (_ $ Abs (_, _, Const _)) = true
    | is_simple _ = false
in
  case Thm.term_of cterm of
    (Const (@{const_name "L2_seq"}, _) $ lhs $ Abs (_, _, rhs)) =>
      let
        fun count_var_usage (a $ b) = count_var_usage a + count_var_usage b
          | count_var_usage (Abs (_, _, x)) = count_var_usage x
          | count_var_usage (Free ("_dummy", _)) = 1
          | count_var_usage _ = 0
        val count = count_var_usage (subst_bounds ([Free ("_dummy", dummyT)], rhs))
      in
        if count <= 1 orelse is_simple lhs then
          SOME l2_gets_bind_thm
        else
          NONE
      end
    | _ => NONE
end
val l2_gets_bind_simproc =
  Utils.mk_simproc' @{context}
    ("L2_gets_bind_simproc", ["L2_seq (L2_gets (%_. ?A) ?n) ?B"], l2_gets_bind_simproc')

(* Simproc to clean up guards. *)
fun l2_guard_simproc' ss ctxt cterm =
let
  val simp_thm = Simplifier.asm_full_rewrite
      (Simplifier.add_cong @{thm HOL.conj_cong} (put_simpset ss ctxt)) cterm
  val [lhs, rhs] = Thm.prop_of (Drule.eta_contraction_rule simp_thm) |> Term.strip_comb |> snd
in
  if Term_Ord.fast_term_ord (lhs, rhs) = EQUAL then
    NONE
  else
    SOME simp_thm
end
fun l2_guard_simproc ss =
  Utils.mk_simproc' @{context} ("L2_guard_simproc", ["L2_guard ?G"], l2_guard_simproc' ss)

(*
 * Adjust "case_prod commands so that constructs such as:
 *
 *    while C (%x. gets (case x of (a, b) => %s. P a b)) ...
 *
 * are transformed into:
 *
 *    while C (%(a, b). gets (%s. P a b)) ...
 *)
fun fix_L2_while_loop_splits_conv ctxt =
  Simplifier.asm_full_rewrite (
    put_simpset HOL_ss ctxt
    addsimps @{thms L2_split_fixups}
    |> fold Simplifier.add_cong @{thms L2_split_fixups_congs})

(*
 * Carry out flow-sensitive optimisations on the given 'thm'.
 *
 * "n" is the argument number to cleanup, counting from 1. So for example, if
 * our input theorem was "corres P A B", an "n" of 2 would simplify "A".
 * If n < 0, then the cleanup is applied to the -n-th argument from the end.
 *
 * If "fast_mode" is 0, perform flow-sensitive optimisations (which tend to be
 * time-consuming). If 1, only apply L2Peephole and L2Opt simplification rules.
 * If 2, do not use AutoCorres' simplification rules at all.
 *)
fun cleanup_thm ctxt thm fast_mode n do_trace =
let
  (* Don't print out warning messages. *)
  val ctxt = Context_Position.set_visible false ctxt

  (* Setup basic simplifier. *)
  fun basic_ss ctxt =
      put_simpset AUTOCORRES_SIMPSET ctxt
      |> (fn ctxt => if fast_mode < 2 then ctxt addsimps (Utils.get_rules ctxt @{named_theorems L2opt}) else ctxt)
      |> (fn ctxt => if fast_mode < 2 then ctxt addsimprocs [l2_gets_bind_simproc] else ctxt)
      |> (fn ctxt => ctxt addsimprocs [l2_guard_simproc (simpset_of ctxt)])
      |> map_opt_simpset false
  fun simp_conv ctxt =
    Drule.beta_eta_conversion
    then_conv (fix_L2_while_loop_splits_conv ctxt)
    then_conv (Simplifier.rewrite (basic_ss ctxt))

  fun l2conv conv =
    Utils.remove_meta_conv (fn ctxt => Utils.nth_arg_conv n (conv ctxt)) ctxt

  (* Apply peephole optimisations to the theorem. *)
  val (new_thm, peephole_trace) =
      AutoCorresTrace.fconv_rule_maybe_traced ctxt (l2conv simp_conv) thm do_trace
      |> apfst Drule.eta_contraction_rule

  (* Apply flow-sensitive optimisations, and then re-apply simple simplifications. *)
  (* TODO: trace monad_equiv using trace_solve_tac rather than fconv_rule_traced *)
  val (new_thm, flow_trace) =
    if fast_mode = 0 then
      AutoCorresTrace.fconv_rule_maybe_traced ctxt (
        l2conv (fn ctxt =>
          monad_equiv ctxt
          then_conv (simp_conv (put_simpset AUTOCORRES_SIMPSET ctxt))
        )) new_thm do_trace
    else
      (new_thm, NONE)

  (* Beta/Eta normalise. *)
  val new_thm = Conv.fconv_rule (l2conv (K Drule.beta_eta_conversion)) new_thm
in
  (new_thm, List.mapPartial I [peephole_trace, flow_trace])
end

(* Also tag the traces in a suitable format to be stored in AutoCorresData. *)
fun cleanup_thm_tagged ctxt thm fast_mode n do_trace phase =
  cleanup_thm ctxt thm fast_mode n do_trace
  |> apsnd (map AutoCorresData.SimpTrace #> Utils.zip [phase ^ " peephole opt", phase ^ " flow opt"])

end
