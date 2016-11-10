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
 * Code to manage converting between L2_monad and other monad types.
 *
 * TypeStrengthen provides a higher level interface for converting entire programs.
 *)

structure Monad_Convert = struct

(* Utilities. *)
fun intersperse _ [] = []
  | intersperse _ [x] = [x]
  | intersperse a (x::xs) = x :: a :: intersperse a xs

fun theE NONE exc = raise exc
  | theE (SOME x) _ = x

fun oneE [] exc = raise exc
  | oneE (x::_) _ = x



(* From Find_Theorems *)
fun apply_dummies tm =
  let
    val (xs, _) = Term.strip_abs tm;
    val tm' = Term.betapplys (tm, map (Term.dummy_pattern o #2) xs);
  in #1 (Term.replace_dummy_patterns tm' 1) end;

fun parse_pattern ctxt nm =
  let
    val consts = Proof_Context.consts_of ctxt;
    val nm' =
      (case Syntax.parse_term ctxt nm of
        Const (c, _) => c
      | _ => Consts.intern consts nm);
  in
    (case try (Consts.the_abbreviation consts) nm' of
      SOME (_, rhs) => apply_dummies (Proof_Context.expand_abbrevs ctxt rhs)
    | NONE => Proof_Context.read_term_pattern ctxt nm)
  end;

(* Breadth-first term search *)
fun term_search_bf cont pred prune = let
  fun fresh_var vars v = if member (op =) vars v then fresh_var vars (v ^ "'") else v
  fun search ((vars, term), queue) =
    if pred term then cont (vars, term) (fn () => walk queue) else
    if prune term then walk queue else
    case term of
        t as Abs (v, typ, _) =>
            let val v' = fresh_var vars v in
                walk (Queue.enqueue
                          ((v'::vars), betapply (t, Free (v', typ))) queue)
            end
      | f $ x => walk (Queue.enqueue (vars, x) (Queue.enqueue (vars, f) queue))
      | _ => walk queue
  and walk queue = if Queue.is_empty queue then () else search (Queue.dequeue queue)
in
  (fn term => search (([], term), Queue.empty))
end

fun term_search_bf_first pred prune term = let
  val r = Unsynchronized.ref NONE
  val _ = term_search_bf (fn result => K (r := SOME result)) pred prune term
in !r end

(* From Pure/Tools/find_theorems.ML, because Florian made it private *)
fun matches_subterm thy (pat, obj) =
  let
    fun msub bounds obj = Pattern.matches thy (pat, obj) orelse
      (case obj of
        Abs (_, T, t) => msub (bounds + 1) (snd (Term.dest_abs (Name.bound bounds, T, t)))
      | t $ u => msub bounds t orelse msub bounds u
      | _ => false)
  in msub 0 obj end;

fun grep_term ctxt pattern =
let
  val thy = Proof_Context.theory_of ctxt
in
  term_search_bf_first
      (fn term => Pattern.matches thy (pattern, term))
      (fn term => not (matches_subterm thy (pattern, term)))
end

(* Check whether the term is in L2_monad notation. *)
val term_is_L2 = Monad_Types.check_lifting_head
    [@{term "L2_unknown"}, @{term "L2_seq"}, @{term "L2_modify"},
     @{term "L2_gets"}, @{term "L2_condition"}, @{term "L2_catch"}, @{term "L2_while"},
     @{term "L2_throw"}, @{term "L2_spec"}, @{term "L2_guard"}, @{term "L2_fail"},
     @{term "L2_recguard"}, @{term "L2_call"}]

(*
 * Perform monad conversion on a term, taking into account any extra
 * simplifying facts. Only a successful conversion is returned.
 *
 * For this conversion to be useful on recursive programs, it needs
 * to be given a fact representing the inductive assumption.
 *)
fun monad_rewrite (lthy : Proof.context) (mt : Monad_Types.monad_type)
                  (more_facts : thm list) (forward : bool)
                  (term : term) : thm option =
let
  val lthy = Utils.set_hidden_ctxt lthy
  val rules = Monad_Types.monad_type_rules mt
  val rules' = if forward then #lift_rules rules else #unlift_rules rules
  val cterm = Thm.cterm_of lthy term
  (* Just apply the simplifier and hope that it works. *)
  val thm = Simplifier.rewrite (
      put_simpset HOL_ss lthy addsimps rules' addsimps more_facts) cterm
  val rhs = Utils.rhs_of (term_of_thm thm)
  val good_rewrite = if forward then #valid_term mt else term_is_L2
in
  if good_rewrite lthy rhs
    then SOME thm else NONE
end

(*
 * Apply polish to a theorem of the form:
 *
 *   <LHS> == <lift> $ <some term to polish>
 *
 * Return the new theorem.
 *)
local
  val case_prod_eta_contract_thm =
      @{lemma "(%x. (case_prod s) x) == (case_prod s)" by simp}
in
fun polish ctxt (mt : Monad_Types.monad_type) do_opt thm =
let
  (* Apply any polishing rules. *)
  val ctxt = Utils.set_hidden_ctxt ctxt
  val simps = if do_opt then Utils.get_rules ctxt @{named_theorems polish} else []

  (* Simplify using polish rules. *)
  val rules = Monad_Types.monad_type_rules mt
  val simp_conv = Simplifier.rewrite (put_simpset HOL_ss ctxt addsimps (#polish_rules rules @ simps))

  (* eta-contract "case_prod clauses, so that they render as:
   * "%(a, b). P a b" instead of "case x of (a, b) => P a b". *)
  val case_prod_conv =
    Conv.bottom_conv (
        K (Conv.try_conv (Conv.rewr_conv case_prod_eta_contract_thm))) ctxt

  val thm_p =
    Conv.fconv_rule (Conv.arg_conv (Utils.rhs_conv (
        simp_conv then_conv case_prod_conv))) thm
in
  thm_p
end
end

(*
 * Wrap a tactic that doesn't handle invalid subgoal numbers to return
 * "Seq.empty" when appropriate.
 *)
fun handle_invalid_subgoals (tac : int -> tactic) n =
  fn thm =>
    if Logic.count_prems (term_of_thm thm) < n then
      no_tac thm
    else
      tac n thm

(*
 * monad_convert tactic.
 *)
fun monad_convert_tac (ctxt : Proof.context) (monad_name : string) (do_opt : bool)
                      (pattern_str : string) (n : int) : tactic =
  fn state => let
    val all_rules = Monad_Types.TSRules.get (Context.Proof ctxt)

    (* Figure out which monad to lift into. *)
    val target_rule = theE (Symtab.lookup all_rules monad_name)
                           (ERROR ("monad_convert: could not find monad type " ^ quote monad_name))

    (* Search the subgoal for the supplied pattern. *)
    val pattern = parse_pattern ctxt pattern_str
    val subgoal = Logic.get_goal (term_of_thm state) n
    val (m_vars, m_term) = theE (grep_term ctxt pattern subgoal)
                                (TERM ("monad_convert: failed to match pattern", [pattern]))

    (* Find a lifting rule whose output matches m_term.
     * This saves us from having to try every unlift rule. *)
    val orig_lift_rule = oneE (filter (fn mt => #valid_term mt ctxt m_term)
                                      (all_rules |> Symtab.dest |> map snd))
                              (TERM ("monad_convert: could not determine monad type", [m_term]))

    (* Unlift back to L2_monad. *)
    val unlift_thm = theE (monad_rewrite ctxt orig_lift_rule [] false m_term)
                          (TERM ("monad_convert: could not unlift term (rule: " ^
                                   #name orig_lift_rule ^ ")", [m_term]))
    val unlift_term = Utils.rhs_of (term_of_thm unlift_thm)

    (* Lift to target monad. *)
    val relift_thm = theE (monad_rewrite ctxt target_rule [] true unlift_term)
                          (TERM ("monad_convert: could not lift to " ^ #name target_rule,
                                 [m_term, unlift_term]))

    (* Polish result. *)
    val relift_thm' = polish ctxt target_rule do_opt relift_thm

    val translate_thm = Thm.transitive unlift_thm relift_thm'

    (* Make variables schematic *)
    val translate_thm' = Goal.prove ctxt (sort_distinct string_ord m_vars) []
                                         (term_of_thm translate_thm)
                                         (K (resolve_tac ctxt [translate_thm] 1))

    val result = EqSubst.eqsubst_tac ctxt [0] [translate_thm'] n state
  in
    case Seq.pull result of
        NONE => raise TERM ("monad_convert: failed to apply conversion",
                            [term_of_thm translate_thm', subgoal])
      | SOME (x, xs) => Seq.cons x xs
  end

val _ = Context.>> (Context.map_theory
          (Method.setup (Binding.name "monad_convert")
            (* Based on subgoal_tac parser *)
            (Args.goal_spec -- Scan.lift (Parse.name -- Args.embedded_inner_syntax) >>
            (fn (quant, (monad_name, term_str)) => fn ctxt =>
                SIMPLE_METHOD'' quant (handle_invalid_subgoals (
                    monad_convert_tac ctxt monad_name true term_str))))
           "autocorres monad conversion"))

end
