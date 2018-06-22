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
 * Functions to perform tracing of AutoCorres's proof steps.
 * Also includes some utilities for printing the traces.
 * The theory data for recording traces is defined in AutoCorresData.
 * See tests/examples/TraceDemo.thy for an output example.
 *)
signature AUTOCORRES_TRACE = sig
  datatype 'a RuleTrace = RuleTrace of {
      input: cterm,
      step: 'a * tactic,
      output: thm,
      trace: 'a RuleTrace list
      }
  datatype SimpTrace = SimpTrace of {
      equation : thm,
      thms : (string * cterm) list
      }
  exception TRACE_SOLVE_TAC_FAIL of (thm * thm) list

  (* Documented in structure *)
  val trace_solve_tac:
        Proof.context ->
        bool ->
        bool ->
        (term -> (thm * tactic) list) ->
        thm ->
        int option ->
        int Unsynchronized.ref ->
        (thm * thm RuleTrace list) option

  val fast_solve_tac:
        Proof.context ->
        bool ->
        bool ->
        (term -> (thm * tactic) list) ->
        thm ->
        int option ->
        int ->
        thm option

  val maybe_trace_solve_tac:
        Proof.context ->
        bool ->
        bool ->
        bool ->
        (term -> (thm * tactic) list) ->
        thm ->
        int option ->
        int Unsynchronized.ref ->
        (thm * thm RuleTrace list) option

  val fconv_rule_traced:
        Proof.context -> (cterm -> thm) -> thm -> thm * SimpTrace
  val fconv_rule_maybe_traced:
        Proof.context -> (cterm -> thm) -> thm -> bool -> thm * SimpTrace option

  val print_ac_trace: thm RuleTrace -> string
  val writeFile: string -> string -> unit
end;

structure AutoCorresTrace: AUTOCORRES_TRACE = struct

(*
 * Custom unifier for trace_solve_tac.
 * Isabelle's built-in unifier has several problems:
 * 1. It gives up when the unifications become “complicated”, even if it is
 *    only due to variables needing large instantiations.
 *    This happens for trace_solve_tac because it unifies subgoals with subgoal proofs,
 *    thus it may instantiate a variable to an entire program term.
 *    We can fall back to tactics replay when this happens, but we would rather not
 *    at the top levels (which is when this problem occurs), as it involves replaying
 *    large branches of the proof tree.
 *
 * 2. When it gives up, it produces a lot of tracing output.
 *    This tracing is a global option, so we cannot turn it off in the local context.
 *    The volume of tracing invariably causes Isabelle/jEdit's poorly-written GUI to lock up.
 *
 * This unifier is less general, but should work for AutoCorres's purposes.
 * It unifies terms t and t', where t' is assumed to be fully concrete (the subgoal proof).
 * Schematic variables in t, including functions, are instantiated by substituting them with
 * the corresponding subterm in t'. We assume that schematic variables do not have schematic
 * arguments. (FIXME: add this test)
 * We also do some instantiations of schematic type variables in t, because it's currently needed
 * by WordAbstract. We assume that the type vars are never applied to arguments.
 *)

(* generalised Term.lambda *)
fun my_lambda args =
  let val n = length args
      fun lambda' depth args t =
        (case Utils.findIndex (fn (a, _) => a = t) args of
            NONE =>
              (case t of
                  f $ x => lambda' depth args f $ lambda' depth args x
                | Abs (v, typ, t) => Abs (v, typ, lambda' (depth + 1) (map (apfst (incr_boundvars 1)) args) t)
                | Bound k => if k >= depth then Bound (k + n) else Bound k
                | _ => t)
          | SOME (_, k) => Bound (k + depth))
  in lambda' 0 (rev args)
     #> fold (fn (_, (name, typ)) => fn t => Abs (name, typ, t)) (rev args)
  end

fun subterm_type absvars t = let
  fun subst absvars (Bound k) = Free (nth absvars k)
    | subst absvars (f $ x) = subst absvars f $ subst absvars x
    | subst absvars (Abs (v, typ, t)) = Abs (v, typ, subst ((v, typ) :: absvars) t)
    | subst _ t = t
  in fastype_of (subst absvars t) end
fun my_typ_insts (Type (_, args)) (Type (_, args')) =
    if length args <> length args' then NONE else
    let val instss = Utils.zipWith my_typ_insts args args'
    in if exists (not o isSome) instss then NONE else
         SOME (List.mapPartial I instss |> List.concat) end
  | my_typ_insts (TFree _) (TFree _) = SOME []
  | my_typ_insts (TVar tv) typ = SOME [(tv, typ)]
  | my_typ_insts _ _ = NONE
fun my_typ_match' absvars (t as f $ x) t' =
      (case strip_comb t of
          (Var _, _) => my_typ_insts (subterm_type absvars t) (subterm_type absvars t')
        | _ => (case t' of
                   f' $ x' => (case (my_typ_match' absvars f f', my_typ_match' absvars x x') of
                                  (SOME fmatch, SOME xmatch) => SOME (fmatch @ xmatch)
                                | _ => NONE)
                 | _ => NONE))
  | my_typ_match' absvars (Abs (_, typ, t)) (Abs (v', typ', t')) =
      (case (my_typ_insts typ typ', my_typ_match' ((v', typ') :: absvars) t t') of
          (SOME absmatch, SOME tmatch) => SOME (absmatch @ tmatch)
        | _ => NONE)
  | my_typ_match' absvars t t' = case my_typ_insts (subterm_type absvars t) (subterm_type absvars t') of
       SOME x => SOME x
     | NONE => raise TYPE ("my_typ_insts fail", [subterm_type absvars t, subterm_type absvars t'], [t, t'])
fun my_typ_match t t' = my_typ_match' [] (Envir.beta_norm t) t'
                        handle TYPE (msg, typs, terms) => raise TYPE (msg, typs, terms @ [t, t'])

fun annotate_boundvar _ absvars (Bound n) =
      if n < length absvars then (Bound n, nth absvars n)
        else raise TYPE ("annotate_boundvar", map snd absvars, [Bound n])
  | annotate_boundvar _ _ (t as Free (name, typ)) = (t, (name, typ))
  | annotate_boundvar i absvars t = (t, ("var" ^ Int.toString i, subterm_type absvars t))
fun my_match' _ (Var v) t' = SOME [(v, [], t')]
  | my_match' absvars (t as f $ x) t' =
      (case strip_comb t of
          (Var v, args) => SOME [(v, map (fn (i, arg) => annotate_boundvar i absvars arg)
                                         (Utils.enumerate args), t')]
        | _ => (case t' of
                   f' $ x' => (case (my_match' absvars f f', my_match' absvars x x') of
                                  (SOME uf, SOME ux) => SOME (uf @ ux)
                                | _ => NONE)
                 | _ => NONE))
  | my_match' absvars (Abs (name, typ, t)) (Abs (_, typ', t')) =
      if typ = typ' then my_match' ((name, typ)::absvars) t t' else NONE
  | my_match' absvars t t' = if t = t' then SOME [] else NONE
fun my_match t t' = my_match' [] (Envir.beta_norm t) t'

fun my_unify_fact_tac ctxt subproof n state =
  let val cterm_of' = Thm.cterm_of ctxt
      val ctyp_of' = Thm.ctyp_of ctxt
  in
  if length (Thm.prems_of state) < n then no_tac state else
  let val stateterm = nth (Thm.prems_of state) (n-1)
      val proofterm = Thm.prop_of subproof
  in
  case my_typ_match stateterm proofterm of
     NONE => Seq.empty
   | SOME typinsts =>
     (case Thm.instantiate (map (fn (v, t) => (v, ctyp_of' t)) (Utils.nubBy fst typinsts), []) state of
       state' =>
        let val stateterm' = nth (Thm.prems_of state') (n-1) in
        case my_match stateterm' proofterm of
           NONE => Seq.empty
         | SOME substs =>
             let val substs' = Utils.nubBy #1 substs
                               |> map (fn (var, args, t') => (var, my_lambda args t'))
                               |> map (fn (v, t) => (v, cterm_of' t))
             in
             case Thm.instantiate ([], substs') state of state' =>
               (case Proof_Context.fact_tac ctxt [Variable.gen_all ctxt subproof] 1 state' |> Seq.pull of
                   NONE => Seq.empty
                 | r => Seq.make (fn () => r))
             handle _ => Seq.empty
             end
       handle _ => Seq.empty
      end)
      handle _ => Seq.empty
  end
  end


datatype 'a RuleTrace = RuleTrace of {
    input: cterm,
    step: 'a * tactic,
    output: thm,
    trace: 'a RuleTrace list
    }

fun trace_steps (RuleTrace tr) = #step tr :: List.concat (map trace_steps (#trace tr))

fun dest_rule_comb (Const (@{const_name "Trueprop"}, _) $ t) = dest_rule_comb t
  | dest_rule_comb t = dest_rule_comb (Logic.dest_all t |> snd)
                       handle TERM _ => strip_comb t
fun get_rule_abstract t = dest_rule_comb t |> snd |> (fn args => nth args (length args - 2))

exception TRACE_SOLVE_TAC_FAIL of (thm * thm) list

(*
 * Meta-tactic that applies the given tactics recursively to all subgoals of a proof state.
 * It is assumed that each of the tactics given, operates only on the first subgoal and may
 * generate zero or more additional subgoals.
 * Returns a trace of all the intermediate subgoals, before and after the tactics are applied.
 * This trace can be used to see how schematic variables are instantiated by the tactics.
 *
 * If backtrack is set, allow backtracking on the tactic list.
 *
 * If backtrack_subgoals is set, failures of later subgoals will cause backtracking in earlier subgoals.
 * This normally just causes exponential blowup for no benefit and AutoCorres currently does not use it.
 *
 * depth specifies an optional depth limit.
 *
 * Failures of my_unify_fact_tac are printed, up to [original value of !replay_failure] times.
 * !replay_failure is decremented for each failure (including those not printed).
 * While these failures are non-fatal (we fall back to tactics replay),
 * too many failures is bad for performance, and we aim for 0.
 *
 * NB: the current implementation only takes the first result of each tactic.
 * TODO: also produce some kind of trace on failure, since we are mostly interested in when AutoCorres fails.
 *)
fun trace_solve_tac (ctxt : Proof.context)
                    (backtrack : bool) (backtrack_subgoals : bool)
                    (get_tacs : term -> (thm * tactic) list)
                    (state : thm)
                    (depth : int option)
                    (replay_failures : int Unsynchronized.ref)
                    : (thm * thm RuleTrace list) option =
  if depth = SOME 0 then raise TRACE_SOLVE_TAC_FAIL [(state, @{thm symmetric})] else
  let val cterm_of' = Thm.cterm_of ctxt in
  case Thm.prems_of state of
     [] => SOME (state, [])
   | (goal::_) =>
        let val cgoal = cterm_of' goal
            val input = Goal.init cgoal
            fun try [] = if backtrack then NONE else raise TRACE_SOLVE_TAC_FAIL [(state, @{thm reflexive})]
              | try ((tag, tactic) :: rules_rest) =
                  case tactic input |> Seq.pull of
                     NONE => try rules_rest
                   | SOME (next, _) =>
                      case trace_solve_tac ctxt backtrack backtrack_subgoals get_tacs next
                                           (Option.map (fn n => n - 1) depth) replay_failures
                           handle TRACE_SOLVE_TAC_FAIL tr => raise TRACE_SOLVE_TAC_FAIL ((state, tag) :: tr) of
                         NONE => if backtrack then try rules_rest else
                                   raise TRACE_SOLVE_TAC_FAIL [(state, tag), (next, @{thm reflexive})]
                       | SOME (output, trace) =>
                          let val output' = Goal.finish ctxt output
                              val exn = THM ("AutoCorresTrace.trace_solve_tac: could not apply subgoal proof", 0,
                                             [state, output', output, input])
                              val state' = (case my_unify_fact_tac ctxt output' 1 state |> Seq.pull of
                                               NONE =>
                                                 let val _ = if !replay_failures <= 0 then () else
                                                               @{trace} ("AutoCorresTrace.trace_solve_tac: using slow replay", state, output)
                                                     val _ = replay_failures := !replay_failures - 1;
                                                     val steps = (tag, tactic) :: List.concat (map trace_steps trace)
                                                 in case EVERY (map snd steps) state |> Seq.pull of
                                                       SOME (state', _) =>
                                                         if length (Thm.prems_of state) = length (Thm.prems_of state') + 1
                                                           then state' else raise exn
                                                     | NONE => raise exn end
                                             | SOME (s, _) => s)
                                           handle THM _ => raise exn
                          in case trace_solve_tac ctxt backtrack backtrack_subgoals get_tacs state' depth replay_failures of
                                NONE => if backtrack_subgoals then try rules_rest else NONE
                              | SOME (full_thm, rest) =>
                                  SOME (full_thm,
                                        RuleTrace { input = cgoal, step = (tag, tactic), output = output', trace = trace } :: rest)
                          end
        in try (get_tacs goal) end
  end

(* Same result as trace_solve_tac, but without the tracing. *)
fun fast_solve_tac (ctxt : Proof.context)
                   (backtrack : bool) (backtrack_subgoals : bool)
                   (get_tacs : term -> (thm * tactic) list)
                   (state : thm)
                   (depth : int option)
                   (num_subgoals : int)
                   : thm option =
  let val n = length (Thm.prems_of state)
      fun try [] = if backtrack then NONE else raise TRACE_SOLVE_TAC_FAIL [(state, @{thm reflexive})]
        | try ((tag, tactic) :: rules_rest) =
            case tactic state |> Seq.pull of
                NONE => try rules_rest
              | SOME (next, _) =>
                case fast_solve_tac ctxt backtrack backtrack_subgoals get_tacs next
                                    (Option.map (fn d => d - 1) depth) n
                     handle TRACE_SOLVE_TAC_FAIL tr => raise TRACE_SOLVE_TAC_FAIL ((state, tag) :: tr) of
                    NONE => if backtrack then try rules_rest else
                            raise TRACE_SOLVE_TAC_FAIL [(state, tag), (next, @{thm reflexive})]
                  | SOME state' =>
                    case fast_solve_tac ctxt backtrack backtrack_subgoals get_tacs state'
                                        depth num_subgoals of
                        NONE => if backtrack_subgoals then try rules_rest else NONE
                      | SOME thm => SOME thm
  in if depth = SOME 0 then raise TRACE_SOLVE_TAC_FAIL [(state, @{thm reflexive})] else
     if n = 0 orelse n < num_subgoals then SOME state else
     try (get_tacs (hd (Thm.prems_of state)))
  end

fun maybe_trace_solve_tac (ctxt : Proof.context)
                          (do_trace : bool)
                          (backtrack : bool) (backtrack_subgoals : bool)
                          (get_tacs : term -> (thm * tactic) list)
                          (state : thm)
                          (depth : int option)
                          (replay_failures : int Unsynchronized.ref)
                          : (thm * thm RuleTrace list) option =
  if do_trace
  then trace_solve_tac ctxt backtrack backtrack_subgoals get_tacs state depth replay_failures
  else fast_solve_tac ctxt backtrack backtrack_subgoals get_tacs state depth 1
       |> Option.map (fn thm => (thm, [ RuleTrace { input = Thm.cprop_of state, output = thm,
                                                    step = (@{thm TrueI}, all_tac), trace = [] } ]))


(* Tracing simplification eg. L2Opt.
 * For now, we just use Apply_Trace to get the list of rewrite rules. *)
datatype SimpTrace = SimpTrace of { equation : thm, thms : (string * cterm) list }

fun fconv_rule_traced ctxt conv thm =
  let val eq_thm = conv (Thm.cprop_of thm)
      val thms = Apply_Trace.used_facts ctxt eq_thm |> map (fn ((nm,idx),ct) => (nm,ct))
  in (if Thm.is_reflexive eq_thm then thm else Thm.equal_elim eq_thm thm, (* Pure/conv.ML *)
      SimpTrace { equation = eq_thm, thms = map (apsnd (Thm.cterm_of ctxt)) thms })
  end

fun fconv_rule_maybe_traced ctxt conv thm do_trace =
  if do_trace then fconv_rule_traced ctxt conv thm |> apsnd SOME
              else (Conv.fconv_rule conv thm, NONE)


(* Display and debugging utils *)
local
fun dropQuotes s = if String.isPrefix "\"" s andalso String.isSuffix "\"" s
                       then String.substring (s, 1, String.size s - 2) else s

fun cterm_to_string no_markup =
  Proof_Display.pp_cterm (fn _ => @{theory Pure})
  #> Pretty.string_of
  #> YXML.parse_body
  #> (if no_markup then XML.content_of else YXML.string_of_body)
  #> dropQuotes

fun intercalate _ [] = []
  | intercalate _ [x] = [x]
  | intercalate l (x::xs) = x :: l @ intercalate l xs

fun print_ac_trace' indent (RuleTrace tr) =
  let val print_cterm = cterm_to_string true
      val print_thm = Thm.cprop_of #> print_cterm
      val indent' = indent ^ "  "
  in
    indent ^ "Subgoal: " ^ print_cterm (#input tr) ^ "\n" ^
    indent ^ "Output:  " ^ print_thm (#output tr) ^ "\n" ^
    (if null (#trace tr) then indent ^ "Proof: " ^ print_thm (#step tr |> fst) ^ "\n" else
       indent ^ "Proof:\n" ^
       indent' ^ "Step: " ^ print_thm (#step tr |> fst) ^ "\n\n" ^
       String.concat (map (print_ac_trace' indent') (#trace tr) |> intercalate ["\n"]))
  end
in
val print_ac_trace = print_ac_trace' ""
end

fun writeFile filename string =
  let val stream = TextIO.openOut filename
      val _ = TextIO.output (stream, string)
      val _ = TextIO.closeOut stream
  in () end

end
