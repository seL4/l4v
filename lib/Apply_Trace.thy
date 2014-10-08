(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Backend for tracing apply statements. Useful for doing proof step dependency analysis.
 * Provides an alternate refinement function which takes an additional stateful journaling operation. *)
theory Apply_Trace
imports Main
begin


ML {*
signature APPLY_TRACE =
sig
  val apply_results :
    {silent_fail : bool} ->
    (Proof.context -> Method.text -> thm -> ((string * int option) * term) list -> unit) -> 
    Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq

  val mentioned_facts: Proof.context -> Method.text -> thm list

  (* Lower level interface. *)
  val clear_deps : thm -> thm
  val join_deps : thm -> thm -> thm
  val used_facts : thm -> (string * term) list
end

structure Apply_Trace : APPLY_TRACE =
struct

(*TODO: Add more robust oracle without hyp clearing *)
fun thm_to_cterm keep_hyps thm =
let
  
  val thy = Thm.theory_of_thm thm
  val crep = crep_thm thm
  val ceqs = map (Thm.cterm_of thy o Logic.mk_equals o pairself term_of) (#tpairs crep)
  val hyps = #hyps crep
  val thm' = if keep_hyps then Drule.list_implies (hyps,#prop crep) else #prop crep

in
  Drule.list_implies (ceqs,thm') end


val (_, clear_thm_deps') =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (Binding.name "count_cheat", thm_to_cterm false)));

fun clear_deps thm =
let
   
  val thm' = try clear_thm_deps' thm
  |> Option.map (fold (fn _ => fn t => (@{thm Pure.reflexive} RS t)) (#tpairs (rep_thm thm)))

in case thm' of SOME thm' => thm' | NONE => error "Can't clear deps here" end


fun can_clear thy = Theory.subthy(@{theory},thy)

fun join_deps thm thm' = Conjunction.intr thm thm' |> Conjunction.elim |> snd 

fun thms_of (PBody {thms,...}) = thms

fun proof_body_descend' (_,("",_,body)) = fold (append o proof_body_descend') (thms_of (Future.join body)) []
  | proof_body_descend' (_,(nm,t,_)) = [(nm,t)]


fun used_facts thm = fold (append o proof_body_descend') (thms_of (Thm.proof_body_of thm)) []

fun raw_primitive_text f = Method.Basic (fn ctxt => (Method.RAW_METHOD (K (fn thm => Seq.single (f thm)))))


fun fold_map_src f m =
let
  fun fold_map' m' a = case m' of
   Method.Source src => let val (src',a') = (f src a) in (Method.Source src',a') end
 | (Method.Then (ci,ms)) => let val (ms',a') = fold_map fold_map' ms a in (Method.Then (ci,ms'),a') end
 | (Method.Orelse (ci,ms)) => let val (ms',a') = fold_map fold_map' ms a in (Method.Orelse (ci,ms'),a') end
 | (Method.Try (ci,m)) => let val (m',a') = fold_map' m a in (Method.Try (ci,m'),a') end
 | (Method.Repeat1 (ci,m)) => let val (m',a') = fold_map' m a in (Method.Repeat1 (ci,m'),a') end
 | (Method.Select_Goals (ci,i,m)) => let val (m',a') = fold_map' m a in (Method.Select_Goals (ci,i,m'),a') end
 | (Method.Basic g) => (Method.Basic g,a)
in
  fold_map' m end

fun map_src f text = fold_map_src (fn src => fn () => (f src,())) text () |> fst

fun fold_src f text a = fold_map_src (fn src => fn a => (src,f src a)) text a |> snd


fun toks_of ctxt src = Args.syntax (Scan.lift (Scan.repeat (Scan.one (not o (Scan.is_stopper Token.stopper))))) src ctxt |> fst

fun mentioned_facts_src ctxt src = 
let

  val toks = toks_of ctxt src
 
  fun sel t = case Token.get_value t of
        SOME (Token.Fact f) => SOME f
      | _ => NONE
  val thmss = map_filter sel toks
  
in flat thmss end

fun mentioned_facts ctxt text = fold_src (append o mentioned_facts_src ctxt) text []
    

(*Find local facts from new hyps*)
fun used_local_facts ctxt thm =
let
  val hyps = #hyps (Thm.rep_thm thm)
  val facts = Proof_Context.facts_of ctxt |> Facts.dest_static true []

  fun match_hyp hyp =
  let
    fun get (nm,thms) = 
      case (get_index (fn t => if (prop_of t) aconv hyp then SOME hyp else NONE) thms)
      of SOME t => SOME (nm,t)
        | NONE => NONE


  in
    get_first get facts
  end

in
  map_filter match_hyp hyps end



(* Perform refinement step, and run the given stateful function
   against computed dependencies afterwards. *)
fun refine args f text state =
let

  val ctxt = Proof.context_of state

  val thm = Proof.simple_goal state |> #goal

  val text' = map_src Args.init_assignable text

  fun save_deps deps = f ctxt (map_src Args.closure text') thm deps

  fun get_used thm = 
  let
    val used_from_pbody = used_facts thm |> map (fn (nm,t) => ((nm,NONE),t))
    val used_from_hyps = used_local_facts ctxt thm |> map (fn (nm,(i,t)) => ((nm,SOME i),t))
  in
    (used_from_hyps @ used_from_pbody)
  end
  
in
 if (can_clear (Proof.theory_of state)) then  
   Proof.refine (Method.Then (Method.no_combinator_info, [raw_primitive_text (clear_deps),text',
	raw_primitive_text (fn thm' => (save_deps (get_used thm');join_deps thm thm'))])) state
 else
   (if (#silent_fail args) then (save_deps [];Proof.refine text state) else error "Apply_Trace theory must be imported to trace applies")
end

(* Boilerplate from Proof.ML *)


fun method_error kind pos state =
  Seq.single (Proof_Display.method_error kind pos (Proof.raw_goal state));

fun apply args f text = Proof.assert_backward #> refine args f text #> Seq.maps (Proof.apply (raw_primitive_text I));

fun apply_results args f (text, range) =
  Seq.APPEND (apply args f text #> Seq.make_results, method_error "" (Position.set_range range));


end
*}

end

