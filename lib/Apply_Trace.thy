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
    (Proof.context -> thm -> ((string * int option) * term) list -> unit) -> 
    Method.text_range -> Proof.state -> Proof.state Seq.result Seq.seq

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
  val crep = Thm.crep_thm thm
  val ceqs = map (Thm.global_cterm_of thy o Logic.mk_equals o apply2 Thm.term_of) (#tpairs crep)
  val hyps = #hyps crep
  val thm' = if keep_hyps then Drule.list_implies (hyps,#prop crep) else #prop crep

in
  Drule.list_implies (ceqs,thm') end


val (_, clear_thm_deps') =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (Binding.name "count_cheat", thm_to_cterm false)));

fun clear_deps thm =
let
   
  val thm' = try clear_thm_deps' thm
  |> Option.map (fold (fn _ => fn t => (@{thm Pure.reflexive} RS t)) (#tpairs (Thm.rep_thm thm)))

in case thm' of SOME thm' => thm' | NONE => error "Can't clear deps here" end


fun can_clear thy = Theory.subthy(@{theory},thy)

fun join_deps thm thm' = Conjunction.intr thm thm' |> Conjunction.elim |> snd 

fun thms_of (PBody {thms,...}) = thms

fun proof_body_descend' (_,("",_,body)) = fold (append o proof_body_descend') (thms_of (Future.join body)) []
  | proof_body_descend' (_,(nm,t,_)) = [(nm,t)]


fun used_facts thm = fold (append o proof_body_descend') (thms_of (Thm.proof_body_of thm)) []

fun raw_primitive_text f = Method.Basic (fn ctxt => (Method.METHOD (K (fn thm => Seq.single (f thm)))))
    

(*Find local facts from new hyps*)
fun used_local_facts ctxt thm =
let
  val hyps = #hyps (Thm.rep_thm thm)
  val facts = Proof_Context.facts_of ctxt |> Facts.dest_static true []

  fun match_hyp hyp =
  let
    fun get (nm,thms) = 
      case (get_index (fn t => if (Thm.prop_of t) aconv hyp then SOME hyp else NONE) thms)
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

  fun save_deps deps = f ctxt thm deps

  fun get_used thm = 
  let
    val used_from_pbody = used_facts thm |> map (fn (nm,t) => ((nm,NONE),t))
    val used_from_hyps = used_local_facts ctxt thm |> map (fn (nm,(i,t)) => ((nm,SOME i),t))
  in
    (used_from_hyps @ used_from_pbody)
  end
  
in
 if (can_clear (Proof.theory_of state)) then  
   Proof.refine (Method.Combinator (Method.no_combinator_info,Method.Then, [raw_primitive_text (clear_deps),text,
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

