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
  val can_clear : theory -> bool
  val clear_deps : thm -> thm
  val join_deps : thm -> thm -> thm
  val used_facts : Proof.context -> thm -> ((string * int option) * term) list
end

structure Apply_Trace : APPLY_TRACE =
struct

(*TODO: Add more robust oracle without hyp clearing *)
fun thm_to_cterm keep_hyps thm =
let
  
  val thy = Thm.theory_of_thm thm
  val pairs = Thm.tpairs_of thm
  val ceqs = map (Thm.global_cterm_of thy o Logic.mk_equals) pairs
  val hyps = Thm.chyps_of thm
  val prop = Thm.cprop_of thm
  val thm' = if keep_hyps then Drule.list_implies (hyps,prop) else prop

in
  Drule.list_implies (ceqs,thm') end


val (_, clear_thm_deps') =
  Context.>>> (Context.map_theory_result (Thm.add_oracle (Binding.name "count_cheat", thm_to_cterm false)));

fun clear_deps thm =
let
   
  val thm' = try clear_thm_deps' thm
  |> Option.map (fold (fn _ => fn t => (@{thm Pure.reflexive} RS t)) (Thm.tpairs_of thm))

in case thm' of SOME thm' => thm' | NONE => error "Can't clear deps here" end


fun can_clear thy = Context.subthy(@{theory},thy)

fun join_deps pre_thm post_thm =
let
  val pre_thm' = Thm.flexflex_rule NONE pre_thm |> Seq.hd
    |> Thm.adjust_maxidx_thm (Thm.maxidx_of post_thm + 1)
in
  Conjunction.intr pre_thm' post_thm |> Conjunction.elim |> snd
end 

fun get_ref_from_nm' nm =
let
  val exploded = space_explode "_" nm;
  val base = List.take (exploded, (length exploded) - 1) |> space_implode "_"
  val idx = List.last exploded |> Int.fromString;
in if is_some idx andalso base <> "" then SOME (base, the idx) else NONE end

fun get_ref_from_nm nm = Option.join (try get_ref_from_nm' nm);

fun maybe_nth l = try (curry List.nth l)

fun fact_from_derivation ctxt xnm =
let

  val facts = Proof_Context.facts_of ctxt;
  (* TODO: Check that exported local fact is equivalent to external one *)

  val idx_result =
    let
      val (name', idx) = get_ref_from_nm xnm |> the;
      val entry = try (Facts.retrieve (Context.Proof ctxt) facts) (name', Position.none) |> the;
      val thm = maybe_nth (#thms entry) (idx - 1) |> the;
    in SOME (#name entry, thm) end handle Option => NONE;

  fun non_idx_result () =
    let
      val entry = try (Facts.retrieve (Context.Proof ctxt) facts) (xnm, Position.none) |> the;
      val thm = try the_single (#thms entry) |> the;
    in SOME (#name entry, thm) end handle Option => NONE;

in
  case idx_result of
    SOME thm => SOME thm
  | NONE => non_idx_result ()
end

fun most_local_fact_of ctxt xnm =
let
  val local_name = try (fn xnm => Long_Name.explode xnm |> tl |> tl |> Long_Name.implode) xnm |> the;
in SOME (fact_from_derivation ctxt local_name |> the) end handle Option =>
  fact_from_derivation ctxt xnm;

fun thms_of (PBody {thms,...}) = thms

fun proof_body_descend' f get_fact (ident,(nm,_ , body)) deptab =
(if not (f nm) then
  (Inttab.update_new (ident, SOME (nm, get_fact nm |> the)) deptab handle Inttab.DUP _ => deptab)
else raise Option) handle Option =>
  ((fold (proof_body_descend' f get_fact) (thms_of (Future.join body))
    (Inttab.update_new (ident, NONE) deptab)) handle Inttab.DUP _ => deptab)

fun used_facts' f get_fact thm =
  let
    val body = thms_of (Thm.proof_body_of thm);

  in fold (proof_body_descend' f get_fact) body Inttab.empty end

fun used_pbody_facts ctxt thm =
  let
    val nm = Thm.get_name_hint thm;
    val get_fact = most_local_fact_of ctxt;
  in
    used_facts' (fn nm' => nm' = "" orelse nm' = nm) get_fact thm
    |> Inttab.dest |> map_filter snd |> map snd |> map (apsnd (Thm.prop_of))
  end

fun raw_primitive_text f = Method.Basic (fn _ => ((K (fn (ctxt, thm) => Seq.make_results (Seq.single (ctxt, f thm))))))
    

(*Find local facts from new hyps*)
fun used_local_facts ctxt thm =
let
  val hyps = Thm.hyps_of thm
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

fun used_facts ctxt thm =
  let
    val used_from_pbody = used_pbody_facts ctxt thm |> map (fn (nm,t) => ((nm,NONE),t))
    val used_from_hyps = used_local_facts ctxt thm |> map (fn (nm,(i,t)) => ((nm,SOME i),t))
  in
    (used_from_hyps @ used_from_pbody)
  end

(* Perform refinement step, and run the given stateful function
   against computed dependencies afterwards. *)
fun refine args f text state =
let

  val ctxt = Proof.context_of state

  val thm = Proof.simple_goal state |> #goal

  fun save_deps deps = f ctxt thm deps

  
in
 if (can_clear (Proof.theory_of state)) then  
   Proof.refine (Method.Combinator (Method.no_combinator_info,Method.Then, [raw_primitive_text (clear_deps),text,
	raw_primitive_text (fn thm' => (save_deps (used_facts ctxt thm');join_deps thm thm'))])) state
 else
   (if (#silent_fail args) then (save_deps [];Proof.refine text state) else error "Apply_Trace theory must be imported to trace applies")
end

(* Boilerplate from Proof.ML *)


fun method_error kind pos state =
  Seq.single (Proof_Display.method_error kind pos (Proof.raw_goal state));

fun apply args f text = Proof.assert_backward #> refine args f text #> 
  Seq.maps_results (Proof.apply ((raw_primitive_text I),(Position.none, Position.none)));

fun apply_results args f (text, range) =
  Seq.APPEND (apply args f text, method_error "" (Position.range_position range));


end
*}

end

