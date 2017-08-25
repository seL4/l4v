(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *
 * Base of autolevity.
 * Needs to be installed to track command start/end locations
 *)

theory AutoLevity_Base
imports Main Apply_Trace
keywords "levity_tag" :: thy_decl
begin


ML \<open>
fun is_simp (_: Proof.context) (_: thm) = true
\<close>

ML \<open>
val is_simp_installed = is_some (
 try (ML_Context.eval ML_Compiler.flags @{here})
  (ML_Lex.read_pos @{here} "val is_simp = Raw_Simplifier.is_simp"));
\<close>

ML\<open>
(* Describing a ordering on Position.T. Optionally we compare absolute document position, or
   just line numbers. Somewhat complicated by the fact that jEdit positions don't have line or
   file identifiers. *)

fun pos_ord use_offset (pos1, pos2) =
  let
    fun get_offset pos = if use_offset then Position.offset_of pos else SOME 0;

    fun get_props pos =
      (SOME (Position.file_of pos |> the,
            (Position.line_of pos |> the,
             get_offset pos |> the)), NONE)
      handle Option => (NONE, Position.parse_id pos)

    val props1 = get_props pos1;
    val props2 = get_props pos2;

  in prod_ord
      (option_ord (prod_ord string_ord (prod_ord int_ord int_ord)))
      (option_ord (int_ord))
      (props1, props2) end

structure Postab = Table(type key = Position.T val ord = (pos_ord false));
structure Postab_strict = Table(type key = Position.T val ord = (pos_ord true));


signature AUTOLEVITY_BASE =
sig
type extras = {levity_tag : string option, subgoals : int}



val get_transactions : unit -> ((string * extras) Postab_strict.table * string list Postab_strict.table) Symtab.table;

val get_applys : unit -> ((string * string list) list) Postab_strict.table Symtab.table;

val add_attribute_test: string -> (Proof.context -> thm -> bool) -> theory -> theory;

val attribs_of: Proof.context -> thm -> string list;

val used_facts: Proof.context option -> thm -> (string * thm) list;
val used_facts_attribs: Proof.context -> thm -> (string * string list) list;

(* Install toplevel hook for tracking command positions. *)

val setup_command_hook: {trace_apply : bool} -> theory -> theory;

(* Used to trace the dependencies of all apply statements.
   They are set up by setup_command_hook if the appropriate hooks in the "Proof"
   module exist. *)

val pre_apply_hook: Proof.context -> Method.text -> thm -> thm;
val post_apply_hook: Proof.context -> Method.text -> thm -> thm -> thm;


end;




structure AutoLevity_Base : AUTOLEVITY_BASE =
struct

val applys = Synchronized.var "applys"
  (Symtab.empty : (((string * string list) list) Postab_strict.table) Symtab.table)

fun get_applys () = Synchronized.value applys;

type extras = {levity_tag : string option, subgoals : int}


val transactions = Synchronized.var "hook"
  (Symtab.empty : ((string * extras) Postab_strict.table * ((string list) Postab_strict.table)) Symtab.table);

fun get_transactions () =
  Synchronized.value transactions;


structure Data = Theory_Data
  (
    type T = (bool *
        string option *
       (Proof.context -> thm -> bool) Symtab.table); (* command_hook * levity tag * attribute tests *)
    val empty = (false, NONE, Symtab.empty);
    val extend = I;
    fun merge (((b1, _, tab), (b2, _, tab')) : T * T) = (b1 orelse b2, NONE, Symtab.merge (fn _ => true) (tab, tab'));
  );

val set_command_hook_flag = Data.map (@{apply 3(1)} (fn _ => true));
val get_command_hook_flag = #1 o Data.get

fun set_levity_tag tag = Data.map (@{apply 3(2)} (fn _ => tag));
val get_levity_tag = #2 o Data.get

fun update_attrib_tab f = Data.map (@{apply 3(3)} f);


fun add_attribute_test nm f =
let
  val f' = (fn ctxt => fn thm => the_default false (try (f ctxt) thm))
in update_attrib_tab (Symtab.update_new (nm,f')) end;

val get_attribute_tests = Symtab.dest o #3 o Data.get;

(* Internal fact names get the naming scheme "foo_3" to indicate the third
   member of the multi-thm "foo". We need to do some work to guess if
   such a fact refers to an indexed multi-thm or a real fact named "foo_3" *)

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
    in SOME thm end handle Option => NONE;

  fun non_idx_result () =
    let
      val entry = try (Facts.retrieve (Context.Proof ctxt) facts) (xnm, Position.none) |> the;
      val thm = try the_single (#thms entry) |> the;
    in SOME thm end handle Option => NONE;

in
  case idx_result of
    SOME thm => SOME thm
  | NONE => non_idx_result ()
end

(* Local facts (from locales) aren't marked in proof bodies, we only
   see their external variants. We guess the local name from the external one
   (i.e. "Theory_Name.Locale_Name.foo" -> "foo")

   This is needed to perform localized attribute tests (e.g.. is this locale assumption marked as simp?) *)

(* TODO: extend_locale breaks this naming scheme by adding the "chunk" qualifier. This can
   probably just be handled as a special case *)

fun most_local_fact_of ctxt xnm =
let
  val local_name = try (fn xnm => Long_Name.explode xnm |> tl |> tl |> Long_Name.implode) xnm |> the;
in SOME (fact_from_derivation ctxt local_name |> the) end handle Option =>
  fact_from_derivation ctxt xnm;


(* We recursively descend into the proof body to find dependent facts.
   We skip over empty derivations or facts that we fail to find, but recurse
   into their dependents. This ensures that an attempt to re-build the proof dependencies
   graph will result in a connected graph. *)

fun thms_of (PBody {thms,...}) = thms

fun proof_body_descend' f get_fact (ident, thm_node) deptab = let
  val nm = Proofterm.thm_node_name thm_node
  val body = Proofterm.thm_node_body thm_node
in
    (if not (f nm) then
      (Inttab.update_new (ident, SOME (nm, get_fact nm |> the)) deptab handle Inttab.DUP _ => deptab)
    else raise Option) handle Option =>
      ((fold (proof_body_descend' f get_fact) (thms_of (Future.join body))
        (Inttab.update_new (ident, NONE) deptab)) handle Inttab.DUP _ => deptab)
end

fun used_facts' f get_fact thm =
  let
    val body = thms_of (Thm.proof_body_of thm);

  in fold (proof_body_descend' f get_fact) body Inttab.empty end

fun used_facts opt_ctxt thm =
  let
    val nm = Thm.get_name_hint thm;
    val get_fact = case opt_ctxt of
      SOME ctxt => most_local_fact_of ctxt
    | NONE => (fn _ => SOME Drule.dummy_thm);
  in
    used_facts' (fn nm' => nm' = "" orelse nm' = nm) get_fact thm
    |> Inttab.dest |> map_filter snd
  end

fun attribs_of ctxt =
let
  val tests = get_attribute_tests (Proof_Context.theory_of ctxt)
  |> map (apsnd (fn test => test ctxt));

in (fn t => map_filter (fn (testnm, test) => if test t then SOME testnm else NONE) tests) end;

fun used_facts_attribs ctxt thm =
let
  val fact_nms = used_facts (SOME ctxt) thm;

  val attribs_of = attribs_of ctxt;

in map (apsnd attribs_of) fact_nms end

(* We identify "apply" applications by the document position of their corresponding method.
   We can only get a document position out of "real" methods, so internal methods
   (i.e. Method.Basic) won't have a position.*)

fun get_pos_of_text' (Method.Source src) = SOME (snd (Token.name_of_src src))
  | get_pos_of_text' (Method.Combinator (_, _, texts)) = get_first get_pos_of_text' texts
  | get_pos_of_text' _ = NONE

(* We only want to apply our hooks in batch mode, so we test if our position has a line number
   (in jEdit it will only have an id number) *)

fun get_pos_of_text text = case get_pos_of_text' text of
  SOME pos => if is_some (Position.line_of pos) then SOME pos else NONE
  | NONE => NONE

(* Clear the theorem dependencies using the apply_trace oracle, then
   pick up the new ones after the apply step is finished. *)

fun pre_apply_hook ctxt text thm =
  case get_pos_of_text text of NONE => thm
  | SOME _ =>
      if Apply_Trace.can_clear (Proof_Context.theory_of ctxt)
      then Apply_Trace.clear_deps thm
      else thm;


val post_apply_hook = (fn ctxt => fn text => fn pre_thm => fn post_thm =>
  case get_pos_of_text text of NONE => post_thm
  | SOME pos => if Apply_Trace.can_clear (Proof_Context.theory_of ctxt) then
    (let
      val thy_nm = Context.theory_name (Thm.theory_of_thm post_thm);

      val used_facts = the_default [] (try (used_facts_attribs ctxt) post_thm);
      val _ =
        Synchronized.change applys
         (Symtab.map_default
           (thy_nm, Postab_strict.empty) (Postab_strict.update (pos, used_facts)))

      (* We want to keep our old theorem dependencies around, so we put them back into
         the goal thm when we are done *)

      val post_thm' = post_thm
        |> Apply_Trace.join_deps pre_thm

    in post_thm' end)
    else post_thm)

(* The Proof hooks need to be patched in to track apply dependencies, but the rest of levity
   can work without them. Here we graciously fail if the hook interface is missing *)

fun setup_pre_apply_hook () =
 try (ML_Context.eval ML_Compiler.flags @{here})
  (ML_Lex.read_pos @{here} "Proof.set_pre_apply_hook AutoLevity_Base.pre_apply_hook");

fun setup_post_apply_hook () =
 try (ML_Context.eval ML_Compiler.flags @{here})
  (ML_Lex.read_pos @{here} "Proof.set_post_apply_hook AutoLevity_Base.post_apply_hook");

(* This command is treated specially by AutoLevity_Theory_Report. The command executed directly
   after this one will be tagged with the given tag *)

val _ =
  Outer_Syntax.command @{command_keyword levity_tag} "tag for levity"
    (Parse.string >> (fn str =>
      Toplevel.local_theory NONE NONE
        (Local_Theory.raw_theory (set_levity_tag (SOME str)))))

fun get_subgoals' state =
let
  val proof_state = Toplevel.proof_of state;
  val {goal, ...} = Proof.raw_goal proof_state;
in Thm.nprems_of goal end

fun get_subgoals state = the_default ~1 (try get_subgoals' state);

fun setup_toplevel_command_hook () =
Toplevel.add_hook (fn transition => fn start_state => fn end_state =>
  let val name = Toplevel.name_of transition
      val pos = Toplevel.pos_of transition;
      val thy = Toplevel.theory_of start_state;
      val thynm = Context.theory_name thy;
      val end_thy = Toplevel.theory_of end_state;
 in
  if name = "clear_deps" orelse name = "dummy_apply" orelse Position.line_of pos = NONE then () else
  (let

    val levity_input = if name = "levity_tag" then get_levity_tag end_thy else NONE;

    val subgoals = get_subgoals start_state;

    val entry = {levity_tag = levity_input, subgoals = subgoals}

    val _ =
      Synchronized.change transactions
              (Symtab.map_default (thynm, (Postab_strict.empty, Postab_strict.empty))
                (apfst (Postab_strict.update (pos, (name, entry)))))
  in () end) handle e => if Exn.is_interrupt e then Exn.reraise e else
    Synchronized.change transactions
              (Symtab.map_default (thynm, (Postab_strict.empty, Postab_strict.empty))
                (apsnd (Postab_strict.map_default (pos, []) (cons (@{make_string} e)))))
  end)

fun setup_attrib_tests theory = if not (is_simp_installed) then
error "Missing interface into Raw_Simplifier. Can't trace apply statements with unpatched isabelle."
else
let
  fun is_first_cong ctxt thm =
    let
      val simpset = Raw_Simplifier.internal_ss (Raw_Simplifier.simpset_of ctxt);
      val (congs, _) = #congs simpset;
      val cong_thm = #mk_cong (#mk_rews simpset) ctxt thm;
    in
      case (find_first (fn (_, thm') => Thm.eq_thm_prop (cong_thm, thm')) congs) of
        SOME (nm, _) =>
          Thm.eq_thm_prop (find_first (fn (nm', _) => nm' = nm) congs |> the |> snd, cong_thm)
      | NONE => false
    end

  fun is_classical proj ctxt thm =
    let
      val intros = proj (Classical.claset_of ctxt |> Classical.rep_cs);
      val results = Item_Net.retrieve intros (Thm.full_prop_of thm);
    in exists (fn (thm', _, _) => Thm.eq_thm_prop (thm',thm)) results end
in
 theory
|> add_attribute_test "simp" is_simp
|> add_attribute_test "cong" is_first_cong
|> add_attribute_test "intro" (is_classical #unsafeIs)
|> add_attribute_test "intro!" (is_classical #safeIs)
|> add_attribute_test "elim" (is_classical #unsafeEs)
|> add_attribute_test "elim!" (is_classical #safeEs)
|> add_attribute_test "dest" (fn ctxt => fn thm => is_classical #unsafeEs ctxt (Tactic.make_elim thm))
|> add_attribute_test "dest!" (fn ctxt => fn thm => is_classical #safeEs ctxt (Tactic.make_elim thm))
end


fun setup_command_hook {trace_apply, ...} theory =
if get_command_hook_flag theory then theory else
let
  val _ = if trace_apply then
    (the (setup_pre_apply_hook ());
     the (setup_post_apply_hook ()))
       handle Option => error "Missing interface into Proof module. Can't trace apply statements with unpatched isabelle"
    else ()

  val _ = setup_toplevel_command_hook ();

  val theory' = theory
    |> trace_apply ? setup_attrib_tests
    |> set_command_hook_flag

in theory' end;


end
\<close>

end
