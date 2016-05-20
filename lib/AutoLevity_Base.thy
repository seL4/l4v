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


ML\<open>

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

val setup_command_hook: unit -> unit;

val add_attribute_test: string -> (Proof.context -> thm -> bool) -> theory -> theory;

val attribs_of: Proof.context -> thm -> string list;

val used_facts: int -> Proof.context option -> thm -> (string * thm) list;
val used_facts_attribs: int -> Proof.context -> thm -> (string * string list) list;

val pre_apply_hook: Proof.context -> thm -> thm;

val post_apply_hook: Proof.context -> Method.text -> thm -> unit;

  
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
    type T = (string option * (Proof.context -> thm -> bool) Symtab.table);
    val empty = (NONE, Symtab.empty);
    val extend = I;
    fun merge (((_, tab), (_, tab')) : T * T) = (NONE, Symtab.merge (fn _ => true) (tab, tab'));
  );

fun set_levity_tag tag = Data.map (apfst (fn _ => tag));
val get_levity_tag = fst o Data.get

fun update_attrib_tab f = Data.map (apsnd f);

fun add_attribute_test nm f = update_attrib_tab (Symtab.update_new (nm,f));

val get_attribute_tests = Symtab.dest o snd o Data.get;

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

fun most_local_fact_of ctxt xnm = 
let
  val local_name = try (fn xnm => Long_Name.explode xnm |> tl |> tl |> Long_Name.implode) xnm |> the;
in SOME (fact_from_derivation ctxt local_name |> the) end handle Option =>
  fact_from_derivation ctxt xnm;

(* Every "apply" gets tagged with this derivation. Its siblings in the proof tree are the
   new dependencies *)
val applyN = "<apply>"

fun thms_of (PBody {thms,...}) = thms


fun proof_body_descend' f get_fact (ident,(nm,_ , body)) deptab =
(if not (f nm) then
  (Inttab.update_new (ident, SOME (nm, get_fact nm |> the)) deptab handle Inttab.DUP _ => deptab)
else raise Option) handle Option => 
  ((fold (proof_body_descend' f get_fact) (thms_of (Future.join body)) 
    (Inttab.update_new (ident, NONE) deptab)) handle Inttab.DUP _ => deptab)


fun breadth_first_apply' 1 bodies = 
let
  val i = find_index (fn (_, (nm, _, _)) => nm = applyN) bodies;
in if i = ~1 then NONE else SOME (nth_drop i bodies) end
 | breadth_first_apply' n bodies = 
    get_first (fn (_, (_, _, body)) => (breadth_first_apply' (n - 1) (thms_of (Future.join body)))) bodies 

fun breadth_first_apply i bodies = 
  case (get_first (fn depth => breadth_first_apply' depth bodies) (1 upto i)) of
  SOME x => x
  | NONE => []

fun used_facts' apply_search_depth f get_fact thm =
  let
    val body = thms_of (Thm.proof_body_of thm);
    val body' = 
     if apply_search_depth > 0 then breadth_first_apply apply_search_depth body else body

  in fold (proof_body_descend' f get_fact) body' Inttab.empty end

fun used_facts meta_search_depth opt_ctxt thm =
  let
    val nm = Thm.get_name_hint thm;
    val get_fact = case opt_ctxt of
      SOME ctxt => most_local_fact_of ctxt
    | NONE => (fn _ => SOME Drule.dummy_thm);
  in
    used_facts' meta_search_depth (fn nm' => nm' = "" orelse nm' = nm orelse nm' = applyN) get_fact thm
    |> Inttab.dest |> map_filter snd
  end

fun attribs_of ctxt =
let
  val tests = get_attribute_tests (Proof_Context.theory_of ctxt)
  |> map (apsnd (fn test => test ctxt));

in (fn t => map_filter (fn (testnm, test) => if test t then SOME testnm else NONE) tests) end;

fun used_facts_attribs meta_search_depth ctxt thm =
let
  val fact_nms = used_facts meta_search_depth (SOME ctxt) thm;

  val attribs_of = attribs_of ctxt;

in map (apsnd attribs_of) fact_nms end

fun pre_apply_hook (_: Proof.context) = Thm.name_derivation applyN;

fun get_pos_of_text (Method.Source src) = SOME (snd (Token.name_of_src src))
  | get_pos_of_text (Method.Combinator (_, _, texts)) = get_first get_pos_of_text texts
  | get_pos_of_text _ = NONE

val post_apply_hook = (fn ctxt => fn text => fn thm => case get_pos_of_text text of NONE => ()
  | SOME pos =>
    let
      val used_facts = used_facts_attribs 5 ctxt thm;
      val thy_nm = Context.theory_name (Thm.theory_of_thm thm);
    in Synchronized.change applys 
      (Symtab.map_default (thy_nm, Postab_strict.empty) (Postab_strict.update (pos, used_facts)))  
    end)

(* The Proof hooks need to be patched in to track apply dependencies, but the rest of levity
   can work without them. Here we graciously fail if the hook interface is missing *)

fun setup_pre_apply_hook () = 
 try (ML_Context.eval ML_Compiler.flags @{here})
  (ML_Lex.read_pos @{here} "Proof.set_pre_apply_hook AutoLevity_Base.pre_apply_hook");

fun setup_post_apply_hook () = 
 try (ML_Context.eval ML_Compiler.flags @{here})
  (ML_Lex.read_pos @{here} "Proof.set_post_apply_hook AutoLevity_Base.post_apply_hook");


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



fun setup_command_hook () = (setup_pre_apply_hook (); setup_post_apply_hook ();
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
  in () end) handle e => if Exn.is_interrupt e then reraise e else
    Synchronized.change transactions 
              (Symtab.map_default (thynm, (Postab_strict.empty, Postab_strict.empty)) 
                (apsnd (Postab_strict.map_default (pos, []) (cons (@{make_string} e)))))
  end))

end
\<close>

ML \<open>
fun context_changed' proj f ctxt thm = pointer_eq (proj ctxt, proj (f thm ctxt))

fun context_changed proj f ctxt = 
let
  val context_changed = context_changed' proj f ctxt;
in (fn thm => the_default false (try (fn thm => context_changed thm) thm)) end;
\<close>

setup \<open>AutoLevity_Base.add_attribute_test "simp" 
  (context_changed Raw_Simplifier.simpset_of Raw_Simplifier.add_simp)\<close>
setup \<open>AutoLevity_Base.add_attribute_test "cong" 
  (context_changed Raw_Simplifier.simpset_of Raw_Simplifier.add_cong)\<close>

ML \<open>
fun wrap_classical' f thm ctxt = f (ctxt,[thm])
fun wrap_classical f = context_changed Classical.claset_of (wrap_classical' f)  
\<close>

setup \<open>AutoLevity_Base.add_attribute_test "intro" (wrap_classical Classical.addIs)\<close>
setup \<open>AutoLevity_Base.add_attribute_test "intro!" (wrap_classical Classical.addSIs)\<close>
setup \<open>AutoLevity_Base.add_attribute_test "elim" (wrap_classical Classical.addEs)\<close>
setup \<open>AutoLevity_Base.add_attribute_test "elim!" (wrap_classical Classical.addSEs)\<close>

setup \<open>AutoLevity_Base.add_attribute_test "dest" (wrap_classical Classical.addDs)\<close>
setup \<open>AutoLevity_Base.add_attribute_test "dest!" (wrap_classical Classical.addSDs)\<close>


end
