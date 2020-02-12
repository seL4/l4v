(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Find_Names
imports Pure
keywords "find_names" :: diag
begin

text \<open>The @{command find_names} command, when given a theorem,
  finds other names the theorem appears under, via matching on the whole
  proposition. It will not identify unnamed theorems.\<close>

ML \<open>

local
(* all_facts_of and pretty_ref taken verbatim from non-exposed version
   in Find_Theorems.ML of official Isabelle/HOL distribution *)
fun all_facts_of ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val transfer = Global_Theory.transfer_theories thy;
    val local_facts = Proof_Context.facts_of ctxt;
    val global_facts = Global_Theory.facts_of thy;
  in
   (Facts.dest_all (Context.Proof ctxt) false [global_facts] local_facts
    @ Facts.dest_all (Context.Proof ctxt) false [] global_facts)
   |> maps Facts.selections
   |> map (apsnd transfer)
  end;

fun pretty_ref ctxt thmref =
  let
    val (name, sel) =
      (case thmref of
        Facts.Named ((name, _), sel) => (name, sel)
      | Facts.Fact _ => raise Fail "Illegal literal fact");
  in
    [Pretty.marks_str (#1 (Proof_Context.markup_extern_fact ctxt name), name),
      Pretty.str (Facts.string_of_selection sel)]
  end;

in

fun find_names ctxt thm =
  let
    fun eq_filter body thmref = (body = Thm.full_prop_of (snd thmref));
  in
    (filter (eq_filter (Thm.full_prop_of thm))) (all_facts_of ctxt)
    |> map #1
  end;

fun pretty_find_names ctxt thm =
  let
    val results = find_names ctxt thm;
    val position_markup = Position.markup (Position.thread_data ()) Markup.position;
  in
    ((Pretty.mark position_markup (Pretty.keyword1 "find_names")) ::
      Par_List.map (Pretty.item o (pretty_ref ctxt)) results)
    |> Pretty.fbreaks |> Pretty.block |> Pretty.writeln
  end

end

val _ =
  Outer_Syntax.command @{command_keyword find_names}
    "find other names of a named theorem"
    (Parse.thms1 >> (fn srcs => Toplevel.keep (fn st =>
      pretty_find_names (Toplevel.context_of st)
        (hd (Attrib.eval_thms (Toplevel.context_of st) srcs)))));
\<close>

end
