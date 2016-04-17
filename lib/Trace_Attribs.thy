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
 * Attribute tracing
 *
 * The idea of this file is to allow users to determine how the simpset,
 * cong set, intro set, wp sets, etc. have changed from an old version
 * of the repository to a new version.
 *
 * The process is as follows:
 *
 *   1. A user runs "save_attributes" on an old, working version of the
 *      theory.
 *
 *   2. This tool will write out a ".foo.attrib_trace" file for each
 *      theory processed.
 *
 *   3. The user modifies imports statements as required, possibly
 *      breaking the proof.
 *
 *   4. The user can now run "diff_attributes" to determine what
 *      commands they should run to restore the simpset / congset /etc
 *      to something closer to the old version.
 *
 * The tool is not complete, in that it won't always suggest the full
 * set of "simp add", "simp del", etc commands. Nor does it know that
 * a rule added to the simpset is causing a problem. It merely lists
 * a hopefully-sensible set of differences.
 *)

theory Trace_Attribs (* FIXME: bitrotted *)
imports HOL
keywords
  "diff_attributes" :: thy_decl
  and "save_attributes" :: thy_decl
begin

ML_file "more_xml.ML"
ML_file "set.ML"
ML_file "trace_attribs.ML"

(* Setup attributes for simpset / claset. *)
setup {*
let
  fun ss ctxt = dest_ss (simpset_of ctxt)
  fun cs ctxt = Classical.rep_cs (claset_of ctxt)

  val pure_names = [
    "HOL.eq_reflection",
    "HOL.Eq_TrueI",
    "HOL.Eq_FalseI",
    "Pure.protectI",
    "Pure.protectD",
    "HOL.meta_eq_to_obj_eq",
    "HOL.simp_implies_def",
    "HOL.iffD1", "HOL.notE"
  ]

  fun cong_rules_eq (x, y) = (snd (fst x) = snd (fst y))

  val attrib_sets = [
      (* Fetch simp rules. *)
      ("simp",   fn ctxt => get_attrib_set ctxt pure_names (
            map snd (#simps (ss ctxt)))),

      (* Fetch cong rules, filtering out duplicates (which may occur
       * due to theory merging --- first takes precedence. *)
      ("cong",   fn ctxt => get_attrib_set ctxt pure_names (
            map snd (#congs (ss ctxt) |> distinct cong_rules_eq))),

      (* Classical rules. *)
      ("intro",  fn ctxt => get_attrib_set ctxt pure_names (Item_Net.content (#safeIs (cs ctxt)))),
      ("intro?", fn ctxt => get_attrib_set ctxt pure_names (Item_Net.content (#hazIs (cs ctxt)))),
      ("elim",   fn ctxt => get_attrib_set ctxt pure_names (Item_Net.content (#safeEs (cs ctxt)))),
      ("elim?",  fn ctxt => get_attrib_set ctxt pure_names (Item_Net.content (#hazEs (cs ctxt))))
  ]
in
   Attrib_Fetchers.map (fold Symtab.update attrib_sets)
end
*}


ML {*
(* Render a thm to a string. *)
fun render_thm ctxt thm =
let
  val ctxt0 = ctxt
    |> Config.put show_markup true
    |> Config.put Printer.show_type_emphasis false
    |> Config.put show_types true
    |> Config.put show_sorts true
    |> Config.put show_structs false
    |> Config.put show_consts true
    |> Config.put show_brackets false
    |> Config.put show_question_marks true
    |> Config.put Name_Space.names_long true
in
  Print_Mode.setmp ["xsymbols"]
   (fn _ => Display.pretty_thm ctxt0 thm
            |> Pretty.str_of
            |> YXML.parse_body
            |> XML.content_of) ()
end
*}

ML {* render_thm @{context} @{thm iffI} *}

(* Setup hook to automatically save theorems. *)
setup {*
  Theory.at_begin (fn thy =>
    (try (fn () =>
      if OS.Process.getEnv "ISABELLE_TRACE_ATTRIBS" <> NONE then
      let
        val ctxt = Proof_Context.init_global thy
      in
        save_attribs_xml ctxt (get_theory_trace_filename thy)
      end
      else ()) ();
    NONE))
*}

ML {*
Outer_Syntax.command @{command_keyword "diff_attributes"}
  "Show commands needed to make the current theory file's simpset closer to its old version."
  (Scan.succeed (
    Toplevel.unknown_theory o Toplevel.keep (fn state =>
      let
        val ctxt = Toplevel.context_of state
        val thy = Proof_Context.theory_of ctxt

        val old_attribs = load_attribs_xml ctxt (get_theory_trace_filename thy)
                 handle IO.Io _ => error (
                      "This command first requires running your proof through with "
                      ^ "the environment variable 'ISABELLE_TRACE_ATTRIBS' set.")
        val new_attribs = get_attrib_data ctxt
      in
        diff_attrib_data ctxt old_attribs new_attribs
        |> render_diffs
        |> writeln
      end)))
*}

ML {*
Outer_Syntax.command @{command_keyword "save_attributes"}
  "Create a .trace_attribs file for the current theory."
  (Scan.succeed (
    Toplevel.unknown_theory o Toplevel.keep (fn state =>
      let
        val ctxt = Toplevel.context_of state
        val thy = Proof_Context.theory_of ctxt
      in
         save_attribs_xml ctxt (get_theory_trace_filename thy)
      end
    )))
*}

(* Test the code paths. *)
context begin
  lemmas [simp del] = simp_thms(1)
  save_attributes

  (* should be empty *)
  diff_attributes

  lemmas [simp] = simp_thms(1)
  lemmas [simp del] = simp_thms(2)

  (* should require adding simp_thms(2), deleting simp_thms(1) *)
  diff_attributes

  lemmas [simp] = simp_thms(2)
end

end
