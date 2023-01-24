(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory ShowTypes_Test
imports
  Lib.ShowTypes
  CParser.LemmaBucket_C
  CParser.CTranslation
begin

text \<open>
  Simple demo and test. The main HOL theories don't have that much
  hidden polymorphism, so we use l4.verified.
\<close>

experiment
  (* The point of this test is to confirm that the generic 'show types' feature
     shows enough type information to fully reconstruct a term; the pointer type
     feature does something similar so we disable it here. *)
  notes [[show_ptr_types = false]]
begin
  lemma c_guard_cast_byte: "c_guard (x :: ('a :: {mem_type}) ptr) \<Longrightarrow> c_guard (ptr_coerce x :: 8 word ptr)"
    goal_show_types 0
    using [[show_sorts]]
    goal_show_types 0
    apply (case_tac x)
    apply (fastforce intro!: byte_ptr_guarded simp: c_guard_def dest: c_null_guard)
    done

  thm c_guard_cast_byte[where x = "Ptr (ucast (0 :: 8 word))"]
  thm_show_types c_guard_cast_byte[where x = "Ptr (ucast (0 :: 8 word))"]

  (* Round-trip test *)
  ML \<open>
  let val ctxt = Config.put show_sorts true @{context}
      (* NB: this test fails if we leave some polymorphism in the term *)
      val term = @{thm c_guard_cast_byte[where x = "Ptr (ucast (0 :: 8 word)) :: unit ptr"]} |> Thm.prop_of
      val string_no_types = Syntax.pretty_term ctxt term
                            |> Pretty.string_of |> YXML.content_of
      val string_show_types = Show_Types.term_show_types true ctxt term

      val _ = assert (Syntax.read_term ctxt string_no_types <> term) "Show_Types test (baseline)"
      val _ = assert (Syntax.read_term ctxt string_show_types = term) "Show_Types test"
  in () end
  \<close>
end

end