(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Apply_Debug_Test
imports
  Eisbach_Tools.Apply_Debug
  Eisbach_Tools.Apply_Trace_Cmd
begin

chapter \<open>Apply_Debug\<close>

text \<open>
 Apply_debug can be invoked as a backwards refinement step (wherever "apply" works). It invokes
 the given proof method (expression) in a managed thread and blocks when it encounters a special
 "#break" method. Either this is written as part of the definition in an inner method written in Eisbach,
 or appears directly in the invoked method.
 Once a break point is hit, the proof thread blocks and the command returns with whatever the proof
 state was at the breakpoint.

 The provided "continue" command allows for execution to resume. Note that regular proof commands
 can be written between continue commands and method execution will continue as if that were
 the proof state at the break point. This can allow for debugging methods without necessarily rewriting
 their implementation.

 Some interactive markup is given in jEdit: clicking on
 an apply_debug or continue command will show the subsequent breakpoint that was hit (and
 the method in the original expression that hit it),
 clicking on a breakpoint will highlight all "continue" commands which stopped at that breakpoint.
 Note that breakpoints inside of Eisbach definitions are highlighted as well.

 Finally the "finish" command will resume execution and ignore all further breakpoints.

 Outside of an apply_debug invocation the #break method is ignored and any "continue" or "finish"
 commands will throw a runtime error. The debug command that finally terminates the method
 (either finish or continue) will exit the debugger and print "Final Result".
\<close>


method some_break = #break

lemma assumes B: B
  shows "A \<Longrightarrow> A \<and> B \<and> A \<and> A"
  apply (rule conjI, #break, assumption) (* #break is ignored here *)
  apply_debug (rule conjI, #break, some_break, #break, assumption?)+
  continue
  continue
    apply (rule B) (* this effect is saved *)
  continue
  continue
  apply assumption
  finish
  done

section \<open>Tags\<close>

text \<open>
  Tags can be used to filter the kind of breakpoints that are hit by any given breakpoint
  invocation. By default apply_debug will only hit untagged breakpoints, if any tags are given
  then both untagged breakpoints and those matching the given tags will trigger a break.
  Each breakpoint can be given 0 or 1 tags.
\<close>

method my_conjI = (#break "conjI", rule conjI)
method my_assumption = (#break "assumption", assumption)

lemma "A \<Longrightarrow> A \<and> A \<and> A \<and> A \<and> A"
  apply_debug (my_conjI, my_assumption) (* no breakpoints hit *)

  apply_debug (tags "assumption")
    (#break, my_conjI, my_assumption) (* inline breakpoint *)
    continue (* assumption breakpoint *)
    finish (* goal finished *)

  apply_debug (tags "conjI")
    (my_conjI, my_assumption) (* conjI is hit *)
  continue (* assumption breakpoint is skipped *)

  apply_debug (tags "assumption", "conjI")
    (my_conjI, my_assumption) (* conjI is hit *)
  continue (* assumption is hit *)
  finish
  by assumption

section \<open>Arguments to Continue Command\<close>

text \<open>Continue can be given a single positive number that will skip over that many breakpoints.
NB: continue 1 is the same as a bare continue.\<close>

lemma
  assumes AB: "A \<Longrightarrow> B"
  assumes BA: "B \<Longrightarrow> A"
  assumes BC: "B \<Longrightarrow> C"
  assumes CB: "C \<Longrightarrow> B"
  assumes CD: "C \<Longrightarrow> D"
  assumes DC: "D \<Longrightarrow> C"
  assumes DE: "D \<Longrightarrow> E"
  assumes ED: "E \<Longrightarrow> D"
  assumes FE: "F \<Longrightarrow> E"
  assumes EF: "E \<Longrightarrow> F"
  assumes E: "E"
  shows
  "A"

  apply_debug ((((#break, rule assms, #break, rule assms,#break, rule assms, #break, rule assms, #break,
                rule assms, #break, rule assms, #break, rule assms)));fail)

  continue 3
  continue 11
  continue
done

text \<open>
  Continue may also be given a method, which is understood as a filter on each breakpoint.
  If the method successfully applies, then the breakpoint is hit and the result of executing the
  method is left as the proof state. If it fails at a given breakpoint, it is ignored and execution
  continues, either until the next breakpoint or until the method terminates.
  NB: "finish" is equivalent to "continue fail".

  Note that a breakpoint alone cannot fail or affect backtracking directly.
\<close>

lemma
  assumes B: B and C: C
  shows "A \<or> D \<or> (B \<and> C)"
  apply_debug ((rule disjI1 disjI2, #break)+, rule conjI, #break)
  continue (rule B) (* skip until conjI reveals B *)
   apply (rule C)
   finish
  done


section \<open>Element binding\<close>

text \<open>
 Inside of a "continue" block we can refer to Eisbach variables that are in the
 lexographical scope of the associated breakpoint.
 This includes arguments passed to Eisbach methods and variables that are bound inside of a
 "match" body.
\<close>

named_theorems rule3

method bazz for C :: int uses rule1 rule2 declares rule3 =
  (match premises in H[OF rule2]:"PROP G" for G \<Rightarrow> \<open>#break\<close>)

schematic_goal Z:
  assumes AC: "A \<Longrightarrow> C"
  assumes BA: "B \<Longrightarrow> A"
  assumes AB: "A \<Longrightarrow> B"
  assumes A: "A"
  assumes rule1: "ZZZ"
  assumes A: "A"
  assumes C
  shows "(A \<Longrightarrow> ?C) \<Longrightarrow> D \<Longrightarrow> A \<and> B \<and> C"

  apply (intro conjI)
  prefer 2

  apply_debug (match premises in H:"PROP C" for C \<Rightarrow>
        \<open>#break, bazz 4 rule1: AB rule2: A\<close>)
    term ?C (* C from match is bound *)
    thm H (* H is bound as the (focused) fact proving C *)
    continue (* inside bazz method now *)
    term ?C (* C is now argument to bazz *)
    term ?G (* G is bound from inner match from bazz *)
    thm rule1 (* bound to AB from call site *)
    thm rule2 (* bound to A from call site *)
    thm H (* bound to match result from bazz (shadows original H) *)
    finish
 oops

section \<open>Tracing used rules\<close>

text \<open>
 We can observe any used rules between breakpoints by passing apply_debug the "trace" flag. This
 implicitly invokes apply_trace after each continue, showing the rules that have been used since
 the last breakpoint. Note that this is subject to backtracking, so any rules that were used
 as part of a backtracking branch that has since been discarded will not appear.
\<close>

lemma assumes A: A and B: B
  shows "A \<and> B"
  apply_debug (trace) ((rule conjI | rule A B), #break)+
  continue
  continue
  finish
  done

text \<open>
 The trace flag can be passed an argument string (in a cartouche) which accepts the same syntax
 as find_theorems. This will filter the list of all used theorems shown.
\<close>

lemma assumes A: A and B: B
  shows "A \<and> B"
  apply_debug (trace \<open>"_ \<and> _"\<close>) ((rule conjI | rule A B), #break)+
  continue
  finish
  done

section \<open>Show currently-executing method\<close>

text \<open>
 Internally, apply_debug manages a proof thread that is restarted periodically depending on
 how far along it is in its execution when "continue" is invoked. This allows us to seamlessly
 interact with it in jEdit where we might want to rewind time by editing a previous continue
 statement.

 We can observe this internal state by passing the flag "show_running" to apply_debug, which
 will give jEdit markup to show which method is currently being executed by the internal thread.
 Note that this is not necessarily the "continue" that is currently in focus in jEdit.

 This can be particularly useful to discover which method is causing the whole execution to fail
 or time out (even in the absence of any breakpoints).

 In the following example, try making whitespace edits to the continues to see how the proof thread
 is affected.
\<close>


lemma "A \<Longrightarrow> A \<and> A \<and> A \<and> A"
  apply_debug (show_running)
               (rule conjI,
               sleep 0.1, #break, sleep 0.1, assumption, sleep 0.1, #break, sleep 0.1, rule conjI,
               sleep 0.1, #break,
               assumption, sleep 0.1, #break, sleep 0.1, rule conjI, sleep 0.1, #break, sleep 0.1,
               assumption)
  continue
  continue
  continue
  continue
  continue
  apply assumption
  done

section \<open>Final Notes\<close>

text \<open>
 Breakpoints are subject to the real execution path of the method, which includes all backtracking
 branches. This can result in potentially confusing traces when, for example, we see the same proof
 state revisited multiple times.
\<close>

text \<open>
 Only the "raw" proof state is lifted when continuing from a breakpoint: any additional context
 information (e.g. from supply or other Isar commands) is discarded.
\<close>

text \<open>
 The jEdit markup is limited in its ability to descend into higher-order method syntax (e.g. in match).
 The highlighted breakpoint/currently executing method will therefore simply show an entire match
 execution being executed, rather than any particular sub-method. This is not a fundamental
 limitation, but requires more cooperation from the Method module to make the method stack trace
 known as context data.
\<close>

end
