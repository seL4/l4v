(*
 *
 * Copyright 2017, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

theory Apply_Debug_Test
imports Apply_Debug
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

 Some interactive markup is given in jEdit, including showing in real-time the currently executing
 method. When printing a proof state (via apply_debug or continue) the associated breakpoint
 will be highlighted (or the final invoked method
 if the proof thread has finished). Note that this includes marking up an Eisbach definition.

 Finally the "finish" command will resume execution and ignore all further breakpoints.

 Outside of an apply_debug invocation the #break method is ignored.
\<close>

method some_break = #break

lemma assumes B: B
  shows "A \<Longrightarrow> A \<and> B \<and> A \<and> A"
  apply (rule conjI, #break, assumption) (* #break is ignored here *)
  apply_debug (rule conjI, #break, some_break, #break, assumption?)+
  continue
  continue
    apply (rule B)
  continue
  finish
  apply assumption
  done

section \<open>Tags\<close>

text \<open>
  Tags can be used to filter the kind of breakpoints that are hit by any given breakpoint
  invocation. By default apply_debug will only hit untagged breakpoints, if any tags are given
  then both untagged breakpoints and those matching the given tags will trigger a break.
  Each breakpoint can be given 0 or 1 tags.

  For more fine-grained control, each "continue" may also be given a list of tags. This expands
  the list of breakpoint tags that can be hit only for the duration of that particular continue.
\<close>

method my_conjI = (#break "conjI", rule conjI)
method my_assumption = (#break "assumption", assumption)

lemma "A \<Longrightarrow> A \<and> A \<and> A \<and> A"
  apply_debug (my_conjI, my_assumption) (* no breakpoints hit *)

  apply_debug (tags "assumption")
    (#break, my_conjI, my_assumption)
    continue
    continue

  apply_debug (tags "conjI")
    (my_conjI, my_assumption)
  continue (tags "assumption")
  finish


  continue
  finish
  apply_debug (tags "assumption", "conjI")
    (my_conjI, my_assumption)
  continue
  finish
  continue
  finish
  by assumption


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
    continue
    term ?C (* C is now argument to bazz *)
    term ?G (* G is bound from inner match from bazz *)
    thm rule1 (* bound to AB from call site *)
    thm rule2 (* bound to A from call site *)
    thm H (* bound to match result from bazz (shadows outermost result) *)
    finish
 oops

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

end
