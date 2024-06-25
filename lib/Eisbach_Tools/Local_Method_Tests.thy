(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Local_Method_Tests
imports
  Eisbach_Methods
begin

text \<open>
  @{command supply_local_method} allows adding named aliases for methods to the local
  proof context, for when duplicating methods would be too difficult to maintain or debug
  but refactoring the proof would take too long.

  Usage:
    supply_local_method my_name = <method text>

    supply_local_method my_name_1 = <method text 1>
                        my_name_2 = <method text 2>
                        ...

  Where <method text> uses the same syntax as the input to @{command apply}.
\<close>

text \<open>
  @{method local_method} allows using a previously supplied local method to the current proof
  state.

  Usage:
    apply (local_method name)
\<close>

experiment
begin
  section \<open>Basic Examples\<close>

  lemma "A \<Longrightarrow> B \<Longrightarrow> A \<or> B"
    supply_local_method my_simp = simp
    apply (local_method my_simp)
    done

  text \<open>Uses standard @{command apply} parser, allowing all the normal combinators\<close>
  lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
    supply_local_method my_slightly_complicated_method = (rule conjI, assumption+)
    apply (local_method my_slightly_complicated_method)
    done

  text \<open>Can supply multiple methods\<close>
  lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
    supply_local_method my_rule = (rule conjI)
                        my_asm = assumption+
    apply (local_method my_rule)
    apply (local_method my_asm)
    done

  section \<open>Failure Modes\<close>

  text \<open>Fails on non-existent arguments\<close>
  lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
    supply_local_method foo = simp
    apply (fails \<open>local_method bar\<close>)
    oops

  text \<open>Doesn't persist between subgoals\<close>
  lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
    apply (rule conjI)
     subgoal
     supply_local_method my_simp = simp
     apply (local_method my_simp)
     done
    apply (fails \<open>local_method my_simp\<close>)
    oops

  text \<open>Does see top-level method definitions\<close>
  method foo = simp
  lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
    supply_local_method magic = foo
    apply (local_method magic)
    done

end

end