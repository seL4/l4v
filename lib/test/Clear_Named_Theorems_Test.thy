(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Clear_Named_Theorems_Test
imports Lib.Clear_Named_Theorems
begin

section \<open>Interacting with named theorems in global theory context\<close>

named_theorems glob_thms

thm glob_thms (* empty *)

declare TrueI[glob_thms]
thm glob_thms (* True *)

clear_named_theorems glob_thms

thm glob_thms (* empty again *)


section \<open>Interacting with named theorems inside locale context\<close>

locale Arch

context Arch begin

named_theorems Arch_assms

declare TrueI[Arch_assms]
thm Arch_assms (* True *)

clear_named_theorems Arch_assms
thm Arch_assms (* empty again *)

end (* Arch *)

text \<open>Remember that named theorems are locale-aware, so attempts to directly access them from a
  different context don't do what one might expect:\<close>

context Arch begin

declare TrueI[Arch_assms]

end (* Arch *)

thm Arch.Arch_assms (* empty! *)
clear_named_theorems Arch.Arch_assms (* no effect! *)

context Arch begin

thm Arch_assms (* True *)

text \<open>In cases where we need direct access to the set of theorems accumulated in a named theorems
  from outside its locale, the current set of theorems must be captured under a non-dynamic name:\<close>

lemmas Arch_assms_final = Arch_assms
thm Arch_assms_final (* True *)

end (* Arch *)

thm Arch.Arch_assms_final (* True *)

end
