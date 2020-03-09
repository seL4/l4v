(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Basic tests for the Qualify tool. *)

theory Qualify_Test
imports
  Lib.Qualify
begin

locale qualify_test

section \<open>datatype\<close>

datatype leaky = leaky

text \<open>
  By default, the datatype package adds constant names to the unqualified global namespace.
  Let's check that this is the case.
\<close>
ML \<open>
  if can dest_Const @{term leaky}
  then ()
  else error "Qualify_Test failed: datatype leaky baseline"
\<close>

text \<open>
  When we wrap the @{command datatype} command in @{command qualify}\<dots>@{command end_qualify},
  the unqualified names should be removed.
\<close>
qualify qualify_test
  datatype nonleaky = nonleaky

  (* unqualified name still exists here *)
  ML \<open>
    if can dest_Const @{term nonleaky}
    then ()
    else error "Qualify_Test failed: datatype nonleaky baseline 1"
  \<close>
end_qualify

(* but not here *)
ML \<open>
  if can dest_Free @{term nonleaky}
  then ()
  else error "Qualify_Test failed: datatype nonleaky test"
\<close>

(* qualified name exists *)
ML \<open>
  if can dest_Const @{term qualify_test.nonleaky}
  then ()
  else error "Qualify_Test failed: datatype nonleaky baseline 2"
\<close>


section \<open>instantiation\<close>

text \<open>
  We can also qualify fact names from class instantiations.
\<close>

instantiation leaky :: ord begin
  definition less_leaky:
    "(x :: leaky) < y = True"
  instance by intro_classes
end

text \<open>
  By default, fact names are added to the unqualified global namespace.
\<close>
ML \<open>
  if can (Proof_Context.get_thm @{context}) "less_leaky"
  then ()
  else error "Qualify_Test failed: instantiation leaky baseline"
\<close>

qualify qualify_test
  instantiation qualify_test.nonleaky :: ord begin
    definition less_nonleaky:
      "(x :: qualify_test.nonleaky) < y = True"
    instance by intro_classes
  end

  (* unqualified name still exists here *)
  ML \<open>
    if can (Proof_Context.get_thm @{context}) "less_nonleaky"
    then ()
    else error "Qualify_Test failed: instantiation nonleaky baseline 1"
  \<close>
end_qualify

(* but not here *)
ML \<open>
  if can (Proof_Context.get_thm @{context}) "less_nonleaky"
  then error "Qualify_Test failed: instantiation nonleaky test"
  else ()
\<close>

(* qualified name exists *)
ML \<open>
  if can (Proof_Context.get_thm @{context}) "qualify_test.less_nonleaky"
  then ()
  else error "Qualify_Test failed: instantiation nonleaky baseline 2"
\<close>

end
