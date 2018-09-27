(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
 *)

(* Basic tests for the Qualify tool. *)

theory Qualify_Test
imports
  Lib.Qualify
begin

locale qualify_test

section \<open>datatype\<close>

datatype leaky = leaky

(* leaks out *)
ML \<open>
  if can dest_Const @{term leaky}
  then ()
  else error "Qualify_Test failed: datatype leaky baseline"
\<close>

qualify qualify_test
  datatype nonleaky = nonleaky

  (* still leaks out *)
  ML \<open>
    if can dest_Const @{term nonleaky}
    then ()
    else error "Qualify_Test failed: datatype nonleaky baseline 1"
  \<close>
end_qualify

(* qualified *)
ML \<open>
  if can dest_Const @{term qualify_test.nonleaky}
  then ()
  else error "Qualify_Test failed: datatype nonleaky baseline 2"
\<close>

ML \<open>
  if can dest_Free @{term nonleaky}
  then ()
  else error "Qualify_Test failed: datatype nonleaky test"
\<close>


section \<open>instantiation\<close>

instantiation leaky :: ord begin
  definition less_leaky:
    "(x :: leaky) < y = True"
  instance by intro_classes
end

(* leaks out *)
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

  (* still leaks out *)
  ML \<open>
    if can (Proof_Context.get_thm @{context}) "less_nonleaky"
    then ()
    else error "Qualify_Test failed: instantiation nonleaky baseline 1"
  \<close>
end_qualify

(* qualified *)
ML \<open>
  if can (Proof_Context.get_thm @{context}) "qualify_test.less_nonleaky"
  then ()
  else error "Qualify_Test failed: instantiation nonleaky baseline 2"
\<close>

ML \<open>
  if can (Proof_Context.get_thm @{context}) "less_nonleaky"
  then error "Qualify_Test failed: instantiation nonleaky test"
  else ()
\<close>

end