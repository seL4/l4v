(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* Equations between monads. Conclusions of the form "f = g" where f and g are monads.
   Should not be Hoare triples (those go into a different theory). *)

theory Trace_Monad_Equations
  imports
    Trace_Lemmas
begin

lemmas bind_then_eq = arg_cong2[where f=bind, OF _ refl]

lemma modify_id:
  "modify id = return ()"
  by (simp add: modify_def get_def bind_def put_def return_def)

lemma modify_modify:
  "(do x \<leftarrow> modify f; modify (g x) od) = modify (g () o f)"
  by (simp add: bind_def simpler_modify_def)

lemmas modify_modify_bind = arg_cong2[where f=bind,
  OF modify_modify refl, simplified bind_assoc]

lemma select_single:
  "select {x} = return x"
  by (simp add: select_def return_def)

lemma put_then_get[unfolded K_bind_def]:
  "do put s; get od = do put s; return s od"
  by (simp add: put_def bind_def get_def return_def)

lemmas put_then_get_then
    = put_then_get[THEN bind_then_eq, simplified bind_assoc return_bind]

lemma select_empty_bind[simp]:
  "select {} >>= f = select {}"
  by (simp add: select_def bind_def)

lemma fail_bind[simp]:
  "fail >>= f = fail"
  by (simp add: bind_def fail_def)

end