(*
 * Copyright 2021, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Value_Type_Test
imports Lib.Value_Type
begin

(*
   Define a type synonym from a term that evaluates to a numeral.
*)

definition num_domains :: int where
  "num_domains = 16"

definition num_prio :: int where
  "num_prio = 256"

text \<open>The RHS does not have to be of type nat, it just has to evaluate to any numeral:\<close>
value_type num_queues = "num_prio * num_domains"

text \<open>This produces a type of the specified size and a constant of type nat:\<close>
typ num_queues
term num_queues
thm num_queues_def

text \<open>You can leave out the constant definition, and just define the type:\<close>
value_type (no_def) num_something = "10 * num_domains"

typ num_something


text \<open>
  @{command value_type} uses @{command value} in the background, so all of this also works in
  anonymous local contexts, provided they don't have assumptions (so that @{command value} can
  produce code)

  Example:
\<close>
context
begin

definition X::int where "X = 10"

value_type x_t = X

typ x_t
term x_t
thm x_t_def

end

text \<open>The following does not work, because @{command value} can't find code equations:\<close>

locale y
begin

definition Y::int where "Y = 10"

(* will fail:
value_type y_t = Y
*)

end

text \<open>But it will work outside the locale after interpretation:\<close>

interpretation y .
value_type y_t = Y

end
