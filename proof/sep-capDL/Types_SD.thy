(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Types_SD
imports Helpers_SD
begin

record user_state =
  kernel_state   :: cdl_state

(* User state monad *)
type_synonym 'a u_monad = "(user_state, 'a) nondet_monad"

(* Return an item from the heap. Fail if no such object exists. *)
abbreviation
  get_spec_object :: "cdl_state \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object u_monad"
where
  "get_spec_object spec p \<equiv> assert_opt (cdl_objects spec p)"

(* End of helper funtions *)

end
