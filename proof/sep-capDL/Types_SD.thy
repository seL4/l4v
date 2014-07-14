(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
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
  "get_spec_object spec p \<equiv> assert_opt (opt_object p spec)"

(* End of helper funtions *)

end
