(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* 
Definition of access rights.
*)

chapter "Access Rights"

theory CapRights_A
imports "~~/src/HOL/Main"
begin

text {* The possible access-control rights that exist in the system.
        Note that some rights are synonyms for others. *}
datatype rights = AllowRead | AllowWrite | AllowGrant

definition
  "AllowSend \<equiv> AllowWrite"
definition
  "AllowRecv \<equiv> AllowRead"
definition
  "CanModify \<equiv> AllowWrite"

text {* Cap rights are just a set of access rights *}
type_synonym cap_rights = "rights set"

text {* The set of all rights: *}
definition
  all_rights :: cap_rights
where
 "all_rights \<equiv> UNIV"

end
