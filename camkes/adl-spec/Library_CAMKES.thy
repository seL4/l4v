(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*<*)
theory Library_CAMKES
imports Types_CAMKES Wellformed_CAMKES
begin
(*>*)

(*<*)
(* Definitions of some built-in CAmkES entities. *)
definition
  seL4RPC :: connector
where
  "seL4RPC \<equiv> SyncConnector (Native RPC)"
lemma[simp]: "wellformed_connector seL4RPC"
  by (auto simp:wellformed_connector_def seL4RPC_def)

definition
  seL4Asynch :: connector
where
  "seL4Asynch \<equiv> AsyncConnector (Native AsynchronousEvent)"
lemma[simp]: "wellformed_connector seL4Asynch"
  by (auto simp:wellformed_connector_def seL4Asynch_def)

definition
  seL4SharedData :: connector
where
  "seL4SharedData \<equiv> MemoryConnector (Native SharedData)"
lemma[simp]: "wellformed_connector seL4SharedData"
  by (auto simp:wellformed_connector_def seL4SharedData_def)

(* These connectors aren't literally identical, but for the purposes of the architectural model they
 * are.
 *)
definition
  seL4RPCSimple :: connector
where
  "seL4RPCSimple \<equiv> seL4RPC"
lemma[simp]: "wellformed_connector seL4RPCSimple"
  by (simp add:seL4RPCSimple_def)
(*>*)

(*<*)end(*>*)
