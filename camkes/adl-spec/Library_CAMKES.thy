(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
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
where [wellformed_CAMKES_simps]:
  "seL4RPC \<equiv>
      \<lparr> connector_type = NativeConnector,
        connector_interface = RPCInterface,
        connector_access =
          \<lparr> access_from_to   = {DeleteDerived},
            access_to_from   = {Reply},
            access_from_from = {},
            access_to_to     = {},
            access_from_conn = {Reset, SyncSend, Call},
            access_to_conn   = {Reset, Receive} \<rparr> \<rparr>"
lemma[wellformed_CAMKES_simps]: "wellformed_connector seL4RPC"
  by (auto simp:wellformed_CAMKES_simps)

definition
  seL4Notification :: connector
where [wellformed_CAMKES_simps]:
  "seL4Notification \<equiv>
      \<lparr> connector_type = NativeConnector,
        connector_interface = EventInterface,
        connector_access =
          \<lparr> access_from_to   = {},
            access_to_from   = {},
            access_from_from = {},
            access_to_to     = {},
            access_from_conn = {Reset, Notify},
            access_to_conn   = {Reset, Receive} \<rparr> \<rparr>"
lemma[wellformed_CAMKES_simps]: "wellformed_connector seL4Notification"
  by (auto simp:wellformed_CAMKES_simps)

definition
  seL4SharedData :: connector
where [wellformed_CAMKES_simps]:
  "seL4SharedData \<equiv>
      \<lparr> connector_type = NativeConnector,
        connector_interface = DataportInterface,
        connector_access =
          \<lparr> access_from_to   = {},
            access_to_from   = {},
            access_from_from = {},
            access_to_to     = {},
            \<comment> \<open>Here, we hardcode that both sides have Read and Write because
                the default dataport implementation uses in-line signalling.\<close>
            access_from_conn = {Read, Write},
            access_to_conn   = {Read, Write} \<rparr> \<rparr>"
lemma[wellformed_CAMKES_simps]: "wellformed_connector seL4SharedData"
  by (auto simp:wellformed_CAMKES_simps)

definition
  seL4HardwareInterrupt :: connector
where [wellformed_CAMKES_simps]:
  "seL4HardwareInterrupt \<equiv>
      \<lparr> connector_type = HardwareConnector,
        connector_interface = EventInterface,
        connector_access =
          \<lparr> access_from_to   = {},
            access_to_from   = {},
            access_from_from = {},
            access_to_to     = {},
            \<comment> \<open>NB: hardware components usually share the label of the software driver,
                    so the following are usually redundant\<close>
            access_from_conn = {Reset, Notify},
            access_to_conn   = {Reset, Receive} \<rparr> \<rparr>"
lemma[wellformed_CAMKES_simps]: "wellformed_connector seL4HardwareInterrupt"
  by (auto simp:wellformed_CAMKES_simps)

definition
  seL4HardwareMMIO :: connector
where [wellformed_CAMKES_simps]:
  "seL4HardwareMMIO \<equiv>
      \<lparr> connector_type = HardwareConnector,
        connector_interface = DataportInterface,
        connector_access =
          \<lparr> access_from_to   = {},
            access_to_from   = {},
            access_from_from = {},
            access_to_to     = {},
            \<comment> \<open>NB: hardware components usually share the label of the software driver,
                    so the following are usually redundant\<close>
            access_from_conn = {Read, Write},
            access_to_conn   = {Read, Write} \<rparr> \<rparr>"
lemma[wellformed_CAMKES_simps]: "wellformed_connector seL4HardwareMMIO"
  by (auto simp:wellformed_CAMKES_simps)

(* These are essentially the same connectors at the model level,
   but have different implementations in the CAmkES library,
   hence have different names. *)
abbreviation "seL4RPCCall \<equiv> seL4RPC"
lemmas seL4RPCCall_def = seL4RPC_def
abbreviation "seL4RPCSimple \<equiv> seL4RPC"
lemmas seL4RPCSimple_def = seL4RPC_def
(*>*)

(*<*)end(*>*)
