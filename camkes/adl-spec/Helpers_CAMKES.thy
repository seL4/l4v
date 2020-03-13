(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Some convenient definitions for accessing members inside types. *)

(*<*)
theory Helpers_CAMKES
imports Types_CAMKES
begin
(*>*)

(*<*)
(* For finding a component or connection. *)
definition
  lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b"
where (* Assumes the filter will return a unique element. *)
  "lookup xs x = snd (hd (filter (\<lambda>y. (x = (fst y))) xs))"

(* For accessing properties of a connection. *)
abbreviation "from_components conn  \<equiv> map fst (conn_from conn)"
abbreviation "from_interfaces conn  \<equiv> map snd (conn_from conn)"
abbreviation "to_components conn    \<equiv> map fst (conn_to conn)"
abbreviation "to_interfaces conn    \<equiv> map snd (conn_to conn)"

(* For finding ''interfaces'' within a component. *)
abbreviation "in_map conns xs \<equiv> (\<exists>s\<in>set conns. s \<in> (fst ` (set xs)))"

abbreviation "does_provide c s \<equiv> (in_map s (provides c))"
abbreviation "does_require c s \<equiv> (in_map s (requires c))"
abbreviation "does_emit c s    \<equiv> (in_map s (emits c))"
abbreviation "does_consume c s \<equiv> (in_map s (consumes c))"
abbreviation "has_dataport c s \<equiv> (in_map s (dataports c))"
(*>*)

(*<*)end(*>*)
