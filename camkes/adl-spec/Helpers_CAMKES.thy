(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
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
abbreviation "from_component conn \<equiv> (fst (conn_from conn))"
abbreviation "from_interface conn  \<equiv> (snd (conn_from conn))"
abbreviation "to_component conn   \<equiv> (fst (conn_to conn))"
abbreviation "to_interface conn    \<equiv> (snd (conn_to conn))"

(* For finding ''interfaces'' within a component. *)
abbreviation "in_map s xs \<equiv> (s \<in> (fst ` (set xs)))"

abbreviation "does_provide c s \<equiv> (in_map s (provides c))"
abbreviation "does_require c s \<equiv> (in_map s (requires c))"
abbreviation "does_emit c s    \<equiv> (in_map s (emits c))"
abbreviation "does_consume c s \<equiv> (in_map s (consumes c))"
abbreviation "has_dataport c s \<equiv> (in_map s (dataports c))"
(*>*)

(*<*)end(*>*)
