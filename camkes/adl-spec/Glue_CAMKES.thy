(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Glue_CAMKES
imports Types_CAMKES
begin

abbreviation "seL4_MsgMaxLength \<equiv> 120::nat"

type_synonym ipc = "nat list"
definition wellformed_ipc :: "ipc \<Rightarrow> bool"
where "wellformed_ipc i = (length i < seL4_MsgMaxLength)"

(* FIXME: These definitions need to diverge from the implementation definitions because we
 * need to distinguish between primitive types and things like strings. The implementation
 * does this in a pretty ad hoc way.
 *)
record parameter_value =
  p_type   :: param_type
  p_value  :: "nat list" (* FIXME: Better type for generic values. *)
definition
  wellformed_parameter :: "parameter_value \<Rightarrow> bool"
where
  "wellformed_parameter p = (case p_type p of
    Primitive _ \<Rightarrow> length (p_value p) = 1
  | Array t \<Rightarrow> (case t of
      SizedArray _ \<Rightarrow> True
    | TerminatedArray _ \<Rightarrow> length (p_value p) > 0 \<and> hd (rev (p_value p)) = 0))"

abbreviation "prim_value \<equiv> \<lambda>(x::parameter_value). hd (p_value x)"

definition
  marshal_primitive :: "ipc \<Rightarrow> parameter_value \<Rightarrow> ipc"
where
  "marshal_primitive i p = i @ [hd (p_value p)]"

(* TODO: The implementation does some optimisations that are not represented in these
 * definitions (e.g. packing multiple chars into a single message register).
 *)
function
  marshal_array :: "ipc \<Rightarrow> parameter_value \<Rightarrow> ipc"
where
  "marshal_array i p = (case p_value p of
    [] \<Rightarrow> i
  | _ # xs \<Rightarrow> marshal_array (marshal_primitive i p) \<lparr>p_type = p_type p, p_value = xs\<rparr>)"
 by fast+

definition
  marshal :: "ipc \<Rightarrow> parameter_value \<Rightarrow> ipc"
where
  "marshal i p = (case p_type p of
    Primitive _ \<Rightarrow> marshal_primitive i p
   |Array _ \<Rightarrow> marshal_array i p)"

definition
  unmarshal_primitive :: "ipc \<Rightarrow> primitive \<Rightarrow> parameter_value \<times> ipc"
where
  "unmarshal_primitive i t = (\<lparr>p_type = Primitive t, p_value = [hd i]\<rparr>, tl i)"

fun
  unmarshal_array_by_size :: "ipc \<Rightarrow> primitive \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> parameter_value \<times> ipc"
where
  "unmarshal_array_by_size i t 0 ac = (\<lparr>p_type = Array (SizedArray t), p_value = ac\<rparr>, i)"
 |"unmarshal_array_by_size i t sz ac = unmarshal_array_by_size (snd (unmarshal_primitive i t)) t (sz - 1) (ac @ p_value (fst (unmarshal_primitive i t)))"

function
  unmarshal_array_by_terminator :: "ipc \<Rightarrow> primitive \<Rightarrow> nat list \<Rightarrow> parameter_value \<times> ipc"
where
  "unmarshal_array_by_terminator i t ac = (case (prim_value (fst (unmarshal_primitive i t))) of
    0 \<Rightarrow> (\<lparr>p_type = Array (TerminatedArray t), p_value = ac @ [0]\<rparr>, snd (unmarshal_primitive i t))
   |_ \<Rightarrow> unmarshal_array_by_terminator (snd (unmarshal_primitive i t)) t (ac @ p_value (fst (unmarshal_primitive i t))))"
 by fast+

definition
  unmarshal_array :: "ipc \<Rightarrow> primitive \<Rightarrow> nat option \<Rightarrow> parameter_value \<times> ipc"
where
  "unmarshal_array i t n = (case n of
    None \<Rightarrow> unmarshal_array_by_terminator i t []
   |Some nn \<Rightarrow> unmarshal_array_by_size i t nn [])"

(* Some sanity checks *)

(* Marshalling something into an empty IPC and then unmarshalling it does not
 * alter the value or the IPC.
 *)
lemma "\<lbrakk>marshal_primitive [] p = i2; wellformed_parameter p; p_type p = Primitive q; unmarshal_primitive i2 q = (n, i3)\<rbrakk>
        \<Longrightarrow> wellformed_ipc i2 \<and> [] = i3 \<and> n = p"
  apply (simp add:marshal_primitive_def unmarshal_primitive_def)
  apply (clarsimp simp:wellformed_ipc_def wellformed_parameter_def)
  apply (induct p, clarsimp, case_tac p_value, simp+)
 done

(* Unmarshalling anything from an empty IPC gives you nothing. *)
lemma "\<forall>t. \<exists>p. (unmarshal_primitive [] t = (\<lparr>p_type = p, p_value = [hd []]\<rparr>, []))"
  by (simp add:unmarshal_primitive_def)

(* TODO: Definitions of send/receive as basically thin wrappers around the syscalls. *)

(* TODO: Definitions of the connectors' operations in terms of send and receive. *)

end
