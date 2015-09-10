(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory ConnectorProperties_CAMKES imports
  Types_CAMKES
  Library_CAMKES
begin

(* Information flow implied by a connector. *)
datatype CommunicationMode
 = NoCommunication
 | Incoming
 | Outgoing
 | Bidirectional

(* We can't prove any of this on this level, so just axiomatise it. *)
consts communication_mode :: "connector \<Rightarrow> CommunicationMode"
axiomatization where seL4RPCMode:"communication_mode seL4RPC = Bidirectional"
axiomatization where seL4AsynchMode:"communication_mode seL4Asynch = Outgoing"
axiomatization where seL4SharedDataMode:"communication_mode seL4SharedData = Bidirectional"

(* Predicate that f leaks information to t within sys. *)
definition
  Communication :: "assembly \<Rightarrow> adl_symbol \<Rightarrow> adl_symbol \<Rightarrow> bool"
where
  "Communication sys f t \<equiv>
    wellformed_assembly sys \<and>
    (\<exists>x \<in> set (map fst (components (composition sys))). x = f) \<and>
    (\<exists>y \<in> set (map fst (components (composition sys))). y = t) \<and>
    (f = t \<or>
    (\<exists>c \<in> set (map snd (connections (composition sys))).
       fst (conn_from c) = f \<and>
       fst (conn_to c) = t \<and>
       communication_mode (conn_type c) \<in> {Outgoing, Bidirectional}))"

definition
  CommunicationBi :: "assembly \<Rightarrow> adl_symbol \<Rightarrow> adl_symbol \<Rightarrow> bool"
where
  "CommunicationBi sys f t \<equiv> Communication sys f t \<and> Communication sys t f"

definition
  CommunicationNone :: "assembly \<Rightarrow> adl_symbol \<Rightarrow> adl_symbol \<Rightarrow> bool"
where
  "CommunicationNone sys f t \<equiv>
    wellformed_assembly sys \<and>
    \<not> (Communication sys f t) \<and>
    \<not> (Communication sys t f)"

(* Sanity check *)
lemma "(CommunicationBi s f t \<longrightarrow> \<not> (CommunicationNone s f t)) \<and>
       (CommunicationNone s f t \<longrightarrow> \<not> (CommunicationBi s f t))"
  by (clarsimp simp:CommunicationBi_def CommunicationNone_def)

lemma blah[code]:"communication_mode = (\<lambda>s. if s = seL4Asynch then Outgoing else communication_mode s)"
  by (rule ext, clarsimp simp:seL4AsynchMode)

(* Sanity check that Communication is executable. *)
code_printing
  constant communication_mode \<rightharpoonup>
    (SML) "!(raise/ Fail/ \"undefined\")"

export_code Communication in SML module_name "Camkes" file "/dev/null"

end
