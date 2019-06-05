(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

chapter \<open>Wellformedness of Specifications\<close>

(*<*)
theory Wellformed_CAMKES
imports Types_CAMKES Helpers_CAMKES
begin
(*>*)

text \<open>
  To prove that a system specification is correct, we need to define what
  correctness means for the entities that can exist in a CAmkES specification.
  This section provides a definition of wellformedness for each syntactic
  element that captures the necessary conditions for it to represent a valid
  system configuration. Any wellformed system is capable of being instantiated
  in a way that corresponds to its ADL.
\<close>

subsection \<open>\label{subsec:winterfaces}Interfaces\<close>

text \<open>
  A procedure method is considered wellformed if the symbols of its name and
  parameters are distinct. This constraint ensures the code generation process
  will produce valid code in the target language.
\<close>
definition
  wellformed_method :: "method \<Rightarrow> bool"
where
  "wellformed_method m \<equiv>
    (m_name m \<notin> set (map p_name (m_parameters m)) \<and>
     distinct (map p_name (m_parameters m)))"

text \<open>
  The code generated for a procedure is within a single namespace and thus
  the names of all methods in a procedure must be distinct.
\<close>
definition
  wellformed_procedure :: "procedure \<Rightarrow> bool"
where
  "wellformed_procedure i \<equiv>
    (i \<noteq> []) \<and>
    (\<forall>x \<in> set i. wellformed_method x) \<and>
     distinct (map m_name i)"

text \<open>
  The implementation currently only supports 32 distinct events (0 - 31). This
  limitation may be removed in a future iteration.
\<close>
definition
  wellformed_event :: "event \<Rightarrow> bool"
where
  "wellformed_event e \<equiv> e < 32"

text \<open>
  Dataports do not have any attributes beyond their type, so their wellformedness
  is trivial.
\<close>
definition
  wellformed_dataport :: "dataport \<Rightarrow> bool"
where
  "wellformed_dataport d \<equiv> True"

definition
  wellformed_interface :: "interface \<Rightarrow> bool"
where
  "wellformed_interface i \<equiv> (case i of
    Procedure p \<Rightarrow> wellformed_procedure p
  | Event e \<Rightarrow> wellformed_event e
  | Dataport d \<Rightarrow> wellformed_dataport d)"

subsection \<open>\label{subsec:wcomponents}Components\<close>
text \<open>
  For a component to be valid internally, its interfaces must not conflict and
  must themselves be wellformed.
\<close>
definition
  wellformed_component :: "component \<Rightarrow> bool"
where
  "wellformed_component c \<equiv>
     \<comment> \<open>No symbol collisions\<close>
    (distinct (map fst (requires c) @ map fst (provides c) @ map fst (dataports c) @
     map fst (emits c) @ map fst (consumes c)) \<and>
     \<comment> \<open>No C symbol collisions.\<close>
    (\<forall>x \<in> set (requires c). wellformed_procedure (snd x)) \<and>
    (\<forall>x \<in> set (provides c). wellformed_procedure (snd x)) \<and>
     \<comment> \<open>Events valid.\<close>
    (\<forall>x \<in> set (emits c). wellformed_event (snd x)) \<and>
    (\<forall>x \<in> set (consumes c). wellformed_event (snd x)) \<and>
     \<comment> \<open>Dataports valid.\<close>
    (\<forall>x \<in> set (dataports c). wellformed_dataport (snd x)))"

subsection \<open>\label{subsec:wconnectors}Connectors\<close>
text \<open>
  For a connector to be valid its mode of interaction must be
  consistent with the underlying mechanism.
\<close>
definition
  wellformed_connector :: "connector \<Rightarrow> bool"
where
  "wellformed_connector c \<equiv> (case c of
    SyncConnector t \<Rightarrow> (case t of
      Native n \<Rightarrow> n \<in> {RPC}
     |Hardware h \<Rightarrow> h \<in> {HardwareIOPort}
     |Export e \<Rightarrow> e \<in> {ExportRPC})
   |AsyncConnector t \<Rightarrow> (case t of
      Native n \<Rightarrow> n \<in> {AsynchronousEvent}
     |Hardware h \<Rightarrow> h \<in> {HardwareInterrupt}
     |Export e \<Rightarrow> e \<in> {ExportAsynchronous})
   |MemoryConnector t \<Rightarrow> (case t of
      Native n \<Rightarrow> n \<in> {SharedData}
     |Hardware h \<Rightarrow> h \<in> {HardwareMMIO}
     |Export e \<Rightarrow> e \<in> {ExportData}))"

subsection \<open>\label{subsec:wconnections}Connections\<close>
definition
  wellformed_connection :: "connection \<Rightarrow> bool"
where
  "wellformed_connection c \<equiv> True"

subsection \<open>\label{subsec:wsymbols}ADL Symbol Resolution\<close>
text \<open>
  All procedures must be satisfied by a unique connection. To define unique connections,
  we first define a general predicate @{text ex_one} that is true when a predicate
  is satisfied for precisely one element in a list.
\<close>
definition
  ex_one :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ex_one xs P \<equiv> length (filter P xs) = 1"

text \<open>
  The following two declarations provide more convenience for this function.
  @{text "\<exists>1 x \<in> xs. P x"} will be translated into @{term "ex_one xs P"}.
\<close>
syntax
  "_ex_one" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(4\<exists>1 _\<in>_./ _)" [0, 0, 10] 10)
translations
  "\<exists>1 x\<in>xs. P" == "CONST ex_one xs (\<lambda>x. P)"

text \<open>
  We can now define valid procedures. For each procedure @{term x} there must be
  precisely one connection @{term y} that fits the component instance.
\<close>

definition
  refs_valid_procedures ::
    "adl_symbol \<Rightarrow> (adl_symbol \<times> procedure) list \<Rightarrow>
     (adl_symbol \<times> connection) list \<Rightarrow> bool"
where
  "refs_valid_procedures component_instance procedures conns \<equiv>
    \<forall>x \<in> set procedures.
     (\<exists>1 y \<in> conns. (\<exists>1 z \<in> conn_from (snd y). z = (component_instance, fst x)))"

text \<open>
  For events and dataports, an interface can be left unconnected in a system with no
  adverse effects.
\<close>

definition
  refs_valid_components ::
    "(adl_symbol \<times> component) list \<Rightarrow> (adl_symbol \<times> connection) list \<Rightarrow> bool"
where
  "refs_valid_components comps conns \<equiv>
    \<forall>x \<in> set comps. refs_valid_procedures (fst x) (requires (snd x)) conns"

text \<open>
  Each connection must be connecting interfaces of the same underlying type.
\<close>

definition
  refs_valid_connection :: "connection \<Rightarrow> (adl_symbol \<times> component) list \<Rightarrow> bool"
where
  "refs_valid_connection conn component_list \<equiv>
  wellformed_connector (conn_type conn) \<and>
  (case conn_type conn of
    SyncConnector _ \<Rightarrow>
      \<comment> \<open>Corresponding procedures exist.\<close>
        (\<forall>to \<in> set (to_components conn).
           \<exists>1comp \<in> component_list.
             fst comp = to \<and> does_provide (snd comp) (to_interfaces conn))
      \<and> (\<forall>from \<in> set (from_components conn).
           \<exists>1comp \<in> component_list.
             fst comp = from \<and> does_require (snd comp) (from_interfaces conn))
  | AsyncConnector _ \<Rightarrow>
      \<comment> \<open>Corresponding events exist.\<close>
        (\<forall>to \<in> set (to_components conn).
           \<exists>1comp \<in> component_list.
             fst comp = to \<and> does_consume (snd comp) (to_interfaces conn))
      \<and> (\<forall>from \<in> set (from_components conn).
           \<exists>1comp \<in> component_list.
             fst comp = from \<and> does_emit (snd comp) (from_interfaces conn))
  | MemoryConnector _ \<Rightarrow>
      \<comment> \<open>Corresponding dataports exist.\<close>
        (\<forall>to \<in> set (to_components conn).
           \<exists>1comp \<in> component_list.
             fst comp = to \<and> has_dataport (snd comp) (to_interfaces conn))
      \<and> (\<forall>from \<in> set (from_components conn).
           \<exists>1comp \<in> component_list.
             fst comp = from \<and> has_dataport (snd comp) (from_interfaces conn))
  )"

definition
  refs_valid_connections ::
    "(adl_symbol \<times> connection) list \<Rightarrow> (adl_symbol \<times> component) list \<Rightarrow> bool"
where
  "refs_valid_connections conns comps \<equiv>
    \<forall>x \<in> set conns. refs_valid_connection (snd x) comps"

definition
  refs_valid_composition :: "composition \<Rightarrow> bool"
where
  "refs_valid_composition c \<equiv>
    refs_valid_components (components c) (connections c) \<and>
    refs_valid_connections (connections c) (components c)"

subsection \<open>\label{subsec:wsystem}Overall System\<close>
text \<open>
  We obtain a guarantee of the correctness of a component composition by composing
  the required properties of its constituents.
\<close>
definition
  wellformed_composition :: "composition \<Rightarrow> bool"
where
  "wellformed_composition c \<equiv>
     \<comment> \<open>This system contains @{text \<open>\<ge> 1\<close>} active component.\<close>
    (\<exists>x \<in> set (components c). control (snd x)) \<and>
     \<comment> \<open>All references resolve.\<close>
    refs_valid_composition c \<and>
     \<comment> \<open>All connectors and components have distinct names.
        These names will correspond to integrity policy labels.\<close>
    distinct (map fst (components c) @ map fst (connections c)) \<and>
     \<comment> \<open>All components are valid.\<close>
    (\<forall>x \<in> set (components c). wellformed_component (snd x)) \<and>
     \<comment> \<open>All connections are valid.\<close>
    (\<forall>x \<in> set (connections c). wellformed_connection (snd x))"

(*<*)
lemma wellformed_composition_is_nonempty:
  "\<lbrakk>wellformed_composition c\<rbrakk> \<Longrightarrow> components c \<noteq> []"
  by (fastforce simp:wellformed_composition_def)
(*>*)

definition
  wellformed_configuration :: "configuration \<Rightarrow> bool"
where
  "wellformed_configuration conf \<equiv> True" (* TODO *)

definition
  wellformed_assembly :: "assembly \<Rightarrow> bool"
where
  "wellformed_assembly a \<equiv>
    wellformed_composition (composition a) \<and>
    (case (configuration a) of
      None \<Rightarrow> True
    | Some x \<Rightarrow> wellformed_configuration x)"

(*<*)
text \<open>
  Automation for proving wellformedness properties.
  We want the simplifier to try known wellformedness facts first
  before unfolding these. Hence we artificially lift the definitions
  into simp backtracking.
\<close>
named_theorems wellformed_CAMKES_simps

lemmas [simplified atomize_eq, THEN iffD2, wellformed_CAMKES_simps] =
  wellformed_assembly_def
  wellformed_composition_def
  wellformed_configuration_def
  wellformed_connector_def
  wellformed_connection_def
  wellformed_component_def
  wellformed_procedure_def
  wellformed_method_def
  wellformed_dataport_def
  wellformed_event_def
  refs_valid_composition_def
  refs_valid_components_def
  refs_valid_connections_def
  refs_valid_connection_def
  refs_valid_procedures_def

lemmas [wellformed_CAMKES_simps] =
  ex_one_def

end
(*>*)
