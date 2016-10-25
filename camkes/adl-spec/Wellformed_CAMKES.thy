(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

chapter {* Wellformedness of Specifications *}

(*<*)
theory Wellformed_CAMKES
imports Types_CAMKES Helpers_CAMKES
begin
(*>*)

text {*
  To prove that a system specification is correct, we need to define what
  correctness means for the entities that can exist in a CAmkES specification.
  This section provides a definition of wellformedness for each syntactic
  element that captures the necessary conditions for it to represent a valid
  system configuration. Any wellformed system is capable of being instantiated
  in a way that corresponds to its ADL.
*}

subsection {* \label{subsec:winterfaces}Interfaces *}

text {*
  A procedure method is considered wellformed if the symbols of its name and
  parameters are distinct. This constraint ensures the code generation process
  will produce valid code in the target language.
*}
definition
  wellformed_method :: "method \<Rightarrow> bool"
where
  "wellformed_method m \<equiv>
    (m_name m \<notin> set (map p_name (m_parameters m)) \<and>
     distinct (map p_name (m_parameters m)))"

text {*
  The code generated for a procedure is within a single namespace and thus
  the names of all methods in a procedure must be distinct.
*}
definition
  wellformed_procedure :: "procedure \<Rightarrow> bool"
where
  "wellformed_procedure i \<equiv>
    (i \<noteq> []) \<and>
    (\<forall>x \<in> set i. wellformed_method x) \<and>
     distinct (map m_name i)"

text {*
  The implementation currently only supports 32 distinct events (0 - 31). This
  limitation may be removed in a future iteration.
*}
definition
  wellformed_event :: "event \<Rightarrow> bool"
where
  "wellformed_event e \<equiv> e < 32"

text {*
  Dataports do not have any attributes beyond their type, so their wellformedness
  is trivial.
*}
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

subsection {* \label{subsec:wcomponents}Components *}
text {*
  For a component to be valid internally, its interfaces must not conflict and
  must themselves be wellformed.
*}
definition
  wellformed_component :: "component \<Rightarrow> bool"
where
  "wellformed_component c \<equiv>
     (* No symbol collisions *)
    (distinct (map fst (requires c) @ map fst (provides c) @ map fst (dataports c) @
     map fst (emits c) @ map fst (consumes c)) \<and>
     (* No C symbol collisions. *)
    (\<forall>x \<in> set (requires c). wellformed_procedure (snd x)) \<and>
    (\<forall>x \<in> set (provides c). wellformed_procedure (snd x)) \<and>
     (* Events valid. *)
    (\<forall>x \<in> set (emits c). wellformed_event (snd x)) \<and>
    (\<forall>x \<in> set (consumes c). wellformed_event (snd x)) \<and>
     (* Dataports valid. *)
    (\<forall>x \<in> set (dataports c). wellformed_dataport (snd x)))"

subsection {* \label{subsec:wconnectors}Connectors *}
text {*
  For a connector to be valid its mode of interaction must be
  consistent with the underlying mechanism.
*}
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

subsection {* \label{subsec:wconnections}Connections *}
definition
  wellformed_connection :: "connection \<Rightarrow> bool"
where
  "wellformed_connection c \<equiv> True"

subsection {* \label{subsec:wsymbols}ADL Symbol Resolution *}
text {*
  All procedures must be satisfied by a unique connection. To define unique connections,
  we first define a general predicate @{text ex_one} that is true when a predicate
  is satisfied for precisely one element in a list.
*}
definition
  ex_one :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "ex_one xs P \<equiv> length (filter P xs) = 1"

text {*
  The following two declarations provide more convenience for this function.
  @{text "\<exists>1 x \<in> xs. P x"} will be translated into @{term "ex_one xs P"}.
*}
syntax
  "_ex_one" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(4\<exists>1 _\<in>_./ _)" [0, 0, 10] 10)
translations
  "\<exists>1 x\<in>xs. P" == "CONST ex_one xs (\<lambda>x. P)"

text {*
  We can now define valid procedures. For each procedure @{term x} there must be
  precisely one connection @{term y} that fits the component instance.
*}

definition
  refs_valid_procedures ::
    "adl_symbol \<Rightarrow> (adl_symbol \<times> procedure) list \<Rightarrow>
     (adl_symbol \<times> connection) list \<Rightarrow> bool"
where
  "refs_valid_procedures component_instance procedures conns \<equiv>
    \<forall>x \<in> set procedures.
     (\<exists>1 y \<in> conns. from_component (snd y) = component_instance \<and>
                    from_interface (snd y) = fst x)"

text {*
  For events and dataports, an interface can be left unconnected in a system with no
  adverse effects.
*}

definition
  refs_valid_components ::
    "(adl_symbol \<times> component) list \<Rightarrow> (adl_symbol \<times> connection) list \<Rightarrow> bool"
where
  "refs_valid_components comps conns \<equiv>
    \<forall>x \<in> set comps. refs_valid_procedures (fst x) (requires (snd x)) conns"

text {*
  Each connection must be connecting interfaces of the same underlying type.
*}

definition
  refs_valid_connection :: "connection \<Rightarrow> (adl_symbol \<times> component) list \<Rightarrow> bool"
where
  "refs_valid_connection x component_list \<equiv> wellformed_connector (conn_type x) \<and>
  (case conn_type x of
    SyncConnector _ \<Rightarrow>
        (* Corresponding procedures exist. *)
      (\<exists>1 y \<in> component_list. to_component x = fst y \<and>
                              does_provide (snd y) (to_interface x)) \<and>
      (\<exists>1 y \<in> component_list. from_component x = fst y \<and>
                              does_require (snd y) (from_interface x))
   |AsyncConnector _ \<Rightarrow>
        (* Corresponding events exist. *)
      (\<exists>1 y \<in> component_list. to_component x = fst y \<and>
                              does_consume (snd y) (to_interface x)) \<and>
      (\<exists>1 y \<in> component_list. from_component x = fst y \<and>
                              does_emit (snd y) (from_interface x))
   |MemoryConnector _ \<Rightarrow>
        (* Corresponding dataports exist. *)
      (\<exists>1 y \<in> component_list. to_component x = fst y \<and>
                              has_dataport (snd y) (to_interface x)) \<and>
      (\<exists>1 y \<in> component_list. from_component x = fst y \<and>
                              has_dataport (snd y) (from_interface x)))"

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

subsection {* \label{subsec:wsystem}Overall System *}
text {*
  We obtain a guarantee of the correctness of a component composition by composing
  the required properties of its constituents.
*}
definition
  wellformed_composition :: "composition \<Rightarrow> bool"
where
  "wellformed_composition c \<equiv>
     (* This system contains \<ge> 1 active component. *)
    (\<exists>x \<in> set (components c). control (snd x)) \<and>
     (* All references resolve. *)
    refs_valid_composition c \<and>
     (* No namespace collisions. *)
    distinct (map fst (components c) @ map fst (connections c)) \<and>
     (* All components are valid. *)
    (\<forall>x \<in> set (components c). wellformed_component (snd x)) \<and>
     (* All connections are valid. *)
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
    wellformed_composition (composition a) \<and> (case (configuration a) of
      None \<Rightarrow> True
    | Some x \<Rightarrow> wellformed_configuration x)"

(*<*)
text {* These definitions are executable, and Isabelle can generate code for them: *}
export_code
  wellformed_component
  wellformed_composition
  wellformed_assembly
  in SML
  module_name "Camkes" file "camkes.ML"

end(*>*)
