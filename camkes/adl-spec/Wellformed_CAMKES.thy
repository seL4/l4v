(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter \<open>Wellformedness of Specifications\<close>

(*<*)
theory Wellformed_CAMKES
imports
  Types_CAMKES
  Helpers_CAMKES
  Lib.GenericTag
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
    distinct (map fst (requires c) @ map fst (provides c) @ map fst (dataports c) @
              map fst (emits c) @ map fst (consumes c)) \<and>
     \<comment> \<open>No C symbol collisions.\<close>
    (\<forall>x \<in> set (requires c). wellformed_procedure (snd (snd x))) \<and>
    (\<forall>x \<in> set (provides c). wellformed_procedure (snd x)) \<and>
    \<comment> \<open>Events valid.\<close>
    (\<forall>x \<in> set (emits c). wellformed_event (snd x)) \<and>
    (\<forall>x \<in> set (consumes c). wellformed_event (snd (snd x))) \<and>
     \<comment> \<open>Dataports valid.\<close>
    (\<forall>x \<in> set (dataports c). wellformed_dataport (snd x))"

subsection \<open>\label{subsec:wconnectors}Connectors\<close>
text \<open>
  For now, we don't really restrict what combinations of communication
  mechanisms connectors can use. This can be refined later.
\<close>
definition
  wellformed_connector :: "connector \<Rightarrow> bool"
where
  "wellformed_connector c \<equiv> True"

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
  More convenient syntax for @{const ex_one}.
\<close>
syntax
  "_ex_one" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool" ("(4\<exists>1 _\<in>_./ _)" [0, 0, 10] 10)
translations
  "\<exists>1 x\<in>xs. P" == "CONST ex_one xs (\<lambda>x. P)"

text \<open>
  We can now define valid procedures. For each procedure @{term x} there must be
  precisely one connection @{term y} that fits the component instance.

  The VirtQueue connector (in global-components) currently uses a dummy empty
  procedure that is not a connector, so we ignore empty procedures as a special case.
\<close>

definition
  refs_valid_procedures ::
    "adl_symbol \<Rightarrow> (adl_symbol \<times> (InterfaceRequired \<times> procedure)) list \<Rightarrow>
     (adl_symbol \<times> connection) list \<Rightarrow> bool"
where
  "refs_valid_procedures component_instance procedures conns \<equiv>
    \<forall>(name, (req, proc)) \<in> set procedures.
      req = InterfaceRequired \<longrightarrow> proc \<noteq> [] \<longrightarrow>
      (\<exists>1 z \<in> (concat (map (\<lambda>y. conn_from (snd y)) conns)). z = (component_instance, name))"

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
       (\<comment> \<open>Every to- and from-end of the component must exist.\<close>
        \<forall>(from_name, from_interface) \<in> set (conn_from conn).
          \<exists>1from \<in> component_list.
            fst from = from_name \<and>
            (\<forall>(to_name, to_interface) \<in> set (conn_to conn).
               \<exists>1to \<in> component_list.
                 fst to = to_name \<and>
                 \<comment> \<open>The following checks that the component interfaces have the correct type.\<close>
                (case connector_interface (conn_type conn) of
                     RPCInterface \<Rightarrow>      from_interface \<in> fst ` set (requires (snd from)) \<and>
                                          to_interface \<in> fst ` set (provides (snd to))
                   | EventInterface \<Rightarrow>    from_interface \<in> fst ` set (emits (snd from)) \<and>
                                          to_interface \<in> fst ` set (consumes (snd to))
                   \<comment> \<open>TODO: the check for memory connectors could be optimised; we don't need to
                             check all pairs of from- and to- for dataports with many subscribers.\<close>
                   | DataportInterface \<Rightarrow> from_interface \<in> fst ` set (dataports (snd from)) \<and>
                                          to_interface \<in> fst ` set (dataports (snd to))
                )
                \<and>
                \<comment> \<open>Next, we check that the kind of components being connected are appropriate.\<close>
                (case connector_type (conn_type conn) of
                    \<comment> \<open>Both endpoints must be regular components.\<close>
                    NativeConnector \<Rightarrow>  \<not> hardware (snd from) \<and> \<not> hardware (snd to)
                    \<comment> \<open>At least one endpoint must be a hardware component.
                        FIXME: might not be quite what we want.\<close>
                  | HardwareConnector \<Rightarrow> hardware (snd from) \<or> hardware (snd to)
                  | ExportConnector \<Rightarrow> undefined ''compound components not supported yet''
                )
            )
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
     \<comment> \<open>The @{const group_labels} mapping refers to existing ADL names.\<close>
    (\<forall>(comp, group) \<in> set (group_labels c).
        comp \<in> (fst ` set (components c) \<union> fst ` set (connections c))) \<and>
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
  These are alternative definitions that have annotations, to help debug
  assemblies that are processed by the CAmkES proof toolchain.
\<close>

abbreviation "check_wellformed entity P \<equiv> generic_tag ''Wellformed_CAMKES'' entity P"

lemma wellformed_method_ann:
  "wellformed_method m =
    check_wellformed (wellformed_method, m)
      (m_name m \<notin> set (map p_name (m_parameters m)) \<and>
       distinct (map p_name (m_parameters m)))"
  by (simp only: wellformed_method_def remove_generic_tag simp_thms)

lemma wellformed_procedure_ann:
  "wellformed_procedure i =
     check_wellformed (wellformed_procedure, i)
       ((\<forall>x \<in> set i. wellformed_method x) \<and>
        distinct (map m_name i))"
  by (simp only: wellformed_procedure_def remove_generic_tag simp_thms)

lemma wellformed_event_ann:
  "wellformed_event e =
     check_wellformed (wellformed_event, e) (e < 32)"
  by (simp only: wellformed_event_def remove_generic_tag simp_thms)

lemma wellformed_component_ann:
  "wellformed_component c = check_wellformed (wellformed_component, c) (
    \<comment> \<open>No symbol collisions\<close>
    (let names = map fst (requires c) @ map fst (provides c) @ map fst (dataports c) @
                 map fst (emits c) @ map fst (consumes c)
     in check_wellformed (wellformed_component, ''distinct'', names) (distinct names)) \<and>
    \<comment> \<open>No C symbol collisions.\<close>
    (\<forall>x \<in> set (requires c). wellformed_procedure (snd (snd x))) \<and>
    (\<forall>x \<in> set (provides c). wellformed_procedure (snd x)) \<and>
    \<comment> \<open>Events valid.\<close>
    (\<forall>x \<in> set (emits c). wellformed_event (snd x)) \<and>
    (\<forall>x \<in> set (consumes c). wellformed_event (snd (snd x))) \<and>
    \<comment> \<open>Dataports valid.\<close>
    (\<forall>x \<in> set (dataports c). wellformed_dataport (snd x))
   )"
  by (simp only: wellformed_component_def remove_generic_tag simp_thms Let_def)

lemma refs_valid_procedures_ann:
  "refs_valid_procedures component_instance procedures conns =
     (\<forall>(name, (req, proc)) \<in> set procedures.
      req = InterfaceRequired \<longrightarrow>
      check_wellformed (refs_valid_procedures, name)
        (proc \<noteq> [] \<longrightarrow> (\<exists>1 z \<in> (concat (map (\<lambda>y. conn_from (snd y)) conns)). z = (component_instance, name))))"
  by (simp only: refs_valid_procedures_def remove_generic_tag simp_thms)

text \<open>
  For events and dataports, an interface can be left unconnected in a system with no
  adverse effects.
\<close>
lemma refs_valid_components_ann:
  "refs_valid_components comps conns =
    (\<forall>x \<in> set comps. check_wellformed (refs_valid_components, fst x)
                         (refs_valid_procedures (fst x) (requires (snd x)) conns))"
  by (simp only: refs_valid_components_def remove_generic_tag simp_thms)

text \<open>
  Each connection must be connecting interfaces of the same underlying type.
\<close>

lemma refs_valid_connection_ann:
  "refs_valid_connection conn component_list =
      (wellformed_connector (conn_type conn) \<and>
       (\<comment> \<open>Every to- and from-end of the component must exist.\<close>
        \<forall>(from_name, from_interface) \<in> set (conn_from conn).
          \<exists>1from \<in> component_list.
            fst from = from_name \<and>
            (\<forall>(to_name, to_interface) \<in> set (conn_to conn).
               \<exists>1to \<in> component_list.
                 fst to = to_name \<and>
                 \<comment> \<open>The following checks that the component interfaces have the correct type.\<close>
                 check_wellformed ((refs_valid_connection, ''interface''), (from_name, to_name))
                   (case connector_interface (conn_type conn) of
                       RPCInterface \<Rightarrow>      from_interface \<in> fst ` set (requires (snd from)) \<and>
                                            to_interface \<in> fst ` set (provides (snd to))
                     | EventInterface \<Rightarrow>    from_interface \<in> fst ` set (emits (snd from)) \<and>
                                            to_interface \<in> fst ` set (consumes (snd to))
                     \<comment> \<open>TODO: the check for memory connectors could be optimised; we don't need to
                               check all pairs of from- and to- for dataports with many subscribers.\<close>
                     | DataportInterface \<Rightarrow> from_interface \<in> fst ` set (dataports (snd from)) \<and>
                                            to_interface \<in> fst ` set (dataports (snd to))
                   )
                 \<and>
                 \<comment> \<open>Next, we check that the kind of components being connected are appropriate.\<close>
                 check_wellformed ((refs_valid_connection, ''component''), (from_name, to_name))
                   (case connector_type (conn_type conn) of
                       \<comment> \<open>Both endpoints must be regular components.\<close>
                       NativeConnector \<Rightarrow>  \<not> hardware (snd from) \<and> \<not> hardware (snd to)
                       \<comment> \<open>At least one endpoint must be a hardware component.
                           FIXME: might not be quite what we want.\<close>
                     | HardwareConnector \<Rightarrow> hardware (snd from) \<or> hardware (snd to)
                     | ExportConnector \<Rightarrow> undefined ''compound components not supported yet''
                   )
            )
     ))"
  by (simp only: refs_valid_connection_def remove_generic_tag simp_thms)

lemma refs_valid_connections_ann:
  "refs_valid_connections conns comps =
     (\<forall>x \<in> set conns. check_wellformed (refs_valid_connections, (fst x))
                          (refs_valid_connection (snd x) comps))"
  by (simp only: refs_valid_connections_def remove_generic_tag simp_thms)

lemma wellformed_composition_ann:
  "wellformed_composition c = (
     \<comment> \<open>This system contains @{text \<open>\<ge> 1\<close>} active component.\<close>
    check_wellformed (wellformed_composition, ''control'', map fst (components c))
                     (\<exists>x \<in> set (components c). control (snd x)) \<and>
     \<comment> \<open>All references resolve.\<close>
    refs_valid_composition c \<and>
     \<comment> \<open>The @{const group_labels} mapping refers to existing ADL names.\<close>
    (\<forall>(comp, group) \<in> set (group_labels c).
        check_wellformed (wellformed_composition, ''group_labels'', comp)
          (comp \<in> (fst ` set (components c) \<union> fst ` set (connections c)))) \<and>
     \<comment> \<open>All connectors and components have distinct names.
        These names will correspond to integrity policy labels.\<close>
    check_wellformed (wellformed_composition, ''distinct'', map fst (components c) @ map fst (connections c))
                     (distinct (map fst (components c) @ map fst (connections c))) \<and>
     \<comment> \<open>All components are valid.\<close>
    (\<forall>x \<in> set (components c). check_wellformed (wellformed_composition, ''component'', fst x)
                                               (wellformed_component (snd x))) \<and>
     \<comment> \<open>All connections are valid.\<close>
    (\<forall>x \<in> set (connections c). check_wellformed (wellformed_composition, ''connection'', fst x)
                                                (wellformed_connection (snd x)))
   )"
  by (simp only: wellformed_composition_def remove_generic_tag simp_thms)
(*>*)

(*<*)
text \<open>Automation for proving wellformedness properties.\<close>
named_theorems wellformed_CAMKES_simps

lemmas [simplified, wellformed_CAMKES_simps] =
  wellformed_composition_ann
  wellformed_component_ann
  wellformed_procedure_ann
  wellformed_method_ann
  wellformed_event_ann
  refs_valid_connections_ann
  refs_valid_connection_ann
  refs_valid_procedures_ann
  refs_valid_components_ann

text \<open>These currently have trivial definitions and don't need annotations.\<close>
lemmas [wellformed_CAMKES_simps] =
  wellformed_assembly_def
  wellformed_configuration_def
  wellformed_connector_def
  wellformed_connection_def
  wellformed_dataport_def
  refs_valid_composition_def

lemmas [wellformed_CAMKES_simps] =
  ex_one_def
  generic_tag_True

text \<open>Helper to visualise nested check failures.\<close>
datatype ('a, 'b) check_wellformed_conds = check_wellformed_conds 'a 'b

(* clagged from HOL.Product_Type *)
nonterminal check_wellformed_args
syntax
  "_check_wellformed_conds" ::
      "'a \<Rightarrow> check_wellformed_args \<Rightarrow> ('a, 'b) check_wellformed_conds" ("(1\<langle>_ \<rightarrow>/ _\<rangle>)")
  "_check_wellformed_arg"   :: "'a \<Rightarrow> check_wellformed_args" ("_")
  "_check_wellformed_args"  :: "'a \<Rightarrow> check_wellformed_args \<Rightarrow> check_wellformed_args" ("_ \<rightarrow> _")
translations
  "\<langle>x \<rightarrow> y\<rangle>" \<rightleftharpoons> "CONST check_wellformed_conds x y"
  "_check_wellformed_conds x (_check_wellformed_args y z)" \<rightleftharpoons>
    "_check_wellformed_conds x (_check_wellformed_arg (_check_wellformed_conds y z))"

lemma check_wellformed_merge[wellformed_CAMKES_simps]:
  "check_wellformed x (check_wellformed y P) = check_wellformed (\<langle>x \<rightarrow> y\<rangle>) P"
  by (simp add: remove_generic_tag)

(* example *)
term "check_wellformed \<langle>x \<rightarrow> y \<rightarrow> z\<rangle> P"

end
(*>*)
