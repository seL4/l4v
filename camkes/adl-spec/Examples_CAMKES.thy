(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

chapter {* \label{sec:examples}Example Systems *}

(*<*)
theory Examples_CAMKES
imports
  Types_CAMKES
  Library_CAMKES
  Wellformed_CAMKES
begin
(*>*)

subsection {* \label{subsec:echo}Echo *}
text {*
  The following ADL and IDL describe an example system involving two
  components, client and echo. There is a single connection between them, from
  a procedure @{text client.s} that client requires to a procedure
  @{text echo.s} that echo provides. The system is depicted in Figure
  \ref{fig:echo}.

  \begin{figure}[h]
  \begin{center}
  \caption{\label{fig:echo}Echo example}
  \includegraphics[width=0.6\textwidth]{imgs/echo}
  \end{center}
  \end{figure}
*}

text {*
  The procedure used in this system is expressed by the following IDL:

\begin{verbatim}
  procedure Simple {
    string echo_string(in string s);
    int echo_int(in int i);
    void echo_parameter(in int pin, out int pout);
  };
\end{verbatim}

  The representation of this in Isabelle is quite similar:\footnote{The
  procedure parameter type @{text int}
  is a synonym for
  @{term integer} and is
  therefore not modelled in Isabelle.}
*}
definition
  simple :: procedure (* Sourced from Simple.idl4 *)
where
  "simple \<equiv> [
    \<lparr> m_return_type = Some (Primitive (Textual String)), m_name = ''echo_string'',
      m_parameters = [
        \<lparr> p_type = Primitive (Textual String),
          p_direction = InParameter,
          p_name = ''s'' \<rparr>
      ] \<rparr>,
    \<lparr> m_return_type = Some (Primitive (Numerical Integer)), m_name = ''echo_int'',
      m_parameters = [
        \<lparr> p_type = Primitive (Numerical Integer),
          p_direction = InParameter,
          p_name = ''i'' \<rparr>
      ] \<rparr>,
    \<lparr> m_return_type = None, m_name = ''echo_parameter'', m_parameters = [
        \<lparr> p_type = Primitive (Numerical Integer),
          p_direction = InParameter,
          p_name = ''pin'' \<rparr>,
        \<lparr> p_type = Primitive (Numerical Integer),
          p_direction = InParameter,
          p_name = ''pout'' \<rparr>
      ] \<rparr>
  ]"

text {*
  Each component of the system is described by a separate IDL representation:

\begin{verbatim}
  component Client {
    control;
    uses Simple s;
  }
\end{verbatim}

\begin{verbatim}
  component Echo {
    provides Simple s;
  }
\end{verbatim}

  These generate the following formal representations in Isabelle:
*}
definition
  client :: component (* Sourced from Client.camkes *)
where
  "client \<equiv> \<lparr>
    control = True,
    requires = [(''s'', simple)],
    provides = [],
    dataports = [],
    emits = [],
    consumes = [],
    attributes = []
  \<rparr>"

definition
  echo :: component (* Sourced from Echo.camkes *)
where
  "echo \<equiv> \<lparr>
    control = False,
    requires = [],
    provides = [(''s'', simple)],
    dataports = [],
    emits = [],
    consumes = [],
    attributes = []
  \<rparr>"

text {*
  A @{term composition} block is used to combine these elements into the
  complete system. There are no attributes in this simple system so the
  @{term configuration} block of the @{term assembly} can be omitted. The two
  components are connected via a seL4RPC connection. Note that the underlying
  implementation mechanism of this seL4RPC connection is abstracted.

\begin{verbatim}
  assembly {
    composition {
      component Echo echo;
      component Client client;
      connection seL4RPC simple(from client.s, to echo.s);
    }
  }
\end{verbatim}

  Once again the generated Isabelle formalism looks similar:
*}
definition
  system :: assembly (* Sourced from simple.camkes *)
where
  "system \<equiv> \<lparr>
    composition = \<lparr>
      components = [(''echo'', echo),(''client'', client)],
      connections = [(''simple'', \<lparr>
        conn_type = seL4RPC,
        conn_from = (''client'', ''s''),
        conn_to = (''echo'', ''s'')
      \<rparr>)]
    \<rparr>,
    configuration = None
  \<rparr>"

text {*
  Since our wellformedness conditions are executable, we can now prove that
  this example is a wellformed assembly by evaluation.
*}
lemma "wellformed_assembly system" by eval

subsection {* \label{subsec:events}Events *}
text {*
  \begin{figure}[h]
  \begin{center}
  \caption{\label{fig:event}Event example}
  \includegraphics[width=0.6\textwidth]{imgs/event}
  \end{center}
  \end{figure}

  The following example shows a system using a single event to provide
  asynchronous communication between two components. The identifier assigned
  to the event, @{text 1}, is unimportant in this example as there is only
  one event in use.
*}
definition
  signal :: event
where
  "signal \<equiv> 1"

text {*
  The active component @{text emitter} generates events of the type
  @{term signal}.
*}
definition
  emitter :: component
where
  "emitter \<equiv> \<lparr>
    control = True,
    requires = [],
    provides = [],
    dataports = [],
    emits = [(''event'', signal)],
    consumes = [],
    attributes = []
  \<rparr>"

text {*
  The component @{text consumer} expects to receive these events. When a
  component is defined to consume an event, a function for registering a
  callback for this event is made available to the component. The component
  is initialised at runtime with no callback registered to allow it to do
  any necessary setup without needing to guard against concurrency. Thus,
  even when consuming components are conceptually passive they are usually
  specified as active (@{text "control = True"}) with an entry function that
  performs some initialisation and then registers an event handler.
*}
definition
  consumer :: component
where
  "consumer \<equiv> \<lparr>
    control = True,
    requires = [],
    provides = [],
    dataports = [],
    emits = [],
    consumes = [(''event'', signal)],
    attributes = []
  \<rparr>"

text {*
  The system assembly looks similar to that shown in Section
  \ref{subsec:echo}, but an asynchronous connector is used between the
  components.
*}
definition
  event_system :: assembly
where
  "event_system \<equiv> \<lparr>
    composition = \<lparr>
      components = [(''source'', emitter), (''sink'', consumer)],
      connections = [(''simpleEvent1'', \<lparr>
        conn_type = seL4Asynch,
        conn_from = (''source'', ''event''),
        conn_to = (''sink'', ''event'')
      \<rparr>)]
    \<rparr>,
    configuration = None
  \<rparr>"

text {*
  Again, wellformedness is proved easily by evaluation.
*}
lemma "wellformed_assembly event_system" by eval

subsection {* \label{subsec:dataport}Dataport Usage *}
text {*
  \begin{figure}[h]
  \begin{center}
  \caption{\label{fig:dataport}Dataport example}
  \includegraphics[width=0.6\textwidth]{imgs/dataport}
  \end{center}
  \end{figure}

  The following example demonstrates the use of a shared memory region, referred
  to as a dataport in CAmkES. It also uses one of the key aspects of a component
  platform, component re-use. First the definition of a simple component that
  uses two dataports:
*}
definition
  data_client :: component
where
  "data_client \<equiv> \<lparr>
    control = True,
    requires = [],
    provides = [],
    dataports = [(''d1'', None), (''d2'', None)],
    emits = [],
    consumes = [],
    attributes = []
  \<rparr>"

text {*
  By instantiating this component twice (once as @{text comp1} and once as
  @{text comp2})
  the system contains two identical components. The assembly below connects the
  first dataport of @{text comp1} to the second dataport of
  @{text comp2} and vice versa.
  It is possible to specify a system that instantiates @{term data_client} once and
  connects one of the instance's dataports to the other, but there is nothing to
  be gained from a component communicating with itself via shared memory.
*}
definition
  data_system :: assembly
where
  "data_system \<equiv> \<lparr>
    composition = \<lparr>
      components = [(''comp1'', data_client), (''comp2'', data_client)],
      connections = [(''simple1'', \<lparr>
        conn_type = seL4SharedData,
        conn_from = (''comp1'', ''d1''),
        conn_to = (''comp2'', ''d2'')
      \<rparr>), (''simple2'', \<lparr>
        conn_type = seL4SharedData,
        conn_from = (''comp2'', ''d1''),
        conn_to = (''comp1'', ''d2'')
      \<rparr>)]
    \<rparr>,
    configuration = None
  \<rparr>"

text {* The data port example is wellformed: *}
lemma "wellformed_assembly data_system" by eval

subsection {* \label{subsec:terminal}Secure Terminal *}
text {*
  This section presents a more realistic component system as a prototype of a
  secure terminal. Two components are each given a separate region of a text
  terminal to which they can write character data. They accomplish this by using
  a connection to a third, trusted component that manages the terminal.

  \begin{figure}[h]
  \begin{center}
  \caption{\label{fig:terminal}Terminal example}
  \includegraphics[width=0.8\textwidth]{imgs/terminal}
  \end{center}
  \end{figure}

  The interface for writing to the terminal takes coordinates to write to and a
  single character to write. The coordinates are relative to the caller's
  dedicated region. That is, (0, 0) represents the upper left corner of the
  caller's region, not the terminal as a whole. The method @{text put_char}
  returns 0 on success and non-zero if the coordinates are out of range.
*}
definition
  display :: procedure
where
  "display \<equiv> [
    \<lparr> m_return_type = Some (Primitive (Numerical uint32_t)), m_name = ''put_char'',
      m_parameters = [
        \<lparr> p_type = Primitive (Numerical uint32_t),
          p_direction = InParameter,
          p_name = ''x'' \<rparr>,
        \<lparr> p_type = Primitive (Numerical uint32_t),
          p_direction = InParameter,
          p_name = ''y'' \<rparr>,
        \<lparr> p_type = Primitive (Numerical uint32_t),
          p_direction = InParameter,
          p_name = ''data'' \<rparr>
      ] \<rparr> ]"

text {*
  The trusted component that manages the terminal is passive and executes only
  in response to @{text put_char} calls from its clients. The component
  described below supports exactly two components. This is a case where a more
  flexible definition would be possible using interface arrays as described in
  Section \ref{subsubsec:iarrays}.
*}
definition
  manager :: component
where
  "manager \<equiv> \<lparr>
    control = False,
    requires = [],
    provides = [(''domain1'', display), (''domain2'', display)],
    dataports = [],
    emits = [],
    consumes = [],
    attributes = []
  \<rparr>"

text {*
  The definition of the client adds an attribute so the execution can branch
  based on which instance of the component is running, but the instances could
  equally well execute exactly the same code and have their (identical) output
  written to the two distinct regions by the manager.
*}
definition
  terminal_client :: component
where
  "terminal_client \<equiv> \<lparr>
    control = True,
    requires = [(''d'', display)],
    provides = [],
    dataports = [],
    emits = [],
    consumes = [],
    attributes = [(''ID'', Primitive (Numerical Integer))]
  \<rparr>"

text {*
  Each client is connected to a single interface of the manager.
*}
definition
  channel1 :: connection
where
  "channel1 \<equiv> \<lparr>
    conn_type = seL4RPC,
    conn_from = (''client1'', ''d''),
    conn_to = (''manager'', ''domain1'')
  \<rparr>"
definition
  channel2 :: connection
where
  "channel2 \<equiv> \<lparr>
    conn_type = seL4RPC,
    conn_from = (''client2'', ''d''),
    conn_to = (''manager'', ''domain2'')
  \<rparr>"

definition
  comp :: composition
where
  "comp \<equiv> \<lparr>
    components = [(''manager'', manager),
                  (''client1'', terminal_client),
                  (''client2'', terminal_client)],
    connections = [(''channel1'', channel1),
                   (''channel2'', channel2)]
  \<rparr>"

text {*
  Each client is given a unique identifier so it can distinguish itself. As
  noted above, this is not necessarily required in all systems with multiple
  instantiations of a single component.
*}
definition
  conf :: configuration
where
  "conf \<equiv> [(''client1'', ''ID'', ''1''),
           (''client2'', ''ID'', ''2'')]"

definition
  terminal :: assembly
where
  "terminal \<equiv> \<lparr>
    composition = comp,
    configuration = Some conf
  \<rparr>"

text {*
  Wellformedness for this more complex example is easy as well.
*}
lemma "wellformed_assembly terminal" by eval

(* An example with an unsatisfied required interface. This should be provable
 * to be not wellformed.
 *)
(*<*)locale FAIL_MissingRequires begin(*>*)
(*<*)
(* This example is just here as a sanity check and not
 * particularly relevant for the docs.
 *)
definition
  x :: component
where
  "x \<equiv> \<lparr>
    control = undefined,
    requires = [(undefined, undefined)], (* 1 required interface...*)
    provides = undefined,
    dataports = undefined,
    emits = undefined,
    consumes = undefined,
    attributes = undefined
  \<rparr>"

definition
  broken_assembly :: assembly
where
  "broken_assembly \<equiv> \<lparr>composition = \<lparr>
    components = [(undefined, x)],
    connections = [] (*... that is unsatisfied. *)
  \<rparr>, configuration = undefined\<rparr>"

lemma "\<not> wellformed_assembly broken_assembly"
  apply (unfold wellformed_assembly_def)
  apply (subst de_Morgan_conj)
  apply (rule disjI1)
  apply (unfold wellformed_composition_def broken_assembly_def, simp)
  apply (unfold refs_valid_composition_def
                refs_valid_components_def
                refs_valid_procedures_def
                x_def ex_one_def)
  apply fastforce
 done
(*>*)
(*<*)end(*>*)

(*<*)locale FAIL_Empty begin(*>*)
(*<*)
(* This example is just here as a sanity check and not
 * particularly relevant for the docs.
 *)
definition
  broken_assembly :: assembly
where
  "broken_assembly \<equiv> \<lparr> composition = \<lparr>
    components = [],
    connections = undefined
  \<rparr>, configuration = undefined \<rparr>"

lemma "\<not>wellformed_assembly broken_assembly"
  apply (unfold wellformed_assembly_def)
  apply (case_tac "wellformed_composition (composition broken_assembly)")
   apply (unfold broken_assembly_def)
   apply (frule wellformed_composition_is_nonempty)
   apply simp+
 done
(*>*)
(*<*)end(*>*)

(*<*)
lemma "\<not>wellformed_assembly \<lparr> composition = \<lparr>
    components = [(''foo'', undefined), (''foo'', undefined)],
    connections = undefined
  \<rparr>, configuration = undefined \<rparr>"
  by (simp add:wellformed_assembly_def wellformed_composition_def)

lemma "\<not>wellformed_assembly \<lparr> composition = \<lparr>
    components = undefined,
    connections = [(''foo'', undefined), (''foo'', undefined)]
  \<rparr>, configuration = undefined \<rparr>"
  by (simp add:wellformed_assembly_def wellformed_composition_def)

lemma "\<not>wellformed_assembly \<lparr> composition = \<lparr>
    components = [(''foo'', undefined)],
    connections = [(''foo'', undefined)]
  \<rparr>, configuration = undefined \<rparr>"
  by (simp add:wellformed_assembly_def wellformed_composition_def)

(* Catch previous issue (\<exists>! x \<in> xs::set \<noteq> \<exists>1 x \<in> xs::list) *)
lemma "\<not>wellformed_assembly \<lparr> composition = \<lparr>
    components = [(''foo'', \<lparr>
      control = undefined,
      requires = [(''bar'', undefined)],
      provides = undefined,
      dataports = undefined,
      emits = undefined,
      consumes = undefined,
      attributes = undefined \<rparr>)],
    connections = [(''bar'', \<lparr>
      conn_type = undefined,
      conn_from = (''foo'', ''bar''),
      conn_to = undefined \<rparr>),
    (''baz'', \<lparr>
      conn_type = undefined,
      conn_from = (''foo'', ''bar''),
      conn_to = undefined \<rparr>)]
  \<rparr>, configuration = undefined \<rparr>"
  by (simp add:wellformed_assembly_def wellformed_composition_def refs_valid_components_def
      refs_valid_composition_def refs_valid_procedures_def ex_one_def)

lemma "\<not>wellformed_procedure []"
  by (simp add:wellformed_procedure_def)
(*>*)

(*<*)end(*>*)
