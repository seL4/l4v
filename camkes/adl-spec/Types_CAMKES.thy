(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

chapter {* \label{sec:types}Types *}

(*<*)
theory Types_CAMKES
imports Main
begin
(*>*)

text {*
  This section describes the types of entities that appear in the CAmkES
  Interface Definition Language (IDL) and Architecture Description Language
  (ADL). The model assumes that all syntactic elements are available in a single
  environment; that is, all @{term import} inclusion statements have already
  been processed and all references are to be resolved within this context.
*}

subsection {* \label{subsec:symbols}Symbols *}
text {*
  CAmkES has two types of symbols that exist in separate namespaces. Symbols of
  the first type are used in IDL descriptions to identify method names and
  parameters. These symbols are used during code generation and therefore need
  to be distinct within a specific interface.
*}
type_synonym idl_symbol = string

text {*
  The second type of symbols are used in ADL descriptions to identify components,
  connectors and other architecture-level entities. These symbols are also used
  during code generation, but are lexically scoped. E.g. Instantiated interfaces
  within separate components can have an identical name.
*}
type_synonym adl_symbol = string

text {*
  Although both symbols map to the same underlying type, these have different
  constraints (e.g. IDL symbols become direct substrings of code-level symbols
  and hence need to respect symbol naming restrictions for the target
  language(s)).
*}

subsection {* \label{subsec:methods}Methods *}
text {*
  Methods are the elements that make up a CAmkES procedure (described below).
  Each method within a CAmkES procedure has a list of parameters defined by a
  type, direction and symbol name. Each method also has an optional return
  value type. The valid types for method parameters and return values include
  a set of high level types designed to abstract the types available in a
  general programming language. By using only these types in a procedure
  description, the interface can be implemented in any valid target language.

  When fixed width types are required for an interface there are a set of types
  available that are C-specific. Using these types in a procedure description
  precludes implementing or using the procedure in a component not written in C.
  In general the high-level types should be used in preference to the C-specific
  types.

  In high-level languages, arrays may have attached size information, while in
  C this information is passed as an extra parameter to their containing
  method. Arrays are parameterised with the underlying type of
  their elements. Similar to primitive types, using a high-level type for the
  elementary type of an array allows it to be implemented or used in any
  component, while using a C-specific type prevents implementing or using it in
  a component not written in C. Arrays of arrays and multidimensional arrays are
  not supported.
*}

datatype number =
    -- "High level types"
    UnsignedInteger
  | Integer
  | Real
  | Boolean
    -- "C-specific types"
  | uint8_t
  | uint16_t
  | uint32_t
  | uint64_t
  | int8_t
  | int16_t
  | int32_t
  | int64_t
  | double
  | float
  | uintptr_t

datatype textual =
    -- "High level types"
    Character
  | String
    -- "C-specific types"
  | char

datatype primitive =
    Numerical number
  | Textual textual

datatype array =
    SizedArray primitive
  | TerminatedArray primitive

datatype param_type =
    Primitive primitive
  | Array array

text {*
  Rather than having a single return value per procedure method, each
  method parameter can be an input parameter, an output parameter, or both.
*}
datatype param_direction =
    InParameter (* also covers 'refin' *)
  | OutParameter
  | InOutParameter

text {*
  Each procedure comprises a collection of methods that each have an
  optional return type,
  identifier and a list of parameters. Each parameter has a type and an
  identifier.
*}
record parameter =
  p_type        :: param_type
  p_direction   :: param_direction
  p_name        :: idl_symbol

record "method" =
  m_return_type :: "param_type option"
  m_name        :: idl_symbol
  m_parameters  :: "parameter list"
text {*
  The translation from procedure methods in IDL to their representation in
  Isabelle is straightforward. The CAmkES method

\begin{verbatim}
  int foo(in string s);
\end{verbatim}

  is translated to the Isabelle representation
*}
(*<*)value(*>*)
  "\<lparr>m_return_type = Some (Primitive (Numerical Integer)),
    m_name = ''foo'',
    m_parameters = [
      \<lparr>p_type = Primitive (Textual String),
       p_direction = InParameter,
       p_name = ''s''\<rparr>
    ]\<rparr>"
text {*
  More examples are given in \autoref{sec:examples}.
*}

subsection {* \label{subsec:interfaces}Interfaces *}
text {*
  Connections between two components are made from one interface to another.
  CAmkES distinguishes between
  interfaces that consist of a list of function calls and interfaces
  that have other patterns of interaction.

  There are three basic types of supported interfaces. The first, @{text procedure},
  is used for modelling traditional caller-callee semantics of interaction. The
  second, @{text event}, is used for asynchronous notifications such as interrupts.
  Finally, @{text dataport}, is used to model shared memory communication.
*}
type_synonym procedure = "method list"
type_synonym event     = nat -- "ID"
type_synonym dataport  = "string option" -- "type"
datatype interface =
    Procedure procedure
  | Event event
  | Dataport dataport

subsection {* \label{subsec:connectors}Connectors *}
text {*
  Two components are connected via a connector. The type of a connector is an
  abstraction of the underlying communication mechanism. Connectors come in three
  distinct types, native connectors, hardware connectors and export connectors.

  Native connectors map directly to implementation mechanisms. These are the
  types of connectors that are found in almost all component platform models. The
  event-style connector, @{text AsynchronousEvent}, is
  used to model communication consisting of an identifier with no associated message
  data.
*}
datatype native_connector_type =
    AsynchronousEvent -- "an asynchronous notification"
  | RPC -- "a synchronous channel"
  | SharedData -- "a shared memory region"

text {*
  Recalling that hardware devices are modelled as components in CAmkES, hardware
  connectors are used to connect the interface of a device to the interface of a
  software component. Devices must be connected using the connector type that
  corresponds to the mode of interaction with the device.
*}
datatype hardware_connector_type =
    HardwareMMIO -- "memory mapped IO"
  | HardwareInterrupt -- "device interrupts"
  | HardwareIOPort -- "IA32 IO ports"

text {*
  Export connectors are used when
  specifying a compound component. A compound component has a set of interfaces
  that are a subset of the unconnected interfaces of its constituent components.
  The exposed interfaces of the compound component are defined by using export
  connectors to map these to the interfaces of the internal components.

  Export connectors are purely an architectural-level entity and do not exist at
  runtime. During code generation connections through exported interfaces are
  flattened. That is, a connection from interface A to exported interface B that
  exports interface C is instantiated as a connection from interface A to interface
  C would be. They can be thought of as a design-level convenience.

  \begin{figure}[h]
  \begin{center}
  \caption{\label{fig:export}An export connector}
  \includegraphics{imgs/composite-passthrough}
  \end{center}
  \end{figure}
*}
datatype export_connector_type =
    ExportAsynchronous
  | ExportRPC
  | ExportData

datatype connector_type =
    Native native_connector_type
  | Hardware hardware_connector_type
  | Export export_connector_type

text {*
  Connectors are distinguished by the mode of interaction they enable. The
  reason for this will become clearer in \autoref{subsec:wconnectors}.
*}
datatype connector =
    SyncConnector connector_type
  | AsyncConnector connector_type
  | MemoryConnector connector_type

subsection {* \label{subsec:components}Components *}
text {*
  Functional entities in a CAmkES system are represented as components. These
  are re-usable collections of source code with explicit descriptions of the
  exposed methods of interaction (@{term interfaces} described above).

  Components have three distinct modes of communication:
  \begin{enumerate}
    \item Synchronous communication over procedures. This communication is
      analogous to a function call and happens over a channel established from
      a @{text requires} interface to a @{text provides} interface.
    \item Asynchronous communication using events. This is suitable for things
      like interrupts and happens over a channel from an @{text emits} interface to
      a @{text consumes} interface.
    \item Bidirectional communication via shared memory. This is suitable for
      passing large data between components. It happens over a channel between
      two @{text dataports}.
  \end{enumerate}
*}
record component =
  control     :: bool
  requires    :: "(adl_symbol \<times> procedure) list"
  provides    :: "(adl_symbol \<times> procedure) list"
  dataports   :: "(adl_symbol \<times> dataport) list"
  emits       :: "(adl_symbol \<times> event) list"
  consumes    :: "(adl_symbol \<times> event) list"
  attributes  :: "(adl_symbol \<times> param_type) list"

subsection {* \label{subsec:assembling}Assembling a System *}
text {*
  A complete system is formed by instantiating component types that have been
  defined, interconnecting these instances and specifying a system
  configuration. Connections are specified by the two interfaces they connect
  and the communication mechanism in use.
*}
record connection =
  conn_type   :: connector
  conn_from   :: "(adl_symbol \<times> adl_symbol)"
  conn_to     :: "(adl_symbol \<times> adl_symbol)"

text {*
  A composition block is used to contain all components of the system and the
  connections that define their communication with each other.
*}
record composition =
  components  :: "(adl_symbol \<times> component) list"
  connections :: "(adl_symbol \<times> connection) list"

text {*
  Configurations are used as a way of adding extra information to a component
  or specialising the component in a particular context. The attributes
  available to set are specified in the definition of the component, as
  indicated above. These attributes are accessible to the component at the
  code level at runtime.
*}
type_synonym configuration =
  "(adl_symbol \<times> adl_symbol \<times> string) list"

text {*
  Finally the system specification is expressed at the top level as an
  assembly. This extra level of abstraction allows more flexible re-use of
  compositions and configurations.
*}
record assembly =
  composition   :: "composition"
  configuration :: "configuration option"

subsection {* \label{subsec:future}Future Work *}
subsubsection {* \label{subsubsec:composites}Component Hierarchy *}
text {*
  Some component platforms support the notion of explicit composite components.
  This allows a composition of components to be re-used as a component itself.
  In the context of the model presented above, this would allow a
  @{term composition} element to appear anywhere a @{term component} element
  is expected. Flexibility like this is desirable to avoid repeatedly
  constructing common design patterns involving fine grained components. There
  are plans to extend CAmkES to add this functionality.
*}

subsubsection {* \label{subsubsec:iarrays}Interface Arrays *}
text {*
  When specifying a more complicated dynamic component, it can be desirable to
  define an array of interfaces. For example, a component that
  provides an arbitrary number of copies of a specified procedure. This would
  be implemented by the size of the array (the number of such copies) being
  made available to the component at runtime and an index being provided with
  each procedure method invocation. An example of how this could be useful is
  discussed in \autoref{subsec:terminal}.

  Extending this further, allowing the specification of interface arrays that
  can be resized at runtime, by adding or removing connections, enables even
  greater flexibility. Supporting this kind of dynamism in a system requires
  meta functions (for modifying the interface array) and introduces further
  complexity in handling failures of these.
*}

(*<*)end(*>*)
