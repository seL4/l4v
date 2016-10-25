(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)
chapter {* \label{h:userstubs}Component Behaviour *}

(*<*)
theory UserStubs
imports Types
begin
(*>*)

text {*
  The definitions of a full system are expected to come from a combination of
  generated and user-provided theories. The \camkes generator utility creates a
  base theory using the types and definitions previously discussed that defines
  primitive operations of a specific system. The user is then expected to
  provide a theory that defines the trusted components of the system, building
  on top of these definitions. The generator also produces a theory describing
  the system as a whole that builds on top of the user's intermediate theory.
  Final reasoning about system properties is expected to be done in another
  theory building on this generated system theory.

  These theory dependencies are depicted in \autoref{fig:thydeps}.

  \begin{figure}[h]
    \begin{center}
      \includegraphics[width=300px]{imgs/thydeps}
    \end{center}
    \caption{\label{fig:thydeps}Theorem dependencies}
  \end{figure}

  The remainder of this section describes the default contents of the intermediate
  user theory if none other is provided.
*}

text {*
  When using the generated theories, the user is expected to provide the
  following type instantiations and definitions:

  \begin{itemize}
    \item A type for @{term component_state} representing the local state that
      should be represented for each component;
    \item An initial @{term component_state} for untrusted components to be
      given on startup; and
    \item A (possibly empty) mapping from component instance identifiers to
      trusted component definitions.
  \end{itemize}

  If parts of this are unnecessary for the user's aims, then they can import
  the default implementations described below.
*}

subsection {* \label{ssec:componentstate}Local Component State *}
text {*
  The user should specify a type for @{term component_state} if they want to
  reason about the behaviour of user-provided code. If not, then the type
  @{term unit} captures the irrelevance of this.
*}
type_synonym component_state = unit

text {*
  The generated theories need to be
  provided with a default value for the local state type. This is used as the
  initial
  local state for untrusted components. This definition must be visible even if
  there are no untrusted components in the system, although in this case it
  will not be used.
*}
definition
  init_component_state :: component_state
where
  "init_component_state \<equiv> ()"

subsection {* \label{ssec:untrusted}Untrusted Components *}
text {*
  Any component which does not have its definition supplied will be given a
  generated definition that allows it to non-deterministically perform any
  local operation or send or receive anything on any channel available to it.
  Without providing definitions of any trusted components it will generally be
  impossible to reason about anything beyond architectural properties of the
  system.
*}

subsection {* \label{ssec:trusted}Trusted Components *}
text {*
  Trusted components should be given a defined program text (type
  @{term component}) and an initial local state. The user should provide a
  definition of @{term trusted}, a mapping from component instances to a pair
  of component and initial local state. Any instance not present in the mapping
  will be assigned the broad definition described in the previous paragraph.

  The default mapping is as defined below, empty, causing all instances to fall
  back on their untrusted definitions. The types @{term component} and
  @{term lstate} are overridden in the generated theories and do not need to be
  provided here or by the user, but they make the definition of @{term trusted}
  more readable.
*}

type_synonym ('channel) component = "('channel, component_state) comp"

type_synonym lstate = "component_state local_state"

definition
  trusted :: "('inst, ('channel component \<times> lstate)) map"
where
  "trusted \<equiv> empty"

(*<*)
end
(*>*)
