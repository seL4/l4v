(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
(*<*)
theory UserFilter2
imports GenFilter2Base "UserStubs"
begin
(*>*)

subsection \<open>\label{behaprop}Behavioural Properties\<close>
text \<open>
  To reason about the behaviour of components themselves, we need to provide
  more information in the intermediate user theory. In this section we present
  an example of this and a proof that @{term client} never receives the secret,
  ``baz''. This property is dependent on the behaviour of @{text filter}, to
  which @{term client} is directly connected.
\<close>

(*<*)
type_synonym component = "(channel, component_state) comp"

type_synonym lstate = "component_state local_state"
(*>*)

text \<open>
  First we specify a more precise set of messages to be sent by @{text filter}.
  We define its valid reponses as only the value ``bar'' or the empty string,
  ``''.
\<close>

definition
  filter_responses :: "channel question set"
where
  "filter_responses \<equiv> {x. \<exists>v \<in> {''bar'', ''''}. q_data x = Return [String v]}"

text \<open>
  Then we give a more constrained definition of @{text filter} that no longer
  allows it to send any message on the channel connected to @{term client}.
  Note that for the target property we can still leave the remainder of its
  behaviour arbitrary.
\<close>

definition
  filter_trusted :: component
where
  "filter_trusted \<equiv>
    LOOP (
      UserStep
    \<squnion> ArbitraryRequest two
    \<squnion> ArbitraryResponse two
    \<squnion> ArbitraryResponse one
    \<squnion> Request (\<lambda>_. filter_responses) discard)"

text \<open>
  This trusted definition of @{text filter} is passed to the generated system
  theory in the definition of @{term trusted}.
\<close>

definition
  trusted :: "(inst, (component \<times> lstate)) map"
where
  "trusted \<equiv> [filter \<mapsto> (filter_trusted, Component init_component_state)]"

(*<*)
end
(*>*)
