(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)
(*<*)
theory UserFilter2
imports GenFilter2Base "../UserStubs"
begin
(*>*)

subsection {* \label{behaprop}Behavioural Properties *}
text {*
  To reason about the behaviour of components themselves, we need to provide
  more information in the intermediate user theory. In this section we present
  an example of this and a proof that @{term client} never receives the secret,
  ``baz''. This property is dependent on the behaviour of @{text filter}, to
  which @{term client} is directly connected.
*}

(*<*)
type_synonym component = "(channel, component_state) comp"

type_synonym lstate = "component_state local_state"
(*>*)

text {*
  First we specify a more precise set of messages to be sent by @{text filter}.
  We define its valid reponses as only the value ``bar'' or the empty string,
  ``''.
*}

definition
  filter_responses :: "channel question set"
where
  "filter_responses \<equiv> {x. \<exists>v \<in> {''bar'', ''''}. q_data x = Return [String v]}"

text {*
  Then we give a more constrained definition of @{text filter} that no longer
  allows it to send any message on the channel connected to @{term client}.
  Note that for the target property we can still leave the remainder of its
  behaviour arbitrary.
*}

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

text {*
  This trusted definition of @{text filter} is passed to the generated system
  theory in the definition of @{term trusted}.
*}

definition
  trusted :: "(inst, (component \<times> lstate)) map"
where
  "trusted \<equiv> [filter \<mapsto> (filter_trusted, Component init_component_state)]"

(*<*)
end
(*>*)
