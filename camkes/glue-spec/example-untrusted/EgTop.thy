(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
(*<*)
theory EgTop
imports GenFilterSystem
begin
(*>*)

subsection \<open>\label{ssec:archprop}Architectural Properties\<close>

text \<open>
  Using the most generalised (untrusted) version of the system, we cannot show
  anything except architectural properties. These are true by construction of
  the generated system. To demonstrate this, we show a proof that the
  @{term client} and @{term store} instances cannot directly communicate.

  First we introduce some definitions to aid the statement of the property. A
  predicate specifying that a component sends on a given channel is defined as
  @{term sends_on}.
\<close>

fun
  sends_on :: "channel \<Rightarrow> component \<Rightarrow> bool"
where
   "sends_on c (Request f _) = (\<exists>s. \<exists>q \<in> f s. q_channel q = c)"
 | "sends_on c (a ;; b) = (sends_on c a \<or> sends_on c b)"
 | "sends_on c (IF cond THEN a ELSE b) =
     (\<forall>s. cond s \<and> sends_on c a \<or> \<not> cond s \<and> sends_on c b)"
 | "sends_on c (WHILE cond DO a) = (\<forall>s. cond s \<and> sends_on c a \<or> \<not> cond s)"
 | "sends_on c (a \<squnion> b) = (sends_on c a \<or> sends_on c b)"
 | "sends_on _ _ = False"

text \<open>
  The corresponding predicate for receiving on a channel is defined as
  @{term receives_on}.
\<close>

fun
  receives_on :: "channel \<Rightarrow> component \<Rightarrow> bool"
where
   "receives_on c (Response f) = (\<exists>q s. \<exists>a \<in> f q s. a_channel (snd a) = c)"
 | "receives_on c (a ;; b) = (receives_on c a \<or> receives_on c b)"
 | "receives_on c (IF cond THEN a ELSE b) =
     (\<forall>s. cond s \<and> receives_on c a \<or> \<not> cond s \<and> receives_on c b)"
 | "receives_on c (WHILE cond DO a) =
     (\<forall>s. cond s \<and> receives_on c a \<or> \<not> cond s)"
 | "receives_on c (a \<squnion> b) = (receives_on c a \<or> receives_on c b)"
 | "receives_on _ _ = False"

text \<open>
  Now whether a component communicates on a channel can be defined as the
  disjunction of these two.
\<close>

definition
  communicates_on :: "channel \<Rightarrow> component \<Rightarrow> bool"
where
  "communicates_on ch c \<equiv> sends_on ch c \<or> receives_on ch c"

text \<open>
  We can now state, and prove, the property that @{term client} and
  @{term store} never directly communicate.
\<close>

lemma "\<forall>c.
  \<not>(communicates_on c client_untrusted \<and> communicates_on c store_untrusted)"
  unfolding communicates_on_def client_untrusted_def Client_untrusted_def
            store_untrusted_def Store_untrusted_def
  apply clarsimp
  unfolding UserStep_def ArbitraryRequest_def ArbitraryResponse_def
  apply clarsimp
  apply (case_tac c, clarsimp+)
  done

text \<open>
  Were we to try reasoning about a property of the system that depended upon
  the behaviour of any component in the system, we would not be able to do it
  using the existing definitions. To show a property of this form we need to
  provide a more precise definition of the critical components. An example of
  this is shown in the next section.
\<close>

(*<*)
(* Whether a component ever sends a question in a given set. *)
fun
  sends :: "component \<Rightarrow> channel question set \<Rightarrow> bool"
where
   "sends (Request f _) qs = (\<exists>s. \<exists>q \<in> f s. q \<in> qs)"
 | "sends (a ;; b) qs = (sends a qs \<or> sends b qs)"
 | "sends (IF cond THEN a ELSE b) qs = (\<forall>s. cond s \<and> sends a qs \<or> \<not> cond s \<and> sends b qs)"
 | "sends (WHILE cond DO a) qs = (\<forall>s. cond s \<and> sends a qs \<or> \<not> cond s)"
 | "sends (a \<squnion> b) qs = (sends a qs \<or> sends b qs)"
 | "sends _ _ = False"

text \<open>
  Reasoning about a property of the system execution itself is not possible
  because we have not described what the components themselves actually do. For
  example, proving that the client never reads the secret is not possible.
\<close>

lemma "\<forall>p. \<exists>e s. gs\<^sub>0 p = Some (e, s) \<and>
           (e = client_untrusted \<or>
            \<not>(\<exists>c. sends e {x. q_channel x = c \<and> q_data x = Return [String ''baz'']} \<and>
              receives_on c client_untrusted))"
  oops

end
(*>*)
