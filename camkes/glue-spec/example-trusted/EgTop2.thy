(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
(*<*)
theory EgTop2
imports GenFilter2System
begin

(* A component may receive on a given channel *)
fun
  receives_on :: "channel \<Rightarrow> component \<Rightarrow> bool"
where
   "receives_on c (Response f) = (\<exists>q s. \<exists>a \<in> f q s. a_channel (snd a) = c)"
 | "receives_on c (a ;; b) = (receives_on c a \<or> receives_on c b)"
 | "receives_on c (IF cond THEN a ELSE b) = (\<forall>s. cond s \<and> receives_on c a \<or> \<not> cond s \<and> receives_on c b)"
 | "receives_on c (WHILE cond DO a) = (\<forall>s. cond s \<and> receives_on c a \<or> \<not> cond s)"
 | "receives_on c (a \<squnion> b) = (receives_on c a \<or> receives_on c b)"
 | "receives_on _ _ = False"

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
(*>*)

text \<open>
  Now it's possible to state and prove the desired property of the system; that
  @{term client} never receives the secret ``baz''.
\<close>

lemma "\<forall>p. \<exists>e s. gs\<^sub>0 p = Some (e, s) \<and>
  (e = client_untrusted \<or>
  \<not>(\<exists>c. sends e {x. q_channel x = c \<and> q_data x = Return [String ''baz'']} \<and>
  receives_on c client_untrusted))"
  unfolding gs\<^sub>0_def trusted_def apply clarsimp
  apply (case_tac p, clarsimp)
    unfolding store_untrusted_def Store_untrusted_def apply clarsimp
    unfolding UserStep_def ArbitraryRequest_def ArbitraryResponse_def
    apply clarsimp
    unfolding client_untrusted_def Client_untrusted_def apply clarsimp
    unfolding UserStep_def ArbitraryRequest_def ArbitraryResponse_def
    apply clarsimp
   apply clarsimp
  apply clarsimp
  unfolding filter_trusted_def UserStep_def ArbitraryRequest_def
            ArbitraryResponse_def apply clarsimp
  unfolding filter_responses_def apply clarsimp
  done

(*<*)
end
(* > *)
