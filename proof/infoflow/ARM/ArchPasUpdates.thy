(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchPasUpdates
imports PasUpdates
begin

context Arch begin global_naming ARM

named_theorems PasUpdates_assms

lemma state_asids_to_policy_aux_pasSubject_update:
  "state_asids_to_policy_aux (aag\<lparr>pasSubject := x\<rparr>) caps asid vrefs =
   state_asids_to_policy_aux aag caps asid vrefs"
  apply (rule equalityI)
   apply clarify
   apply (erule state_asids_to_policy_aux.cases
          | simp
          | fastforce intro: state_asids_to_policy_aux.intros)+
  apply clarify
  apply (erule state_asids_to_policy_aux.cases)
    apply (simp, subst pasObjectAbs_pasSubject_update[symmetric]
               , subst pasASIDAbs_pasSubject_update[symmetric]
               , rule state_asids_to_policy_aux.intros
               , assumption+)+
  done

lemma state_asids_to_policy_pasSubject_update[PasUpdates_assms]:
  "state_asids_to_policy (aag\<lparr>pasSubject := x\<rparr>) s =
   state_asids_to_policy aag s"
  by (simp add: state_asids_to_policy_aux_pasSubject_update)

lemma state_asids_to_policy_aux_pasMayActivate_update:
  "state_asids_to_policy_aux (aag\<lparr>pasMayActivate := x\<rparr>) caps asid_tab vrefs =
   state_asids_to_policy_aux aag caps asid_tab vrefs"
  apply (rule equalityI)
   apply clarify
   apply (erule state_asids_to_policy_aux.cases
          | simp
          | fastforce intro: state_asids_to_policy_aux.intros)+
  apply clarify
  apply (erule state_asids_to_policy_aux.cases)
    apply (simp, subst pasObjectAbs_pasMayActivate_update[symmetric]
               , subst pasASIDAbs_pasMayActivate_update[symmetric]
               , rule state_asids_to_policy_aux.intros
               , assumption+)+
  done

lemma state_asids_to_policy_pasMayActivate_update[PasUpdates_assms]:
  "state_asids_to_policy (aag\<lparr>pasMayActivate := x\<rparr>) s =
   state_asids_to_policy aag s"
  by (simp add: state_asids_to_policy_aux_pasMayActivate_update)

lemma state_asids_to_policy_aux_pasMayEditReadyQueues_update:
  "state_asids_to_policy_aux (aag\<lparr>pasMayEditReadyQueues := x\<rparr>) caps asid_tab vrefs =
   state_asids_to_policy_aux aag caps asid_tab vrefs"
  apply (rule equalityI)
   apply (clarify)
   apply (erule state_asids_to_policy_aux.cases
          | simp
          | fastforce intro: state_asids_to_policy_aux.intros)+
  apply (clarify)
  apply (erule state_asids_to_policy_aux.cases)
    apply (simp, subst pasObjectAbs_pasMayEditReadyQueues_update[symmetric]
               , subst pasASIDAbs_pasMayEditReadyQueues_update[symmetric]
               , rule state_asids_to_policy_aux.intros
               , assumption+)+
  done

lemma state_asids_to_policy_pasMayEditReadyQueues_update[PasUpdates_assms]:
  "state_asids_to_policy (aag\<lparr>pasMayEditReadyQueues := x\<rparr>) s =
   state_asids_to_policy aag s"
  by (simp add: state_asids_to_policy_aux_pasMayEditReadyQueues_update)

declare arch_post_set_flags_inv[PasUpdates_assms]
declare arch_prepare_set_domain_inv[PasUpdates_assms]

end


global_interpretation PasUpdates_2?: PasUpdates_2
proof goal_cases
  interpret Arch .
  case 1 show ?case
    by (unfold_locales; (fact PasUpdates_assms)?)
qed

end
