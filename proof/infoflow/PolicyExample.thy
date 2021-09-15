(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory PolicyExample
imports ArchNoninterference
begin

(* This first example_auth_graphample shows how notifications and endpoints differ.
   Endpoints tend to spray information in all directions, while
   notifications are unidirectional.

   This example is a subset of the SAC example from access *)
datatype auth_graph_label = T | NTFN1 | NTFN2 | CTR | C | EP | RM

abbreviation partition_label where
  "partition_label x \<equiv> OrdinaryLabel x"

definition example_auth_graph :: "(auth_graph_label subject_label \<times> auth \<times> auth_graph_label subject_label) set" where
  "example_auth_graph \<equiv>
   { (partition_label T,Notify,partition_label NTFN1),
     (partition_label CTR,Receive,partition_label NTFN1),
     (partition_label C,Read,partition_label CTR),
     (partition_label C,Write,partition_label CTR),
     (partition_label CTR,Read,partition_label C),
     (partition_label CTR,Write,partition_label C),
     (partition_label CTR,SyncSend,partition_label EP),
     (partition_label T,Notify,partition_label NTFN2),
     (partition_label RM,Receive,partition_label NTFN2),
     (partition_label RM,Receive,partition_label EP)
   } \<union> {(a,b,c). a = c}"

declare example_auth_graph_def [simp]

lemma subjectReads_T:
  "subjectReads example_auth_graph (partition_label T) = {partition_label T}"
  apply(auto elim: subjectReads.induct)
  done

lemma CTR_in_subjectReads_NTFN1:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label NTFN1)"
  apply(rule read_sync_ep_read_receivers[where ep="partition_label NTFN1"], auto)
  done

lemma EP_in_subjectReads_NTFN1:
  "partition_label EP \<in> subjectReads example_auth_graph (partition_label NTFN1)"
  apply(rule reads_read_queued_thread_read_ep[where t="partition_label CTR" and a="partition_label EP"], auto intro: CTR_in_subjectReads_NTFN1[simplified])
  done

lemma C_in_subjectReads_NTFN1:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label NTFN1)"
  apply(rule reads_read_thread_read_pages)
  apply (rule CTR_in_subjectReads_NTFN1)
  apply simp
  done

lemma RM_in_subjectReads_NTFN1:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label NTFN1)"
  by (rule read_sync_ep_read_receivers; fastforce intro: EP_in_subjectReads_NTFN1)

lemma NTFN2_in_subjectReads_NTFN1:
  "partition_label NTFN2 \<in> subjectReads example_auth_graph (partition_label NTFN1)"
  apply (rule reads_read_queued_thread_read_ep[where t="partition_label RM" and a="partition_label NTFN2"])
  by (auto intro: RM_in_subjectReads_NTFN1[simplified])

lemmas subjectReads_NTFN1' = reads_lrefl[of "partition_label NTFN1"]
                            CTR_in_subjectReads_NTFN1
                            EP_in_subjectReads_NTFN1
                            RM_in_subjectReads_NTFN1
                            C_in_subjectReads_NTFN1
                            NTFN2_in_subjectReads_NTFN1

lemma subjectReads_NTFN1:
  "subjectReads example_auth_graph (partition_label NTFN1) = {partition_label NTFN1, partition_label CTR, partition_label EP, partition_label C, partition_label RM, partition_label NTFN2}"
  apply(rule equalityI)
   apply (rule subsetI)
   apply (erule subjectReads.induct)
           apply (fastforce simp: subjectReads_NTFN1'[simplified])+
  done

lemma RM_in_subjectReads_NTFN2:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label NTFN2)"
  apply(rule read_sync_ep_read_receivers[where ep="partition_label NTFN2"], auto)
  done

lemma EP_in_subjectReads_NTFN2:
  "partition_label EP \<in> subjectReads example_auth_graph (partition_label NTFN2)"
  apply(rule reads_read_queued_thread_read_ep[where t="partition_label RM" and a="partition_label EP"], auto intro: RM_in_subjectReads_NTFN2[simplified])
  done

lemma CTR_in_subjectReads_NTFN2:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label NTFN2)"
  apply(rule read_sync_ep_read_senders[where ep="partition_label EP"], auto intro: EP_in_subjectReads_NTFN2[simplified])
  done

lemma C_in_subjectReads_NTFN2:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label NTFN2)"
  apply(rule reads_read_thread_read_pages)
  apply (rule CTR_in_subjectReads_NTFN2)
  apply simp
  done


lemma NTFN1_in_subjectReads_NTFN2:
  "partition_label NTFN1 \<in> subjectReads example_auth_graph (partition_label NTFN2)"
  apply(rule reads_read_queued_thread_read_ep[where t="partition_label CTR" and a="partition_label NTFN1"], auto intro: CTR_in_subjectReads_NTFN2[simplified])
  done

lemmas subjectReads_NTFN2' = reads_lrefl[of "partition_label NTFN2"]
                            CTR_in_subjectReads_NTFN2
                            EP_in_subjectReads_NTFN2
                            RM_in_subjectReads_NTFN2
                            C_in_subjectReads_NTFN2
                            NTFN1_in_subjectReads_NTFN2

lemma subjectReads_NTFN2:
  "subjectReads example_auth_graph (partition_label NTFN2) = {partition_label NTFN2, partition_label NTFN1, partition_label C, partition_label CTR, partition_label RM, partition_label EP}"
  apply(rule equalityI)
   apply (rule subsetI)
   apply (erule subjectReads.induct)
           apply (fastforce simp: subjectReads_NTFN2'[simplified])+
  done


lemma EP_in_subjectReads_CTR:
  "partition_label EP \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule_tac a="partition_label CTR" and t="partition_label CTR" in reads_read_queued_thread_read_ep)
      apply auto
  done

lemma RM_in_subjectReads_CTR:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(clarsimp)
  apply(rule_tac ep="partition_label EP" in read_sync_ep_read_receivers)
   apply(rule EP_in_subjectReads_CTR[simplified])
  apply fastforce
  done

lemma C_in_subjectReads_CTR:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule reads_read, auto)
  done

lemma NTFN1_in_subjectReads_CTR:
  "partition_label NTFN1 \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule_tac t="partition_label CTR" and auth="Receive" and a="partition_label T" and auth'="Notify" in reads_read_queued_thread_read_ep)
  apply (auto)
  done

lemma NTFN2_in_subjectReads_CTR:
  "partition_label NTFN2 \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule_tac t="partition_label RM" and auth="Receive" and a="partition_label T" and auth'="Notify" in reads_read_queued_thread_read_ep)
  apply (auto intro: RM_in_subjectReads_CTR[simplified])
  done

lemmas subjectReads_CTR' = reads_lrefl[of "partition_label CTR"]
                           NTFN2_in_subjectReads_CTR NTFN1_in_subjectReads_CTR
                           C_in_subjectReads_CTR RM_in_subjectReads_CTR EP_in_subjectReads_CTR

lemma subjectReads_CTR:
  "subjectReads example_auth_graph (partition_label CTR) = {partition_label CTR,partition_label C,partition_label EP, partition_label RM, partition_label NTFN1, partition_label NTFN2}"
  apply(clarsimp)
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct; auto)
  apply(auto simp: subjectReads_CTR'[simplified])
  done

lemma NTFN1_in_subjectReads_C:
  "partition_label NTFN1 \<in> subjectReads example_auth_graph (partition_label C)"
  apply(rule_tac a="partition_label T" and ep="partition_label NTFN1" and t="partition_label CTR" in reads_read_queued_thread_read_ep)
      apply (auto intro: reads_read)
  done

lemma EP_in_subjectReads_C:
  "partition_label EP \<in> subjectReads example_auth_graph (partition_label C)"
  apply(rule_tac a="partition_label CTR" and t="partition_label CTR" in reads_read_queued_thread_read_ep)
      apply (auto intro: reads_read)
  done

lemma RM_in_subjectReads_C:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label C)"
  apply(clarsimp)
  apply(rule read_sync_ep_read_receivers[OF EP_in_subjectReads_C[simplified]])
  apply simp
  done

lemma CTR_in_subjectReads_C:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label C)"
  apply(rule reads_read, auto)
  done

lemma NTFN2_in_subjectReads_C:
  "partition_label NTFN2 \<in> subjectReads example_auth_graph (partition_label C)"
  apply(rule_tac a="partition_label T" and ep="partition_label NTFN2" and t="partition_label RM" in reads_read_queued_thread_read_ep)
  apply(fastforce simp: RM_in_subjectReads_C[simplified])+
  done

lemmas subjectReads_C' = reads_lrefl[of "partition_label C"]
                         NTFN2_in_subjectReads_C NTFN1_in_subjectReads_C
                         RM_in_subjectReads_C EP_in_subjectReads_C CTR_in_subjectReads_C


lemma subjectReads_C:
  "subjectReads example_auth_graph (partition_label C) = {partition_label C,partition_label CTR,partition_label NTFN1, partition_label EP, partition_label RM, partition_label NTFN2}"
  apply(clarsimp)
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct; auto)
  apply(auto simp: subjectReads_C'[simplified])
  done


lemma CTR_in_subjectReads_EP:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(clarsimp)
  apply(rule_tac ep="partition_label EP" in read_sync_ep_read_senders)
     apply simp+
  done

lemma NTFN1_in_subjectReads_EP:
  "partition_label NTFN1 \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule reads_read_queued_thread_read_ep[where a="partition_label NTFN1", OF _ _ _ _ CTR_in_subjectReads_EP])
  apply(auto)
  done

lemma C_in_subjectReads_EP:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule reads_read_thread_read_pages[OF CTR_in_subjectReads_EP])
  apply(auto)
  done

lemma RM_in_subjectReads_EP:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule read_sync_ep_read_receivers[OF reads_lrefl])
  apply(auto)
  done

lemma NTFN2_in_subjectReads_EP:
  "partition_label NTFN2 \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule reads_read_queued_thread_read_ep[where a="partition_label NTFN2", OF _ _ _ _ RM_in_subjectReads_EP])
  apply(auto)
  done

lemmas subjectReads_EP' = reads_lrefl[of "partition_label EP"]
                         CTR_in_subjectReads_EP
                         C_in_subjectReads_EP
                         RM_in_subjectReads_EP
                         NTFN2_in_subjectReads_EP
                         NTFN1_in_subjectReads_EP

lemma subjectReads_EP:
  "subjectReads example_auth_graph (partition_label EP) = {partition_label EP,partition_label CTR,partition_label NTFN1, partition_label C, partition_label RM, partition_label NTFN2}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct; auto)
  apply(auto simp: subjectReads_EP'[simplified])
  done

lemma NTFN2_in_subjectReads_RM:
   "partition_label NTFN2 \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_ep, auto)
  done

lemma EP_in_subjectReads_RM:
   "partition_label EP \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_ep, auto)
  done

lemma CTR_in_subjectReads_RM:
   "partition_label CTR \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule read_sync_ep_read_senders[where ep="partition_label EP", OF EP_in_subjectReads_RM], auto)
  done

lemma C_in_subjectReads_RM:
   "partition_label C \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_read_thread_read_pages[where t="partition_label CTR", OF CTR_in_subjectReads_RM], auto)
  done


lemma NTFN1_in_subjectReads_RM:
   "partition_label NTFN1 \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_read_queued_thread_read_ep[where a="partition_label T" and t="partition_label CTR", OF _ _ _ _ CTR_in_subjectReads_RM], auto)
  done

lemmas subjectReads_RM' = reads_lrefl[of "partition_label RM"]
                         CTR_in_subjectReads_RM
                         C_in_subjectReads_RM
                         EP_in_subjectReads_RM
                         NTFN1_in_subjectReads_RM
                         NTFN2_in_subjectReads_RM

lemma subjectReads_RM:
  "subjectReads example_auth_graph (partition_label RM) = {partition_label RM, partition_label NTFN2,partition_label EP,partition_label CTR, partition_label C, partition_label NTFN1}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct; auto)
  apply(auto simp: subjectReads_RM'[simplified])
  done


lemma NTFN1_in_subjectAffects_T:
  "partition_label NTFN1 \<in> subjectAffects example_auth_graph (partition_label T)
" apply(auto intro: affects_ep)
  done

lemma NTFN2_in_subjectAffects_T:
  "partition_label NTFN2 \<in> subjectAffects example_auth_graph (partition_label T)
" apply(auto intro: affects_ep)
  done

lemma C_in_subjectAffects_T:
  "partition_label C \<in> subjectAffects example_auth_graph (partition_label T)
" apply(rule affects_send[where auth="Notify" and ep="partition_label NTFN1"], auto)
  done

lemma CTR_in_subjectAffects_T:
  "partition_label CTR \<in> subjectAffects example_auth_graph (partition_label T)
" apply(rule affects_send[where auth="Notify" and ep="partition_label NTFN1"], auto)
  done

lemma RM_in_subjectAffects_T:
  "partition_label RM \<in> subjectAffects example_auth_graph (partition_label T)
" apply(rule affects_send[where auth="Notify" and ep="partition_label NTFN2"], auto)
  done

lemma EP_in_subjectAffects_T:
  "partition_label EP \<in> subjectAffects example_auth_graph (partition_label T)"
  by (rule affects_ep_bound_trans, auto)

lemmas subjectAffects_T' = affects_lrefl[of "partition_label T"]
                           NTFN1_in_subjectAffects_T
                           NTFN2_in_subjectAffects_T
                           C_in_subjectAffects_T
                           CTR_in_subjectAffects_T
                           RM_in_subjectAffects_T
                           EP_in_subjectAffects_T



lemma subjectAffects_T:
  "subjectAffects example_auth_graph (partition_label T) = {partition_label NTFN1,partition_label NTFN2,partition_label T,partition_label C, partition_label CTR, partition_label RM, partition_label EP}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases; fastforce)
  apply(auto simp: subjectAffects_T'[simplified])
  done

lemma CTR_in_subjectAffects_NTFN1:
  "partition_label CTR \<in> subjectAffects example_auth_graph (partition_label NTFN1)"
  apply(rule affects_send[where ep="partition_label NTFN1"], auto)
  done

lemma C_in_subjectAffects_NTFN1:
  "partition_label C \<in> subjectAffects example_auth_graph (partition_label NTFN1)"
  apply(rule affects_send[where ep="partition_label NTFN1"], auto)
  done

lemmas subjectAffects_NTFN1' = affects_lrefl[of "partition_label NTFN1"]
                           C_in_subjectAffects_NTFN1
                           CTR_in_subjectAffects_NTFN1


lemma subjectAffects_NTFN1:
  "subjectAffects example_auth_graph (partition_label NTFN1) = {partition_label NTFN1,partition_label CTR,partition_label C}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases; fastforce)
  apply(auto simp: subjectAffects_NTFN1'[simplified])
  done

lemma RM_in_subjectAffects_NTFN2:
  "partition_label RM \<in> subjectAffects example_auth_graph (partition_label NTFN2)"
  apply(rule affects_send[where ep="partition_label NTFN2"], auto)
  done

lemma EP_in_subjectAffects_NTFN2:
  "partition_label EP \<in> subjectAffects example_auth_graph (partition_label NTFN2)"
  apply(rule affects_ep_bound_trans, auto)
  done


lemmas subjectAffects_NTFN2' = affects_lrefl[of "partition_label NTFN2"]
                           RM_in_subjectAffects_NTFN2
                           EP_in_subjectAffects_NTFN2


lemma subjectAffects_NTFN2:
  "subjectAffects example_auth_graph (partition_label NTFN2) = {partition_label NTFN2,partition_label RM, partition_label EP}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases; fastforce)
  apply(auto simp: subjectAffects_NTFN2'[simplified])
  done

lemma C_in_subjectAffects_CTR:
  "partition_label C \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_write[where auth="Write"], auto)
  done

lemma EP_in_subjectAffects_CTR:
  "partition_label EP \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_ep, auto)
  done

lemma NTFN1_in_subjectAffects_CTR:
  "partition_label NTFN1 \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_ep, auto)
  done

lemma RM_in_subjectAffects_CTR:
  "partition_label RM \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_send, auto)
  done

lemmas subjectAffects_CTR' = affects_lrefl[of "partition_label CTR"]
                           NTFN1_in_subjectAffects_CTR
                           C_in_subjectAffects_CTR
                           EP_in_subjectAffects_CTR
                           RM_in_subjectAffects_CTR

lemma subjectAffects_CTR:
  "subjectAffects example_auth_graph (partition_label CTR) = {partition_label CTR,partition_label C,partition_label EP,partition_label NTFN1, partition_label RM}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases; auto)
  apply(auto simp: subjectAffects_CTR'[simplified])
  done

lemma CTR_in_subjectAffects_C:
  "partition_label CTR \<in> subjectAffects example_auth_graph (partition_label C)"
  apply(rule affects_write[where auth=Write], auto)
  done

lemmas subjectAffects_C' = affects_lrefl[of "partition_label C"]
                           CTR_in_subjectAffects_C


lemma subjectAffects_C:
  "subjectAffects example_auth_graph (partition_label C) = {partition_label C,partition_label CTR}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases; auto)
  apply(auto simp: subjectAffects_C'[simplified])
  done

lemma RM_in_subjectAffects_EP:
  "partition_label RM \<in> subjectAffects example_auth_graph (partition_label EP)"
  apply(rule affects_send, auto)
  done

lemma CTR_in_subjectAffects_EP:
  "partition_label CTR \<in> subjectAffects example_auth_graph (partition_label EP)"
  apply(rule affects_recv, auto)
  done

lemma C_in_subjectAffects_EP:
  "partition_label C \<in> subjectAffects example_auth_graph (partition_label EP)"
  apply(rule affects_reset[where ep="partition_label EP" and l'="partition_label CTR"], auto)
  done

lemma NTFN2_in_subjectAffects_EP:
  "partition_label NTFN2 \<in> subjectAffects example_auth_graph (partition_label EP)"
  apply(rule affects_ep_bound_trans, auto)
  done


lemmas subjectAffects_EP' = affects_lrefl[of "partition_label EP"]
                           CTR_in_subjectAffects_EP
                           C_in_subjectAffects_EP
                           RM_in_subjectAffects_EP
                           NTFN2_in_subjectAffects_EP


lemma subjectAffects_EP:
  "subjectAffects example_auth_graph (partition_label EP) = {partition_label EP, partition_label RM, partition_label CTR, partition_label C, partition_label NTFN2}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases; fastforce)
  apply(auto simp: subjectAffects_EP'[simplified])
  done

lemma EP_in_subjectAffects_RM:
  "partition_label EP \<in> subjectAffects example_auth_graph (partition_label RM)"
  apply(rule affects_ep, auto)
  done

lemma CTR_in_subjectAffects_RM:
  "partition_label CTR \<in> subjectAffects example_auth_graph (partition_label RM)"
  apply(rule affects_recv, auto)
  done

lemma NTFN2_in_subjectAffects_RM:
  "partition_label NTFN2 \<in> subjectAffects example_auth_graph (partition_label RM)"
  apply(rule affects_ep, auto)
  done

lemmas subjectAffects_RM' = affects_lrefl[of "partition_label RM"]
                            EP_in_subjectAffects_RM
                            NTFN2_in_subjectAffects_RM
                            CTR_in_subjectAffects_RM


lemma subjectAffects_RM:
  "subjectAffects example_auth_graph (partition_label RM) = {partition_label RM,partition_label EP,partition_label CTR,partition_label NTFN2}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases; auto)
  apply(auto simp: subjectAffects_RM'[simplified])
  done

lemmas subjectReads = subjectReads_T subjectReads_NTFN1 subjectReads_NTFN2 subjectReads_CTR
                      subjectReads_EP subjectReads_RM subjectReads_C

declare example_auth_graph_def [simp del]

lemma partsSubjectAffects_T:
  "partsSubjectAffects example_auth_graph T = {Partition T,Partition NTFN1, Partition NTFN2, Partition CTR, Partition C, Partition EP, Partition RM}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_T | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_NTFN1:
  "partsSubjectAffects example_auth_graph NTFN1 = {Partition NTFN1, Partition CTR, Partition C, Partition EP, Partition RM, Partition NTFN2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_NTFN1 | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_NTFN2:
  "partsSubjectAffects example_auth_graph NTFN2 = {Partition NTFN2, Partition CTR, Partition C, Partition EP, Partition RM, Partition NTFN1}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_NTFN2 | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_CTR:
  "partsSubjectAffects example_auth_graph CTR = {Partition NTFN1, Partition CTR, Partition C, Partition EP, Partition RM, Partition NTFN2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_CTR | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_C:
  "partsSubjectAffects example_auth_graph C = {Partition CTR, Partition C, Partition EP, Partition RM, Partition NTFN1, Partition NTFN2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_C | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_EP:
  "partsSubjectAffects example_auth_graph EP = {Partition CTR, Partition C, Partition EP, Partition RM, Partition NTFN1, Partition NTFN2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_EP | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_RM:
  "partsSubjectAffects example_auth_graph RM = {Partition CTR, Partition C, Partition EP, Partition RM, Partition NTFN2, Partition NTFN1}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_RM | rename_tac xa, case_tac xa)+
  done

lemmas partsSubjectAffects = partsSubjectAffects_T partsSubjectAffects_NTFN1
                            partsSubjectAffects_NTFN2 partsSubjectAffects_CTR
                            partsSubjectAffects_C partsSubjectAffects_RM partsSubjectAffects_EP

definition example_policy :: "(auth_graph_label partition \<times> auth_graph_label partition) set" where
  "example_policy \<equiv> {(PSched,d)|d. True} \<union>
                    {(Partition l,Partition k)|l k. (k = T \<longrightarrow> l = T)}"


lemma "example_policy = policyFlows example_auth_graph"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(clarsimp simp: example_policy_def)
   apply(elim disjE)
    apply(fastforce intro: policy_scheduler)
   apply clarsimp
   apply (rule policy_affects)
   apply (case_tac "k = T")
    apply (clarsimp simp: partsSubjectAffects)
   apply(case_tac l; (auto simp: partsSubjectAffects | case_tac k)+)
  apply(rule subsetI)
  apply(clarsimp simp: example_policy_def)
  apply(erule policyFlows.cases)
   apply(case_tac l, auto simp: partsSubjectAffects)
  done


(* This second example is a classic 'one way information flow'
   example, where information is allowed to flow from Low to High,
   but not the reverse. We consider a typical scenario where
   shared memory and an notification for notifications are used to
   implement a ring-buffer. *)
datatype auth_graph_label2 = High | Low | SharedPage | NTFN

definition example_auth_graph2 :: "(auth_graph_label2 subject_label \<times> auth \<times> auth_graph_label2 subject_label) set" where
  "example_auth_graph2 \<equiv>
   { (partition_label Low,Write,partition_label SharedPage),
     (partition_label Low,Read,partition_label SharedPage),
     (partition_label High,Read,partition_label SharedPage),
     (partition_label Low,Notify,partition_label NTFN),
     (partition_label High,Receive,partition_label NTFN)
   } \<union> {(x,a,y). x = y}"

declare example_auth_graph2_def [simp]

lemma subjectReads_Low: "subjectReads example_auth_graph2 (partition_label Low) = {partition_label Low,partition_label SharedPage}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply (auto intro: reads_read)
  done

lemma subjectReads_SharedPage: "subjectReads example_auth_graph2 (partition_label SharedPage) = {partition_label Low,partition_label SharedPage}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply (auto intro: reads_read_page_read_thread)
  done

lemma High_in_subjectReads_NTFN:
  "partition_label High \<in> subjectReads example_auth_graph2 (partition_label NTFN)"
  apply(rule read_sync_ep_read_receivers)
  apply auto
  done

lemma SharedPage_in_subjectReads_NTFN:
  "partition_label SharedPage \<in> subjectReads example_auth_graph2 (partition_label NTFN)"
  apply(rule reads_read_thread_read_pages[OF High_in_subjectReads_NTFN])
  apply auto
  done

lemma Low_in_subjectReads_NTFN:
  "partition_label Low \<in> subjectReads example_auth_graph2 (partition_label NTFN)"
  apply(rule reads_read_page_read_thread[OF SharedPage_in_subjectReads_NTFN])
  apply auto
  done

lemma subjectReads_NTFN: "subjectReads example_auth_graph2 (partition_label NTFN) = {partition_label NTFN,partition_label High,partition_label SharedPage, partition_label Low}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply (auto intro: High_in_subjectReads_NTFN Low_in_subjectReads_NTFN SharedPage_in_subjectReads_NTFN simp del: example_auth_graph2_def)
  done

lemma NTFN_in_subjectReads_High:
  "partition_label NTFN \<in> subjectReads example_auth_graph2 (partition_label High)"
  apply(fastforce intro: reads_ep)
  done

lemma SharedPage_in_subjectReads_High:
  "partition_label SharedPage \<in> subjectReads example_auth_graph2 (partition_label High)"
  apply(fastforce intro: reads_read_thread_read_pages)
  done

lemma Low_in_subjectReads_High:
  "partition_label Low \<in> subjectReads example_auth_graph2 (partition_label High)"
  apply(fastforce intro: reads_read_page_read_thread[OF SharedPage_in_subjectReads_High])
  done

lemma subjectReads_High: "subjectReads example_auth_graph2 (partition_label High) = {partition_label High,partition_label NTFN, partition_label SharedPage,partition_label Low}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply(auto intro: NTFN_in_subjectReads_High SharedPage_in_subjectReads_High Low_in_subjectReads_High simp del: example_auth_graph2_def)
  done

lemma SharedPage_in_subjectAffects_Low:
  "partition_label SharedPage \<in> subjectAffects example_auth_graph2 (partition_label Low)"
  apply(fastforce intro: affects_write)
  done

lemma NTFN_in_subjectAffects_Low:
  "partition_label NTFN \<in> subjectAffects example_auth_graph2 (partition_label Low)"
  apply(fastforce intro: affects_ep)
  done

lemma High_in_subjectAffects_Low:
  "partition_label High \<in> subjectAffects example_auth_graph2 (partition_label Low)"
  apply(rule affects_send[where ep="partition_label NTFN"])
  apply(auto)
  done

lemma subjectAffects_Low: "subjectAffects example_auth_graph2 (partition_label Low) = {partition_label Low,partition_label NTFN,partition_label SharedPage, partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl SharedPage_in_subjectAffects_Low NTFN_in_subjectAffects_Low High_in_subjectAffects_Low simp del: example_auth_graph2_def)
  done

lemma subjectAffects_SharedPage: "subjectAffects example_auth_graph2 (partition_label SharedPage) = {partition_label SharedPage}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl)
  done

lemma High_in_subjectAffects_NTFN:
  "partition_label High \<in> subjectAffects example_auth_graph2 (partition_label NTFN)"
  apply(rule affects_send[where ep="partition_label NTFN"])
  apply auto
  done

lemma subjectAffects_NTFN: "subjectAffects example_auth_graph2 (partition_label NTFN) = {partition_label NTFN,partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl High_in_subjectAffects_NTFN simp del: example_auth_graph2_def)
  done

lemma NTFN_in_subjectAffects_High:
  "partition_label NTFN \<in> subjectAffects example_auth_graph2 (partition_label High)"
  apply(fastforce intro: affects_ep)
  done

lemma subjectAffects_High: "subjectAffects example_auth_graph2 (partition_label High) = {partition_label NTFN,partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl NTFN_in_subjectAffects_High simp del: example_auth_graph2_def)
  done



lemmas subjectReads_2 = subjectReads_High subjectReads_Low subjectReads_NTFN subjectReads_SharedPage

declare example_auth_graph2_def [simp del]



lemma partsSubjectAffects_Low: "partsSubjectAffects example_auth_graph2 Low = {Partition Low, Partition High, Partition SharedPage, Partition NTFN}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_Low | case_tac xa, rename_tac xa)+
  done

lemma partsSubjectAffects_SharedPage: "partsSubjectAffects example_auth_graph2 SharedPage = {Partition SharedPage, Partition High, Partition Low, Partition NTFN}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_SharedPage | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_NTFN: "partsSubjectAffects example_auth_graph2 NTFN = {Partition NTFN, Partition High}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_NTFN | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_High: "partsSubjectAffects example_auth_graph2 High = {Partition High, Partition NTFN}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_High | rename_tac xa, case_tac xa)+
  done

lemmas partsSubjectAffects2 =
   partsSubjectAffects_High partsSubjectAffects_Low partsSubjectAffects_NTFN
   partsSubjectAffects_SharedPage


definition example_policy2 where
  "example_policy2 \<equiv> {(PSched, d)|d. True} \<union>
                     {(d,e). d = e} \<union>
                     {(Partition Low, Partition NTFN), (Partition Low, Partition SharedPage),
                      (Partition Low, Partition High)} \<union>
                     {(Partition SharedPage,Partition High), (Partition SharedPage, Partition Low),
                      (Partition SharedPage,Partition NTFN)} \<union>
                     {(Partition NTFN, Partition High)} \<union>
                     {(Partition High, Partition NTFN)}"

lemma "policyFlows example_auth_graph2 = example_policy2"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(clarsimp simp: example_policy2_def)
   apply(erule policyFlows.cases)
    apply(case_tac l; auto simp: partsSubjectAffects2)
   apply assumption
  apply(rule subsetI)
  apply(clarsimp simp: example_policy2_def)
  apply(elim disjE)
           apply(fastforce simp: partsSubjectAffects2 intro: policy_affects)+
   apply(fastforce intro: policy_scheduler)
  apply(fastforce intro: policyFlows_refl refl_onD)
  done


end
