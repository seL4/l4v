(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory PolicyExample
imports Noninterference
begin

(* This first example shows how async and sync endpoints differ.
   Sync endpoints tend to spray information in all directions, while
   async ones are unidirectional.

   This example is a subset of the SAC example from access *)
datatype auth_graph_label = T | AEP1 | AEP2 | CTR | C | EP | RM

abbreviation partition_label where
  "partition_label x \<equiv> OrdinaryLabel x"

definition example_auth_graph :: "(auth_graph_label subject_label \<times> auth \<times> auth_graph_label subject_label) set" where
  "example_auth_graph \<equiv> 
   { (partition_label T,AsyncSend,partition_label AEP1),
     (partition_label CTR,Receive,partition_label AEP1),
     (partition_label C,Read,partition_label CTR),
     (partition_label C,Write,partition_label CTR),
     (partition_label CTR,Read,partition_label C),
     (partition_label CTR,Write,partition_label C),
     (partition_label CTR,SyncSend,partition_label EP),
     (partition_label T,AsyncSend,partition_label AEP2),
     (partition_label RM,Receive,partition_label AEP2),
     (partition_label RM,Receive,partition_label EP)
   } \<union> {(a,b,c). a = c}"

declare example_auth_graph_def [simp]

lemma subjectReads_T:
  "subjectReads example_auth_graph (partition_label T) = {partition_label T}"
  apply(auto simp: reads_lrefl elim: subjectReads.induct)
  done

lemma CTR_in_subjectReads_AEP1:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label AEP1)"
  apply(rule read_sync_ep_read_receivers[where ep="partition_label AEP1"], auto intro: reads_lrefl)
  done

lemma EP_in_subjectReads_AEP1:
  "partition_label EP \<in> subjectReads example_auth_graph (partition_label AEP1)"
  apply(rule reads_read_queued_thread_read_ep[where t="partition_label CTR" and a="partition_label EP"], auto intro: CTR_in_subjectReads_AEP1[simplified])
  done

lemma C_in_subjectReads_AEP1:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label AEP1)"
  apply(rule reads_read_thread_read_pages, auto intro: CTR_in_subjectReads_AEP1[simplified])
  done

lemma RM_in_subjectReads_AEP1:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label AEP1)"
  apply(rule read_sync_ep_read_receivers, auto intro: EP_in_subjectReads_AEP1[simplified])
  done

lemma AEP2_in_subjectReads_AEP1:
  "partition_label AEP2 \<in> subjectReads example_auth_graph (partition_label AEP1)"
  apply(rule reads_read_queued_thread_read_ep[where t="partition_label RM" and a="partition_label AEP2"], auto intro: RM_in_subjectReads_AEP1[simplified])
  done

lemmas subjectReads_AEP1' = reads_lrefl[of "partition_label AEP1"]
                            CTR_in_subjectReads_AEP1
                            EP_in_subjectReads_AEP1
                            RM_in_subjectReads_AEP1
                            C_in_subjectReads_AEP1
                            AEP2_in_subjectReads_AEP1

lemma subjectReads_AEP1:
  "subjectReads example_auth_graph (partition_label AEP1) = {partition_label AEP1, partition_label CTR, partition_label EP, partition_label C, partition_label RM, partition_label AEP2}"
  apply(rule equalityI)
   apply (rule subsetI)
   apply (erule subjectReads.induct)
           apply (fastforce simp: subjectReads_AEP1'[simplified])+
  done

lemma RM_in_subjectReads_AEP2:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label AEP2)"
  apply(rule read_sync_ep_read_receivers[where ep="partition_label AEP2"], auto intro: reads_lrefl)
  done

lemma EP_in_subjectReads_AEP2:
  "partition_label EP \<in> subjectReads example_auth_graph (partition_label AEP2)"
  apply(rule reads_read_queued_thread_read_ep[where t="partition_label RM" and a="partition_label EP"], auto intro: RM_in_subjectReads_AEP2[simplified])
  done

lemma CTR_in_subjectReads_AEP2:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label AEP2)"
  apply(rule read_sync_ep_read_senders[where ep="partition_label EP" and a="partition_label EP"], auto intro: EP_in_subjectReads_AEP2[simplified])
  done

lemma C_in_subjectReads_AEP2:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label AEP2)"
  apply(rule reads_read_thread_read_pages, auto intro: CTR_in_subjectReads_AEP2[simplified])
  done


lemma AEP1_in_subjectReads_AEP2:
  "partition_label AEP1 \<in> subjectReads example_auth_graph (partition_label AEP2)"
  apply(rule reads_read_queued_thread_read_ep[where t="partition_label CTR" and a="partition_label AEP1"], auto intro: CTR_in_subjectReads_AEP2[simplified])
  done

lemmas subjectReads_AEP2' = reads_lrefl[of "partition_label AEP2"]
                            CTR_in_subjectReads_AEP2
                            EP_in_subjectReads_AEP2
                            RM_in_subjectReads_AEP2
                            C_in_subjectReads_AEP2
                            AEP1_in_subjectReads_AEP2

lemma subjectReads_AEP2:
  "subjectReads example_auth_graph (partition_label AEP2) = {partition_label AEP2, partition_label AEP1, partition_label C, partition_label CTR, partition_label RM, partition_label EP}"
  apply(rule equalityI)
   apply (rule subsetI)
   apply (erule subjectReads.induct)
           apply (fastforce simp: subjectReads_AEP2'[simplified])+
  done


lemma EP_in_subjectReads_CTR:
  "partition_label EP \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule_tac a="partition_label CTR" and t="partition_label CTR" in reads_read_queued_thread_read_ep)
      apply (auto intro: reads_lrefl)
  done

lemma RM_in_subjectReads_CTR:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(clarsimp)
  apply(rule_tac ep="partition_label EP" and auth="SyncSend" in read_sync_ep_read_receivers)
     apply blast
    apply blast
   apply(rule EP_in_subjectReads_CTR[simplified])
  apply fastforce
  done

lemma C_in_subjectReads_CTR:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule reads_read, auto)
  done

lemma AEP1_in_subjectReads_CTR:
  "partition_label AEP1 \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule_tac t="partition_label CTR" and auth="Receive" and a="partition_label T" and auth'="AsyncSend" in reads_read_queued_thread_read_ep)
  apply (auto intro: reads_lrefl)
  done
  
lemma AEP2_in_subjectReads_CTR:
  "partition_label AEP2 \<in> subjectReads example_auth_graph (partition_label CTR)"
  apply(rule_tac t="partition_label RM" and auth="Receive" and a="partition_label T" and auth'="AsyncSend" in reads_read_queued_thread_read_ep)
  apply (auto intro: RM_in_subjectReads_CTR[simplified])
  done

lemmas subjectReads_CTR' = reads_lrefl[of "partition_label CTR"]
                           AEP2_in_subjectReads_CTR AEP1_in_subjectReads_CTR
                           C_in_subjectReads_CTR RM_in_subjectReads_CTR EP_in_subjectReads_CTR

lemma subjectReads_CTR:
  "subjectReads example_auth_graph (partition_label CTR) = {partition_label CTR,partition_label C,partition_label EP, partition_label RM, partition_label AEP1, partition_label AEP2}"
  apply(clarsimp)
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct)
           apply(auto)[9]
  apply(auto simp: subjectReads_CTR'[simplified])
  done

lemma AEP1_in_subjectReads_C:
  "partition_label AEP1 \<in> subjectReads example_auth_graph (partition_label C)"
  apply(rule_tac a="partition_label T" and ep="partition_label AEP1" and t="partition_label CTR" in reads_read_queued_thread_read_ep)
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
  apply(rule_tac a="partition_label CTR" in read_sync_ep_read_receivers[OF _ _ EP_in_subjectReads_C[simplified]])
    apply simp+
  done

lemma CTR_in_subjectReads_C:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label C)"
  apply(rule reads_read, auto)
  done

lemma AEP2_in_subjectReads_C:
  "partition_label AEP2 \<in> subjectReads example_auth_graph (partition_label C)"
  apply(rule_tac a="partition_label T" and ep="partition_label AEP2" and t="partition_label RM" in reads_read_queued_thread_read_ep)
  apply(fastforce simp: RM_in_subjectReads_C[simplified])+
  done

lemmas subjectReads_C' = reads_lrefl[of "partition_label C"]
                         AEP2_in_subjectReads_C AEP1_in_subjectReads_C
                         RM_in_subjectReads_C EP_in_subjectReads_C CTR_in_subjectReads_C


lemma subjectReads_C:
  "subjectReads example_auth_graph (partition_label C) = {partition_label C,partition_label CTR,partition_label AEP1, partition_label EP, partition_label RM, partition_label AEP2}"
  apply(clarsimp simp: example_auth_graph_def)
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct)
           apply(auto)[9]
  apply(auto simp: subjectReads_C'[simplified])
  done
  

lemma CTR_in_subjectReads_EP:
  "partition_label CTR \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(clarsimp)
  apply(rule_tac a="partition_label RM" and ep="partition_label EP" in read_sync_ep_read_senders)
     apply (simp add: reads_lrefl)+
  done

lemma AEP1_in_subjectReads_EP:
  "partition_label AEP1 \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule reads_read_queued_thread_read_ep[where a="partition_label AEP1", OF _ _ _ _ CTR_in_subjectReads_EP])
  apply(auto)
  done

lemma C_in_subjectReads_EP:
  "partition_label C \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule reads_read_thread_read_pages[OF CTR_in_subjectReads_EP])
  apply(auto)
  done

lemma RM_in_subjectReads_EP:
  "partition_label RM \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule read_sync_ep_read_receivers[OF _ _ reads_lrefl])
  apply(auto)
  done

lemma AEP2_in_subjectReads_EP:
  "partition_label AEP2 \<in> subjectReads example_auth_graph (partition_label EP)"
  apply(rule reads_read_queued_thread_read_ep[where a="partition_label AEP2", OF _ _ _ _ RM_in_subjectReads_EP])
  apply(auto)
  done

lemmas subjectReads_EP' = reads_lrefl[of "partition_label EP"]
                         CTR_in_subjectReads_EP
                         C_in_subjectReads_EP
                         RM_in_subjectReads_EP
                         AEP2_in_subjectReads_EP
                         AEP1_in_subjectReads_EP

lemma subjectReads_EP:
  "subjectReads example_auth_graph (partition_label EP) = {partition_label EP,partition_label CTR,partition_label AEP1, partition_label C, partition_label RM, partition_label AEP2}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct)
           apply(auto)[9]
  apply(auto simp: subjectReads_EP'[simplified])
  done

lemma AEP2_in_subjectReads_RM:
   "partition_label AEP2 \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_ep, auto)
  done

lemma EP_in_subjectReads_RM:
   "partition_label EP \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_ep, auto)
  done

lemma CTR_in_subjectReads_RM:
   "partition_label CTR \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule read_sync_ep_read_senders[where a="partition_label RM" and ep="partition_label EP", OF _ _ EP_in_subjectReads_RM], auto)
  done

lemma C_in_subjectReads_RM:
   "partition_label C \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_read_thread_read_pages[where t="partition_label CTR", OF CTR_in_subjectReads_RM], auto)
  done


lemma AEP1_in_subjectReads_RM:
   "partition_label AEP1 \<in> subjectReads example_auth_graph (partition_label RM)"
  apply(rule reads_read_queued_thread_read_ep[where a="partition_label T" and t="partition_label CTR", OF _ _ _ _ CTR_in_subjectReads_RM], auto)
  done

lemmas subjectReads_RM' = reads_lrefl[of "partition_label RM"]
                         CTR_in_subjectReads_RM
                         C_in_subjectReads_RM
                         EP_in_subjectReads_RM
                         AEP1_in_subjectReads_RM
                         AEP2_in_subjectReads_RM

lemma subjectReads_RM:
  "subjectReads example_auth_graph (partition_label RM) = {partition_label RM, partition_label AEP2,partition_label EP,partition_label CTR, partition_label C, partition_label AEP1}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct)
           apply(auto)[9]
  apply(auto simp: subjectReads_RM'[simplified])
  done


lemma AEP1_in_subjectAffects_T:
  "partition_label AEP1 \<in> subjectAffects example_auth_graph (partition_label T)
" apply(auto intro: affects_ep)
  done

lemma AEP2_in_subjectAffects_T:
  "partition_label AEP2 \<in> subjectAffects example_auth_graph (partition_label T)
" apply(auto intro: affects_ep)
  done

lemma C_in_subjectAffects_T:
  "partition_label C \<in> subjectAffects example_auth_graph (partition_label T)
" apply(rule affects_send[where auth="AsyncSend" and ep="partition_label AEP1"], auto)
  done

lemma CTR_in_subjectAffects_T:
  "partition_label CTR \<in> subjectAffects example_auth_graph (partition_label T)
" apply(rule affects_send[where auth="AsyncSend" and ep="partition_label AEP1"], auto)
  done

lemma RM_in_subjectAffects_T:
  "partition_label RM \<in> subjectAffects example_auth_graph (partition_label T)
" apply(rule affects_send[where auth="AsyncSend" and ep="partition_label AEP2"], auto)
  done

lemmas subjectAffects_T' = affects_lrefl[of "partition_label T"]
                           AEP1_in_subjectAffects_T
                           AEP2_in_subjectAffects_T
                           C_in_subjectAffects_T
                           CTR_in_subjectAffects_T
                           RM_in_subjectAffects_T
 


lemma subjectAffects_T:
  "subjectAffects example_auth_graph (partition_label T) = {partition_label AEP1,partition_label AEP2,partition_label T,partition_label C, partition_label CTR, partition_label RM}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases)
           apply(fastforce+)[7]
  apply(auto simp: subjectAffects_T'[simplified])
  done

lemma CTR_in_subjectAffects_AEP1:
  "partition_label CTR \<in> subjectAffects example_auth_graph (partition_label AEP1)"
  apply(rule affects_send[where ep="partition_label AEP1"], auto)
  done

lemma C_in_subjectAffects_AEP1:
  "partition_label C \<in> subjectAffects example_auth_graph (partition_label AEP1)"
  apply(rule affects_send[where ep="partition_label AEP1"], auto)
  done

lemmas subjectAffects_AEP1' = affects_lrefl[of "partition_label AEP1"]
                           C_in_subjectAffects_AEP1
                           CTR_in_subjectAffects_AEP1


lemma subjectAffects_AEP1:
  "subjectAffects example_auth_graph (partition_label AEP1) = {partition_label AEP1,partition_label CTR,partition_label C}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases)
           apply(auto)[7]
  apply(auto simp: subjectAffects_AEP1'[simplified])
  done

lemma RM_in_subjectAffects_AEP2:
  "partition_label RM \<in> subjectAffects example_auth_graph (partition_label AEP2)"
  apply(rule affects_send[where ep="partition_label AEP2"], auto)
  done


lemmas subjectAffects_AEP2' = affects_lrefl[of "partition_label AEP2"]
                           RM_in_subjectAffects_AEP2


lemma subjectAffects_AEP2:
  "subjectAffects example_auth_graph (partition_label AEP2) = {partition_label AEP2,partition_label RM}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases)
           apply(auto)[7]
  apply(auto simp: subjectAffects_AEP2'[simplified])
  done

lemma C_in_subjectAffects_CTR:
  "partition_label C \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_write[where auth="Write"], auto)
  done

lemma EP_in_subjectAffects_CTR:
  "partition_label EP \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_ep, auto)
  done
  
lemma AEP1_in_subjectAffects_CTR:
  "partition_label AEP1 \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_ep, auto)
  done

lemma RM_in_subjectAffects_CTR:
  "partition_label RM \<in> subjectAffects example_auth_graph (partition_label CTR)"
  apply(rule affects_send, auto)
  done

lemmas subjectAffects_CTR' = affects_lrefl[of "partition_label CTR"]
                           AEP1_in_subjectAffects_CTR
                           C_in_subjectAffects_CTR
                           EP_in_subjectAffects_CTR
                           RM_in_subjectAffects_CTR

lemma subjectAffects_CTR:
  "subjectAffects example_auth_graph (partition_label CTR) = {partition_label CTR,partition_label C,partition_label EP,partition_label AEP1, partition_label RM}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases)
           apply(fastforce+)[7]
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
   apply(erule subjectAffects.cases)
           apply(auto)[7]
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

lemmas subjectAffects_EP' = affects_lrefl[of "partition_label EP"]
                           CTR_in_subjectAffects_EP
                           C_in_subjectAffects_EP
                           RM_in_subjectAffects_EP


lemma subjectAffects_EP:
  "subjectAffects example_auth_graph (partition_label EP) = {partition_label EP, partition_label RM, partition_label CTR, partition_label C}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases)
           apply(fastforce+)[7]
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

lemma AEP2_in_subjectAffects_RM:
  "partition_label AEP2 \<in> subjectAffects example_auth_graph (partition_label RM)"
  apply(rule affects_ep, auto)
  done

lemmas subjectAffects_RM' = affects_lrefl[of "partition_label RM"]
                            EP_in_subjectAffects_RM
                            AEP2_in_subjectAffects_RM
                            CTR_in_subjectAffects_RM


lemma subjectAffects_RM:
  "subjectAffects example_auth_graph (partition_label RM) = {partition_label RM,partition_label EP,partition_label CTR,partition_label AEP2}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.cases)
           apply(auto)[7]
  apply(auto simp: subjectAffects_RM'[simplified])
  done

lemmas subjectReads = subjectReads_T subjectReads_AEP1 subjectReads_AEP2 subjectReads_CTR
                      subjectReads_EP subjectReads_RM subjectReads_C

declare example_auth_graph_def [simp del]

lemma partsSubjectAffects_T:
  "partsSubjectAffects example_auth_graph T = {Partition T,Partition AEP1, Partition AEP2, Partition CTR, Partition C, Partition EP, Partition RM}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_T | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_AEP1:
  "partsSubjectAffects example_auth_graph AEP1 = {Partition AEP1, Partition CTR, Partition C, Partition EP, Partition RM, Partition AEP2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_AEP1 | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_AEP2:
  "partsSubjectAffects example_auth_graph AEP2 = {Partition AEP2, Partition CTR, Partition C, Partition EP, Partition RM, Partition AEP1}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_AEP2 | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_CTR:
  "partsSubjectAffects example_auth_graph CTR = {Partition AEP1, Partition CTR, Partition C, Partition EP, Partition RM, Partition AEP2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_CTR | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_C:
  "partsSubjectAffects example_auth_graph C = {Partition CTR, Partition C, Partition EP, Partition RM, Partition AEP1, Partition AEP2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_C | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_EP:
  "partsSubjectAffects example_auth_graph EP = {Partition CTR, Partition C, Partition EP, Partition RM, Partition AEP1, Partition AEP2}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_EP | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_RM:
  "partsSubjectAffects example_auth_graph RM = {Partition CTR, Partition C, Partition EP, Partition RM, Partition AEP2, Partition AEP1}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_RM | rename_tac xa, case_tac xa)+
  done

lemmas partsSubjectAffects = partsSubjectAffects_T partsSubjectAffects_AEP1 
                            partsSubjectAffects_AEP2 partsSubjectAffects_CTR 
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
   apply(case_tac l, (auto simp: partsSubjectAffects | case_tac k)+)[1]
  apply(rule subsetI)
  apply(clarsimp simp: example_policy_def)
  apply(erule policyFlows.cases)
   apply(case_tac l, auto simp: partsSubjectAffects)
  done


(* This second example is a classic 'one way information flow'
   example, where information is allowed to flow from Low to High,
   but not the reverse. We consider a typical scenario where
   shared memory and an async endpoint for notifications are used to
   implement a ring-buffer. *)
datatype auth_graph_label2 = High | Low | SharedPage | AEP

definition example_auth_graph2 :: "(auth_graph_label2 subject_label \<times> auth \<times> auth_graph_label2 subject_label) set" where
  "example_auth_graph2 \<equiv> 
   { (partition_label Low,Write,partition_label SharedPage),
     (partition_label Low,Read,partition_label SharedPage),
     (partition_label High,Read,partition_label SharedPage),
     (partition_label Low,AsyncSend,partition_label AEP),
     (partition_label High,Receive,partition_label AEP)
   } \<union> {(x,a,y). x = y}"

declare example_auth_graph2_def [simp]

lemma subjectReads_Low: "subjectReads example_auth_graph2 (partition_label Low) = {partition_label Low,partition_label SharedPage}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply (auto intro: reads_lrefl reads_read)
  done

lemma subjectReads_SharedPage: "subjectReads example_auth_graph2 (partition_label SharedPage) = {partition_label Low,partition_label SharedPage}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply (auto intro: reads_lrefl reads_read_page_read_thread)
  done

lemma High_in_subjectReads_AEP:
  "partition_label High \<in> subjectReads example_auth_graph2 (partition_label AEP)"
  apply(rule read_sync_ep_read_receivers)
  apply(auto intro: reads_lrefl)
  done

lemma SharedPage_in_subjectReads_AEP:
  "partition_label SharedPage \<in> subjectReads example_auth_graph2 (partition_label AEP)"
  apply(rule reads_read_thread_read_pages[OF High_in_subjectReads_AEP])
  apply(auto)
  done

lemma Low_in_subjectReads_AEP:
  "partition_label Low \<in> subjectReads example_auth_graph2 (partition_label AEP)"
  apply(rule reads_read_page_read_thread[OF SharedPage_in_subjectReads_AEP])
  apply(auto)
  done

lemma subjectReads_AEP: "subjectReads example_auth_graph2 (partition_label AEP) = {partition_label AEP,partition_label High,partition_label SharedPage, partition_label Low}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply (auto intro: High_in_subjectReads_AEP Low_in_subjectReads_AEP SharedPage_in_subjectReads_AEP simp del: example_auth_graph2_def intro: reads_lrefl)
  done

lemma AEP_in_subjectReads_High:
  "partition_label AEP \<in> subjectReads example_auth_graph2 (partition_label High)"
  apply(fastforce intro: reads_ep)
  done

lemma SharedPage_in_subjectReads_High:
  "partition_label SharedPage \<in> subjectReads example_auth_graph2 (partition_label High)"
  apply(fastforce intro: reads_read_thread_read_pages reads_lrefl)
  done

lemma Low_in_subjectReads_High:
  "partition_label Low \<in> subjectReads example_auth_graph2 (partition_label High)"
  apply(fastforce intro: reads_read_page_read_thread[OF SharedPage_in_subjectReads_High])
  done

lemma subjectReads_High: "subjectReads example_auth_graph2 (partition_label High) = {partition_label High,partition_label AEP, partition_label SharedPage,partition_label Low}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, fastforce+)
  apply(auto intro: reads_lrefl AEP_in_subjectReads_High SharedPage_in_subjectReads_High Low_in_subjectReads_High simp del: example_auth_graph2_def)
  done

lemma SharedPage_in_subjectAffects_Low:
  "partition_label SharedPage \<in> subjectAffects example_auth_graph2 (partition_label Low)"
  apply(fastforce intro: affects_write)
  done

lemma AEP_in_subjectAffects_Low:
  "partition_label AEP \<in> subjectAffects example_auth_graph2 (partition_label Low)"
  apply(fastforce intro: affects_ep)
  done

lemma High_in_subjectAffects_Low:
  "partition_label High \<in> subjectAffects example_auth_graph2 (partition_label Low)"
  apply(rule affects_send[where ep="partition_label AEP"])
  apply(auto)
  done

lemma subjectAffects_Low: "subjectAffects example_auth_graph2 (partition_label Low) = {partition_label Low,partition_label AEP,partition_label SharedPage, partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl SharedPage_in_subjectAffects_Low AEP_in_subjectAffects_Low High_in_subjectAffects_Low simp del: example_auth_graph2_def)
  done

lemma subjectAffects_SharedPage: "subjectAffects example_auth_graph2 (partition_label SharedPage) = {partition_label SharedPage}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl)
  done

lemma High_in_subjectAffects_AEP:
  "partition_label High \<in> subjectAffects example_auth_graph2 (partition_label AEP)"
  apply(rule affects_send[where ep="partition_label AEP"])
  apply auto
  done
  
lemma subjectAffects_AEP: "subjectAffects example_auth_graph2 (partition_label AEP) = {partition_label AEP,partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl High_in_subjectAffects_AEP simp del: example_auth_graph2_def)
  done

lemma AEP_in_subjectAffects_High:
  "partition_label AEP \<in> subjectAffects example_auth_graph2 (partition_label High)"
  apply(fastforce intro: affects_ep)
  done

lemma subjectAffects_High: "subjectAffects example_auth_graph2 (partition_label High) = {partition_label AEP,partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, fastforce+)
  apply(auto intro: affects_lrefl AEP_in_subjectAffects_High simp del: example_auth_graph2_def)
  done



lemmas subjectReads_2 = subjectReads_High subjectReads_Low subjectReads_AEP subjectReads_SharedPage

declare example_auth_graph2_def [simp del]



lemma partsSubjectAffects_Low: "partsSubjectAffects example_auth_graph2 Low = {Partition Low, Partition High, Partition SharedPage, Partition AEP}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_Low | case_tac xa, rename_tac xa)+
  done

lemma partsSubjectAffects_SharedPage: "partsSubjectAffects example_auth_graph2 SharedPage = {Partition SharedPage, Partition High, Partition Low, Partition AEP}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_SharedPage | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_AEP: "partsSubjectAffects example_auth_graph2 AEP = {Partition AEP, Partition High}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_AEP | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_High: "partsSubjectAffects example_auth_graph2 High = {Partition High, Partition AEP}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads_2 subjectAffects_High | rename_tac xa, case_tac xa)+
  done

lemmas partsSubjectAffects2 =
   partsSubjectAffects_High partsSubjectAffects_Low partsSubjectAffects_AEP    
   partsSubjectAffects_SharedPage


definition example_policy2 where
  "example_policy2 \<equiv> {(PSched, d)|d. True} \<union> 
                     {(d,e). d = e} \<union> 
                     {(Partition Low, Partition AEP), (Partition Low, Partition SharedPage), 
                      (Partition Low, Partition High)} \<union> 
                     {(Partition SharedPage,Partition High), (Partition SharedPage, Partition Low),
                      (Partition SharedPage,Partition AEP)} \<union>
                     {(Partition AEP, Partition High)} \<union>
                     {(Partition High, Partition AEP)}"

lemma "policyFlows example_auth_graph2 = example_policy2"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(clarsimp simp: example_policy2_def)
   apply(erule policyFlows.cases)
    apply(case_tac l, auto simp: partsSubjectAffects2)[1]
   apply assumption
  apply(rule subsetI)
  apply(clarsimp simp: example_policy2_def)
  apply(elim disjE)
           apply(fastforce simp: partsSubjectAffects2 intro: policy_affects)+
   apply(fastforce intro: policy_scheduler)
  apply(fastforce intro: policyFlows_refl refl_onD)
  done

 
end
