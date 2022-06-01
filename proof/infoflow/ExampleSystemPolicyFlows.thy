(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ExampleSystemPolicyFlows
imports
  ArchNoninterference
  "Access.ExampleSystem"
begin

subsection \<open>Example 1 -- similar to Sys1 in ../access-control/ExampleSystem.thy\<close>

subsubsection \<open>Definitions\<close>

datatype Sys3Labels = UT3 | T3 | EP3 | IRQ3

definition Sys3AuthGraph_aux :: "Sys3Labels subject_label auth_graph"
where
  "Sys3AuthGraph_aux \<equiv>
   { (OrdinaryLabel (UT3), auth.SyncSend, OrdinaryLabel (EP3)),
     (OrdinaryLabel (UT3), auth.Reset, OrdinaryLabel (EP3)),
     (OrdinaryLabel (T3), auth.Receive, OrdinaryLabel (EP3)),
     (OrdinaryLabel (T3), auth.Reset, OrdinaryLabel (EP3)) }"

definition Sys3AuthGraph :: "Sys3Labels subject_label auth_graph"
where
  "Sys3AuthGraph \<equiv> complete_AuthGraph Sys3AuthGraph_aux {OrdinaryLabel (T3),
                                                         OrdinaryLabel (UT3)}"

definition Sys3PolicyFlows :: "(Sys3Labels partition \<times> Sys3Labels partition) set"
where
  "Sys3PolicyFlows \<equiv>
   { (Partition UT3, Partition UT3),
     (Partition UT3, Partition EP3),
     (Partition UT3, Partition T3),
     (Partition T3, Partition T3),
     (Partition T3, Partition UT3),
     (Partition T3, Partition EP3),
     (Partition EP3, Partition UT3),
     (Partition EP3, Partition EP3),
     (Partition EP3, Partition T3),
     (Partition IRQ3, Partition IRQ3),
     (PSched, Partition EP3),
     (PSched, Partition UT3),
     (PSched, Partition T3),
     (PSched, Partition IRQ3),
     (PSched, PSched) }"

subsubsection \<open>Generalisations\<close>

definition Sys3Reads where
  "Sys3Reads \<equiv> { (OrdinaryLabel (UT3)), (OrdinaryLabel (EP3)), (OrdinaryLabel (T3)) }"

definition Sys3Affects where
  "Sys3Affects \<equiv> { (OrdinaryLabel (UT3)), (OrdinaryLabel (EP3)), (OrdinaryLabel (T3)) }"

lemma Sys3Reads_correct_fw : "\<lbrakk>x \<in> subjectReads Sys3AuthGraph (OrdinaryLabel (l)); l \<in> {T3, UT3, EP3}\<rbrakk> \<Longrightarrow> x \<in> Sys3Reads"
  apply (induct x rule:subjectReads.induct)
         apply (auto simp:Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3Reads_def)
  done

lemma Sys3Affects_correct_fw : "\<lbrakk>x \<in> subjectAffects Sys3AuthGraph (OrdinaryLabel (l)); l \<in> {T3, UT3}\<rbrakk> \<Longrightarrow> x \<in> Sys3Affects"
  apply (induct x rule:subjectAffects.induct)
        apply (auto simp:Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3Affects_def)
  done

subsubsection \<open>UT3\<close>

lemma Sys3UT3Reads_correct_bw : "x \<in> Sys3Reads \<Longrightarrow> x \<in> subjectReads Sys3AuthGraph (OrdinaryLabel (UT3))"
  apply (simp add: Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3Reads_def)
  apply (erule disjE)
   (* UT3 reads UT3 *)
   apply simp
  (* UT3 reads EP3 *)
  apply (erule disjE)
   apply (rule_tac auth = SyncSend in reads_ep)
    apply (simp)
   apply (simp add:insertI1)
  (* UT3 reads T3 *)
  apply (rule_tac ep = "OrdinaryLabel (EP3)" in read_sync_ep_read_receivers)
   apply (rule_tac auth = SyncSend in reads_ep)
    apply (simp)
   apply (rule insertI1)
  apply (simp add: insertI1)
  done

lemma Sys3UT3Affects_correct_bw : "x \<in> Sys3Affects \<Longrightarrow> x \<in> subjectAffects Sys3AuthGraph (OrdinaryLabel (UT3))"
  apply (simp add:Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3Affects_def)
  apply (erule disjE)
   (* UT3 affects UT3 *)
   apply (simp add:affects_lrefl)
  (* UT3 affects EP3 *)
  apply (erule disjE)
   apply (rule_tac auth=SyncSend in affects_ep)
    apply simp
   apply (simp add:insertI1)
  (* UT3 affects T3 *)
  apply (rule_tac auth=SyncSend and l' = "OrdinaryLabel (T3)" and ep="OrdinaryLabel (EP3)" in affects_send)
     apply (simp_all add:insertI1)
  done

subsubsection \<open>T3\<close>

lemma Sys3T3Reads_correct_bw : "x \<in> Sys3Reads \<Longrightarrow> x \<in> subjectReads Sys3AuthGraph (OrdinaryLabel (T3))"
  apply (simp add: Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3Reads_def)
  apply (erule disjE)
   (* T3 reads UT3 *)
   apply (rule_tac ep = "OrdinaryLabel (EP3)" in read_sync_ep_read_senders)
    apply (rule_tac auth = Receive in reads_ep)
     apply (simp)
    apply (simp add:insertI1)
   apply (simp add: insertI1)
  (* T3 reads EP3 *)
  apply (erule disjE)
   apply (rule_tac auth = Receive in reads_ep)
    apply (simp)
   apply (simp add:insertI1)
  (* T3 reads T3 *)
  apply simp
  done

lemma Sys3T3Affects_correct_bw : "x \<in> Sys3Affects \<Longrightarrow> x \<in> subjectAffects Sys3AuthGraph (OrdinaryLabel (T3))"
  apply (simp add:Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3Affects_def)
  apply (erule disjE)
   (* T3 affects UT3 *)
   apply simp
   apply (rule_tac l = "OrdinaryLabel (T3)" and l' = "OrdinaryLabel (UT3)" and ep="OrdinaryLabel (EP3)" in affects_recv)
    apply (simp_all add:insertI1)
  (* T3 affects EP3 *)
  apply (erule disjE)
   apply (rule_tac auth=Receive in affects_ep)
    apply simp
   apply (simp add:insertI1)
  (* T3 affects T3 *)
  apply (simp add:affects_lrefl)
  done

subsubsection \<open>EP3\<close>

definition Sys3EP3Affects :: "(Sys3Labels subject_label) set"
where
  "Sys3EP3Affects \<equiv> { OrdinaryLabel (EP3) }"

lemma Sys3EP3Reads_correct_bw : "x \<in> Sys3Reads \<Longrightarrow> x \<in> subjectReads Sys3AuthGraph (OrdinaryLabel (EP3))"
  apply (simp add: Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3Reads_def)
  apply (erule disjE)
   (* EP3 reads UT3 *)
   apply simp
   apply (rule_tac ep = "OrdinaryLabel (EP3)" and b = "OrdinaryLabel (UT3)" in read_sync_ep_read_senders)
    apply (simp)
   apply (simp add:insertI1)
  (* EP3 reads EP3 *)
  apply (erule disjE)
   apply simp
  (* EP3 reads T3 *)
  apply (rule_tac ep = "OrdinaryLabel (EP3)" in read_sync_ep_read_receivers)
   apply simp_all
  done

lemma Sys3EP3Affects_correct_fw : "x \<in> subjectAffects Sys3AuthGraph (OrdinaryLabel (EP3)) \<Longrightarrow> x \<in> Sys3EP3Affects"
  apply (induct x rule:subjectAffects.induct)
        apply (auto simp:Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3EP3Affects_def)
  done

lemma Sys3EP3Affects_correct_bw : "x \<in> Sys3EP3Affects \<Longrightarrow> x \<in> subjectAffects Sys3AuthGraph (OrdinaryLabel (EP3))"
  by (simp add:Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def Sys3EP3Affects_def affects_lrefl)

lemma Sys3EP3Affects_correct : "subjectAffects Sys3AuthGraph (OrdinaryLabel (EP3)) = Sys3EP3Affects"
  apply (rule subset_antisym)
   apply (simp_all add:subsetI Sys3EP3Affects_correct_fw Sys3EP3Affects_correct_bw)
  done

subsubsection \<open>Generalisations pt2\<close>

lemma Sys3Reads_correct : "l \<in> {T3, UT3, EP3} \<Longrightarrow> subjectReads Sys3AuthGraph (OrdinaryLabel (l)) = Sys3Reads"
  by (auto simp:subsetI Sys3Reads_correct_fw Sys3UT3Reads_correct_bw Sys3T3Reads_correct_bw Sys3EP3Reads_correct_bw)

lemma Sys3Affects_correct : "l \<in> {T3, UT3} \<Longrightarrow> subjectAffects Sys3AuthGraph (OrdinaryLabel (l)) = Sys3Affects"
  by (auto simp:subsetI Sys3Affects_correct_fw Sys3UT3Affects_correct_bw Sys3T3Affects_correct_bw)

subsubsection \<open>IRQ3\<close>

lemma IRQ3Reads : " d \<in> subjectReads Sys3AuthGraph (OrdinaryLabel (IRQ3)) \<Longrightarrow> d = OrdinaryLabel (IRQ3)"
  apply (simp add: Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def)
  apply (induct d rule: subjectReads.induct, auto)
  done

lemma IRQ3Affects : "d \<in> subjectAffects Sys3AuthGraph (OrdinaryLabel (IRQ3)) \<Longrightarrow> d = OrdinaryLabel (IRQ3)"
  apply (simp add: Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def)
  apply (induct d rule: subjectAffects.induct, auto)
  done

lemma IRQ3ReadsAndAffects :
  "\<lbrakk> d \<in> subjectAffects Sys3AuthGraph (OrdinaryLabel (l))
   ; d \<in> subjectReads Sys3AuthGraph (OrdinaryLabel (IRQ3))
   \<rbrakk> \<Longrightarrow> l = IRQ3"
  apply (drule IRQ3Reads)
  apply (simp add: Sys3AuthGraph_def Sys3AuthGraph_aux_def complete_AuthGraph_def)
  apply (erule subjectAffects.cases, auto)
  done

subsubsection \<open>Policy flows\<close>

lemma Sys3_policyFlows_correct_fw : "(a,b) \<in> policyFlows Sys3AuthGraph \<Longrightarrow> (a,b) \<in> Sys3PolicyFlows"
  apply (induct a b rule:policyFlows.induct)
   apply (simp add:partsSubjectAffects_def label_can_affect_partition_def)
   (* Partition l *)
   apply (erule imageE)
   apply simp
   apply (case_tac "x \<in> {T3, UT3, EP3}")
    (* x in {T3, UT3, EP3} *)
    apply (simp add:Sys3Reads_correct Sys3Reads_def)
    apply (case_tac "l \<in> {T3, UT3}")
     (* l in {T3, UT3} *)
     apply (simp add:Sys3Affects_correct Sys3Affects_def Sys3PolicyFlows_def)
     apply (erule exE)
     apply ((erule disjE)+, simp, simp, simp)+
    (* l not in {T3, UT3} *)
    apply (simp)
    apply (case_tac l)
    apply (simp, simp, simp)
       apply (auto simp:Sys3PolicyFlows_def)[1]
     apply (simp add:Sys3PolicyFlows_def)
    apply (erule exE)
    apply (erule conjE, drule IRQ3Affects)
    apply (blast)
    (* x not in {T3, UT3, EP3} *)
    apply (case_tac x)
    apply (simp, simp, simp, simp)
   apply (erule exE)
   apply (erule conjE)
      apply (frule IRQ3ReadsAndAffects, assumption)
   apply (simp add: Sys3PolicyFlows_def)
   (* PSched *)
   apply (case_tac d, simp add: Sys3PolicyFlows_def)
  apply (rename_tac a)
  apply (case_tac a)
  apply (auto simp: Sys3PolicyFlows_def)
  done

lemma Sys3_policyFlows_correct_bw : "(a,b) \<in> Sys3PolicyFlows \<Longrightarrow> (a,b) \<in> policyFlows Sys3AuthGraph"
  apply (simp add:Sys3PolicyFlows_def)
  (* All UT3/T3 cases *)
  apply (erule disjE, simp, rule policy_affects, simp add: partsSubjectAffects_def label_can_affect_partition_def, rule imageI, simp add: Sys3Affects_correct Sys3Reads_correct Sys3Affects_def Sys3Reads_def, blast)+
  (* All EP3 cases *)
  apply (erule disjE,simp, rule policy_affects, simp add: partsSubjectAffects_def label_can_affect_partition_def, rule imageI, simp add: Sys3EP3Affects_correct Sys3Reads_correct Sys3Reads_def Sys3EP3Affects_def)+
   (* IRQ3 case *)
   apply (rule_tac x = "OrdinaryLabel (IRQ3)" in exI)
   apply (rule conjI)
   apply (rule affects_lrefl)
  apply (rule reads_lrefl)
  (* All PSched cases *)
  apply (erule disjE, simp add: PSched_flows_to_all)+
  apply (simp add: PSched_flows_to_all)
  done

lemma Sys3_policyFlows_correct : "policyFlows Sys3AuthGraph = Sys3PolicyFlows"
  by (auto simp:Sys3_policyFlows_correct_fw Sys3_policyFlows_correct_bw)

end
