(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory PolicySystemSAC
imports
  ArchNoninterference
  "Access.ExampleSystem"
begin

text \<open>
  Reads/Affects sets:
  - NicA, NicB, NicD: reads all except T
       affects {RM, R, NicA, NicB, NicD}
  - NicC: reads all except T, affects self only
  - R:  reads all except T
        affects {NicA, NicB, NicD, R, RM, NTFN3}
  - RM: reads all except T
        affects {SC, EP, RM, R, NicA, NicB, NicD, NTFN2}
  - SC: reads all except T
        affects {EP, SC, NicC, RM, R, NicA, NicB, NicD, NTFN1}
  - EP: reads all except T
        affects {EP, SC, NicC, RM, R, NicA, NicB, NicD}
  - NTFN1: reads all except T, affects {NTFN1, SC, NicC}
  - NTFN2: ''                , affects {NTFN2, RM, R, NicA, NicB, NicD}
  - NTFN3: ''                , affects {NTFN3, R, NicB, NicD}
  - T: reads T, affects all except EP
\<close>

subsection \<open>Definitions\<close>

datatype SACLabels =
    NicA | NicB | NicC | NicD
  | R | RM |  SC | EP
  | T | NTFN1 | NTFN2 | NTFN3

definition complete_AgentAuthGraph where
  "complete_AgentAuthGraph g \<equiv>
     g \<union> {(y,a,y) | a y. True}
       \<union> {(x,a,y) | x a y. (x,Control,y) \<in> g }
       \<union> {(x,a,y)|x a y. \<exists>z. (x,Control,z) \<in> g \<and> (z, Control,y) \<in> g} "
declare complete_AgentAuthGraph_def [simp]

abbreviation partition_label where
  "partition_label l \<equiv> OrdinaryLabel l"

definition SACGraph where
  "SACGraph \<equiv>
  { (partition_label R, Read,  partition_label NicB), (partition_label R, Write, partition_label NicB),
    (partition_label R, Read,  partition_label NicD), (partition_label R, Write, partition_label NicD),
    (partition_label SC, Read,  partition_label NicC), (partition_label SC, Write, partition_label NicC),
    (partition_label SC, SyncSend, partition_label EP),
    (partition_label RM, Receive, partition_label EP),
    (partition_label RM, Control, partition_label R),
    (partition_label RM, Control, partition_label NicA),
    (partition_label RM, Control, partition_label NicB),
    (partition_label RM, Control, partition_label NicD),
    (partition_label T, Notify, partition_label NTFN1),
    (partition_label T, Notify, partition_label NTFN2),
    (partition_label T, Notify, partition_label NTFN3),
    (partition_label SC, Receive, partition_label NTFN1),
    (partition_label RM, Receive, partition_label NTFN2),
    (partition_label R, Receive, partition_label NTFN3)
  }"
declare SACGraph_def [simp]

definition SACAuthGraph  where
  "SACAuthGraph = complete_AgentAuthGraph SACGraph"
declare SACAuthGraph_def [simp]

definition SACAllLabels where
  "SACAllLabels \<equiv> {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC}"

definition RMControls where
  "RMControls = {partition_label RM, partition_label R, partition_label NicA, partition_label NicB, partition_label NicD}"
declare RMControls_def [simp]

lemma reads_all_rm_controlled_subjects : "\<lbrakk>partition_label RM \<in> subjectReads SACAuthGraph (partition_label x); l \<in> RMControls\<rbrakk> \<Longrightarrow> l \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (simp only:RMControls_def)
  apply (erule insertE, rule_tac t="partition_label RM" in reads_read_thread_read_pages, simp, simp)+
  apply simp
done

lemma reads_ntfn3_via_r : "partition_label R \<in> subjectReads SACAuthGraph (partition_label x) \<Longrightarrow> partition_label NTFN3 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label NTFN3" and t="partition_label R" and auth="Receive" and auth'="Notify" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply simp_all
done

lemma reads_ntfn2_via_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label x) \<Longrightarrow> partition_label NTFN2 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label NTFN2" and t="partition_label RM" and auth="Receive" and auth'="Notify" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply simp_all
done

lemma reads_ntfn1_via_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label x) \<Longrightarrow> partition_label NTFN1 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label NTFN1" and t="partition_label SC" and auth="Receive" and auth'="Notify" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply simp_all
done

subsection \<open>NicA, NicB, NicD reads/affects\<close>

lemma reads_Control_rev':
  "(x,Control,y) \<in> aag \<Longrightarrow>
    x \<in> subjectReads (complete_AgentAuthGraph aag) y"
  apply(rule reads_read_page_read_thread)
   apply(rule reads_lrefl)
  apply simp
  done

lemma reads_Control_rev:
  "(x,Control,y) \<in> SACGraph \<Longrightarrow>
   x \<in> subjectReads SACAuthGraph y"
  apply(subst SACAuthGraph_def)
  apply(erule reads_Control_rev')
  done


lemma abdrm_reads_ep : "x \<in> {NicA, NicB, NicD, RM} \<Longrightarrow> partition_label EP \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac t = "partition_label RM" and a = "partition_label SC" and auth' = "SyncSend" and auth = "Receive" in reads_read_queued_thread_read_ep)
      apply (simp+)[4]
  apply safe
     apply(fastforce intro: reads_Control_rev simp del: complete_AgentAuthGraph_def)
    apply(fastforce intro: reads_Control_rev simp del: complete_AgentAuthGraph_def)
   apply(fastforce intro: reads_Control_rev simp del: complete_AgentAuthGraph_def)
  done

lemma abdrm_reads_sc : "x \<in> {NicA, NicB, NicD, RM} \<Longrightarrow> partition_label SC \<in> subjectReads SACAuthGraph (partition_label x)"
    apply (rule_tac b = "partition_label SC" and ep = "partition_label EP" in read_sync_ep_read_senders)
      apply (simp del: SACAuthGraph_def add: abdrm_reads_ep, simp)
done

lemma abd_reads_rm : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> partition_label RM \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule reads_Control_rev)
  apply auto
done

lemma abd_reads_c : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> partition_label NicC \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac t = "partition_label SC" in reads_read_thread_read_pages)
  apply (rule abdrm_reads_sc, simp, blast, simp)
done

lemma abd_reads_r : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> partition_label R \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac p="partition_label R" and t="partition_label RM" in reads_read_thread_read_pages)
  apply (rule abd_reads_rm, simp, simp)
done

lemma abd_reads_ntfn3 : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> partition_label NTFN3 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label NTFN3" and t="partition_label R" and auth="Receive" and auth'="Notify" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply (simp_all add: abd_reads_r del:SACAuthGraph_def, simp_all)
done

lemma abd_reads_all_bw : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3} \<subseteq> subjectReads SACAuthGraph (partition_label x)"
  apply (rule subsetI)
  (* refl cases *)
  apply (case_tac "partition_label x = xa")
  apply simp
  (* non refl cases *)
  apply (case_tac "xa \<in> RMControls")
    apply (rule reads_all_rm_controlled_subjects, rule abd_reads_rm, simp, simp)
  apply (erule_tac a = xa in insertE, simp)
  apply (erule_tac a = xa in insertE, simp only:, rule abd_reads_rm, simp)
  apply (erule_tac a = xa in insertE, simp)
  apply (erule_tac a = xa in insertE, simp)
  apply (erule_tac a = xa in insertE, simp)
  apply (erule_tac a = xa in insertE, simp only:, rule abdrm_reads_ep, simp, blast)
  apply (erule_tac a = xa in insertE, simp only:, rule abdrm_reads_sc, simp, blast)
  apply (erule_tac a = xa in insertE, simp only:, rule abd_reads_c, simp)
  apply (erule_tac a = xa in insertE, simp only:, rule reads_ntfn1_via_sc, rule abdrm_reads_sc, simp, blast)
  apply (erule_tac a = xa in insertE, simp only:, rule reads_ntfn2_via_rm, rule abd_reads_rm, simp)
  apply (erule_tac a = xa in insertE, simp only:, rule reads_ntfn3_via_r, rule abd_reads_r, simp)
  apply simp
done

lemma abd_reads : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> subjectReads SACAuthGraph (partition_label x) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3}"
   apply (rule subset_antisym)
   defer
   apply (rule abd_reads_all_bw)
   apply (simp)
   apply (rule subsetI)
     apply (erule subjectReads.induct)
     (* warning: slow *)
     by (simp, blast?)+


definition abd_affects_set where
 "abd_affects_set \<equiv> {NicB, RM, R, NicA, NicD,
                     EP, NTFN2}" (* these two added for NTFN binding *)
declare abd_affects_set_def[simp]

lemma abd_affects_bw : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> partition_label ` abd_affects_set \<subseteq> subjectAffects SACAuthGraph (partition_label x)"
  apply (simp only:abd_affects_set_def)
  apply (rule subsetI)
  (* refl cases *)
  apply (case_tac "partition_label x = xa")
    apply (simp add: affects_lrefl)
  (* non-refl cases *)
  apply (simp only: image_insert)
  apply (erule_tac a = xa in insertE)
    apply (rule_tac auth = SyncSend and ep = "partition_label x" and l' = "partition_label RM" in affects_send)
    apply (simp, simp, simp, simp)
  apply (erule_tac a = xa in insertE)
    apply (simp only:)
    apply (rule_tac ep = "partition_label x" and l' = "partition_label RM" in affects_recv)
      apply (simp)
      apply (auto)[1]
  apply (erule_tac a = xa in insertE)
    apply (simp only:)
    apply (rule_tac auth = SyncSend and ep = "partition_label x" and l' = "partition_label RM" in affects_send)
    apply (simp, simp, simp, simp)
  apply (erule_tac a = xa in insertE)
    apply (simp only:)
    apply (clarify)
    apply (erule notE)
    apply (rule_tac auth = SyncSend and ep = "partition_label x" and l' = "partition_label RM" in affects_send)
    apply (simp, simp, simp, simp)
  apply (erule_tac a = xa in insertE)
    apply (rule_tac auth = SyncSend and ep = "partition_label x" and l' = "partition_label RM" in affects_send)
    apply (simp, simp, simp, simp)
  apply (erule_tac a = xa in insertE)
    apply (rule_tac ep = "xa" and l = "partition_label x" in affects_ep_bound_trans)
    apply (rule_tac x = "partition_label RM" in exI)
    apply (rule_tac x = "partition_label x" in exI)
    apply (intro conjI)
    apply (simp,simp,simp)
  apply (erule_tac a = xa in insertE)
    apply (rule_tac ep = "xa" and l = "partition_label x" in affects_ep_bound_trans)
    apply (rule_tac x = "partition_label RM" in exI)
    apply (rule_tac x = "partition_label x" in exI)
    apply (intro conjI)
    apply (simp,simp,simp,simp)
  done

lemma abd_affects : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> subjectAffects SACAuthGraph (partition_label x) = partition_label ` abd_affects_set"
   apply (rule subset_antisym)
   defer
   apply (rule abd_affects_bw)
   apply (simp)
   apply (rule subsetI)
     apply (erule subjectAffects.induct)
     by auto

subsection \<open>NicC reads/affects\<close>

lemma c_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label NicC)"
  apply (rule_tac b = "partition_label NicC" in reads_read_page_read_thread)
  apply (rule reads_lrefl)
  apply (simp)
done

lemma c_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label NicC)"
  apply (rule_tac a = "partition_label EP" and ep = "partition_label EP" and t = "partition_label SC" and auth = "SyncSend" and auth' = "Reset" in reads_read_queued_thread_read_ep)
  apply (simp,simp,simp,simp)
  apply (rule c_reads_sc)
done

lemma c_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label NicC)"
  apply (rule_tac ep = "partition_label EP" in read_sync_ep_read_receivers)
   apply (rule c_reads_ep)
   apply (simp)
done

lemma c_reads_any_controlled_by_rm : "x \<in> {partition_label R, partition_label NicA, partition_label NicB, partition_label NicD} \<Longrightarrow> x \<in> subjectReads SACAuthGraph (partition_label NicC)"
  apply (rule_tac t = "partition_label RM" in reads_read_thread_read_pages)
    apply (rule c_reads_rm)
    apply auto
done

lemma c_reads : "subjectReads SACAuthGraph (partition_label NicC) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3}"
  apply (rule subset_antisym)
    defer
    (* backward *)
    apply (rule subsetI)
      apply (case_tac "x \<in> {partition_label R, partition_label NicA, partition_label NicB, partition_label NicD}")
        apply (rule c_reads_any_controlled_by_rm, assumption)
        apply (erule insertE, simp)
        apply (erule insertE, simp only:, rule c_reads_rm)
        apply (erule insertE, simp, erule insertE, simp, erule insertE, simp)
        apply (erule insertE, simp only:, rule c_reads_ep)
        apply (erule insertE, simp only:, rule c_reads_sc)
        apply (erule insertE, simp only:, rule reads_lrefl)
        apply (erule insertE, simp only:, rule reads_ntfn1_via_sc, rule c_reads_sc)
        apply (erule insertE, simp only:, rule reads_ntfn2_via_rm, rule c_reads_rm)
        apply (erule insertE, simp only:, rule reads_ntfn3_via_r, rule c_reads_any_controlled_by_rm, simp)
        apply simp
    (* forward *)
    apply (rule subsetI)
    apply (erule subjectReads.induct)
    by (simp, blast?)+

lemma c_affects_self_only : "x \<in> {partition_label NicC} \<Longrightarrow> x \<in> subjectAffects SACAuthGraph (partition_label NicC)"
  apply (erule insertE)
    apply (simp only:, rule affects_lrefl)
    apply simp
done

lemma c_affects : "subjectAffects SACAuthGraph (partition_label NicC) = {partition_label NicC}"
  apply (rule subset_antisym)
  defer
    (* backward *)
    apply (rule subsetI)
    apply (rule c_affects_self_only, assumption)
    (* forward *)
    apply (rule subsetI)
    apply (erule subjectAffects.induct)
    by (simp, blast?)+

subsection \<open>R reads/affects\<close>

lemma r_reads_bd : "x \<in> {partition_label NicB, partition_label NicD} \<Longrightarrow> x \<in> subjectReads SACAuthGraph (partition_label R)"
  apply (rule reads_read)
  apply auto
done

lemma r_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label R)"
    apply (rule_tac a="partition_label SC" and auth'="SyncSend" and ep="partition_label EP" and t="partition_label RM" and auth="Receive" in reads_read_queued_thread_read_ep)
    apply (simp, simp, simp, simp, rule reads_Control_rev, simp)
done

lemma r_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label R)"
    apply (rule_tac ep="partition_label EP" and b="partition_label SC" in read_sync_ep_read_senders)
    apply (rule r_reads_ep, simp)
done

lemma r_reads_a : "partition_label NicA \<in> subjectReads SACAuthGraph (partition_label R)"
  apply (rule_tac a="partition_label NicA" and auth'="Reset" and ep="partition_label NicA" and t="partition_label RM" and auth="Receive" in reads_read_queued_thread_read_ep)
  apply (simp_all add:reads_Control_rev[simplified])
done

lemma r_reads_c : "partition_label NicC \<in> subjectReads SACAuthGraph (partition_label R)"
  apply (rule_tac t="partition_label SC" in reads_read_thread_read_pages)
  apply (rule r_reads_sc, simp)
done

lemma r_reads : "subjectReads SACAuthGraph (partition_label R) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3}"
  apply (rule subset_antisym)
    defer
    (* backward *)
    apply (rule subsetI)
    apply (erule insertE, rule r_reads_bd, simp)
    apply (erule insertE, rule reads_Control_rev, simp)
    apply (erule insertE, simp only:, rule reads_lrefl)
    apply (erule insertE, simp only:, rule r_reads_a)
    apply (erule insertE, rule r_reads_bd, simp)
    apply (erule insertE, simp only:, rule r_reads_ep)
    apply (erule insertE, simp only:, rule r_reads_sc)
    apply (erule insertE, simp only:, rule r_reads_c)
    apply (erule insertE, simp only:, rule reads_ntfn1_via_sc, rule r_reads_sc)
    apply (erule insertE, simp only:, rule reads_ntfn2_via_rm, rule reads_Control_rev, simp)
    apply (erule insertE, simp only:, rule reads_ntfn3_via_r, rule reads_lrefl)
    apply simp
    (* forward *)
    apply (rule subsetI)
    apply (erule subjectReads.induct)
    by (simp, blast?)+

lemma r_affects_bd : "x \<in> {partition_label NicB, partition_label NicD} \<Longrightarrow> x \<in> subjectAffects SACAuthGraph (partition_label R)"
  apply (rule_tac auth="Write" in affects_write)
  apply auto
done

lemma r_affects_rm : "partition_label RM \<in> subjectAffects SACAuthGraph (partition_label R)"
  apply (rule_tac l="partition_label R" and ep="partition_label R" in affects_recv)
  apply simp_all
done

lemma r_affects_a : "partition_label NicA \<in> subjectAffects SACAuthGraph (partition_label R)"
  apply (rule_tac l="partition_label R" and ep="partition_label R" and l'="partition_label RM" and auth="Receive" in affects_reset)
  apply auto
done

lemma r_affects_ntfn3 : "partition_label NTFN3 \<in> subjectAffects SACAuthGraph (partition_label R)"
  apply (rule_tac l="partition_label R" and auth="Receive" in affects_ep)
  apply simp_all
done

lemma r_affects_ntfn2 : "partition_label NTFN2 \<in> subjectAffects SACAuthGraph (partition_label R)"
  apply (rule_tac l="partition_label R" in affects_ep_bound_trans)
  by auto

lemma r_affects_ep : "partition_label EP \<in> subjectAffects SACAuthGraph (partition_label R)"
  apply (rule_tac l="partition_label R" in affects_ep_bound_trans)
  by auto

lemma r_affects : "subjectAffects SACAuthGraph (partition_label R) =
                   {partition_label NicB, partition_label NicD, partition_label R,
                    partition_label RM, partition_label NicA, partition_label NTFN3,
                    partition_label EP, partition_label NTFN2 \<comment> \<open>these 2 added for NTFN binding\<close> }"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, rule r_affects_bd, simp)
  apply (erule insertE, rule r_affects_bd, simp)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule r_affects_rm)
  apply (erule insertE, simp only:, rule r_affects_a)
  apply (erule insertE, simp only:, rule r_affects_ntfn3)
  apply (erule insertE, simp only:, rule r_affects_ep)
  apply (erule insertE, simp only:, rule r_affects_ntfn2)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  by (simp, blast?)+

subsection \<open>RM reads/affects\<close>

lemma rm_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label RM)"
  apply (rule_tac ep="partition_label EP" in read_sync_ep_read_senders)
  apply (simp_all add:reads_ep)
done

lemma rm_reads_c : "partition_label NicC \<in> subjectReads SACAuthGraph (partition_label RM)"
  apply (rule_tac t="partition_label SC" in reads_read_thread_read_pages)
  apply (rule rm_reads_sc, simp)
done

lemma rm_reads : "subjectReads SACAuthGraph (partition_label RM) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, simp only:, rule reads_read, simp)
  apply (erule insertE, simp only:, rule reads_lrefl)
  apply (erule insertE, simp only:, rule reads_read, simp)
  apply (erule insertE, simp only:, rule reads_read, simp)
  apply (erule insertE, simp only:, rule reads_read, simp)
  apply (erule insertE, simp only:, rule reads_ep, simp, simp)
  apply (erule insertE, simp only:, rule rm_reads_sc)
  apply (erule insertE, simp only:, rule rm_reads_c)
  apply (erule insertE, simp only:, rule reads_ntfn1_via_sc, rule rm_reads_sc)
  apply (erule insertE, simp only:, rule reads_ntfn2_via_rm, rule reads_lrefl)
  apply (erule insertE, simp only:, rule reads_ntfn3_via_r, rule reads_read, simp)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectReads.induct)
  by (simp, blast?)+

lemma rm_affects_via_control : "x \<in> {partition_label R, partition_label NicA, partition_label NicB, partition_label NicD} \<Longrightarrow> x \<in> subjectAffects SACAuthGraph (partition_label RM)"
  apply (rule_tac l="partition_label RM" and auth="Control" in affects_write)
  apply (simp, simp)
done

lemma rm_affects_ep : "partition_label EP \<in> subjectAffects SACAuthGraph (partition_label RM)"
  apply (rule_tac auth="Receive" in affects_ep)
  apply simp_all
done

lemma rm_affects_sc : "partition_label SC \<in> subjectAffects SACAuthGraph (partition_label RM)"
  apply (rule_tac l="partition_label RM" and ep="partition_label EP" in affects_recv)
  apply simp_all
done

lemma rm_affects_ntfn2 : "partition_label NTFN2 \<in> subjectAffects SACAuthGraph (partition_label RM)"
  apply (rule_tac l="partition_label RM" and auth="Receive" in affects_ep)
  apply simp_all
done

lemma rm_affects_ntfn3 : "partition_label NTFN3 \<in> subjectAffects SACAuthGraph (partition_label RM)"
  apply (rule_tac l="partition_label RM" in affects_ep_bound_trans)
  apply clarsimp
  by auto


lemma rm_affects : "subjectAffects SACAuthGraph (partition_label RM) =
                    {partition_label NicA, partition_label NicB, partition_label NicD,
                     partition_label R, partition_label SC, partition_label EP,
                     partition_label RM, partition_label NTFN2,
                     partition_label NTFN3 \<comment> \<open>added for NTFN binding\<close>}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, simp only:, rule rm_affects_via_control, simp)
  apply (erule insertE, simp only:, rule rm_affects_via_control, simp)
  apply (erule insertE, simp only:, rule rm_affects_via_control, simp)
  apply (erule insertE, simp only:, rule rm_affects_via_control, simp)
  apply (erule insertE, simp only:, rule rm_affects_sc)
  apply (erule insertE, simp only:, rule rm_affects_ep)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule rm_affects_ntfn2)
  apply (erule insertE, simp only:, rule rm_affects_ntfn3)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  by (simp, blast?)+

subsection \<open>SC\<close>

lemma sc_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label SC)"
  apply (rule_tac ep="partition_label EP" and b="partition_label RM" in read_sync_ep_read_receivers)
  apply (simp_all add:reads_ep)
done

lemma sc_reads : "subjectReads SACAuthGraph (partition_label SC) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, rule reads_all_rm_controlled_subjects, rule sc_reads_rm, simp)
apply (erule insertE, rule reads_all_rm_controlled_subjects, rule sc_reads_rm, simp)
apply (erule insertE, rule reads_all_rm_controlled_subjects, rule sc_reads_rm, simp)
apply (erule insertE, rule reads_all_rm_controlled_subjects, rule sc_reads_rm, simp)
apply (erule insertE, rule reads_all_rm_controlled_subjects, rule sc_reads_rm, simp)
  apply (erule insertE, simp only:, rule_tac auth="SyncSend" in reads_ep, simp, simp)
  apply (erule insertE, simp only:, rule reads_lrefl)
  apply (erule insertE, simp only:, rule reads_read, simp)
  apply (erule insertE, simp only:, rule reads_ntfn1_via_sc, rule reads_lrefl)
  apply (erule insertE, simp only:, rule reads_ntfn2_via_rm, rule sc_reads_rm)
  apply (erule insertE, simp only:, rule reads_ntfn3_via_r, rule reads_all_rm_controlled_subjects, rule sc_reads_rm, simp)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectReads.induct)
  apply (simp, blast?)+
done

lemma sc_affects_all_rm_controls : "l \<in> RMControls \<Longrightarrow> l \<in> subjectAffects SACAuthGraph (partition_label SC)"
  apply (simp only:RMControls_def)
  apply (erule insertE, rule_tac l="partition_label SC" and auth="SyncSend" and ep="partition_label EP" and l'="partition_label RM" in affects_send, simp, simp, simp, simp)+
  apply simp
done

lemma sc_affects : "subjectAffects SACAuthGraph (partition_label SC) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, rule sc_affects_all_rm_controls, simp)
  apply (erule insertE, rule sc_affects_all_rm_controls, simp)
  apply (erule insertE, rule sc_affects_all_rm_controls, simp)
  apply (erule insertE, rule sc_affects_all_rm_controls, simp)
  apply (erule insertE, rule sc_affects_all_rm_controls, simp)
  apply (erule insertE, simp only:, rule_tac l="partition_label SC" and auth="SyncSend" in affects_ep, simp, simp)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule_tac l="partition_label SC" and auth="Write" in affects_write, simp, simp)
  apply (erule insertE, simp only:, rule_tac l="partition_label SC" and auth="Receive" in affects_ep, simp, simp)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp, blast?)+
done

subsection \<open>EP\<close>

lemma ep_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label EP)"
  apply (rule_tac ep="partition_label EP" in read_sync_ep_read_senders)
  apply (rule reads_lrefl, simp_all)
done

lemma ep_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label EP)"
  apply (rule_tac ep="partition_label EP" and b="partition_label RM" in read_sync_ep_read_receivers)
  apply (rule reads_lrefl, simp)
done

lemma ep_reads_c : "partition_label NicC \<in> subjectReads SACAuthGraph (partition_label EP)"
  apply (rule_tac t="partition_label SC" and p="partition_label NicC" in reads_read_thread_read_pages)
  apply (rule ep_reads_sc, simp)
done

lemma ep_reads : "subjectReads SACAuthGraph (partition_label EP) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, rule reads_all_rm_controlled_subjects, rule ep_reads_rm, simp)
  apply (erule insertE, simp only:, rule ep_reads_rm)
  apply (erule insertE, rule reads_all_rm_controlled_subjects, rule ep_reads_rm, simp)
  apply (erule insertE, rule reads_all_rm_controlled_subjects, rule ep_reads_rm, simp)
  apply (erule insertE, rule reads_all_rm_controlled_subjects, rule ep_reads_rm, simp)
  apply (erule insertE, simp only:, rule reads_lrefl)
  apply (erule insertE, simp only:, rule ep_reads_sc)
  apply (erule insertE, simp only:, rule ep_reads_c)
  apply (erule insertE, simp only:, rule reads_ntfn1_via_sc, rule ep_reads_sc)
  apply (erule insertE, simp only:, rule reads_ntfn2_via_rm, rule ep_reads_rm)
  apply (erule insertE, simp only:, rule reads_ntfn3_via_r, rule reads_all_rm_controlled_subjects, rule ep_reads_rm, simp)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectReads.induct)
  apply (simp, blast?)+
done

lemma ep_affects_sc : "partition_label SC \<in> subjectAffects SACAuthGraph (partition_label EP)"
  apply (rule_tac l="partition_label EP" and ep="partition_label EP" in affects_recv)
  apply simp_all
done

lemma ep_affects_c : "partition_label NicC \<in> subjectAffects SACAuthGraph (partition_label EP)"
  apply (rule_tac l="partition_label EP" and l'="partition_label SC" and auth="SyncSend" and ep="partition_label EP" in affects_reset)
  apply simp_all
done

lemma ep_affects_ntfn2 : "partition_label NTFN2 \<in> subjectAffects SACAuthGraph (partition_label EP)"
  apply (rule_tac ep="partition_label NTFN2" in affects_ep_bound_trans)
  by auto

lemma ep_affects_rm_controls : "x \<in> RMControls \<Longrightarrow> x \<in> subjectAffects SACAuthGraph (partition_label EP)"
  apply (rule_tac l="partition_label EP" and ep="partition_label EP" and auth="SyncSend" and l'="partition_label RM" in affects_send)
  apply (simp_all)
done

lemma ep_affects: "subjectAffects SACAuthGraph (partition_label EP) = {partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN2} \<union> RMControls"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule UnE)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule ep_affects_sc)
  apply (erule insertE, simp only:, rule ep_affects_c)
  apply (erule insertE, simp only:, rule ep_affects_ntfn2)
  apply simp
  apply (rule ep_affects_rm_controls, simp)
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  by (simp, blast?)+

subsection \<open>NTFN1,2,3\<close>

subsubsection \<open>NTFN1 reads SC, EP, RM, R\<close>

lemma ntfn1_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label NTFN1)"
  apply (rule_tac ep="partition_label NTFN1" in read_sync_ep_read_receivers)
  apply (rule reads_lrefl, simp)
done

lemma ntfn1_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label NTFN1)"
  apply (rule_tac ep="partition_label EP" and auth="SyncSend" and t="partition_label SC" and auth'="Reset" and a="partition_label EP" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp, rule ntfn1_reads_sc)
done

lemma ntfn1_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label NTFN1)"
  apply (rule_tac b="partition_label RM" and ep="partition_label EP" in read_sync_ep_read_receivers)
  apply (rule ntfn1_reads_ep, simp)
done

subsubsection \<open>NTFN2 reads SC, EP, RM, R\<close>

lemma ntfn2_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label NTFN2)"
  apply (rule_tac ep="partition_label NTFN2" in read_sync_ep_read_receivers)
  apply (rule reads_lrefl, simp)
done

lemma ntfn2_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label NTFN2)"
  apply (rule_tac ep="partition_label EP" and auth="Receive" and t="partition_label RM" and auth'="Reset" and a="partition_label EP" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp, rule ntfn2_reads_rm)
done

lemma ntfn2_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label NTFN2)"
  apply (rule_tac b="partition_label SC" and ep="partition_label EP" in read_sync_ep_read_senders)
  apply (rule ntfn2_reads_ep, simp)
done

subsubsection \<open>NTFN3 reads SC, EP, RM, R\<close>

lemma ntfn3_reads_r : "partition_label R \<in> subjectReads SACAuthGraph (partition_label NTFN3)"
  apply (rule_tac ep="partition_label NTFN3" in read_sync_ep_read_receivers)
  apply (rule reads_lrefl, simp)
done

lemma ntfn3_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label NTFN3)"
  apply (rule_tac b="partition_label R" in reads_read_page_read_thread)
  apply (rule ntfn3_reads_r, simp)
done

lemma ntfn3_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label NTFN3)"
  apply (rule_tac t="partition_label RM" and auth="Receive" and auth'="SyncSend" and a="partition_label SC" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp, rule ntfn3_reads_rm)
done

lemma ntfn3_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label NTFN3)"
  apply (rule_tac ep="partition_label EP" in read_sync_ep_read_senders)
  apply (rule ntfn3_reads_ep, simp)
done

subsubsection \<open>NTFN1,2,3 reads C\<close>

lemma ntfn123_reads_c : "x \<in> {NTFN1, NTFN2, NTFN3} \<Longrightarrow> partition_label NicC \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac t="partition_label SC" in reads_read_thread_read_pages)
  apply (erule insertE, simp only:, rule ntfn1_reads_sc, erule insertE, simp only:, rule ntfn2_reads_sc, erule insertE, simp only:, rule ntfn3_reads_sc, simp)
  apply simp
done

subsubsection \<open>NTFN1,2,3 reads each other\<close>

lemma ntfn13_reads_ntfn2 : "l \<in> {NTFN1, NTFN3} \<Longrightarrow> partition_label NTFN2 \<in> subjectReads SACAuthGraph (partition_label l)"
  apply (rule_tac t="partition_label RM" and auth="Receive" and auth'="Reset" and a="partition_label NTFN2" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp)
  apply (erule insertE, simp only:, rule ntfn1_reads_rm, erule insertE, simp only:, rule ntfn3_reads_rm, simp)
done

lemma ntfn12_reads_ntfn3 : "l \<in> {NTFN1, NTFN2} \<Longrightarrow> partition_label NTFN3 \<in> subjectReads SACAuthGraph (partition_label l)"
  apply (rule_tac t="partition_label R" and auth="Receive" and auth'="Reset" and a="partition_label NTFN3" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp)
  apply (erule insertE, simp only:, rule reads_all_rm_controlled_subjects, rule ntfn1_reads_rm, simp, erule insertE, simp only:, rule reads_all_rm_controlled_subjects, rule ntfn2_reads_rm, simp_all)
done

lemma ntfn23_reads_ntfn1 : "l \<in> {NTFN2, NTFN3} \<Longrightarrow> partition_label NTFN1 \<in> subjectReads SACAuthGraph (partition_label l)"
  apply (rule_tac t="partition_label SC" and auth="Receive" and auth'="Reset" and a="partition_label NTFN1" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp)
  apply (erule insertE, simp only:, rule ntfn2_reads_sc, erule insertE, simp only:, rule ntfn3_reads_sc, simp)
done

subsubsection \<open>NTFN1,2,3 reads\<close>
declare SACAuthGraph_def[simp del]

lemma ntfn123_reads_rm : "l \<in> {NTFN1, NTFN2, NTFN3} \<Longrightarrow> partition_label RM \<in> subjectReads SACAuthGraph (partition_label l)"
by (auto simp:ntfn1_reads_rm ntfn2_reads_rm ntfn3_reads_rm)

lemma ntfn123_reads_sc : "l \<in> {NTFN1, NTFN2, NTFN3} \<Longrightarrow> partition_label SC \<in> subjectReads SACAuthGraph (partition_label l)"
by (auto simp:ntfn1_reads_sc ntfn2_reads_sc ntfn3_reads_sc)

lemma ntfn123_reads_ep : "l \<in> {NTFN1, NTFN2, NTFN3} \<Longrightarrow> partition_label EP \<in> subjectReads SACAuthGraph (partition_label l)"
by (auto simp:ntfn1_reads_ep ntfn2_reads_ep ntfn3_reads_ep)

lemma ntfn123_reads_ntfn123 : "\<lbrakk>l \<in> {NTFN1, NTFN2, NTFN3}; x \<in> {NTFN1, NTFN2, NTFN3}\<rbrakk> \<Longrightarrow> partition_label l \<in> subjectReads SACAuthGraph (partition_label x)"
by (auto simp:ntfn12_reads_ntfn3 ntfn13_reads_ntfn2 ntfn23_reads_ntfn1)

lemma ntfn123_reads : "l \<in> {NTFN1, NTFN2, NTFN3} \<Longrightarrow> subjectReads SACAuthGraph (partition_label l) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label NTFN1, partition_label NTFN2, partition_label NTFN3}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule ntfn123_reads_rm, simp, simp)
  apply (erule_tac a=x in insertE, simp only:, rule ntfn123_reads_rm, simp)
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule ntfn123_reads_rm, simp, simp)
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule ntfn123_reads_rm, simp, simp)
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule ntfn123_reads_rm, simp, simp)
  apply (erule_tac a=x in insertE, simp only:, rule ntfn123_reads_ep, simp)
  apply (erule_tac a=x in insertE, simp only:, rule ntfn123_reads_sc, simp)
  apply (erule_tac a=x in insertE, simp only:, rule ntfn123_reads_c, simp)
  apply (auto simp:ntfn123_reads_ntfn123)[1]
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectReads.induct)
  by (simp add:SACAuthGraph_def, blast?)+

subsubsection \<open>NTFN1,2,3 affects\<close>

lemma ntfn1_affects_sc : "partition_label SC \<in> subjectAffects SACAuthGraph (partition_label NTFN1)"
  apply (rule_tac l''="partition_label SC" and l'="partition_label SC" and ep="partition_label NTFN1" and auth="Notify" and l="partition_label NTFN1" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma ntfn1_affects_c : "partition_label NicC \<in> subjectAffects SACAuthGraph (partition_label NTFN1)"
  apply (rule_tac l'="partition_label SC" and ep="partition_label NTFN1" and l="partition_label NTFN1" and auth="Notify" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma ntfn1_affects : "subjectAffects SACAuthGraph (partition_label NTFN1) = {partition_label NTFN1, partition_label SC, partition_label NicC}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule ntfn1_affects_sc)
  apply (erule insertE, simp only:, rule ntfn1_affects_c)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
done

lemma ntfn2_affects_rm : "partition_label RM \<in> subjectAffects SACAuthGraph (partition_label NTFN2)"
  apply (rule_tac l'="partition_label RM" and ep="partition_label NTFN2" and auth="Notify" and l="partition_label NTFN2" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma ntfn2_affects_ep : "partition_label EP \<in> subjectAffects SACAuthGraph (partition_label NTFN2)"
  apply (rule affects_ep_bound_trans)
  by (auto simp: SACAuthGraph_def)

lemma ntfn2_affects_rm_controls : "x \<in> RMControls \<Longrightarrow> x \<in> subjectAffects SACAuthGraph (partition_label NTFN2)"
  apply (rule_tac l="partition_label NTFN2" and ep="partition_label NTFN2" and auth="SyncSend" and l'="partition_label RM" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma ntfn2_affects : "subjectAffects SACAuthGraph (partition_label NTFN2) = {partition_label NTFN2, partition_label RM, partition_label EP} \<union> RMControls"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule UnE)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule ntfn2_affects_rm)
  apply (erule insertE, simp only:, rule ntfn2_affects_ep)
  apply simp
  apply (rule ntfn2_affects_rm_controls, simp)
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  by (simp add:SACAuthGraph_def, blast?)+

lemma ntfn3_affects_r : "partition_label R \<in> subjectAffects SACAuthGraph (partition_label NTFN3)"
  apply (rule_tac l'="partition_label R" and ep="partition_label NTFN3" and auth="Notify" and l="partition_label NTFN3" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma ntfn3_affects_bd : "l \<in> {NicB, NicD} \<Longrightarrow> partition_label l \<in> subjectAffects SACAuthGraph (partition_label NTFN3)"
  apply (rule_tac l'="partition_label R" and ep="partition_label NTFN3" and l="partition_label NTFN3" and auth="Notify" in affects_send)
  apply (simp add:SACAuthGraph_def, blast?)+
done

lemma ntfn3_affects : "subjectAffects SACAuthGraph (partition_label NTFN3) = {partition_label NTFN3, partition_label R} \<union> {partition_label NicB, partition_label NicD}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI, erule UnE)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule ntfn3_affects_r, simp)
  apply (auto simp:ntfn3_affects_bd)[1]
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
done

subsection \<open>T\<close>

lemma t_reads : "subjectReads SACAuthGraph (partition_label T) = {partition_label T}"
  apply (rule subset_antisym)
  defer
  apply (rule subsetI, erule insertE, simp only:, rule reads_lrefl, simp)
  apply (rule subsetI, erule subjectReads.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
done

lemma t_affects_ntfn123 : "l \<in> {NTFN1, NTFN2, NTFN3} \<Longrightarrow>  partition_label l \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac auth="Notify" in affects_ep)
  apply (simp_all add:SACAuthGraph_def, blast)
done

lemma t_affects_sc : "partition_label SC \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label SC" and l'="partition_label SC" and ep="partition_label NTFN1" and auth="Notify" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_rm : "partition_label RM \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label RM" and l'="partition_label RM" and ep="partition_label NTFN2" and auth="Notify" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_r : "partition_label R \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label R" and l'="partition_label R" and ep="partition_label NTFN3" and auth="Notify" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_ep : "partition_label EP \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule affects_ep_bound_trans)
  by (auto simp: SACAuthGraph_def)

lemma t_affects_c : "partition_label NicC \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label NicC" and l'="partition_label SC" and ep="partition_label NTFN1" and auth="Notify" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_a : "partition_label NicA \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label NicA" and l'="partition_label RM" and ep="partition_label NTFN2" and auth="Notify" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_bd : "l \<in> {NicB, NicD} \<Longrightarrow> partition_label l \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l'="partition_label R" and ep="partition_label NTFN3" and auth="Notify" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def, blast)
done

lemma t_affects : "subjectAffects SACAuthGraph (partition_label T) = {partition_label NTFN1, partition_label NTFN2, partition_label NTFN3} \<union> {partition_label T, partition_label SC, partition_label RM, partition_label R, partition_label NicA, partition_label NicB, partition_label NicD, partition_label NicC, partition_label EP}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI, erule UnE)
  apply (auto simp:t_affects_ntfn123)[1]
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule t_affects_sc)
  apply (erule insertE, simp only:, rule t_affects_rm)
  apply (erule insertE, simp only:, rule t_affects_r)
  apply (erule insertE, simp only:, rule t_affects_a)
  apply (erule insertE, simp only:, rule t_affects_bd, simp)
  apply (erule insertE, simp only:, rule t_affects_bd, simp)
  apply (erule insertE, simp only:, rule t_affects_c)
  apply (erule insertE, simp only:, rule t_affects_ep)
  apply simp
  (* forward *)
  apply (rule subsetI, erule subjectAffects.induct)
  by (simp add:SACAuthGraph_def, blast?)+

subsection \<open>Policy\<close>

lemmas SAC_reads = sc_reads ep_reads c_reads rm_reads r_reads abd_reads ntfn123_reads t_reads

lemmas SAC_affects = sc_affects ep_affects c_affects rm_affects r_affects abd_affects ntfn1_affects ntfn2_affects ntfn3_affects t_affects

definition SACFlowDoms where
  "SACFlowDoms \<equiv> {Partition EP, Partition SC, Partition NicC, Partition RM, Partition R, Partition NicA, Partition NicB, Partition NicD, Partition NTFN1, Partition NTFN2, Partition NTFN3}"
declare SACFlowDoms_def [simp]

definition SACPolicyFlows :: "(SACLabels partition \<times> SACLabels partition) set" where
  "SACPolicyFlows \<equiv>
     {(PSched,d)| d. True}
   \<union> {(Partition l, Partition k)| l k. (k = T \<longrightarrow> l = T)}"

lemma SAC_partsSubjectAffects_exceptT : "x \<noteq> T \<Longrightarrow> partsSubjectAffects SACAuthGraph x = SACFlowDoms"
  apply (rule equalityI)
  defer
  apply (rule subsetI)
    apply (simp add:partsSubjectAffects_def image_def label_can_affect_partition_def)
    apply (case_tac x)
     apply ((erule disjE, clarify, simp add:SAC_affects SAC_reads, blast?)+, simp add:SAC_affects SAC_reads, blast?)+
  apply (rule subsetI)
    apply (simp add:partsSubjectAffects_def image_def label_can_affect_partition_def)
    apply (clarify)
    apply (case_tac x)
      apply (case_tac[!] xaa)
        apply (auto simp: SAC_affects SAC_reads)
done

lemma SAC_partsSubjectAffects_T : "(partsSubjectAffects SACAuthGraph T) = {Partition NTFN1, Partition NTFN2, Partition NTFN3} \<union> {Partition T, Partition SC, Partition RM, Partition R, Partition NicA, Partition NicB, Partition NicD, Partition NicC, Partition EP}"
    apply (rule equalityI)
    apply (rule subsetI)
    apply (simp add: partsSubjectAffects_def image_def label_can_affect_partition_def SAC_affects SAC_reads)
    apply (clarify)
    apply (case_tac xa, simp_all)[1]
    apply (rule subsetI)
    apply (simp add: partsSubjectAffects_def image_def label_can_affect_partition_def SAC_affects SAC_reads)
    apply (erule disjE, simp add: SAC_reads) (* Do not collapse this in with a blast? because attempting blast takes too long *)
    apply ((erule disjE)?, simp add: SAC_reads, blast)+
done

lemma SAC_policyFlows : "policyFlows SACAuthGraph = SACPolicyFlows"
  apply (rule subset_antisym)
  (* forward *)
  apply (rule subsetI)
  apply clarify
  apply (erule policyFlows.cases)
    (* subject case *)
    apply (clarsimp simp:SACPolicyFlows_def)
    apply (case_tac "d = Partition T")
      apply (case_tac l, auto simp:SAC_partsSubjectAffects_T SAC_partsSubjectAffects_exceptT)[1]
      apply (case_tac l, auto simp:SAC_partsSubjectAffects_T SAC_partsSubjectAffects_exceptT)[1]
    (* scheduler case *)
    apply (simp add:SACPolicyFlows_def)
  (* backward *)
  apply (rule subsetI)
  apply (clarsimp simp:SACPolicyFlows_def)
  apply (erule disjE)
    (* scheduler flows to all *)
    apply (simp add:PSched_flows_to_all)
    (* all subjects flow to all subjects *)
    apply (clarify, simp)
    apply (rule policy_affects)
    apply (case_tac l, case_tac[1-12] k, auto simp:SAC_partsSubjectAffects_T SAC_partsSubjectAffects_exceptT)
done

end
