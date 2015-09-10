(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory PolicySystemSAC
imports
  Noninterference
  "../access-control/ExampleSystem"
begin

text {*
  Reads/Affects sets: 
  - NicA, NicB, NicD: reads all except T
       affects {RM, R, NicA, NicB, NicD} 
  - NicC: reads all except T, affects self only
  - R:  reads all except T
        affects {NicA, NicB, NicD, R, RM, AEP3}
  - RM: reads all except T
        affects {SC, EP, RM, R, NicA, NicB, NicD, AEP2}
  - SC: reads all except T
        affects {EP, SC, NicC, RM, R, NicA, NicB, NicD, AEP1}
  - EP: reads all except T
        affects {EP, SC, NicC, RM, R, NicA, NicB, NicD}
  - AEP1: reads all except T, affects {AEP1, SC, NicC}
  - AEP2: ''                , affects {AEP2, RM, R, NicA, NicB, NicD}
  - AEP3: ''                , affects {AEP3, R, NicB, NicD}
  - T: reads T, affects all except EP
*}

subsection {* Definitions *}

datatype SACLabels = 
    NicA | NicB | NicC | NicD
  | R | RM |  SC | EP
  | T | AEP1 | AEP2 | AEP3

definition complete_AgentAuthGraph where 
  "complete_AgentAuthGraph g \<equiv> 
     g \<union> {(y,a,y) | a y. True} 
       \<union> {(x,a,y) | x a y. (x,Control,y) \<in> g }
       \<union> {(x,a,y)|x a y. \<exists> z. (x,Control,z) \<in> g \<and> (z, Control,y) \<in> g} " 
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
    (partition_label T, AsyncSend, partition_label AEP1),
    (partition_label T, AsyncSend, partition_label AEP2),
    (partition_label T, AsyncSend, partition_label AEP3),
    (partition_label SC, Receive, partition_label AEP1),
    (partition_label RM, Receive, partition_label AEP2),
    (partition_label R, Receive, partition_label AEP3)
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

lemma reads_aep3_via_r : "partition_label R \<in> subjectReads SACAuthGraph (partition_label x) \<Longrightarrow> partition_label AEP3 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label AEP3" and t="partition_label R" and auth="Receive" and auth'="AsyncSend" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply simp_all
done

lemma reads_aep2_via_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label x) \<Longrightarrow> partition_label AEP2 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label AEP2" and t="partition_label RM" and auth="Receive" and auth'="AsyncSend" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply simp_all
done

lemma reads_aep1_via_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label x) \<Longrightarrow> partition_label AEP1 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label AEP1" and t="partition_label SC" and auth="Receive" and auth'="AsyncSend" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply simp_all
done

subsection {* NicA, NicB, NicD reads/affects *}

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
  apply(rule reads_lrefl)
  done

lemma abdrm_reads_sc : "x \<in> {NicA, NicB, NicD, RM} \<Longrightarrow> partition_label SC \<in> subjectReads SACAuthGraph (partition_label x)"
    apply (rule_tac auth = "Receive" and b = "partition_label SC" and a = "partition_label RM" and ep = "partition_label EP" in read_sync_ep_read_senders)
      apply (simp, simp, simp del: SACAuthGraph_def add: abdrm_reads_ep, simp)
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

lemma abd_reads_aep3 : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> partition_label AEP3 \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac ep="partition_label AEP3" and t="partition_label R" and auth="Receive" and auth'="AsyncSend" and a="partition_label T" in reads_read_queued_thread_read_ep)
  apply (simp_all add: abd_reads_r del:SACAuthGraph_def, simp_all)
done

lemma abd_reads_all_bw : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3} \<subseteq> subjectReads SACAuthGraph (partition_label x)"
  apply (rule subsetI)
  (* refl cases *)
  apply (case_tac "partition_label x = xa")
  apply (simp add: reads_lrefl)
  (* non refl cases *)
  apply (case_tac "xa \<in> RMControls")
    apply (rule reads_all_rm_controlled_subjects, rule abd_reads_rm, simp, simp)
  apply (erule_tac a = xa in insertE, simp add:RMControls_def)
  apply (erule_tac a = xa in insertE, simp only:, rule abd_reads_rm, simp)
  apply (erule_tac a = xa in insertE, simp add:RMControls_def)
  apply (erule_tac a = xa in insertE, simp add:RMControls_def)
  apply (erule_tac a = xa in insertE, simp add:RMControls_def)
  apply (erule_tac a = xa in insertE, simp only:, rule abdrm_reads_ep, simp, blast)
  apply (erule_tac a = xa in insertE, simp only:, rule abdrm_reads_sc, simp, blast)
  apply (erule_tac a = xa in insertE, simp only:, rule abd_reads_c, simp)
  apply (erule_tac a = xa in insertE, simp only:, rule reads_aep1_via_sc, rule abdrm_reads_sc, simp, blast)
  apply (erule_tac a = xa in insertE, simp only:, rule reads_aep2_via_rm, rule abd_reads_rm, simp)
  apply (erule_tac a = xa in insertE, simp only:, rule reads_aep3_via_r, rule abd_reads_r, simp)
  apply simp
done
                  
lemma abd_reads : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> subjectReads SACAuthGraph (partition_label x) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3}"
   apply (rule subset_antisym)
   defer
   apply (rule abd_reads_all_bw)
   apply (simp)
   apply (rule subsetI)
     apply (erule subjectReads.induct)
     (* warning: slow *)
     apply (simp, blast?)+
done    

definition abd_affects_set where
 "abd_affects_set \<equiv> {NicB, RM, R, NicA, NicD}"
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
  apply (simp)
done

lemma abd_affects : "x \<in> {NicA, NicB, NicD} \<Longrightarrow> subjectAffects SACAuthGraph (partition_label x) = partition_label ` abd_affects_set"
   apply (rule subset_antisym)
   defer
   apply (rule abd_affects_bw)
   apply (simp)
   apply (rule subsetI)
     apply (erule subjectAffects.induct)
     apply (auto)
  sorry

subsection {* NicC reads/affects *}

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
  apply (rule_tac auth = SyncSend and a = "partition_label SC" and ep = "partition_label EP" in read_sync_ep_read_receivers)
   apply (simp, simp)
   apply (rule c_reads_ep)
   apply (simp)
done

lemma c_reads_any_controlled_by_rm : "x \<in> {partition_label R, partition_label NicA, partition_label NicB, partition_label NicD} \<Longrightarrow> x \<in> subjectReads SACAuthGraph (partition_label NicC)"
  apply (rule_tac t = "partition_label RM" in reads_read_thread_read_pages)
    apply (rule c_reads_rm)
    apply auto
done

lemma c_reads : "subjectReads SACAuthGraph (partition_label NicC) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3}"
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
        apply (erule insertE, simp only:, rule reads_aep1_via_sc, rule c_reads_sc)
        apply (erule insertE, simp only:, rule reads_aep2_via_rm, rule c_reads_rm)
        apply (erule insertE, simp only:, rule reads_aep3_via_r, rule c_reads_any_controlled_by_rm, simp)
        apply simp 
    (* forward *)
    apply (rule subsetI)
    apply (erule subjectReads.induct)
    apply (simp, blast?)+
done

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
    apply (simp, blast?)+
done

subsection {* R reads/affects *}

lemma r_reads_bd : "x \<in> {partition_label NicB, partition_label NicD} \<Longrightarrow> x \<in> subjectReads SACAuthGraph (partition_label R)"
  apply (rule reads_read)
  apply auto
done

lemma r_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label R)"
    apply (rule_tac a="partition_label SC" and auth'="SyncSend" and ep="partition_label EP" and t="partition_label RM" and auth="Receive" in reads_read_queued_thread_read_ep)
    apply (simp, simp, simp, simp, rule reads_Control_rev, simp)
done

lemma r_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label R)"
    apply (rule_tac a="partition_label RM" and auth="Receive" and ep="partition_label EP" and b="partition_label SC" in read_sync_ep_read_senders)
    apply (simp, simp, rule r_reads_ep, simp)
done

lemma r_reads_a : "partition_label NicA \<in> subjectReads SACAuthGraph (partition_label R)"
  apply (rule_tac a="partition_label NicA" and auth'="Reset" and ep="partition_label NicA" and t="partition_label RM" and auth="Receive" in reads_read_queued_thread_read_ep)
  apply (simp_all add:reads_Control_rev[simplified])
done 

lemma r_reads_c : "partition_label NicC \<in> subjectReads SACAuthGraph (partition_label R)"
  apply (rule_tac t="partition_label SC" in reads_read_thread_read_pages)
  apply (rule r_reads_sc, simp)
done

lemma r_reads : "subjectReads SACAuthGraph (partition_label R) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3}"
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
    apply (erule insertE, simp only:, rule reads_aep1_via_sc, rule r_reads_sc)
    apply (erule insertE, simp only:, rule reads_aep2_via_rm, rule reads_Control_rev, simp)
    apply (erule insertE, simp only:, rule reads_aep3_via_r, rule reads_lrefl)
    apply simp
    (* forward *)
    apply (rule subsetI)
    apply (erule subjectReads.induct)
    apply (simp, blast?)+
done

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

lemma r_affects_aep3 : "partition_label AEP3 \<in> subjectAffects SACAuthGraph (partition_label R)"
  apply (rule_tac l="partition_label R" and auth="Receive" in affects_ep)
  apply simp_all
done

lemma r_affects : "subjectAffects SACAuthGraph (partition_label R) = {partition_label NicB, partition_label NicD, partition_label R, partition_label RM, partition_label NicA, partition_label AEP3}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, rule r_affects_bd, simp)
  apply (erule insertE, rule r_affects_bd, simp)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule r_affects_rm)
  apply (erule insertE, simp only:, rule r_affects_a)
  apply (erule insertE, simp only:, rule r_affects_aep3)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp, blast?)+
 sorry

subsection {* RM reads/affects *}

lemma rm_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label RM)" 
  apply (rule_tac a="partition_label RM" and auth="Receive" and ep="partition_label EP" in read_sync_ep_read_senders)
  apply (simp_all add:reads_ep)
done

lemma rm_reads_c : "partition_label NicC \<in> subjectReads SACAuthGraph (partition_label RM)"
  apply (rule_tac t="partition_label SC" in reads_read_thread_read_pages)
  apply (rule rm_reads_sc, simp)
done

lemma rm_reads : "subjectReads SACAuthGraph (partition_label RM) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3}"
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
  apply (erule insertE, simp only:, rule reads_aep1_via_sc, rule rm_reads_sc)
  apply (erule insertE, simp only:, rule reads_aep2_via_rm, rule reads_lrefl)
  apply (erule insertE, simp only:, rule reads_aep3_via_r, rule reads_read, simp)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectReads.induct)
  apply (simp, blast?)+
done

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

lemma rm_affects_aep2 : "partition_label AEP2 \<in> subjectAffects SACAuthGraph (partition_label RM)"
  apply (rule_tac l="partition_label RM" and auth="Receive" in affects_ep)
  apply simp_all
done

lemma rm_affects : "subjectAffects SACAuthGraph (partition_label RM) = {partition_label NicA, partition_label NicB, partition_label NicD, partition_label R, partition_label SC, partition_label EP, partition_label RM, partition_label AEP2}"
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
  apply (erule insertE, simp only:, rule rm_affects_aep2)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp, blast?)+
  sorry

subsection {* SC *}

lemma sc_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label SC)"
  apply (rule_tac a="partition_label SC" and ep="partition_label EP" and auth="SyncSend" and b="partition_label RM" in read_sync_ep_read_receivers)
  apply (simp_all add:reads_ep)
done

lemma sc_reads : "subjectReads SACAuthGraph (partition_label SC) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3}"
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
  apply (erule insertE, simp only:, rule reads_aep1_via_sc, rule reads_lrefl)
  apply (erule insertE, simp only:, rule reads_aep2_via_rm, rule sc_reads_rm)
  apply (erule insertE, simp only:, rule reads_aep3_via_r, rule reads_all_rm_controlled_subjects, rule sc_reads_rm, simp)
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

lemma sc_affects : "subjectAffects SACAuthGraph (partition_label SC) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1}"
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

subsection {* EP *}

lemma ep_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label EP)"
  apply (rule_tac a="partition_label EP" and ep="partition_label EP" and auth="Receive" in read_sync_ep_read_senders)
  apply (simp, simp, rule reads_lrefl, simp_all)
done

lemma ep_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label EP)"
  apply (rule_tac a="partition_label SC" and ep="partition_label EP" and b="partition_label RM" and auth="SyncSend" in read_sync_ep_read_receivers)
  apply (simp, simp, rule reads_lrefl, simp)
done

lemma ep_reads_c : "partition_label NicC \<in> subjectReads SACAuthGraph (partition_label EP)"
  apply (rule_tac t="partition_label SC" and p="partition_label NicC" in reads_read_thread_read_pages)
  apply (rule ep_reads_sc, simp)
done

lemma ep_reads : "subjectReads SACAuthGraph (partition_label EP) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3}"
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
  apply (erule insertE, simp only:, rule reads_aep1_via_sc, rule ep_reads_sc)
  apply (erule insertE, simp only:, rule reads_aep2_via_rm, rule ep_reads_rm)
  apply (erule insertE, simp only:, rule reads_aep3_via_r, rule reads_all_rm_controlled_subjects, rule ep_reads_rm, simp)
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

lemma ep_affects_rm_controls : "x \<in> RMControls \<Longrightarrow> x \<in> subjectAffects SACAuthGraph (partition_label EP)"
  apply (rule_tac l="partition_label EP" and ep="partition_label EP" and auth="SyncSend" and l'="partition_label RM" in affects_send)
  apply (simp_all)
done

lemma ep_affects: "subjectAffects SACAuthGraph (partition_label EP) = {partition_label EP, partition_label SC, partition_label NicC} \<union> RMControls"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule UnE)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule ep_affects_sc)
  apply (erule insertE, simp only:, rule ep_affects_c, simp)
  apply (rule ep_affects_rm_controls, simp)
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
  sorry

subsection {* AEP1,2,3 *}

subsubsection {* AEP1 reads SC, EP, RM, R*}

lemma aep1_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label AEP1)"
  apply (rule_tac ep="partition_label AEP1" and auth="SyncSend" and a="partition_label AEP1" in read_sync_ep_read_receivers)
  apply (simp, simp, rule reads_lrefl, simp)
done

lemma aep1_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label AEP1)"
  apply (rule_tac ep="partition_label EP" and auth="SyncSend" and t="partition_label SC" and auth'="Reset" and a="partition_label EP" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp, rule aep1_reads_sc)
done

lemma aep1_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label AEP1)"
  apply (rule_tac b="partition_label RM" and ep="partition_label EP" and auth="SyncSend" and a="partition_label SC" in read_sync_ep_read_receivers)
  apply (simp, simp, rule aep1_reads_ep, simp)
done

subsubsection {* AEP2 reads SC, EP, RM, R *}

lemma aep2_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label AEP2)"
  apply (rule_tac ep="partition_label AEP2" and auth="SyncSend" and a="partition_label AEP2" in read_sync_ep_read_receivers)
  apply (simp, simp, rule reads_lrefl, simp)
done

lemma aep2_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label AEP2)"
  apply (rule_tac ep="partition_label EP" and auth="Receive" and t="partition_label RM" and auth'="Reset" and a="partition_label EP" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp, rule aep2_reads_rm)
done

lemma aep2_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label AEP2)"
  apply (rule_tac b="partition_label SC" and ep="partition_label EP" and auth="Reset" and a="partition_label EP" in read_sync_ep_read_senders)
  apply (simp, simp, rule aep2_reads_ep, simp)
done

subsubsection {* AEP3 reads SC, EP, RM, R *}

lemma aep3_reads_r : "partition_label R \<in> subjectReads SACAuthGraph (partition_label AEP3)"
  apply (rule_tac ep="partition_label AEP3" and auth="SyncSend" and a="partition_label AEP3" in read_sync_ep_read_receivers)
  apply (simp, simp, rule reads_lrefl, simp)
done

lemma aep3_reads_rm : "partition_label RM \<in> subjectReads SACAuthGraph (partition_label AEP3)"
  apply (rule_tac b="partition_label R" in reads_read_page_read_thread)
  apply (rule aep3_reads_r, simp)
done

lemma aep3_reads_ep : "partition_label EP \<in> subjectReads SACAuthGraph (partition_label AEP3)"
  apply (rule_tac t="partition_label RM" and auth="Receive" and auth'="SyncSend" and a="partition_label SC" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp, rule aep3_reads_rm)
done

lemma aep3_reads_sc : "partition_label SC \<in> subjectReads SACAuthGraph (partition_label AEP3)"
  apply (rule_tac ep="partition_label EP" and auth="Receive" and a="partition_label RM" in read_sync_ep_read_senders)
  apply (simp, simp, rule aep3_reads_ep, simp)
done

subsubsection {* AEP1,2,3 reads C *}

lemma aep123_reads_c : "x \<in> {AEP1, AEP2, AEP3} \<Longrightarrow> partition_label NicC \<in> subjectReads SACAuthGraph (partition_label x)"
  apply (rule_tac t="partition_label SC" in reads_read_thread_read_pages)
  apply (erule insertE, simp only:, rule aep1_reads_sc, erule insertE, simp only:, rule aep2_reads_sc, erule insertE, simp only:, rule aep3_reads_sc, simp)
  apply simp
done

subsubsection {* AEP1,2,3 reads each other *}

lemma aep13_reads_aep2 : "l \<in> {AEP1, AEP3} \<Longrightarrow> partition_label AEP2 \<in> subjectReads SACAuthGraph (partition_label l)"
  apply (rule_tac t="partition_label RM" and auth="Receive" and auth'="Reset" and a="partition_label AEP2" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp)
  apply (erule insertE, simp only:, rule aep1_reads_rm, erule insertE, simp only:, rule aep3_reads_rm, simp)
done

lemma aep12_reads_aep3 : "l \<in> {AEP1, AEP2} \<Longrightarrow> partition_label AEP3 \<in> subjectReads SACAuthGraph (partition_label l)"
  apply (rule_tac t="partition_label R" and auth="Receive" and auth'="Reset" and a="partition_label AEP3" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp)
  apply (erule insertE, simp only:, rule reads_all_rm_controlled_subjects, rule aep1_reads_rm, simp, erule insertE, simp only:, rule reads_all_rm_controlled_subjects, rule aep2_reads_rm, simp_all)
done

lemma aep23_reads_aep1 : "l \<in> {AEP2, AEP3} \<Longrightarrow> partition_label AEP1 \<in> subjectReads SACAuthGraph (partition_label l)"
  apply (rule_tac t="partition_label SC" and auth="Receive" and auth'="Reset" and a="partition_label AEP1" in reads_read_queued_thread_read_ep)
  apply (simp, simp, simp, simp)
  apply (erule insertE, simp only:, rule aep2_reads_sc, erule insertE, simp only:, rule aep3_reads_sc, simp)
done

subsubsection {* AEP1,2,3 reads *}
declare SACAuthGraph_def[simp del]

lemma aep123_reads_rm : "l \<in> {AEP1, AEP2, AEP3} \<Longrightarrow> partition_label RM \<in> subjectReads SACAuthGraph (partition_label l)"
by (auto simp:aep1_reads_rm aep2_reads_rm aep3_reads_rm)

lemma aep123_reads_sc : "l \<in> {AEP1, AEP2, AEP3} \<Longrightarrow> partition_label SC \<in> subjectReads SACAuthGraph (partition_label l)"
by (auto simp:aep1_reads_sc aep2_reads_sc aep3_reads_sc)

lemma aep123_reads_ep : "l \<in> {AEP1, AEP2, AEP3} \<Longrightarrow> partition_label EP \<in> subjectReads SACAuthGraph (partition_label l)"
by (auto simp:aep1_reads_ep aep2_reads_ep aep3_reads_ep)

lemma aep123_reads_aep123 : "\<lbrakk>l \<in> {AEP1, AEP2, AEP3}; x \<in> {AEP1, AEP2, AEP3}\<rbrakk> \<Longrightarrow> partition_label l \<in> subjectReads SACAuthGraph (partition_label x)"
by (auto simp:aep12_reads_aep3 aep13_reads_aep2 aep23_reads_aep1 reads_lrefl)

lemma aep123_reads : "l \<in> {AEP1, AEP2, AEP3} \<Longrightarrow> subjectReads SACAuthGraph (partition_label l) = {partition_label NicB, partition_label RM, partition_label R, partition_label NicA, partition_label NicD, partition_label EP, partition_label SC, partition_label NicC, partition_label AEP1, partition_label AEP2, partition_label AEP3}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule aep123_reads_rm, simp, simp)
  apply (erule_tac a=x in insertE, simp only:, rule aep123_reads_rm, simp)
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule aep123_reads_rm, simp, simp)  
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule aep123_reads_rm, simp, simp)  
  apply (erule_tac a=x in insertE, rule reads_all_rm_controlled_subjects, rule aep123_reads_rm, simp, simp)  
  apply (erule_tac a=x in insertE, simp only:, rule aep123_reads_ep, simp)
  apply (erule_tac a=x in insertE, simp only:, rule aep123_reads_sc, simp)
  apply (erule_tac a=x in insertE, simp only:, rule aep123_reads_c, simp)
  apply (auto simp:aep123_reads_aep123)[1]
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectReads.induct)
  by (simp add:SACAuthGraph_def, blast?)+

subsubsection {* AEP1,2,3 affects *}

lemma aep1_affects_sc : "partition_label SC \<in> subjectAffects SACAuthGraph (partition_label AEP1)"
  apply (rule_tac l''="partition_label SC" and l'="partition_label SC" and ep="partition_label AEP1" and auth="AsyncSend" and l="partition_label AEP1" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma aep1_affects_c : "partition_label NicC \<in> subjectAffects SACAuthGraph (partition_label AEP1)"
  apply (rule_tac l'="partition_label SC" and ep="partition_label AEP1" and l="partition_label AEP1" and auth="AsyncSend" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma aep1_affects : "subjectAffects SACAuthGraph (partition_label AEP1) = {partition_label AEP1, partition_label SC, partition_label NicC}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule aep1_affects_sc)
  apply (erule insertE, simp only:, rule aep1_affects_c)
  apply simp
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
done

lemma aep2_affects_rm : "partition_label RM \<in> subjectAffects SACAuthGraph (partition_label AEP2)"
  apply (rule_tac l'="partition_label RM" and ep="partition_label AEP2" and auth="AsyncSend" and l="partition_label AEP2" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma aep2_affects_rm_controls : "x \<in> RMControls \<Longrightarrow> x \<in> subjectAffects SACAuthGraph (partition_label AEP2)"
  apply (rule_tac l="partition_label AEP2" and ep="partition_label AEP2" and auth="SyncSend" and l'="partition_label RM" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma aep2_affects : "subjectAffects SACAuthGraph (partition_label AEP2) = {partition_label AEP2, partition_label RM} \<union> RMControls"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI)
  apply (erule UnE)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule aep2_affects_rm, simp)
  apply (rule aep2_affects_rm_controls, simp)
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
  sorry

lemma aep3_affects_r : "partition_label R \<in> subjectAffects SACAuthGraph (partition_label AEP3)"
  apply (rule_tac l'="partition_label R" and ep="partition_label AEP3" and auth="AsyncSend" and l="partition_label AEP3" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma aep3_affects_bd : "l \<in> {NicB, NicD} \<Longrightarrow> partition_label l \<in> subjectAffects SACAuthGraph (partition_label AEP3)"
  apply (rule_tac l'="partition_label R" and ep="partition_label AEP3" and l="partition_label AEP3" and auth="AsyncSend" in affects_send)
  apply (simp add:SACAuthGraph_def, blast?)+
done

lemma aep3_affects : "subjectAffects SACAuthGraph (partition_label AEP3) = {partition_label AEP3, partition_label R} \<union> {partition_label NicB, partition_label NicD}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI, erule UnE)
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule aep3_affects_r, simp)
  apply (auto simp:aep3_affects_bd)[1]
  (* forward *)
  apply (rule subsetI)
  apply (erule subjectAffects.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
done

subsection {* T *}

lemma t_reads : "subjectReads SACAuthGraph (partition_label T) = {partition_label T}"
  apply (rule subset_antisym)
  defer
  apply (rule subsetI, erule insertE, simp only:, rule reads_lrefl, simp)
  apply (rule subsetI, erule subjectReads.induct)
  apply (simp add:SACAuthGraph_def, blast?)+
done

lemma t_affects_aep123 : "l \<in> {AEP1, AEP2, AEP3} \<Longrightarrow>  partition_label l \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac auth="AsyncSend" in affects_ep)
  apply (simp_all add:SACAuthGraph_def, blast)
done

lemma t_affects_sc : "partition_label SC \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label SC" and l'="partition_label SC" and ep="partition_label AEP1" and auth="AsyncSend" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_rm : "partition_label RM \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label RM" and l'="partition_label RM" and ep="partition_label AEP2" and auth="AsyncSend" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_r : "partition_label R \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label R" and l'="partition_label R" and ep="partition_label AEP3" and auth="AsyncSend" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_c : "partition_label NicC \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label NicC" and l'="partition_label SC" and ep="partition_label AEP1" and auth="AsyncSend" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_a : "partition_label NicA \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l''="partition_label NicA" and l'="partition_label RM" and ep="partition_label AEP2" and auth="AsyncSend" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def)
done

lemma t_affects_bd : "l \<in> {NicB, NicD} \<Longrightarrow> partition_label l \<in> subjectAffects SACAuthGraph (partition_label T)"
  apply (rule_tac l'="partition_label R" and ep="partition_label AEP3" and auth="AsyncSend" and l="partition_label T" in affects_send)
  apply (simp_all add:SACAuthGraph_def, blast)
done

lemma t_affects : "subjectAffects SACAuthGraph (partition_label T) = {partition_label AEP1, partition_label AEP2, partition_label AEP3} \<union> {partition_label T, partition_label SC, partition_label RM, partition_label R, partition_label NicA, partition_label NicB, partition_label NicD, partition_label NicC}"
  apply (rule subset_antisym)
  defer
  (* backward *)
  apply (rule subsetI, erule UnE)
  apply (auto simp:t_affects_aep123)[1]
  apply (erule insertE, simp only:, rule affects_lrefl)
  apply (erule insertE, simp only:, rule t_affects_sc)
  apply (erule insertE, simp only:, rule t_affects_rm)
  apply (erule insertE, simp only:, rule t_affects_r)
  apply (erule insertE, simp only:, rule t_affects_a)
  apply (erule insertE, simp only:, rule t_affects_bd, simp)
  apply (erule insertE, simp only:, rule t_affects_bd, simp)
  apply (erule insertE, simp only:, rule t_affects_c)
  apply simp
  (* forward *)
  apply (rule subsetI, erule subjectAffects.induct)
  (*apply (simp add:SACAuthGraph_def, blast?)+*)
  sorry

subsection {* Policy *}

declare SACAuthGraph_def [simp del] 

lemmas SAC_reads = sc_reads ep_reads c_reads rm_reads r_reads abd_reads aep123_reads t_reads

lemmas SAC_affects = sc_affects ep_affects c_affects rm_affects r_affects abd_affects aep1_affects aep2_affects aep3_affects t_affects

definition SACFlowDoms where
  "SACFlowDoms \<equiv> {Partition EP, Partition SC, Partition NicC, Partition RM, Partition R, Partition NicA, Partition NicB, Partition NicD, Partition AEP1, Partition AEP2, Partition AEP3}"
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

lemma SAC_partsSubjectAffects_T : "(partsSubjectAffects SACAuthGraph T) = {Partition AEP1, Partition AEP2, Partition AEP3} \<union> {Partition T, Partition SC, Partition RM, Partition R, Partition NicA, Partition NicB, Partition NicD, Partition NicC, Partition EP}"
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
    apply (clarify, simp del:SACAuthGraph_def)
    apply (rule policy_affects)
    apply (case_tac l, case_tac[1-12] k, auto simp:SAC_partsSubjectAffects_T SAC_partsSubjectAffects_exceptT)
done

end
