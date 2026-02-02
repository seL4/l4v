(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ExampleSystem
imports ArchAccess_AC
begin

context begin interpretation Arch . (*FIXME: arch-split*)

definition
  nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list option"
where
  "nat_to_bl bits n \<equiv>
    if n \<ge> 2^bits then
      None
    else
      Some $ bin_to_bl bits (of_nat n)"

lemma nat_to_bl_id [simp]: "nat_to_bl (size (x :: (('a::len) word))) (unat x) = Some (to_bl x)"
  apply (clarsimp simp: nat_to_bl_def to_bl_def)
  apply (auto simp: le_def word_size)
  done


(*---------------------------------------------------------*)

subsection \<open>Purpose\<close>

text \<open>

This file defines some example systems using the access control
definitions. The aim is a sanity check of the AC definitions, to
ensure they enable to reason about reasonable systems.

In particular, we want to make sure that

  . the function state_objs_to_policy does not connect everything to
  everything (Example 1)
  . we can talk about components sharing cnodes
  . we can talk about components sharing frames
  . we can have more than 1 untrusted component
  . we can have an EP between two untrusted components

\<close>

(*---------------------------------------------------------*)

subsection \<open>Generic functions / lemmas\<close>


text \<open>Defining the authority between labels.

In addition to the intuitive authority we want, we need to add all the
authority required to have a wellformed graph. So we define
complete_AgentAuthGraph to add these 'extra' authorities (at least all
the ones not depending on the current label). These are:

  . self-authority (each label needs all the authorities to itself).
  . if Control edge is present between 2 labels then we add all
    authorities between them.
  . Control authority is transitive: we add an Control edge
    between 2 labels if we can connect them via Control
    edges. Actually we add all authorities because of the second
    clause.

\<close>


definition
  complete_AuthGraph :: "'a auth_graph \<Rightarrow> 'a set \<Rightarrow> 'a auth_graph"
where
  "complete_AuthGraph g ls \<equiv>
     g \<union> {(l,a,l) | a l. l \<in> ls}"

text \<open>converting a nat to a bool list of size 10 - for the cnodes\<close>

definition
  the_nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list"
where
  "the_nat_to_bl sz n \<equiv> the (nat_to_bl sz n)"

definition
  the_nat_to_bl_10  :: "nat \<Rightarrow> bool list"
where
  "the_nat_to_bl_10 n \<equiv> the_nat_to_bl 10 n"

lemma tcb_cnode_index_nat_to_bl:
  "n<10 \<Longrightarrow> the_nat_to_bl_10 n \<noteq> tcb_cnode_index n"
  by (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def
                     tcb_cnode_index_def
                     nat_to_bl_def to_bl_def bin_to_bl_aux_def)


(*---------------------------------------------------------*)
subsection \<open>Example 1\<close>

text \<open>

This example aims at checking that we can extract a reasonable policy
from the state, i.e. that the function state_objs_to_policy does not connect
everything to everything.

This example is a system Sys1 made of 2 main components UT1 and T1,
connected through and endpoint EP1. EP1 is made of one single kernel
object: obj1_9, the endpoint. Both UT1 and T1 contains:

  . one TCB (obj1_3079 and obj1_3080 resp.)
  . one vspace made up of one page directory (obj1_6063 and obj1_3065 resp.)
  . each pd contains a single page table (obj1_3072 and obj1_3077 resp.)
  . one cspace made up of one cnode (obj1_6 and obj1_7 resp.)
  . each cspace contains 4 caps:
         one to the tcb
         one to the cnode itself
         one to the vspace
         one to the ep

UT1 can send to the ep while T1 can receive from it.

Attempt to ASCII art:


          --------    ----                      ----     --------
          |       |   |  |                      |  |     |      |
          V       |   |  V     S             R  |  V     |      V
obj1_3079(tcb)-->obj1_6(cnode)--->obj1_9(ep)<---obj1_7(cnode)<--obj1_3080(tcb)
  |               |                                   |            |
  V               |                                   |            V
obj1_3063(pd)<-----                                    -------> obj1_3065(pd)
  |                                                                |
  V                                                                V
obj1_3072(pt)                                                      obj1_3077(pt)


(the references are derived from the dump of the SAC system)


The aim is to be able to prove

  pas_refined Sys1PAS s1

where Sys1PAS is the label graph defining the AC policy for Sys1 and
s1 is the state of Sys1 described above.

This shows that the aag extracted from s1 (by state_objs_to_policy) is
included in the policy graph Sys1PAS.

\<close>


subsubsection \<open>Defining the State\<close>

text \<open>We need to define the asids of each pd and pt to ensure that
the object is included in the right ASID-label\<close>

text \<open>UT1's ASID\<close>

definition
  asid1_3063 :: machine_word
where
  "asid1_3063 \<equiv> 1<<asid_low_bits"

text \<open>T1's ASID\<close>

definition
  asid1_3065 :: machine_word
where
  "asid1_3065 \<equiv> 2<<asid_low_bits"

lemma "asid_high_bits_of asid1_3065 \<noteq> asid_high_bits_of asid1_3063"
by (simp add: asid1_3063_def asid_high_bits_of_def asid1_3065_def asid_low_bits_def)


text \<open>UT1's CSpace\<close>

definition
  caps1_6 :: cnode_contents
where
  "caps1_6 \<equiv>
   (empty_cnode 10)
      ( (the_nat_to_bl_10 1)
            \<mapsto> ThreadCap 3079,
        (the_nat_to_bl_10 2)
            \<mapsto> CNodeCap 6 undefined undefined,
        (the_nat_to_bl_10 3)
            \<mapsto> ArchObjectCap (PageDirectoryCap 3063
                                             (Some asid1_3063)),
        (the_nat_to_bl_10 318)
            \<mapsto> EndpointCap  9 0 {AllowSend} )"


definition
  obj1_6 :: kernel_object
where
  "obj1_6 \<equiv> CNode 10 caps1_6"

text \<open>T1's Cspace\<close>

definition
  caps1_7 :: cnode_contents
where
  "caps1_7 \<equiv>
   (empty_cnode 10)
      ( (the_nat_to_bl_10 1)
            \<mapsto> ThreadCap 3080,
        (the_nat_to_bl_10 2)
            \<mapsto> CNodeCap 7 undefined undefined,
        (the_nat_to_bl_10 3)
           \<mapsto> ArchObjectCap (PageDirectoryCap 3065
                                            (Some asid1_3065)),
        (the_nat_to_bl_10 318)
           \<mapsto> EndpointCap  9 0 {AllowRecv}) "

definition
  obj1_7 :: kernel_object
where
  "obj1_7 \<equiv> CNode 10 caps1_7"


text \<open>endpoint between UT1 and T1\<close>

definition
  obj1_9 :: kernel_object
where
  "obj1_9 \<equiv> Endpoint IdleEP"


text \<open>UT1's VSpace (PageDirectory)\<close>

definition
  pt1_3072 :: "word8 \<Rightarrow> pte "
where
  "pt1_3072 \<equiv> (\<lambda>_. InvalidPTE)"

definition
  obj1_3072 :: kernel_object
where
  "obj1_3072 \<equiv> ArchObj (PageTable pt1_3072)"


definition
  pd1_3063 :: "12 word \<Rightarrow> pde "
where
  "pd1_3063 \<equiv>
    (\<lambda>_. InvalidPDE)
     (0 := PageTablePDE
              (addrFromPPtr 3072)
              undefined
              undefined )"

(* used addrFromPPtr because proof gives me ptrFromAddr.. TODO: check
if it's right *)

definition
  obj1_3063 :: kernel_object
where
  "obj1_3063 \<equiv> ArchObj (PageDirectory pd1_3063)"


text \<open>T1's VSpace (PageDirectory)\<close>


definition
  pt1_3077 :: "word8 \<Rightarrow> pte "
where
  "pt1_3077 \<equiv>
    (\<lambda>_. InvalidPTE)"


definition
  obj1_3077 :: kernel_object
where
  "obj1_3077 \<equiv> ArchObj (PageTable pt1_3077)"


definition
  pd1_3065 :: "12 word \<Rightarrow> pde "
where
  "pd1_3065 \<equiv>
    (\<lambda>_. InvalidPDE)
     (0 := PageTablePDE
             (addrFromPPtr 3077)
             undefined
             undefined )"

(* used addrFromPPtr because proof gives me ptrFromAddr.. TODO: check
if it's right *)

definition
  obj1_3065 :: kernel_object
where
  "obj1_3065 \<equiv> ArchObj (PageDirectory pd1_3065)"


text \<open>UT1's tcb\<close>

definition
  obj1_3079 :: kernel_object
where
  "obj1_3079 \<equiv>
   TCB \<lparr>
     tcb_ctable             = CNodeCap 6 undefined undefined,
     tcb_vtable             = ArchObjectCap (PageDirectoryCap 3063 (Some asid1_3063)),
     tcb_reply              = ReplyCap 3079 True {AllowGrant,AllowWrite}, \<comment> \<open>master reply cap to itself\<close>
     tcb_caller             = NullCap,
     tcb_ipcframe           = NullCap,
     tcb_state              = Running,
     tcb_fault_handler      = undefined,
     tcb_ipc_buffer         = undefined,
     tcb_fault              = undefined,
     tcb_bound_notification = None,
     tcb_mcpriority         = undefined,
     tcb_priority           = undefined,
     tcb_time_slice         = undefined,
     tcb_domain             = 0,
     tcb_flags              = undefined,
     tcb_arch               = \<lparr>tcb_context = undefined\<rparr> \<rparr>"


text \<open>T1's tcb\<close>

definition
  obj1_3080 :: kernel_object
where
  "obj1_3080 \<equiv>
   TCB \<lparr>
     tcb_ctable             = CNodeCap 7 undefined undefined,
     tcb_vtable             = ArchObjectCap (PageDirectoryCap 3065 (Some asid1_3065)),
     tcb_reply              = ReplyCap 3080 True {AllowGrant,AllowWrite}, \<comment> \<open>master reply cap to itself\<close>
     tcb_caller             = NullCap,
     tcb_ipcframe           = NullCap,
     tcb_state              = BlockedOnReceive 9 \<lparr> receiver_can_grant = False \<rparr>,
     tcb_fault_handler      = undefined,
     tcb_ipc_buffer         = undefined,
     tcb_fault              = undefined,
     tcb_bound_notification = None,
     tcb_mcpriority         = undefined,
     tcb_priority           = undefined,
     tcb_time_slice         = undefined,
     tcb_domain             = 0,
     tcb_flags              = undefined,
     tcb_arch               = \<lparr>tcb_context = undefined\<rparr>\<rparr>"

definition
 "obj1_10 \<equiv> CNode 10 (Map.empty([] \<mapsto> cap.NullCap))"


(* the boolean in BlockedOnReceive is True if the object can receive but not send.
but Tom says it only matters if the sender can grant - which is not the case of the UT1 - I think *)

definition
  kh1 :: kheap
where
  "kh1 \<equiv> [ 6 \<mapsto> obj1_6,
          7 \<mapsto> obj1_7,
          9 \<mapsto> obj1_9,
          10 \<mapsto> obj1_10,
          3063 \<mapsto> obj1_3063,
          3065 \<mapsto> obj1_3065,
          3072 \<mapsto> obj1_3072,
          3077 \<mapsto> obj1_3077,
          3079 \<mapsto> obj1_3079,
          3080 \<mapsto> obj1_3080 ]"

lemmas kh1_obj_def =
  obj1_6_def obj1_7_def obj1_9_def obj1_10_def obj1_3063_def obj1_3065_def
  obj1_3072_def obj1_3077_def obj1_3079_def obj1_3080_def

definition exst1 :: "det_ext" where
  "exst1 \<equiv> \<lparr>work_units_completed_internal = undefined,
             cdt_list_internal = undefined\<rparr>"

definition
  s1 :: "det_ext state"
where
  "s1 \<equiv>  \<lparr>
    kheap = kh1,
    cdt = Map.empty,
    is_original_cap = undefined,
    cur_thread = undefined,
    idle_thread = undefined,
    scheduler_action = undefined,
    domain_list = undefined,
    domain_index = undefined,
    domain_start_index = undefined,
    cur_domain = undefined,
    domain_time = undefined,
    ready_queues = undefined,
    machine_state = undefined,
    interrupt_irq_node = (\<lambda>_. 10),
    interrupt_states = undefined,
    arch_state = \<lparr>
        arm_asid_table = (\<lambda> x. None),
        arm_hwasid_table = undefined,
        arm_next_asid = undefined,
        arm_asid_map = undefined,
        arm_global_pd = undefined,
        arm_global_pts = undefined,
        arm_kernel_vspace = undefined
        \<rparr>,
     exst = exst1
    \<rparr>"


subsubsection \<open>Defining the policy graph\<close>


datatype Sys1Labels =
    UT1 | T1 | EP1 | IRQ1

definition
  Sys1AgentMap :: "Sys1Labels agent_map"
where
  "Sys1AgentMap \<equiv>
   (\<lambda>_. undefined)
     (6 := UT1,
      7 := T1,
      9 := EP1,
      10 := IRQ1,
      3063 := UT1,
      3065 := T1,
      3072 := UT1,
      3077 := T1,
      3079 := UT1,
      3080 := T1 )"

lemma Sys1AgentMap_simps:
  "Sys1AgentMap 6 = UT1"
      "Sys1AgentMap 7 = T1"
      "Sys1AgentMap 9 = EP1"
      "Sys1AgentMap 10 = IRQ1"
      "Sys1AgentMap 3063 = UT1"
      "Sys1AgentMap 3065 = T1"
      "Sys1AgentMap 3072 = UT1"
      "Sys1AgentMap 3077 = T1"
      "Sys1AgentMap 3079 = UT1"
      "Sys1AgentMap 3080 = T1"
  unfolding Sys1AgentMap_def by simp_all

definition
  Sys1AuthGraph_aux :: "Sys1Labels auth_graph"
where
    "Sys1AuthGraph_aux \<equiv>
  { (UT1, auth.SyncSend,    EP1),
    (UT1, auth.Reset,   EP1),
    (T1,  auth.Receive, EP1),
    (T1,  auth.Reset,   EP1) }"

definition
  Sys1AuthGraph:: "Sys1Labels auth_graph"
where
    "Sys1AuthGraph \<equiv> complete_AuthGraph Sys1AuthGraph_aux {T1, UT1}"


definition
  Sys1ASIDMap :: "Sys1Labels agent_asid_map"
where
  "Sys1ASIDMap \<equiv>
    (\<lambda>x. if (asid_high_bits_of x = asid_high_bits_of asid1_3063)
          then UT1
         else if (asid_high_bits_of x = asid_high_bits_of asid1_3065)
          then T1 else undefined)"

definition Sys1DomainMap :: "Sys1Labels agent_domain_map" where
  "Sys1DomainMap \<equiv> (\<lambda>_. {}) (0 := {UT1, T1})"

definition Sys1PAS :: "Sys1Labels PAS" where
  "Sys1PAS \<equiv> \<lparr> pasObjectAbs = Sys1AgentMap, pasASIDAbs = Sys1ASIDMap, pasIRQAbs = (\<lambda>_. IRQ1),
               pasPolicy = Sys1AuthGraph, pasSubject = UT1, pasMayActivate = True, pasMayEditReadyQueues = True,
               pasMaySendIrqs = True, pasDomainAbs = Sys1DomainMap \<rparr>"

subsubsection \<open>Proof of pas_refined for Sys1\<close>

lemma caps1_7_well_formed: "well_formed_cnode_n 10 caps1_7"
 apply (clarsimp simp: caps1_7_def well_formed_cnode_n_def)
 apply (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def nat_to_bl_def)
 apply (clarsimp simp: empty_cnode_def dom_def)
 apply (rule set_eqI, clarsimp)
 apply (rule iffI)
  apply (elim disjE, insert size_bin_to_bl, simp_all)[1]
 apply clarsimp
done

lemma caps1_6_well_formed: "well_formed_cnode_n 10 caps1_6"
 apply (clarsimp simp: caps1_6_def well_formed_cnode_n_def)
 apply (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def nat_to_bl_def)
 apply (clarsimp simp: empty_cnode_def dom_def)
 apply (rule set_eqI, clarsimp)
 apply (rule iffI)
  apply (elim disjE, insert size_bin_to_bl, simp_all)[1]
 apply clarsimp
done

lemma s1_caps_of_state :
  "caps_of_state s1 p = Some cap \<Longrightarrow>
     cap = NullCap \<or>
     (p,cap) \<in>
       { ((6::obj_ref,(the_nat_to_bl_10 1)),  ThreadCap 3079),
         ((6::obj_ref,(the_nat_to_bl_10 2)),  CNodeCap 6 undefined undefined),
         ((6::obj_ref,(the_nat_to_bl_10 3)),  ArchObjectCap (PageDirectoryCap 3063 (Some asid1_3063))),
         ((6::obj_ref,(the_nat_to_bl_10 318)),EndpointCap  9 0 {AllowSend}),
         ((7::obj_ref,(the_nat_to_bl_10 1)),  ThreadCap 3080),
         ((7::obj_ref,(the_nat_to_bl_10 2)),  CNodeCap 7 undefined undefined),
         ((7::obj_ref,(the_nat_to_bl_10 3)),  ArchObjectCap (PageDirectoryCap 3065 (Some asid1_3065))),
         ((7::obj_ref,(the_nat_to_bl_10 318)),EndpointCap  9 0 {AllowRecv}) ,
         ((3079::obj_ref, (tcb_cnode_index 0)), CNodeCap 6 undefined undefined ),
         ((3079::obj_ref, (tcb_cnode_index 1)), ArchObjectCap (PageDirectoryCap 3063 (Some asid1_3063))),
         ((3079::obj_ref, (tcb_cnode_index 2)), ReplyCap 3079 True {AllowGrant,AllowWrite}),
         ((3079::obj_ref, (tcb_cnode_index 3)), NullCap),
         ((3079::obj_ref, (tcb_cnode_index 4)), NullCap),
         ((3080::obj_ref, (tcb_cnode_index 0)), CNodeCap 7 undefined undefined ),
         ((3080::obj_ref, (tcb_cnode_index 1)), ArchObjectCap (PageDirectoryCap 3065 (Some asid1_3065))),
         ((3080::obj_ref, (tcb_cnode_index 2)), ReplyCap 3080 True {AllowGrant,AllowWrite}),
         ((3080::obj_ref, (tcb_cnode_index 3)), NullCap),
         ((3080::obj_ref, (tcb_cnode_index 4)), NullCap)} "
  apply (insert caps1_7_well_formed)
  apply (insert caps1_6_well_formed)
  apply (simp add: caps_of_state_cte_wp_at cte_wp_at_cases s1_def kh1_def kh1_obj_def)
  apply (case_tac p, clarsimp)
  apply (clarsimp split: if_splits)
     apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def
                     split: if_split_asm)+
   apply (clarsimp simp: caps1_7_def split: if_splits)
  apply (clarsimp simp: caps1_6_def cte_wp_at_cases  split: if_splits)
done


lemma Sys1_wellformed: "pas_wellformed Sys1PAS"
 apply (clarsimp simp: Sys1PAS_def
                    policy_wellformed_def
                    Sys1AuthGraph_def
                    Sys1AuthGraph_aux_def
                    complete_AuthGraph_def)
 apply blast
 done

lemma tcb_states_of_state_1:
  "tcb_states_of_state s1 = [0xC08 \<mapsto> thread_state.BlockedOnReceive 9 \<lparr> receiver_can_grant = False \<rparr>,  0xC07 \<mapsto> thread_state.Running ]"
  unfolding s1_def tcb_states_of_state_def
  apply (rule ext)
  apply (simp add: get_tcb_def)
  apply (simp add: kh1_def kh1_obj_def )
  done

lemma thread_bound_ntfns_1:
  "thread_bound_ntfns s1 = Map.empty"
  unfolding s1_def thread_bound_ntfns_def
  apply (rule ext)
  apply (simp add: get_tcb_def)
  apply (simp add: kh1_def kh1_obj_def )
  done

declare AllowSend_def[simp] AllowRecv_def[simp]

lemma etcbs_of_s1:
  "etcbs_of s1 = [3079 \<mapsto> etcb_of (un_TCB obj1_3079), 3080 \<mapsto> etcb_of (un_TCB obj1_3080)]"
  by (fastforce simp: etcbs_of'_def s1_def kh1_def kh1_obj_def)

lemma domains_of_state_s1:
  "domains_of_state s1 = {(3079, 0), (3080, 0)}"
   by (fastforce simp: etcbs_of_s1 kh1_obj_def
                 elim: domains_of_state_aux.cases
                split: if_split_asm
               intro!: domtcbs)

lemma tcb_domain_map_wellformed_s1:
  "tcb_domain_map_wellformed Sys1PAS s1"
  by (clarsimp simp: tcb_domain_map_wellformed_aux_def Sys1PAS_def domains_of_state_s1
                        Sys1AgentMap_simps Sys1DomainMap_def)

lemma state_hyp_refs_of_s1_empty[simp]:
  "state_hyp_refs_of s1 = (\<lambda>_. {})"
  by (auto simp: state_hyp_refs_of_def hyp_refs_of_def split: option.splits kernel_object.splits)

lemma "pas_refined Sys1PAS s1"
  apply (clarsimp simp: pas_refined_def)
  apply (intro conjI)
       subgoal by (simp add: Sys1_wellformed)
      subgoal by (simp add: irq_map_wellformed_aux_def s1_def Sys1AgentMap_simps Sys1PAS_def)
     subgoal by (simp add: tcb_domain_map_wellformed_s1)
    apply (clarsimp simp: auth_graph_map_def
                           Sys1PAS_def
                           state_objs_to_policy_def
                           )+
    apply (erule state_bits_to_policy.cases, simp_all, clarsimp)
          apply (drule s1_caps_of_state, clarsimp)
          apply (simp add: Sys1AuthGraph_def complete_AuthGraph_def Sys1AuthGraph_aux_def)
          apply (elim disjE conjE; solves\<open>clarsimp simp: Sys1AgentMap_simps cap_auth_conferred_def cap_rights_to_auth_def\<close>)
         apply (drule s1_caps_of_state, clarsimp)
         apply (elim disjE; solves \<open>simp add: thread_bound_ntfns_def\<close>)
        apply (clarsimp simp: state_refs_of_def thread_st_auth_def tcb_states_of_state_1
               Sys1AuthGraph_def Sys1AgentMap_simps
               complete_AuthGraph_def
               Sys1AuthGraph_aux_def
               split: if_splits)
       apply (simp add:  thread_bound_ntfns_1)
      apply (simp add: s1_def) (* this is OK because cdt is empty..*)
     apply (simp add: s1_def) (* this is OK because cdt is empty..*)
    apply (fastforce simp: state_vrefs_def
                           vs_refs_no_global_pts_def
                           s1_def kh1_def  Sys1AgentMap_simps
                           kh1_obj_def comp_def pt1_3072_def pt1_3077_def pte_ref_def pde_ref2_def pd1_3065_def pd1_3063_def
                           Sys1AuthGraph_def ptr_range_def
                           complete_AuthGraph_def
                           Sys1AuthGraph_aux_def
                     dest!: graph_ofD
                     split: if_splits)
   apply (rule subsetI, clarsimp)
   apply (erule state_asids_to_policy_aux.cases)
     apply clarsimp
     apply (drule s1_caps_of_state, clarsimp)
     apply (simp add: Sys1AuthGraph_def complete_AuthGraph_def Sys1AuthGraph_aux_def Sys1PAS_def Sys1ASIDMap_def)
     apply (elim disjE conjE, simp_all add: Sys1AgentMap_simps cap_auth_conferred_def cap_rights_to_auth_def asid1_3065_def asid1_3063_def
       asid_low_bits_def asid_high_bits_of_def )[1]
    apply (clarsimp simp: state_vrefs_def
                           vs_refs_no_global_pts_def
                           s1_def kh1_def  Sys1AgentMap_simps
                           kh1_obj_def comp_def pt1_3072_def pt1_3077_def pte_ref_def pde_ref2_def pd1_3065_def pd1_3063_def
                           Sys1AuthGraph_def ptr_range_def
                           complete_AuthGraph_def
                           Sys1AuthGraph_aux_def
                     dest!: graph_ofD
                     split: if_splits)
   apply (clarsimp simp: s1_def)
  apply (rule subsetI, clarsimp)
  apply (erule state_irqs_to_policy_aux.cases)
  apply (simp add: Sys1AuthGraph_def complete_AuthGraph_def Sys1AuthGraph_aux_def Sys1PAS_def Sys1ASIDMap_def)
  apply (drule s1_caps_of_state)
  by (auto simp: Sys1AuthGraph_def complete_AuthGraph_def Sys1AuthGraph_aux_def Sys1PAS_def
                    Sys1ASIDMap_def Sys1AgentMap_simps cap_auth_conferred_def cap_rights_to_auth_def
                    asid1_3065_def asid1_3063_def asid_low_bits_def asid_high_bits_of_def)


(*---------------------------------------------------------*)
subsection \<open>Example 2\<close>

text \<open>

This example systems Sys2 aims at checking that we can have 2
components, one untrusted UT2 and one truted T1, sharing a cnode obj2_5.

Both UT2 and T2 contains:

  . one TCB (obj2_3079 and obj2_3080 resp.)
  . one vspace made up of one page directory (obj2_6063 and obj2_3065 resp.)
  . each pd contains a single page table (obj2_3072 and obj2_3077 resp.)
  . one cspace made up of one cnode (obj2_6 and obj2_7 resp.)
  . each cspace contains 4 caps:
         one to the tcb
         one to the cnode itself
         one to the vspace
         one to obj2_5


Attempt to ASCII art:


          --------    ----                          ----     --------
          |       |   |  |                          |  |     |      |
          V       |   |  V     S             R      |  V     |      V
obj2_3079(tcb)-->obj2_6(cnode)--->obj2_5(cnode)<---obj2_7(cnode)<--obj2_3080(tcb)
  |               |                                   |            |
  V               |                                   |            V
obj2_3063(pd)<-----                                    -------> obj2_3065(pd)
  |                                                                |
  V                                                                V
obj2_3072(pt)                                                      obj2_3077(pt)


(the references are derived from the dump of the SAC system)


The aim is to be able to prove

  pas_refined Sys2PAS s2

where Sys2PAS is the label graph defining the AC policy for Sys2 and
s2 is the state of Sys2 described above.

This shows that the aag extracted from s2 (by state_objs_to_policy) is
included in the policy graph Sys2PAS.

\<close>


subsubsection \<open>Defining the State\<close>



text \<open>We need to define the asids of each pd and pt to ensure that
the object is included in the right ASID-label\<close>

text \<open>UT2's ASID\<close>

definition
  asid2_3063 :: machine_word
where
  "asid2_3063 \<equiv> 1<<asid_low_bits"

text \<open>T2's ASID\<close>

definition
  asid2_3065 :: machine_word
where
  "asid2_3065 \<equiv> 2<<asid_low_bits"

lemma "asid_high_bits_of asid2_3065 \<noteq> asid_high_bits_of asid2_3063"
by (simp add: asid2_3063_def asid_high_bits_of_def asid2_3065_def asid_low_bits_def)



text \<open>the intermediaite CSpace\<close>

definition
  caps2_5 :: cnode_contents
where
  "caps2_5 \<equiv>
   (empty_cnode 10)"

definition
  obj2_5 :: kernel_object
where
  "obj2_5 \<equiv> CNode 10 caps2_5"



text \<open>UT2's CSpace\<close>

definition
  caps2_6 :: cnode_contents
where
  "caps2_6 \<equiv>
   (empty_cnode 10)
      ( (the_nat_to_bl_10 1)
            \<mapsto> ThreadCap 3079,
        (the_nat_to_bl_10 2)
            \<mapsto> CNodeCap 6 undefined undefined,
        (the_nat_to_bl_10 3)
            \<mapsto> ArchObjectCap (PageDirectoryCap 3063
                                             (Some asid2_3063)),
        (the_nat_to_bl_10 4)
            \<mapsto> CNodeCap 5 undefined undefined )"


definition
  obj2_6 :: kernel_object
where
  "obj2_6 \<equiv> CNode 10 caps2_6"

text \<open>T2's Cspace\<close>

definition
  caps2_7 :: cnode_contents
where
  "caps2_7 \<equiv>
   (empty_cnode 10)
      ( (the_nat_to_bl_10 1)
            \<mapsto> ThreadCap 3080,
        (the_nat_to_bl_10 2)
            \<mapsto> CNodeCap 7 undefined undefined,
        (the_nat_to_bl_10 3)
           \<mapsto> ArchObjectCap (PageDirectoryCap 3065
                                            (Some asid2_3065)),
        (the_nat_to_bl_10 4)
            \<mapsto> CNodeCap 5 undefined undefined) "

definition
  obj2_7 :: kernel_object
where
  "obj2_7 \<equiv> CNode 10 caps2_7"


text \<open>endpoint between UT2 and T2\<close>

definition
  obj2_9 :: kernel_object
where
  "obj2_9 \<equiv> Endpoint IdleEP"


text \<open>UT2's VSpace (PageDirectory)\<close>

definition
  pt2_3072 :: "word8 \<Rightarrow> pte "
where
  "pt2_3072 \<equiv> (\<lambda>_. InvalidPTE)"

definition
  obj2_3072 :: kernel_object
where
  "obj2_3072 \<equiv> ArchObj (PageTable pt2_3072)"


definition
  pd2_3063 :: "12 word \<Rightarrow> pde "
where
  "pd2_3063 \<equiv>
    (\<lambda>_. InvalidPDE)
     (0 := PageTablePDE
              (addrFromPPtr 3072)
              undefined
              undefined )"

(* used addrFromPPtr because proof gives me ptrFromAddr.. TODO: check
if it's right *)

definition
  obj2_3063 :: kernel_object
where
  "obj2_3063 \<equiv> ArchObj (PageDirectory pd2_3063)"


text \<open>T1's VSpace (PageDirectory)\<close>


definition
  pt2_3077 :: "word8 \<Rightarrow> pte "
where
  "pt2_3077 \<equiv>
    (\<lambda>_. InvalidPTE)"

definition
  obj2_3077 :: kernel_object
where
  "obj2_3077 \<equiv> ArchObj (PageTable pt2_3077)"


definition
  pd2_3065 :: "12 word \<Rightarrow> pde "
where
  "pd2_3065 \<equiv>
    (\<lambda>_. InvalidPDE)
     (0 := PageTablePDE
             (addrFromPPtr 3077)
             undefined
             undefined )"

(* used addrFromPPtr because proof gives me ptrFromAddr.. TODO: check
if it's right *)

definition
  obj2_3065 :: kernel_object
where
  "obj2_3065 \<equiv> ArchObj (PageDirectory pd2_3065)"


text \<open>UT1's tcb\<close>

definition
  obj2_3079 :: kernel_object
where
  "obj2_3079 \<equiv>
   TCB \<lparr>
     tcb_ctable             = CNodeCap 6 undefined undefined ,
     tcb_vtable             = ArchObjectCap (PageDirectoryCap 3063 (Some asid2_3063)),
     tcb_reply              = ReplyCap 3079 True {AllowGrant,AllowWrite}, \<comment> \<open>master reply cap to itself\<close>
     tcb_caller             = NullCap,
     tcb_ipcframe           = NullCap,
     tcb_state              = Running,
     tcb_fault_handler      = undefined,
     tcb_ipc_buffer         = undefined,
     tcb_fault              = undefined,
     tcb_bound_notification = None,
     tcb_mcpriority         = undefined,
     tcb_priority           = undefined,
     tcb_time_slice         = undefined,
     tcb_domain             = 0,
     tcb_flags              = undefined,
     tcb_arch          = \<lparr>tcb_context = undefined\<rparr>\<rparr>"


text \<open>T1's tcb\<close>

definition
  obj2_3080 :: kernel_object
where
  "obj2_3080 \<equiv>
   TCB \<lparr>
     tcb_ctable             = CNodeCap 7 undefined undefined ,
     tcb_vtable             = ArchObjectCap (PageDirectoryCap 3065 (Some asid2_3065)),
     tcb_reply              = ReplyCap 3080 True {AllowGrant,AllowWrite}, \<comment> \<open>master reply cap to itself\<close>
     tcb_caller             = NullCap,
     tcb_ipcframe           = NullCap,
     tcb_state              = BlockedOnReceive 9 \<lparr> receiver_can_grant = False \<rparr>,
     tcb_fault_handler      = undefined,
     tcb_ipc_buffer         = undefined,
     tcb_fault              = undefined,
     tcb_bound_notification = None,
     tcb_mcpriority         = undefined,
     tcb_priority           = undefined,
     tcb_time_slice         = undefined,
     tcb_domain             = 0,
     tcb_flags              = undefined,
     tcb_arch               = \<lparr>tcb_context = undefined\<rparr>\<rparr>"

(* the boolean in BlockedOnReceive is True if the object can receive but not send.
but Tom says it only matters if the sender can grant - which is not the case of the UT1 - I think *)

definition
  kh2 :: kheap
where
  "kh2 \<equiv> [ 6 \<mapsto> obj2_6,
          7 \<mapsto> obj2_7,
          9 \<mapsto> obj2_9,
          3063 \<mapsto> obj2_3063,
          3065 \<mapsto> obj2_3065,
          3072 \<mapsto> obj2_3072,
          3077 \<mapsto> obj2_3077,
          3079 \<mapsto> obj2_3079,
          3080 \<mapsto> obj2_3080 ]"

lemmas kh2_obj_def =
  obj2_6_def obj2_7_def obj2_9_def obj2_3063_def obj2_3065_def
  obj2_3072_def obj2_3077_def obj2_3079_def obj2_3080_def


definition
  s2 :: "det_ext state"
where
  "s2 \<equiv>  \<lparr>
    kheap = kh2,
    cdt = Map.empty,
    is_original_cap = undefined,
    cur_thread = undefined,
    idle_thread = undefined,
    scheduler_action = undefined,
    domain_list = undefined,
    domain_index = undefined,
    domain_start_index = undefined,
    cur_domain = undefined,
    domain_time = undefined,
    ready_queues = undefined,
    machine_state = undefined,
    interrupt_irq_node = (\<lambda>_. 9001),
    interrupt_states = undefined,
    arch_state = \<lparr>
        arm_asid_table = (\<lambda> x. None),
        arm_hwasid_table = undefined,
        arm_next_asid = undefined,
        arm_asid_map = undefined,
        arm_global_pd = undefined,
        arm_global_pts = undefined,
        arm_kernel_vspace = undefined
        \<rparr>,
    exst = exst1
    \<rparr>"


subsubsection \<open>Defining the policy graph\<close>


datatype Sys2Labels =
    UT2 | T2 | IRQ2

definition
  Sys2AgentMap :: "Sys2Labels agent_map"
where
  "Sys2AgentMap \<equiv>
   (\<lambda>_. undefined)
     (5 := UT2,
      6 := UT2,
      7 := T2,
      9 := T2,
      3063 := UT2,
      3065 := T2,
      3072 := UT2,
      3077 := T2,
      3079 := UT2,
      3080 := T2,
      9001 := IRQ2 )"


definition
  Sys2AuthGraph_aux :: "Sys2Labels auth_graph"
where
    "Sys2AuthGraph_aux \<equiv>
       { (T2, Control, UT2) }"

definition
  Sys2AuthGraph:: "Sys2Labels auth_graph"
where
    "Sys2AuthGraph \<equiv> complete_AuthGraph Sys2AuthGraph_aux {T2, UT2}"


definition
  Sys2ASIDMap :: "Sys2Labels agent_asid_map"
where
  "Sys2ASIDMap \<equiv>
    (\<lambda>_. undefined)
     (asid2_3063 := UT2,
      asid2_3065 := T2 )"

definition Sys2DomainMap :: "Sys2Labels agent_domain_map" where
  "Sys2DomainMap \<equiv> (\<lambda>_. {}) (0 := {UT2, T2})"

definition Sys2PAS :: "Sys2Labels PAS" where
  "Sys2PAS \<equiv> \<lparr> pasObjectAbs = Sys2AgentMap, pasASIDAbs = Sys2ASIDMap,
              pasIRQAbs = (\<lambda>_. IRQ2),
              pasPolicy = Sys2AuthGraph, pasSubject = UT2, pasMayActivate = True, pasMayEditReadyQueues = True,
              pasMaySendIrqs = True, pasDomainAbs = Sys2DomainMap \<rparr>"



subsubsection \<open>Proof of pas_refined for Sys2\<close>

lemma caps2_7_well_formed: "well_formed_cnode_n 10 caps2_7"
 apply (clarsimp simp: caps2_7_def well_formed_cnode_n_def)
 apply (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def nat_to_bl_def)
 apply (clarsimp simp: empty_cnode_def dom_def)
 apply (rule set_eqI, clarsimp)
 apply (rule iffI)
  apply (elim disjE, insert size_bin_to_bl, simp_all)[1]
 apply clarsimp
done

lemma caps2_6_well_formed: "well_formed_cnode_n 10 caps2_6"
 apply (clarsimp simp: caps2_6_def well_formed_cnode_n_def)
 apply (clarsimp simp: the_nat_to_bl_10_def the_nat_to_bl_def nat_to_bl_def)
 apply (clarsimp simp: empty_cnode_def dom_def)
 apply (rule set_eqI, clarsimp)
 apply (rule iffI)
  apply (elim disjE, insert size_bin_to_bl, simp_all)[1]
 apply clarsimp
done

lemma s2_caps_of_state :
  "caps_of_state s2 p = Some cap \<Longrightarrow>
     cap = NullCap \<or>
     (p,cap) \<in>
       { ((6::obj_ref,(the_nat_to_bl_10 1)),  ThreadCap 3079),
         ((6::obj_ref,(the_nat_to_bl_10 2)),  CNodeCap 6 undefined undefined),
         ((6::obj_ref,(the_nat_to_bl_10 3)),  ArchObjectCap (PageDirectoryCap 3063 (Some asid2_3063))),
         ((6::obj_ref,(the_nat_to_bl_10 4)),  CNodeCap 5 undefined undefined),
         ((7::obj_ref,(the_nat_to_bl_10 1)),  ThreadCap 3080),
         ((7::obj_ref,(the_nat_to_bl_10 2)),  CNodeCap 7 undefined undefined),
         ((7::obj_ref,(the_nat_to_bl_10 3)),  ArchObjectCap (PageDirectoryCap 3065 (Some asid2_3065))),
         ((7::obj_ref,(the_nat_to_bl_10 4)),  CNodeCap 5 undefined undefined),
         ((3079::obj_ref, (tcb_cnode_index 0)), CNodeCap 6 undefined undefined ),
         ((3079::obj_ref, (tcb_cnode_index 1)), ArchObjectCap (PageDirectoryCap 3063 (Some asid2_3063))),
         ((3079::obj_ref, (tcb_cnode_index 2)), ReplyCap 3079 True {AllowGrant,AllowWrite}),
         ((3079::obj_ref, (tcb_cnode_index 3)), NullCap),
         ((3079::obj_ref, (tcb_cnode_index 4)), NullCap),
         ((3080::obj_ref, (tcb_cnode_index 0)), CNodeCap 7 undefined undefined ),
         ((3080::obj_ref, (tcb_cnode_index 1)), ArchObjectCap (PageDirectoryCap 3065 (Some asid2_3065))),
         ((3080::obj_ref, (tcb_cnode_index 2)), ReplyCap 3080 True {AllowGrant,AllowWrite}),
         ((3080::obj_ref, (tcb_cnode_index 3)), NullCap),
         ((3080::obj_ref, (tcb_cnode_index 4)), NullCap)} "
  apply (insert caps2_7_well_formed)
  apply (insert caps2_6_well_formed)
  apply (simp add: caps_of_state_cte_wp_at cte_wp_at_cases s2_def kh2_def kh2_obj_def)
  apply (case_tac p, clarsimp)
  apply (clarsimp simp: cte_wp_at_cases split: if_splits)
     apply (clarsimp simp: tcb_cap_cases_def split: if_splits)+
   apply (clarsimp simp: caps2_7_def split: if_splits)
  apply (clarsimp simp: caps2_6_def cte_wp_at_cases  split: if_splits)
  done

lemma Sys2_wellformed: "pas_wellformed Sys2PAS"
  apply (clarsimp simp: Sys2PAS_def policy_wellformed_def)
  apply (intro conjI)
  apply (simp_all add: Sys2AuthGraph_def complete_AuthGraph_def
                       Sys2AuthGraph_aux_def)
  done

lemma Sys2AgentMap_simps:
  "Sys2AgentMap 5 = UT2"
  "Sys2AgentMap 6 = UT2"
  "Sys2AgentMap 7 = T2"
  "Sys2AgentMap 9 = T2"
  "Sys2AgentMap 3063 = UT2"
  "Sys2AgentMap 3065 = T2"
  "Sys2AgentMap 3072 = UT2"
  "Sys2AgentMap 3077 = T2"
  "Sys2AgentMap 3079 = UT2"
  "Sys2AgentMap 3080 = T2"
  "Sys2AgentMap 9001 = IRQ2"
  by (simp_all add: Sys2AgentMap_def)

lemma etcbs_of_s2:
  "etcbs_of s2 = [3079 \<mapsto> etcb_of (un_TCB obj2_3079), 3080 \<mapsto> etcb_of (un_TCB obj2_3080)]"
  by (fastforce simp: etcbs_of'_def s2_def kh2_def kh2_obj_def)

lemma domains_of_state_s2:
  "domains_of_state s2 = {(3079, 0), (3080, 0)}"
   by (fastforce simp: etcbs_of_s2 kh2_obj_def
                 elim: domains_of_state_aux.cases
                split: if_split_asm
               intro!: domtcbs)

lemma tcb_domain_map_wellformed_s2:
  "tcb_domain_map_wellformed Sys2PAS s2"
  by (clarsimp simp: tcb_domain_map_wellformed_aux_def Sys2PAS_def domains_of_state_s2
                        Sys2AgentMap_simps Sys2DomainMap_def)

lemma thread_bound_ntfns_2[simp]:
  "thread_bound_ntfns s2 = Map.empty"
  unfolding s2_def thread_bound_ntfns_def
  apply (rule ext)
  apply (simp add: get_tcb_def)
  apply (simp add: kh2_def kh2_obj_def)
  done

lemma state_hyp_refs_of_s2_empty[simp]:
  "state_hyp_refs_of s2 = (\<lambda>_. {})"
  by (auto simp: state_hyp_refs_of_def hyp_refs_of_def split: option.splits kernel_object.splits)

lemma "pas_refined Sys2PAS s2"
  apply (clarsimp simp: pas_refined_def)
  apply (intro conjI)
       apply (simp add: Sys2_wellformed)
      apply (simp add: Sys2PAS_def s2_def Sys2AgentMap_def
                       irq_map_wellformed_aux_def)
     apply (clarsimp simp: tcb_domain_map_wellformed_s2)
    apply (clarsimp simp: auth_graph_map_def
                          Sys2PAS_def
                          state_objs_to_policy_def
                          state_bits_to_policy_def)
    apply (erule state_bits_to_policyp.cases, simp_all)
         apply (drule s2_caps_of_state, clarsimp)
         apply (elim disjE, simp_all add: cap_auth_conferred_def
                                          Sys2AgentMap_simps
                                          Sys2AuthGraph_def Sys2AuthGraph_aux_def
                                          complete_AuthGraph_def
                              split: if_split_asm)[1]
        apply (drule s2_caps_of_state, clarsimp)
        apply (elim disjE, simp_all)[1]
       apply (clarsimp simp: state_refs_of_def s2_def kh2_def kh2_obj_def
                       split: if_splits)
       apply (clarsimp split:if_splits option.splits
                       simp: thread_st_auth_def tcb_states_of_state_def
                             Sys2AgentMap_simps Sys2AuthGraph_def
                             complete_AuthGraph_def Sys2AuthGraph_aux_def
                      dest!: get_tcb_SomeD)
      apply (simp add: s2_def) (* this is OK because cdt is empty..*)
     apply (simp add: s2_def) (* this is OK because cdt is empty..*)

    apply ((clarsimp simp: state_vrefs_def
                           vs_refs_no_global_pts_def
                           s2_def kh2_def
                           kh2_obj_def
                     split: if_splits,
           ((clarsimp split: if_splits
                     simp: pd2_3065_def pd2_3063_def graph_of_def pde_ref_def
                           Sys2AgentMap_simps Sys2AuthGraph_def
                           complete_AuthGraph_def pt2_3077_def pte_ref_def
                           pt2_3072_def pde_ref2_def
                           Sys2AuthGraph_aux_def ptr_range_def)+))+)[1]
   apply clarsimp
   apply (erule state_asids_to_policy_aux.cases)
    apply clarsimp
    apply (auto simp: Sys2PAS_def Sys2AuthGraph_def Sys2AuthGraph_aux_def
                      complete_AuthGraph_def Sys2AgentMap_simps
                      Sys2ASIDMap_def asid2_3063_def asid2_3065_def
                      asid_low_bits_def
               dest!: s2_caps_of_state)[1]
   apply (clarsimp simp: state_vrefs_def
                         vs_refs_no_global_pts_def
                         s2_def kh2_def
                         kh2_obj_def
                  split: if_splits)
   apply (clarsimp simp: s2_def)
  apply (clarsimp)
  apply (erule state_irqs_to_policy_aux.cases)
  apply (auto simp: Sys2PAS_def Sys2AuthGraph_def Sys2AuthGraph_aux_def
                    complete_AuthGraph_def Sys2AgentMap_simps
                    Sys2ASIDMap_def asid2_3063_def asid2_3065_def
             dest!: s2_caps_of_state)[1]
  done

end

end
