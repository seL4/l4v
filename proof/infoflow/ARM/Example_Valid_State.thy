(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Example_Valid_State
imports
  "ArchNoninterference"
  "Lib.Distinct_Cmd"
begin

section \<open>Example\<close>

(* This example is a classic 'one way information flow'
   example, where information is allowed to flow from Low to High,
   but not the reverse. We consider a typical scenario where
   shared memory and an notification for notifications are used to
   implement a ring-buffer. We consider the NTFN to be in the domain of High,
   and the shared memory to be in the domain of Low. *)

(* basic machine-level declarations that need to happen outside the locale *)

consts s0_context :: user_context

(* define the irqs to come regularly every 10 *)

axiomatization where
  irq_oracle_def: "ARM.irq_oracle \<equiv> \<lambda>pos. if pos mod 10 = 0 then 10 else 0"

context begin interpretation Arch . (*FIXME: arch_split*)

subsection \<open>We show that the authority graph does not let
              information flow from High to Low\<close>

datatype auth_graph_label = High | Low | IRQ0

abbreviation partition_label where
  "partition_label x \<equiv> OrdinaryLabel x"

definition Sys1AuthGraph :: "(auth_graph_label subject_label) auth_graph" where
  "Sys1AuthGraph \<equiv>
   { (partition_label High,Read,partition_label Low),
     (partition_label Low,Notify,partition_label High),
     (partition_label Low,Reset,partition_label High),
     (SilcLabel,Notify,partition_label High),
     (SilcLabel,Reset,partition_label High)
   } \<union> {(x, a, y). x = y}"

lemma subjectReads_Low: "subjectReads Sys1AuthGraph (partition_label Low) = {partition_label Low}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, (fastforce simp: Sys1AuthGraph_def)+)
  done

lemma Low_in_subjectReads_High:
  "partition_label Low \<in> subjectReads Sys1AuthGraph (partition_label High)"
  apply (simp add: Sys1AuthGraph_def reads_read)
  done

lemma subjectReads_High: "subjectReads Sys1AuthGraph (partition_label High) = {partition_label High,partition_label Low}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply(auto intro: Low_in_subjectReads_High)
  done

lemma subjectReads_IRQ0: "subjectReads Sys1AuthGraph (partition_label IRQ0) = {partition_label IRQ0}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectReads.induct, (fastforce simp: Sys1AuthGraph_def)+)
  done

lemma High_in_subjectAffects_Low:
  "partition_label High \<in> subjectAffects Sys1AuthGraph (partition_label Low)"
  apply(rule affects_ep)
   apply (simp add: Sys1AuthGraph_def)
   apply (rule disjI1, simp+)
   done

lemma subjectAffects_Low: "subjectAffects Sys1AuthGraph (partition_label Low) = {partition_label Low, partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply(auto intro: affects_lrefl High_in_subjectAffects_Low)
  done

lemma subjectAffects_High: "subjectAffects Sys1AuthGraph (partition_label High) = {partition_label High}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply(auto intro: affects_lrefl)
  done

lemma subjectAffects_IRQ0: "subjectAffects Sys1AuthGraph (partition_label IRQ0) = {partition_label IRQ0}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(erule subjectAffects.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply(auto intro: affects_lrefl)
  done



lemmas subjectReads = subjectReads_High subjectReads_Low subjectReads_IRQ0



lemma partsSubjectAffects_Low: "partsSubjectAffects Sys1AuthGraph Low = {Partition Low, Partition High}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_Low | case_tac xa, rename_tac xa)+
  done

lemma partsSubjectAffects_High: "partsSubjectAffects Sys1AuthGraph High = {Partition High}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_High | rename_tac xa, case_tac xa)+
  done

lemma partsSubjectAffects_IRQ0: "partsSubjectAffects Sys1AuthGraph IRQ0 = {Partition IRQ0}"
  apply(auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def subjectReads subjectAffects_IRQ0 | rename_tac xa, case_tac xa)+
  done

lemmas partsSubjectAffects =
   partsSubjectAffects_High partsSubjectAffects_Low partsSubjectAffects_IRQ0


definition example_policy where
  "example_policy \<equiv> {(PSched, d)|d. True} \<union>
                    {(d,e). d = e} \<union>
                    {(Partition Low, Partition High)}"

lemma "policyFlows Sys1AuthGraph = example_policy"
  apply(rule equalityI)
   apply(rule subsetI)
   apply(clarsimp simp: example_policy_def)
   apply(erule policyFlows.cases)
    apply(case_tac l, auto simp: partsSubjectAffects)[1]
   apply assumption
  apply(rule subsetI)
  apply(clarsimp simp: example_policy_def)
  apply(elim disjE)
    apply(fastforce simp: partsSubjectAffects intro: policy_affects)
   apply(fastforce intro: policy_scheduler)
  apply(fastforce intro: policyFlows_refl refl_onD)
  done

subsection \<open>We show there exists a valid initial state associated to the
              above authority graph\<close>

text \<open>

This example (modified from ../access-control/ExampleSystem) is a system Sys1 made
of 2 main components Low and High, connected through an notification NTFN.
Both Low and High contains:

  . one TCB
  . one vspace made up of one page directory
  . each pd contains a single page table, with access to a shared page in memory
     Low can read/write to this page, High can only read
  . one cspace made up of one cnode
  . each cspace contains 4 caps:
         one to the tcb
         one to the cnode itself
         one to the vspace
         one to the ntfn

Low can send to the ntfn while High can receive from it.

Attempt to ASCII art:


          --------    ----                    ----   --------
          |       |   |  |                    |  |   |      |
          V       |   |  V    S         R     |  V   |      V
Low_tcb(3079)-->Low_cnode(6)--->ntfn(9)<---High_cnode(7)<--High_tcb(3080)
  |              |                               |          |
  V              |                               |          V
Low_pd(3063)<-----                               -------> High_pd(3065)
  |                                                         |
  V               R/W                           R           V
Low_pt(3072)---------------->shared_page<-----------------High_pt(3077)


(the references are derived from the dump of the SAC system)


The aim is to be able to prove

  valid_initial_state s0_internal Sys1PAS timer_irq utf

where Sys1PAS is the label graph defining the AC policy for Sys1 using
the authority graph defined above and s0 is the state of Sys1 described above.

\<close>

subsubsection \<open>Defining the State\<close>


definition "ntfn_ptr \<equiv> kernel_base + 0x10"

definition "Low_tcb_ptr \<equiv> kernel_base + 0x200"
definition "High_tcb_ptr = kernel_base + 0x400"
definition "idle_tcb_ptr = kernel_base + 0x1000"

definition "Low_pt_ptr = kernel_base + 0x800"
definition "High_pt_ptr = kernel_base + 0xC00"


(* init_globals_frame \<equiv> {kernel_base + 0x5000,... kernel_base + 0x5FFF} *)

definition "shared_page_ptr_virt = kernel_base + 0x6000"
definition "shared_page_ptr_phys = addrFromPPtr shared_page_ptr_virt"

definition "Low_pd_ptr = kernel_base + 0x20000"
definition "High_pd_ptr = kernel_base + 0x24000"

definition "Low_cnode_ptr = kernel_base + 0x10000"
definition "High_cnode_ptr = kernel_base + 0x14000"
definition "Silc_cnode_ptr = kernel_base + 0x18000"
definition "irq_cnode_ptr = kernel_base + 0x1C000"

(* init_global_pd \<equiv> {kernel_base + 0x60000,... kernel_base + 0x603555} *)

definition "timer_irq \<equiv> 10" (* not sure exactly how this fits in *)

definition "Low_mcp \<equiv> 5 :: word8"
definition "Low_prio \<equiv> 5 :: word8"
definition "High_mcp \<equiv> 5 :: word8"
definition "High_prio \<equiv> 5 :: word8"
definition "Low_time_slice \<equiv> 0 :: nat"
definition "High_time_slice \<equiv> 5 :: nat"
definition "Low_domain \<equiv> 0 :: word8"
definition "High_domain \<equiv> 1 :: word8"

lemmas s0_ptr_defs =
  Low_cnode_ptr_def High_cnode_ptr_def Silc_cnode_ptr_def ntfn_ptr_def irq_cnode_ptr_def
  Low_pd_ptr_def High_pd_ptr_def Low_pt_ptr_def High_pt_ptr_def Low_tcb_ptr_def
  High_tcb_ptr_def idle_tcb_ptr_def timer_irq_def Low_prio_def High_prio_def Low_time_slice_def
  Low_domain_def High_domain_def init_irq_node_ptr_def init_globals_frame_def init_global_pd_def
  kernel_base_def shared_page_ptr_virt_def

(* Distinctness proof of kernel pointers. *)

distinct ptrs_distinct [simp]:
  Low_tcb_ptr High_tcb_ptr idle_tcb_ptr
  Low_pt_ptr High_pt_ptr
  shared_page_ptr_virt ntfn_ptr
  Low_pd_ptr High_pd_ptr
  Low_cnode_ptr High_cnode_ptr Silc_cnode_ptr irq_cnode_ptr
  init_globals_frame init_global_pd
  by (auto simp: s0_ptr_defs)


text \<open>We need to define the asids of each pd and pt to ensure that
the object is included in the right ASID-label\<close>

text \<open>Low's ASID\<close>

definition
  Low_asid :: machine_word
where
  "Low_asid \<equiv> 1<<asid_low_bits"

text \<open>High's ASID\<close>

definition
  High_asid :: machine_word
where
  "High_asid \<equiv> 2<<asid_low_bits"

lemma "asid_high_bits_of High_asid \<noteq> asid_high_bits_of Low_asid"
by (simp add: Low_asid_def asid_high_bits_of_def High_asid_def asid_low_bits_def)


text \<open>converting a nat to a bool list of size 10 - for the cnodes\<close>

definition
  nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list option"
where
  "nat_to_bl bits n \<equiv>
    if n \<ge> 2^bits then
      None
    else
      Some $ bin_to_bl bits (of_nat n)"

lemma nat_to_bl_id [simp]: "nat_to_bl (size (x :: (('a::len) word))) (unat x) = Some (to_bl x)"
  by (clarsimp simp: nat_to_bl_def to_bl_def le_def word_size)

definition
  the_nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list"
where
  "the_nat_to_bl sz n \<equiv>
      the (nat_to_bl sz (n mod 2^sz))"

abbreviation (input)
  the_nat_to_bl_10  :: "nat \<Rightarrow> bool list"
where
  "the_nat_to_bl_10 n \<equiv> the_nat_to_bl 10 n"

lemma len_the_nat_to_bl [simp]:
    "length (the_nat_to_bl x y) = x"
  apply (clarsimp simp: the_nat_to_bl_def nat_to_bl_def)
  apply safe
   apply (metis le_def mod_less_divisor nat_zero_less_power_iff zero_less_numeral)
  apply (clarsimp simp: len_bin_to_bl_aux not_le)
  done

lemma tcb_cnode_index_nat_to_bl [simp]:
  "the_nat_to_bl_10 n \<noteq> tcb_cnode_index n"
  by (clarsimp simp: tcb_cnode_index_def intro!: length_neq)

lemma mod_less_self [simp]:
    "a \<le> b mod a \<longleftrightarrow> ((a :: nat) = 0)"
  by (metis mod_less_divisor nat_neq_iff not_less not_less0)

lemma split_div_mod:
    "a = (b::nat) \<longleftrightarrow> (a div k = b div k \<and> a mod k = b mod k)"
  by (metis mult_div_mod_eq)

lemma nat_to_bl_eq:
  assumes "a < 2 ^ n \<or> b < 2 ^ n"
  shows "nat_to_bl n a = nat_to_bl n b \<longleftrightarrow> a = b"
  using assms
  apply -
  apply (erule disjE_R)
   apply (clarsimp simp: nat_to_bl_def)
  apply (case_tac "a \<ge> 2 ^ n")
   apply (clarsimp simp: nat_to_bl_def)
  apply (clarsimp simp: not_le)
  apply (induct n arbitrary: a b)
   apply (clarsimp simp: nat_to_bl_def)
  apply atomize
  apply (clarsimp simp: nat_to_bl_def)
  apply (erule_tac x="a div 2" in allE)
  apply (erule_tac x="b div 2" in allE)
  apply (erule impE)
   apply (metis power_commutes td_gal_lt zero_less_numeral)
  apply (clarsimp simp: bin_last_def zdiv_int)
  apply (rule iffI [rotated], clarsimp)
  apply (subst (asm) (1 2 3 4) bin_to_bl_aux_alt)
  apply (clarsimp simp: mod_eq_dvd_iff)
  apply (subst split_div_mod [where k=2])
  apply clarsimp
  apply presburger
  done

lemma nat_to_bl_mod_n_eq [simp]:
    "nat_to_bl n a = nat_to_bl n b \<longleftrightarrow> ((a = b \<and> a < 2 ^ n) \<or> (a \<ge> 2 ^ n \<and> b \<ge> 2 ^ n))"
  apply (rule iffI)
  apply (clarsimp simp: not_le)
  apply (subst (asm) nat_to_bl_eq, simp)
  apply clarsimp
  apply (erule disjE)
   apply clarsimp
  apply (clarsimp simp: nat_to_bl_def)
  done

lemma the_the_eq:
    "\<lbrakk> x \<noteq> None; y \<noteq> None \<rbrakk> \<Longrightarrow> (the x = the y) = (x = y)"
  by auto

lemma the_nat_to_bl_eq [simp]:
    "(the_nat_to_bl n a = the_nat_to_bl m b) \<longleftrightarrow> (n = m \<and> (a mod 2 ^ n = b mod 2 ^ n))"
  apply (case_tac "n = m")
   apply (clarsimp simp: the_nat_to_bl_def)
   apply (subst the_the_eq)
     apply (clarsimp simp: nat_to_bl_def)
    apply (clarsimp simp: nat_to_bl_def)
   apply simp
  apply simp
  apply (metis len_the_nat_to_bl)
  done

lemma empty_cnode_eq_Some [simp]:
    "(empty_cnode n x = Some y) = (length x = n \<and> y = NullCap)"
  by (clarsimp simp: empty_cnode_def, metis)

lemma empty_cnode_eq_None [simp]:
    "(empty_cnode n x = None) = (length x \<noteq> n)"
  by (clarsimp simp: empty_cnode_def)

text \<open>Low's CSpace\<close>

definition
  Low_caps :: cnode_contents
where
  "Low_caps \<equiv>
   (empty_cnode 10)
      ( (the_nat_to_bl_10 1)
            \<mapsto> ThreadCap Low_tcb_ptr,
        (the_nat_to_bl_10 2)
            \<mapsto> CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2),
        (the_nat_to_bl_10 3)
            \<mapsto> ArchObjectCap (PageDirectoryCap Low_pd_ptr
                                             (Some Low_asid)),
        (the_nat_to_bl_10 318)
            \<mapsto> NotificationCap ntfn_ptr 0 {AllowSend} )"

definition
  Low_cnode :: kernel_object
where
  "Low_cnode \<equiv> CNode 10 Low_caps"

lemma ran_empty_cnode [simp]:
    "ran (empty_cnode C) = {NullCap}"
  by (auto simp: empty_cnode_def ran_def Ex_list_of_length intro: set_eqI)

lemma empty_cnode_app [simp]:
    "length x = n \<Longrightarrow> empty_cnode n x = Some NullCap"
  by (auto simp: empty_cnode_def)

lemma in_ran_If [simp]:
      "(x \<in> ran (\<lambda>n. if P n then A n else B n))
            \<longleftrightarrow>  (\<exists>n. P n \<and> A n = Some x) \<or> (\<exists>n. \<not> P n \<and> B n = Some x)"
 by (auto simp: ran_def)


lemma Low_caps_ran:
  "ran Low_caps = {ThreadCap Low_tcb_ptr,
                   CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2),
                   ArchObjectCap (PageDirectoryCap Low_pd_ptr
                                              (Some Low_asid)),
                   NotificationCap ntfn_ptr 0 {AllowSend},
                   NullCap}"
  apply (rule equalityI)
   apply (clarsimp simp: Low_caps_def fun_upd_def empty_cnode_def split: if_split_asm)
  apply (clarsimp simp: Low_caps_def fun_upd_def empty_cnode_def split: if_split_asm
                  cong: conj_cong)
  apply (rule exI [where x="the_nat_to_bl_10 0"])
  apply simp
  done

text \<open>High's Cspace\<close>

definition
  High_caps :: cnode_contents
where
  "High_caps \<equiv>
   (empty_cnode 10)
      ( (the_nat_to_bl_10 1)
            \<mapsto> ThreadCap High_tcb_ptr,
        (the_nat_to_bl_10 2)
            \<mapsto> CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2),
        (the_nat_to_bl_10 3)
           \<mapsto> ArchObjectCap (PageDirectoryCap High_pd_ptr
                                            (Some High_asid)),
        (the_nat_to_bl_10 318)
           \<mapsto> NotificationCap ntfn_ptr 0 {AllowRecv}) "

definition
  High_cnode :: kernel_object
where
  "High_cnode \<equiv> CNode 10 High_caps"

lemma High_caps_ran:
  "ran High_caps = {ThreadCap High_tcb_ptr,
                    CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2),
                    ArchObjectCap (PageDirectoryCap High_pd_ptr
                                               (Some High_asid)),
                    NotificationCap ntfn_ptr 0 {AllowRecv},
                    NullCap}"
  apply (rule equalityI)
   apply (clarsimp simp: High_caps_def ran_def empty_cnode_def split: if_split_asm)
  apply (clarsimp simp: High_caps_def ran_def empty_cnode_def split: if_split_asm
                  cong: conj_cong)
  apply (rule exI [where x="the_nat_to_bl_10 0"])
  apply simp
  done

text \<open>We need a copy of boundary crossing caps owned by SilcLabel.
        The only such cap is Low's cap to the notification\<close>

definition
  Silc_caps :: cnode_contents
where
  "Silc_caps \<equiv>
   (empty_cnode 10)
      ( (the_nat_to_bl_10 2)
            \<mapsto> CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2),
        (the_nat_to_bl_10 318)
            \<mapsto> NotificationCap ntfn_ptr 0 {AllowSend} )"


definition
  Silc_cnode :: kernel_object
where
  "Silc_cnode \<equiv> CNode 10 Silc_caps"

lemma Silc_caps_ran:
  "ran Silc_caps = {CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2),
                    NotificationCap ntfn_ptr 0 {AllowSend},
                    NullCap}"
  apply (rule equalityI)
   apply (clarsimp simp: Silc_caps_def ran_def empty_cnode_def)
  apply (clarsimp simp: ran_def Silc_caps_def empty_cnode_def cong: conj_cong)
  apply (rule_tac x="the_nat_to_bl_10 0" in exI)
  apply simp
  done

text \<open>notification between Low and High\<close>

definition
  ntfn :: kernel_object
where
  "ntfn \<equiv> Notification \<lparr>ntfn_obj = WaitingNtfn [High_tcb_ptr], ntfn_bound_tcb=None\<rparr>"


text \<open>Low's VSpace (PageDirectory)\<close>

definition
  Low_pt' :: "word8 \<Rightarrow> pte "
where
  "Low_pt' \<equiv> (\<lambda>_. InvalidPTE)
            (0 := SmallPagePTE shared_page_ptr_phys {} vm_read_write)"

definition
  Low_pt :: kernel_object
where
  "Low_pt \<equiv> ArchObj (PageTable Low_pt')"


definition
  Low_pd' :: "12 word \<Rightarrow> pde "
where
  "Low_pd' \<equiv>
    global_pd
     (0 := PageTablePDE
              (addrFromPPtr Low_pt_ptr)
              {}
              undefined )"

(* used addrFromPPtr because proof gives me ptrFromAddr.. TODO: check
if it's right *)

definition
  Low_pd :: kernel_object
where
  "Low_pd \<equiv> ArchObj (PageDirectory Low_pd')"


text \<open>High's VSpace (PageDirectory)\<close>


definition
  High_pt' :: "word8 \<Rightarrow> pte "
where
  "High_pt' \<equiv>
    (\<lambda>_. InvalidPTE)
     (0 := SmallPagePTE shared_page_ptr_phys {} vm_read_only)"


definition
  High_pt :: kernel_object
where
  "High_pt \<equiv> ArchObj (PageTable High_pt')"


definition
  High_pd' :: "12 word \<Rightarrow> pde "
where
  "High_pd' \<equiv>
    global_pd
     (0 := PageTablePDE
             (addrFromPPtr High_pt_ptr)
             {}
             undefined )"

(* used addrFromPPtr because proof gives me ptrFromAddr.. TODO: check
if it's right *)

definition
  High_pd :: kernel_object
where
  "High_pd \<equiv> ArchObj (PageDirectory High_pd')"


text \<open>Low's tcb\<close>

definition
  Low_tcb :: kernel_object
where
  "Low_tcb \<equiv>
   TCB \<lparr>
     tcb_ctable        = CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2),
     tcb_vtable        = ArchObjectCap
                           (PageDirectoryCap Low_pd_ptr (Some Low_asid)),
     tcb_reply         = ReplyCap Low_tcb_ptr True {AllowGrant, AllowWrite}, \<comment> \<open>master reply cap\<close>
     tcb_caller        = NullCap,
     tcb_ipcframe      = NullCap,
     tcb_state         = Running,
     tcb_fault_handler = replicate word_bits False,
     tcb_ipc_buffer    = 0,
     tcb_fault         = None,
     tcb_bound_notification     = None,
     tcb_mcpriority    = Low_mcp,
     tcb_arch = \<lparr>tcb_context = undefined\<rparr>\<rparr>"

definition
  Low_etcb :: etcb
where
  "Low_etcb \<equiv> \<lparr>tcb_priority   = Low_prio,
               tcb_time_slice = Low_time_slice,
               tcb_domain     = Low_domain\<rparr>"


text \<open>High's tcb\<close>

definition
  High_tcb :: kernel_object
where
  "High_tcb \<equiv>
   TCB \<lparr>
     tcb_ctable        = CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2) ,
     tcb_vtable        = ArchObjectCap
                           (PageDirectoryCap High_pd_ptr (Some High_asid)),
     tcb_reply         = ReplyCap High_tcb_ptr True {AllowGrant,AllowWrite}, \<comment> \<open>master reply cap to itself\<close>
     tcb_caller        = NullCap,
     tcb_ipcframe      = NullCap,
     tcb_state         = BlockedOnNotification ntfn_ptr,
     tcb_fault_handler = replicate word_bits False,
     tcb_ipc_buffer    = 0,
     tcb_fault         = None,
     tcb_bound_notification     = None,
     tcb_mcpriority    = High_mcp,
     tcb_arch = \<lparr>tcb_context = undefined\<rparr>\<rparr>"

definition
  High_etcb :: etcb
where
  "High_etcb \<equiv> \<lparr>tcb_priority   = High_prio,
                tcb_time_slice = High_time_slice,
                tcb_domain     = High_domain\<rparr>"


text \<open>idle's tcb\<close>

definition
  idle_tcb :: kernel_object
where
  "idle_tcb \<equiv>
   TCB \<lparr>
     tcb_ctable        = NullCap,
     tcb_vtable        = NullCap,
     tcb_reply         = NullCap,
     tcb_caller        = NullCap,
     tcb_ipcframe      = NullCap,
     tcb_state         = IdleThreadState,
     tcb_fault_handler = replicate word_bits False,
     tcb_ipc_buffer    = 0,
     tcb_fault         = None,
     tcb_bound_notification     = None,
     tcb_mcpriority    = default_priority,
     tcb_arch = \<lparr>tcb_context = empty_context\<rparr>\<rparr>"


definition
 "irq_cnode \<equiv> CNode 0 (Map.empty([] \<mapsto> cap.NullCap))"

definition
  kh0 :: kheap
where
  "kh0 \<equiv> (\<lambda>x. if \<exists>irq::10 word. init_irq_node_ptr + (ucast irq << cte_level_bits) = x
          then Some (CNode 0 (empty_cnode 0)) else None)
         (Low_cnode_ptr  \<mapsto> Low_cnode,
          High_cnode_ptr \<mapsto> High_cnode,
          Silc_cnode_ptr \<mapsto> Silc_cnode,
          ntfn_ptr        \<mapsto> ntfn,
          irq_cnode_ptr  \<mapsto> irq_cnode,
          Low_pd_ptr     \<mapsto> Low_pd,
          High_pd_ptr    \<mapsto> High_pd,
          Low_pt_ptr     \<mapsto> Low_pt,
          High_pt_ptr    \<mapsto> High_pt,
          Low_tcb_ptr    \<mapsto> Low_tcb,
          High_tcb_ptr   \<mapsto> High_tcb,
          idle_tcb_ptr   \<mapsto> idle_tcb,
          init_globals_frame \<mapsto> ArchObj (DataPage False ARMSmallPage),
          init_global_pd \<mapsto> ArchObj (PageDirectory global_pd))"

lemma irq_node_offs_min:
  "init_irq_node_ptr \<le> init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits)"
  apply (rule_tac sz=28 in machine_word_plus_mono_right_split)
   apply (simp add: unat_word_ariths mask_def shiftl_t2n s0_ptr_defs cte_level_bits_def)
   apply (cut_tac x=irq and 'a=32 in ucast_less)
    apply simp
   apply (simp add: word_less_nat_alt)
  apply (simp add: word_bits_def)
  done

lemma irq_node_offs_max:
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) < init_irq_node_ptr + 0x4000"
  apply (simp add: s0_ptr_defs cte_level_bits_def shiftl_t2n)
  apply (cut_tac x=irq and 'a=32 in ucast_less)
   apply simp
  apply (simp add: word_less_nat_alt unat_word_ariths)
  done

definition irq_node_offs_range where
  "irq_node_offs_range \<equiv> {x. init_irq_node_ptr \<le> x \<and> x < init_irq_node_ptr + 0x4000}
                         \<inter> {x. is_aligned x cte_level_bits}"



lemma irq_node_offs_in_range:
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits)
     \<in> irq_node_offs_range"
  apply (clarsimp simp: irq_node_offs_min irq_node_offs_max irq_node_offs_range_def)
  apply (rule is_aligned_add[OF _ is_aligned_shift])
  apply (simp add: is_aligned_def s0_ptr_defs cte_level_bits_def)
  done

lemma irq_node_offs_range_correct:
  "x \<in> irq_node_offs_range
    \<Longrightarrow> \<exists>irq. x = init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits)"
  apply (clarsimp simp: irq_node_offs_min irq_node_offs_max irq_node_offs_range_def
                        s0_ptr_defs cte_level_bits_def)
  apply (rule_tac x="ucast ((x - 0xE0008000) >> 4)" in exI)
  apply (clarsimp simp: ucast_ucast_mask)
  apply (subst aligned_shiftr_mask_shiftl)
   apply (rule aligned_sub_aligned)
     apply assumption
    apply (simp add: is_aligned_def)
   apply simp
  apply simp
  apply (rule_tac n=14 in mask_eqI)
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_def)
   apply (simp add: mask_twice)
   apply (simp add: diff_conv_add_uminus del: add_uminus_conv_diff)
   apply (subst add.commute[symmetric])
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_def)
   apply simp
  apply (simp add: diff_conv_add_uminus del: add_uminus_conv_diff)
  apply (subst add_mask_lower_bits)
    apply (simp add: is_aligned_def)
   apply clarsimp
  apply (cut_tac x=x and y="0xE000BFFF" and n=14 in neg_mask_mono_le)
   apply (force dest: word_less_sub_1)
  apply (drule_tac n=14 in aligned_le_sharp)
   apply (simp add: is_aligned_def)
  apply (simp add: mask_def)
  done

lemma irq_node_offs_range_distinct[simp]:
  "Low_cnode_ptr \<notin> irq_node_offs_range"
  "High_cnode_ptr \<notin> irq_node_offs_range"
  "Silc_cnode_ptr \<notin> irq_node_offs_range"
  "ntfn_ptr \<notin> irq_node_offs_range"
  "irq_cnode_ptr \<notin> irq_node_offs_range"
  "Low_pd_ptr \<notin> irq_node_offs_range"
  "High_pd_ptr \<notin> irq_node_offs_range"
  "Low_pt_ptr \<notin> irq_node_offs_range"
  "High_pt_ptr \<notin> irq_node_offs_range"
  "Low_tcb_ptr \<notin> irq_node_offs_range"
  "High_tcb_ptr \<notin> irq_node_offs_range"
  "idle_tcb_ptr \<notin> irq_node_offs_range"
  "init_globals_frame \<notin> irq_node_offs_range"
  "init_global_pd \<notin> irq_node_offs_range"
  by(simp add:irq_node_offs_range_def s0_ptr_defs)+

lemma irq_node_offs_distinct[simp]:
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> Low_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> High_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> Silc_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> ntfn_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> irq_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> Low_pd_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> High_pd_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> Low_pt_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> High_pt_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> Low_tcb_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> High_tcb_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> idle_tcb_ptr"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> init_globals_frame"
  "init_irq_node_ptr + (ucast (irq:: 10 word) << cte_level_bits) \<noteq> init_global_pd"
  by (simp add:not_inD[symmetric, OF _ irq_node_offs_in_range])+

lemma kh0_dom:
  "dom kh0 = {init_globals_frame, init_global_pd, idle_tcb_ptr, High_tcb_ptr, Low_tcb_ptr,
              High_pt_ptr, Low_pt_ptr, High_pd_ptr, Low_pd_ptr, irq_cnode_ptr, ntfn_ptr,
              Silc_cnode_ptr, High_cnode_ptr, Low_cnode_ptr} \<union>
             irq_node_offs_range"
  apply (rule equalityI)
   apply (simp add: kh0_def dom_def)
   apply (clarsimp simp: irq_node_offs_in_range)
  apply (clarsimp simp: dom_def)
  apply (rule conjI, clarsimp simp: kh0_def)+
  apply (force simp: kh0_def cte_level_bits_def dest: irq_node_offs_range_correct)
  done

lemmas kh0_SomeD' = set_mp[OF equalityD1[OF kh0_dom[simplified dom_def]], OF CollectI, simplified, OF exI]

lemma kh0_SomeD:
  "kh0 x = Some y \<Longrightarrow>
        x = init_globals_frame \<and> y = ArchObj (DataPage False ARMSmallPage) \<or>
        x = init_global_pd \<and> y = ArchObj (PageDirectory global_pd) \<or>
        x = idle_tcb_ptr \<and> y = idle_tcb \<or>
        x = High_tcb_ptr \<and> y = High_tcb \<or>
        x = Low_tcb_ptr \<and> y = Low_tcb \<or>
        x = High_pt_ptr \<and> y = High_pt \<or>
        x = Low_pt_ptr \<and> y = Low_pt \<or>
        x = High_pd_ptr \<and> y = High_pd \<or>
        x = Low_pd_ptr \<and> y = Low_pd \<or>
        x = irq_cnode_ptr \<and> y = irq_cnode \<or>
        x = ntfn_ptr \<and> y = ntfn \<or>
        x = Silc_cnode_ptr \<and> y = Silc_cnode \<or>
        x = High_cnode_ptr \<and> y = High_cnode \<or>
        x = Low_cnode_ptr \<and> y = Low_cnode \<or>
        x \<in> irq_node_offs_range \<and> y = CNode 0 (empty_cnode 0)"
  apply (frule kh0_SomeD')
  apply (erule disjE, simp add: kh0_def
        | force simp: kh0_def split: if_split_asm)+
  done

lemmas kh0_obj_def =
  Low_cnode_def High_cnode_def Silc_cnode_def ntfn_def irq_cnode_def Low_pd_def
  High_pd_def Low_pt_def High_pt_def Low_tcb_def High_tcb_def idle_tcb_def

definition exst0 :: "det_ext" where
  "exst0 \<equiv> \<lparr>work_units_completed_internal = undefined,
             scheduler_action_internal = resume_cur_thread,
             ekheap_internal = [Low_tcb_ptr  \<mapsto> Low_etcb,
                                High_tcb_ptr \<mapsto> High_etcb,
                                idle_tcb_ptr \<mapsto> default_etcb],
             domain_list_internal = [(0, 10), (1, 10)],
             domain_index_internal = 0,
             cur_domain_internal = 0,
             domain_time_internal = 5,
             ready_queues_internal = (const (const [])),
             cdt_list_internal = const []\<rparr>"

lemmas ekh0_obj_def =
  Low_etcb_def High_etcb_def default_etcb_def

definition machine_state0 :: "machine_state" where
  "machine_state0 \<equiv> \<lparr>irq_masks = (\<lambda>irq. if irq = timer_irq then False else True),
                     irq_state = 0,
                     underlying_memory = const 0,
                     device_state = Map.empty,
                     exclusive_state = undefined,
                     machine_state_rest = undefined\<rparr>"

definition arch_state0 :: "arch_state" where
  "arch_state0 \<equiv> \<lparr>arm_asid_table = Map.empty,
                  arm_hwasid_table = Map.empty, arm_next_asid = 0, arm_asid_map = Map.empty,
                  arm_global_pd = init_global_pd, arm_global_pts = [],
                  arm_kernel_vspace =
       \<lambda>ref. if ref \<in> {kernel_base..kernel_base + mask 20} then ArmVSpaceKernelWindow
               else ArmVSpaceInvalidRegion\<rparr>"

definition
  s0_internal :: "det_ext state"
where
  "s0_internal \<equiv>  \<lparr>
    kheap = kh0,
    cdt = Map.empty,
    is_original_cap =  (\<lambda>_. False) ((Low_tcb_ptr, tcb_cnode_index 2) := True,
                                    (High_tcb_ptr, tcb_cnode_index 2) := True),
    cur_thread = Low_tcb_ptr,
    idle_thread = idle_tcb_ptr,
    machine_state = machine_state0,
    interrupt_irq_node = (\<lambda>irq. init_irq_node_ptr + (ucast irq << cte_level_bits)),
    interrupt_states = (\<lambda>_. irq_state.IRQInactive) (timer_irq := irq_state.IRQTimer),
    arch_state = arch_state0,
     exst = exst0
   \<rparr>"


subsubsection \<open>Defining the policy graph\<close>

(* FIXME: should incorporate SharedPage above *)

(* There is an NTFN in the High label, a SharedPage in the Low label *)

definition
  Sys1AgentMap :: "(auth_graph_label subject_label) agent_map"
where
  "Sys1AgentMap \<equiv>
   (\<lambda>p. if p \<in> ptr_range shared_page_ptr_virt pageBits
          then partition_label Low else partition_label IRQ0)
            \<comment> \<open>set the range of the shared_page to Low, default everything else to IRQ0\<close>
     (Low_cnode_ptr := partition_label Low,
      High_cnode_ptr := partition_label High,
      ntfn_ptr := partition_label High,
      irq_cnode_ptr := partition_label IRQ0,
      Silc_cnode_ptr := SilcLabel,
      Low_pd_ptr := partition_label Low,
      High_pd_ptr := partition_label High,
      Low_pt_ptr := partition_label Low,
      High_pt_ptr := partition_label High,
      Low_tcb_ptr := partition_label Low,
      High_tcb_ptr := partition_label High,
      idle_tcb_ptr := partition_label Low)"

lemma Sys1AgentMap_simps:
  "Sys1AgentMap Low_cnode_ptr = partition_label Low"
      "Sys1AgentMap High_cnode_ptr = partition_label High"
      "Sys1AgentMap ntfn_ptr = partition_label High"
      "Sys1AgentMap irq_cnode_ptr = partition_label IRQ0"
      "Sys1AgentMap Silc_cnode_ptr = SilcLabel"
      "Sys1AgentMap Low_pd_ptr = partition_label Low"
      "Sys1AgentMap High_pd_ptr = partition_label High"
      "Sys1AgentMap Low_pt_ptr = partition_label Low"
      "Sys1AgentMap High_pt_ptr = partition_label High"
      "Sys1AgentMap Low_tcb_ptr = partition_label Low"
      "Sys1AgentMap High_tcb_ptr = partition_label High"
      "Sys1AgentMap idle_tcb_ptr = partition_label Low"
      "\<And>p. p \<in> ptr_range shared_page_ptr_virt pageBits
          \<Longrightarrow> Sys1AgentMap p = partition_label Low"
  unfolding Sys1AgentMap_def
  apply simp_all
  by (auto simp: s0_ptr_defs ptr_range_def pageBits_def)

definition
  Sys1ASIDMap :: "(auth_graph_label subject_label) agent_asid_map"
where
  "Sys1ASIDMap \<equiv>
    (\<lambda>x. if (asid_high_bits_of x = asid_high_bits_of Low_asid)
          then partition_label Low
         else if (asid_high_bits_of x = asid_high_bits_of High_asid)
          then partition_label High else undefined)"

(* We include 2 domains, Low is associated to domain 0, High to domain 1, we default the rest of the possible domains to High *)

definition Sys1PAS :: "(auth_graph_label subject_label) PAS" where
  "Sys1PAS \<equiv> \<lparr>
    pasObjectAbs = Sys1AgentMap,
    pasASIDAbs = Sys1ASIDMap,
    pasIRQAbs = (\<lambda>_. partition_label IRQ0),
    pasPolicy = Sys1AuthGraph,
    pasSubject = partition_label Low,
    pasMayActivate = True,
    pasMayEditReadyQueues = True, pasMaySendIrqs = False,
    pasDomainAbs = ((\<lambda>_. {partition_label High})(0 := {partition_label Low}))
   \<rparr>"

subsubsection \<open>Proof of pas_refined for Sys1\<close>

lemma High_caps_well_formed: "well_formed_cnode_n 10 High_caps"
  by (auto simp: High_caps_def well_formed_cnode_n_def  split: if_split_asm)

lemma Low_caps_well_formed: "well_formed_cnode_n 10 Low_caps"
  by (auto simp: Low_caps_def well_formed_cnode_n_def  split: if_split_asm)

lemma Silc_caps_well_formed: "well_formed_cnode_n 10 Silc_caps"
  by (auto simp: Silc_caps_def well_formed_cnode_n_def  split: if_split_asm)

lemma s0_caps_of_state :
  "caps_of_state s0_internal p = Some cap \<Longrightarrow>
     cap = NullCap \<or>
     (p,cap) \<in>
       { ((Low_cnode_ptr::obj_ref,(the_nat_to_bl_10 1)),  ThreadCap Low_tcb_ptr),
         ((Low_cnode_ptr::obj_ref,(the_nat_to_bl_10 2)),  CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((Low_cnode_ptr::obj_ref,(the_nat_to_bl_10 3)),  ArchObjectCap (PageDirectoryCap Low_pd_ptr (Some Low_asid))),
         ((Low_cnode_ptr::obj_ref,(the_nat_to_bl_10 318)),NotificationCap ntfn_ptr 0 {AllowSend}),
         ((High_cnode_ptr::obj_ref,(the_nat_to_bl_10 1)),  ThreadCap High_tcb_ptr),
         ((High_cnode_ptr::obj_ref,(the_nat_to_bl_10 2)),  CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((High_cnode_ptr::obj_ref,(the_nat_to_bl_10 3)),  ArchObjectCap (PageDirectoryCap High_pd_ptr (Some High_asid))),
         ((High_cnode_ptr::obj_ref,(the_nat_to_bl_10 318)),NotificationCap  ntfn_ptr 0 {AllowRecv}) ,
         ((Silc_cnode_ptr::obj_ref,(the_nat_to_bl_10 2)),CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((Silc_cnode_ptr::obj_ref,(the_nat_to_bl_10 318)),NotificationCap ntfn_ptr 0 {AllowSend}),
         ((Low_tcb_ptr::obj_ref, (tcb_cnode_index 0)), CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((Low_tcb_ptr::obj_ref, (tcb_cnode_index 1)), ArchObjectCap (PageDirectoryCap Low_pd_ptr (Some Low_asid))),
         ((Low_tcb_ptr::obj_ref, (tcb_cnode_index 2)), ReplyCap Low_tcb_ptr True {AllowGrant, AllowWrite}),
         ((Low_tcb_ptr::obj_ref, (tcb_cnode_index 3)), NullCap),
         ((Low_tcb_ptr::obj_ref, (tcb_cnode_index 4)), NullCap),
         ((High_tcb_ptr::obj_ref, (tcb_cnode_index 0)), CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((High_tcb_ptr::obj_ref, (tcb_cnode_index 1)), ArchObjectCap (PageDirectoryCap High_pd_ptr (Some High_asid))),
         ((High_tcb_ptr::obj_ref, (tcb_cnode_index 2)), ReplyCap High_tcb_ptr True {AllowGrant, AllowWrite}),
         ((High_tcb_ptr::obj_ref, (tcb_cnode_index 3)), NullCap),
         ((High_tcb_ptr::obj_ref, (tcb_cnode_index 4)), NullCap)} "
  supply if_cong[cong]
  apply (insert High_caps_well_formed)
  apply (insert Low_caps_well_formed)
  apply (insert Silc_caps_well_formed)
  apply (simp add: caps_of_state_cte_wp_at cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def)
  apply (case_tac p, clarsimp)
  apply (clarsimp split: if_splits)
       apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def
                       split: if_split_asm)+
    apply (clarsimp simp: Silc_caps_def split: if_splits)
   apply (clarsimp simp: High_caps_def split: if_splits)
  apply (clarsimp simp: Low_caps_def cte_wp_at_cases split: if_splits)
  done

lemma tcb_states_of_state_s0:
  "tcb_states_of_state s0_internal = [High_tcb_ptr \<mapsto> thread_state.BlockedOnNotification ntfn_ptr,  Low_tcb_ptr \<mapsto> thread_state.Running, idle_tcb_ptr \<mapsto> thread_state.IdleThreadState ]"
  unfolding s0_internal_def tcb_states_of_state_def
  apply (rule ext)
  apply (simp add: get_tcb_def)
  apply (simp add: kh0_def kh0_obj_def)
  done

lemma thread_bounds_of_state_s0:
  "thread_bound_ntfns s0_internal = Map.empty"
  unfolding s0_internal_def thread_bound_ntfns_def
  apply (rule ext)
  apply (simp add: get_tcb_def)
  apply (simp add: kh0_def kh0_obj_def)
  done

lemma Sys1_wellformed':
  "policy_wellformed (pasPolicy Sys1PAS) False irqs x"
  apply (clarsimp simp: Sys1PAS_def policy_wellformed_def Sys1AuthGraph_def)
  done

corollary Sys1_wellformed:
  "x \<in> range (pasObjectAbs Sys1PAS) \<union> \<Union>(range (pasDomainAbs Sys1PAS)) - {SilcLabel} \<Longrightarrow>
   policy_wellformed (pasPolicy Sys1PAS) False irqs x"
  by (rule Sys1_wellformed')

lemma Sys1_pas_wellformed:
  "pas_wellformed Sys1PAS"
  apply (clarsimp simp: Sys1PAS_def policy_wellformed_def Sys1AuthGraph_def)
  done

lemma domains_of_state_s0[simp]:
  "domains_of_state s0_internal = {(High_tcb_ptr, High_domain), (Low_tcb_ptr, Low_domain), (idle_tcb_ptr, default_domain)}"
  apply(rule equalityI)
   apply(rule subsetI)
   apply clarsimp
   apply (erule domains_of_state_aux.cases)
   apply (clarsimp simp: s0_internal_def exst0_def ekh0_obj_def split: if_split_asm)
  apply clarsimp
  apply (force simp: s0_internal_def exst0_def ekh0_obj_def intro: domains_of_state_aux.domtcbs)+
  done

lemma Sys1_pas_refined:
  "pas_refined Sys1PAS s0_internal"
  apply (clarsimp simp: pas_refined_def)
  apply (intro conjI)
       apply (simp add: Sys1_pas_wellformed)
      apply (clarsimp simp: irq_map_wellformed_aux_def s0_internal_def Sys1PAS_def)
      apply (clarsimp simp: Sys1AgentMap_def)
      apply (clarsimp simp: s0_ptr_defs ptr_range_def pageBits_def cte_level_bits_def)
      apply word_bitwise
     apply (clarsimp simp: tcb_domain_map_wellformed_aux_def
                           Sys1PAS_def Sys1AgentMap_def
                           default_domain_def minBound_word
                           High_domain_def Low_domain_def cte_level_bits_def)
    apply (clarsimp simp: auth_graph_map_def
                          Sys1PAS_def
                          state_objs_to_policy_def
                          state_bits_to_policy_def)
    apply (erule state_bits_to_policyp.cases, simp_all, clarsimp)
        apply (drule s0_caps_of_state, clarsimp)
        apply (simp add: Sys1AuthGraph_def)
        apply (elim disjE conjE, auto simp: Sys1AgentMap_simps cap_auth_conferred_def cap_rights_to_auth_def)[1]
       apply (drule s0_caps_of_state, clarsimp)
       apply (elim disjE, simp_all)[1]
      apply (clarsimp simp: state_refs_of_def thread_st_auth_def tcb_states_of_state_s0
             Sys1AuthGraph_def Sys1AgentMap_simps split: if_splits)
      apply (clarsimp simp: state_refs_of_def thread_st_auth_def thread_bounds_of_state_s0)
     apply (simp add: s0_internal_def) (* this is OK because cdt is empty..*)
     apply (simp add: s0_internal_def) (* this is OK because cdt is empty..*)
    apply (clarsimp simp: state_vrefs_def
                           vs_refs_no_global_pts_def
                           s0_internal_def kh0_def  Sys1AgentMap_simps
                           kh0_obj_def comp_def Low_pt'_def High_pt'_def
                           pte_ref_def pde_ref2_def Low_pd'_def High_pd'_def
                           Sys1AuthGraph_def ptr_range_def vspace_cap_rights_to_auth_def
                           vm_read_only_def vm_read_write_def

                     dest!: graph_ofD
                     split: if_splits)
     apply (rule Sys1AgentMap_simps(13))
     apply (simp add: ptr_range_def pageBits_def shared_page_ptr_phys_def)
    apply (erule notE)
    apply (rule Sys1AgentMap_simps(13)[symmetric])
    apply (simp add: ptr_range_def pageBits_def shared_page_ptr_phys_def)

   apply (rule subsetI, clarsimp)
   apply (erule state_asids_to_policy_aux.cases)
     apply clarsimp
     apply (drule s0_caps_of_state, clarsimp)
     apply (simp add: Sys1AuthGraph_def Sys1PAS_def Sys1ASIDMap_def)
     apply (elim disjE conjE, simp_all add: Sys1AgentMap_simps cap_auth_conferred_def
                                            cap_rights_to_auth_def Low_asid_def High_asid_def
       asid_low_bits_def asid_high_bits_of_def )[1]
    apply (clarsimp simp: state_vrefs_def
                           vs_refs_no_global_pts_def
                           s0_internal_def kh0_def  Sys1AgentMap_simps
                           kh0_obj_def comp_def Low_pt'_def High_pt'_def
                           pte_ref_def pde_ref2_def Low_pd'_def High_pd'_def
                           Sys1AuthGraph_def ptr_range_def
                     dest!: graph_ofD
                     split: if_splits)
   apply (clarsimp simp: s0_internal_def arch_state0_def)
  apply (rule subsetI, clarsimp)
  apply (erule state_irqs_to_policy_aux.cases)
   apply (simp add: Sys1AuthGraph_def Sys1PAS_def Sys1ASIDMap_def)
   apply (drule s0_caps_of_state)
   apply (simp add: Sys1AuthGraph_def Sys1PAS_def Sys1ASIDMap_def)
   apply (elim disjE conjE, simp_all add: Sys1AgentMap_simps cap_auth_conferred_def cap_rights_to_auth_def Low_asid_def High_asid_def
     asid_low_bits_def asid_high_bits_of_def )[1]
   done

lemma Sys1_pas_cur_domain:
  "pas_cur_domain Sys1PAS s0_internal"
  by (simp add: s0_internal_def exst0_def Sys1PAS_def)

lemma Sys1_current_subject_idemp:
  "Sys1PAS\<lparr>pasSubject := the_elem (pasDomainAbs Sys1PAS (cur_domain s0_internal))\<rparr> = Sys1PAS"
  apply (simp add: Sys1PAS_def s0_internal_def exst0_def)
  done

lemma pasMaySendIrqs_Sys1PAS[simp]:
  "pasMaySendIrqs Sys1PAS = False"
  by(auto simp: Sys1PAS_def)

lemma Sys1_pas_domains_distinct:
  "pas_domains_distinct Sys1PAS"
  apply (clarsimp simp: Sys1PAS_def pas_domains_distinct_def)
  done

lemma Sys1_pas_wellformed_noninterference:
  "pas_wellformed_noninterference Sys1PAS"
  apply (simp add: pas_wellformed_noninterference_def)
  apply (intro conjI ballI allI)
    apply (blast intro: Sys1_wellformed)
   apply (clarsimp simp: Sys1PAS_def policy_wellformed_def Sys1AuthGraph_def)
  apply (rule Sys1_pas_domains_distinct)
  done

lemma silc_inv_s0:
  "silc_inv Sys1PAS s0_internal s0_internal"
  apply (clarsimp simp: silc_inv_def)
  apply (rule conjI, simp add: Sys1PAS_def)
  apply (rule conjI)
   apply (clarsimp simp: Sys1PAS_def Sys1AgentMap_def
                         s0_internal_def kh0_def obj_at_def kh0_obj_def
                         is_cap_table_def Silc_caps_well_formed split: if_split_asm)
  apply (rule conjI)
   apply (clarsimp simp: Sys1PAS_def Sys1AuthGraph_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=Silc_cnode_ptr in exI)
   apply (rule conjI)
    apply (rule_tac x="the_nat_to_bl_10 318" in exI)
    apply (clarsimp simp: slots_holding_overlapping_caps_def2)
    apply (case_tac "cap = NullCap")
     apply clarsimp
     apply (simp add: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def)
     apply (case_tac a, clarsimp)
     apply (clarsimp split: if_splits)
            apply ((clarsimp simp: intra_label_cap_def cte_wp_at_cases tcb_cap_cases_def
                                   cap_points_to_label_def split: if_split_asm)+)[8]
    apply (clarsimp simp: intra_label_cap_def cap_points_to_label_def)
    apply (drule cte_wp_at_caps_of_state' s0_caps_of_state)+
    apply ((erule disjE |
          clarsimp simp: Sys1PAS_def Sys1AgentMap_simps
              the_nat_to_bl_def nat_to_bl_def ctes_wp_at_def cte_wp_at_cases
              s0_internal_def kh0_def kh0_obj_def Silc_caps_well_formed obj_refs_def
         | simp add: Silc_caps_def)+)[1]
   apply (simp add: Sys1PAS_def Sys1AgentMap_simps)
  apply (intro conjI)
  apply (clarsimp simp: all_children_def s0_internal_def silc_dom_equiv_def equiv_for_refl)
  apply (clarsimp simp: all_children_def s0_internal_def silc_dom_equiv_def equiv_for_refl)
  apply (clarsimp simp: Invariants_AI.cte_wp_at_caps_of_state )
  by (auto simp:is_transferable.simps dest:s0_caps_of_state)


lemma only_timer_irq_s0:
  "only_timer_irq timer_irq s0_internal"
  apply (clarsimp simp: only_timer_irq_def s0_internal_def irq_is_recurring_def is_irq_at_def
                        irq_at_def Let_def irq_oracle_def machine_state0_def timer_irq_def)
  apply presburger
  done

lemma domain_sep_inv_s0:
  "domain_sep_inv False s0_internal s0_internal"
  apply (clarsimp simp: domain_sep_inv_def)
  apply (force dest: cte_wp_at_caps_of_state' s0_caps_of_state
        | rule conjI allI | clarsimp simp: s0_internal_def)+
  done

lemma only_timer_irq_inv_s0:
  "only_timer_irq_inv timer_irq s0_internal s0_internal"
  by (simp add: only_timer_irq_inv_def only_timer_irq_s0 domain_sep_inv_s0)

lemma Sys1_guarded_pas_domain:
  "guarded_pas_domain Sys1PAS s0_internal"
  by (clarsimp simp: guarded_pas_domain_def Sys1PAS_def s0_internal_def
                     exst0_def Sys1AgentMap_simps)

lemma s0_valid_domain_list:
  "valid_domain_list s0_internal"
  by (clarsimp simp: valid_domain_list_2_def s0_internal_def exst0_def)


definition
  "s0 \<equiv> ((if ct_idle s0_internal then idle_context s0_internal else s0_context,s0_internal),KernelExit)"



subsubsection \<open>einvs\<close>


lemma well_formed_cnode_n_s0_caps[simp]:
  "well_formed_cnode_n 10 High_caps"
  "well_formed_cnode_n 10 Low_caps"
  "well_formed_cnode_n 10 Silc_caps"
  "\<not> well_formed_cnode_n 10 [[] \<mapsto> NullCap]"
  apply ((force simp: High_caps_def Low_caps_def Silc_caps_def well_formed_cnode_n_def
                  the_nat_to_bl_def nat_to_bl_def dom_empty_cnode)+)[3]
  apply (clarsimp simp: well_formed_cnode_n_def)
  apply (drule eqset_imp_iff[where x="[]"])
  apply simp
  done

lemma valid_caps_s0[simp]:
  "s0_internal \<turnstile> ThreadCap Low_tcb_ptr"
  "s0_internal \<turnstile> ThreadCap High_tcb_ptr"
  "s0_internal \<turnstile> CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2)"
  "s0_internal \<turnstile> CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2)"
  "s0_internal \<turnstile> CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2)"
  "s0_internal \<turnstile> ArchObjectCap (PageDirectoryCap Low_pd_ptr (Some Low_asid))"
  "s0_internal \<turnstile> ArchObjectCap (PageDirectoryCap High_pd_ptr (Some High_asid))"
  "s0_internal \<turnstile> NotificationCap ntfn_ptr 0 {AllowWrite}"
  "s0_internal \<turnstile> NotificationCap ntfn_ptr 0 {AllowRead}"
  "s0_internal \<turnstile> ReplyCap Low_tcb_ptr True {AllowGrant,AllowWrite}"
  "s0_internal \<turnstile> ReplyCap High_tcb_ptr True {AllowGrant,AllowWrite}"
  by (simp_all add: valid_cap_def s0_internal_def s0_ptr_defs cap_aligned_def is_aligned_def
                       word_bits_def cte_level_bits_def the_nat_to_bl_def
                       nat_to_bl_def Low_asid_def High_asid_def asid_low_bits_def asid_bits_def
                       obj_at_def kh0_def kh0_obj_def is_tcb_def is_cap_table_def a_type_def
                       is_ntfn_def)

lemma valid_obj_s0[simp]:
  "valid_obj Low_cnode_ptr  Low_cnode s0_internal"
  "valid_obj High_cnode_ptr High_cnode s0_internal"
  "valid_obj Silc_cnode_ptr Silc_cnode s0_internal"
  "valid_obj ntfn_ptr        ntfn s0_internal"
  "valid_obj irq_cnode_ptr  irq_cnode s0_internal"
  "valid_obj Low_pd_ptr     Low_pd s0_internal"
  "valid_obj High_pd_ptr    High_pd s0_internal"
  "valid_obj Low_pt_ptr     Low_pt s0_internal"
  "valid_obj High_pt_ptr    High_pt s0_internal"
  "valid_obj Low_tcb_ptr    Low_tcb s0_internal"
  "valid_obj High_tcb_ptr   High_tcb s0_internal"
  "valid_obj idle_tcb_ptr   idle_tcb s0_internal"
  "valid_obj init_global_pd (ArchObj (PageDirectory ((\<lambda>_. InvalidPDE)
            (ucast (kernel_base >> 20) := SectionPDE (addrFromPPtr kernel_base) {} 0 {}))))
                                     s0_internal"
  "valid_obj init_globals_frame (ArchObj (DataPage False ARMSmallPage)) s0_internal"
               apply (simp_all add: valid_obj_def kh0_obj_def)
              apply (simp add: valid_cs_def Low_caps_ran High_caps_ran Silc_caps_ran
                               valid_cs_size_def word_bits_def cte_level_bits_def)+
           apply (simp add: valid_ntfn_def obj_at_def s0_internal_def kh0_def
                            High_tcb_def is_tcb_def)
          apply (simp add: valid_cs_def valid_cs_size_def word_bits_def cte_level_bits_def)
          apply (simp add: well_formed_cnode_n_def)
         apply (fastforce simp: Low_pd'_def High_pd'_def Low_pt'_def High_pt'_def
                                Low_pt_ptr_def High_pt_ptr_def
                                shared_page_ptr_phys_def shared_page_ptr_virt_def
                                valid_vm_rights_def vm_kernel_only_def
                                kernel_base_def pageBits_def pt_bits_def vmsz_aligned_def
                                is_aligned_def[THEN iffD2]
                                is_aligned_addrFromPPtr_n)+
     apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def is_master_reply_cap_def
                           valid_ipc_buffer_cap_def valid_tcb_state_def valid_arch_tcb_def
           | simp add: obj_at_def s0_internal_def kh0_def kh0_obj_def is_ntfn_def
                       is_valid_vtable_root_def)+
  apply (simp add: valid_vm_rights_def vm_kernel_only_def
                   kernel_base_def pageBits_def vmsz_aligned_def
                   is_aligned_def[THEN iffD2]
                   is_aligned_addrFromPPtr_n)
  done

lemma valid_objs_s0:
  "valid_objs s0_internal"
  apply (clarsimp simp: valid_objs_def)
  apply (subst(asm) s0_internal_def kh0_def)+
  apply (simp split: if_split_asm)
    apply force+
  apply (clarsimp simp: valid_obj_def valid_cs_def empty_cnode_def valid_cs_size_def ran_def
                        cte_level_bits_def word_bits_def well_formed_cnode_n_def dom_def)
  done

lemma pspace_aligned_s0:
  "pspace_aligned s0_internal"
  apply (clarsimp simp: pspace_aligned_def s0_internal_def)
  apply (drule kh0_SomeD)
  apply (erule disjE
         | (subst is_aligned_def,
           fastforce simp: s0_ptr_defs cte_level_bits_def kh0_def kh0_obj_def))+
  apply (clarsimp simp: cte_level_bits_def)
  apply (drule irq_node_offs_range_correct)
  apply (clarsimp simp: s0_ptr_defs cte_level_bits_def)
  apply (rule is_aligned_add[OF _ is_aligned_shift])
  apply (simp add: is_aligned_def s0_ptr_defs cte_level_bits_def)
  done

lemma pspace_distinct_s0:
  "pspace_distinct s0_internal"
  apply (clarsimp simp: pspace_distinct_def s0_internal_def)
  apply (drule kh0_SomeD)+
  apply (case_tac "x \<in> irq_node_offs_range \<and> y \<in> irq_node_offs_range")
   apply clarsimp
   apply (drule irq_node_offs_range_correct)+
   apply clarsimp
   apply (clarsimp simp: s0_ptr_defs cte_level_bits_def)
   apply (case_tac "(ucast irq << 4) < (ucast irqa << 4)")
    apply (frule udvd_decr'[where K="0x10::32 word" and ua=0, simplified])
       apply (simp add: shiftl_t2n uint_word_ariths)
       apply (subst mod_mult_mult1[where c="2^4" and b="2^28", simplified])
       apply simp
      apply (simp add: shiftl_t2n uint_word_ariths)
      apply (subst mod_mult_mult1[where c="2^4" and b="2^28", simplified])
      apply simp
     apply (simp add: shiftl_def uint_shiftl word_size bintrunc_shiftl)
     apply (simp add: shiftl_int_def take_bit_eq_mod push_bit_eq_mult)
    apply (frule_tac y="ucast irq << 4" in word_plus_mono_right[where x="0xE000800F"])
     apply (simp add: shiftl_t2n)
     apply (case_tac "(1::32 word) \<le> ucast irqa")
      apply (drule_tac i=1 and k="0x10" in word_mult_le_mono1)
        apply simp
       apply (cut_tac x=irqa and 'a=32 in ucast_less)
        apply simp
       apply (simp add: word_less_nat_alt)
      apply (simp add: mult.commute)
      apply (drule_tac y="0x10" and x="0xE0007FFF" in word_plus_mono_right)
       apply (rule_tac sz=28 in machine_word_plus_mono_right_split)
        apply (simp add: unat_word_ariths mask_def)
        apply (cut_tac x=irqa and 'a=32 in ucast_less)
         apply simp
        apply (simp add: word_less_nat_alt)
       apply (simp add: word_bits_def)
      apply simp
     apply (simp add: lt1_neq0)
    apply (drule(1) order_trans_rules(23))
    apply clarsimp
    apply (drule_tac a="0xE0008000 + (ucast irqa << 4)" and b="ucast irqa << 4"
                 and c="0xE0007FFF + (ucast irqa << 4)" and d="ucast irqa << 4" in word_sub_mono)
       apply simp
      apply simp
      apply (rule_tac sz=28 in machine_word_plus_mono_right_split)
       apply (simp add: unat_word_ariths mask_def shiftl_t2n)
       apply (cut_tac x=irqa and 'a=32 in ucast_less)
        apply simp
       apply (simp add: word_less_nat_alt)
      apply (simp add: word_bits_def)
     apply simp
     apply (rule_tac sz=28 in machine_word_plus_mono_right_split)
      apply (simp add: unat_word_ariths mask_def shiftl_t2n)
      apply (cut_tac x=irqa and 'a=32 in ucast_less)
       apply simp
      apply (simp add: word_less_nat_alt)
     apply (simp add: word_bits_def)
    apply simp
   apply (case_tac "(ucast irq << 4) > (ucast irqa << 4)")
    apply (frule udvd_decr'[where K="0x10::32 word" and ua=0, simplified])
       apply (simp add: shiftl_t2n uint_word_ariths)
       apply (subst mod_mult_mult1[where c="2^4" and b="2^28", simplified])
       apply simp
      apply (simp add: shiftl_t2n uint_word_ariths)
      apply (subst mod_mult_mult1[where c="2^4" and b="2^28", simplified])
      apply simp
     apply (simp add: shiftl_def uint_shiftl word_size bintrunc_shiftl)
     apply (simp add: shiftl_int_def take_bit_eq_mod push_bit_eq_mult)
    apply (frule_tac y="ucast irqa << 4" in word_plus_mono_right[where x="0xE000800F"])
     apply (simp add: shiftl_t2n)
     apply (case_tac "(1::32 word) \<le> ucast irq")
      apply (drule_tac i=1 and k="0x10" in word_mult_le_mono1)
        apply simp
       apply (cut_tac x=irq and 'a=32 in ucast_less)
        apply simp
       apply (simp add: word_less_nat_alt)
      apply (simp add: mult.commute)
      apply (drule_tac y="0x10" and x="0xE0007FFF" in word_plus_mono_right)
       apply (rule_tac sz=28 in machine_word_plus_mono_right_split)
        apply (simp add: unat_word_ariths mask_def)
        apply (cut_tac x=irq and 'a=32 in ucast_less)
         apply simp
        apply (simp add: word_less_nat_alt)
       apply (simp add: word_bits_def)
      apply simp
     apply (simp add: lt1_neq0)
    apply (drule(1) order_trans_rules(23))
    apply clarsimp
    apply (drule_tac a="0xE0008000 + (ucast irq << 4)" and b="ucast irq << 4"
                 and c="0xE0007FFF + (ucast irq << 4)" and d="ucast irq << 4" in word_sub_mono)
       apply simp
      apply simp
      apply (rule_tac sz=28 in machine_word_plus_mono_right_split)
       apply (simp add: unat_word_ariths mask_def shiftl_t2n)
       apply (cut_tac x=irq and 'a=32 in ucast_less)
        apply simp
       apply (simp add: word_less_nat_alt)
      apply (simp add: word_bits_def)
     apply simp
     apply (rule_tac sz=28 in machine_word_plus_mono_right_split)
      apply (simp add: unat_word_ariths mask_def shiftl_t2n)
      apply (cut_tac x=irq and 'a=32 in ucast_less)
       apply simp
      apply (simp add: word_less_nat_alt)
     apply (simp add: word_bits_def)
    apply simp
   apply simp
  by ((simp | erule disjE | clarsimp simp: kh0_obj_def cte_level_bits_def s0_ptr_defs
        | clarsimp simp: irq_node_offs_range_def s0_ptr_defs,
          drule_tac x="0xF" in word_plus_strict_mono_right, simp, simp add: add.commute,
          drule(1) notE[rotated, OF less_trans, OF _ _ leD, rotated 2] |
          drule(1) notE[rotated, OF le_less_trans, OF _ _ leD, rotated 2], simp, assumption)+)

lemma valid_pspace_s0[simp]:
  "valid_pspace s0_internal"
  apply (simp add: valid_pspace_def pspace_distinct_s0 pspace_aligned_s0 valid_objs_s0)
  apply (rule conjI)
   apply (clarsimp simp: if_live_then_nonz_cap_def)
   apply (subst(asm) s0_internal_def)
   apply (clarsimp simp: live_def hyp_live_def obj_at_def kh0_def kh0_obj_def s0_ptr_defs split: if_split_asm)
     apply (clarsimp simp: ex_nonz_cap_to_def)
     apply (rule_tac x="High_cnode_ptr" in exI)
     apply (rule_tac x="the_nat_to_bl_10 1" in exI)
     apply (force simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def s0_ptr_defs tcb_cap_cases_def High_caps_def the_nat_to_bl_def nat_to_bl_def well_formed_cnode_n_def dom_empty_cnode)
    apply (clarsimp simp: ex_nonz_cap_to_def)
    apply (rule_tac x="Low_cnode_ptr" in exI)
    apply (rule_tac x="the_nat_to_bl_10 1" in exI)
    apply (force simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def s0_ptr_defs tcb_cap_cases_def Low_caps_def the_nat_to_bl_def nat_to_bl_def well_formed_cnode_n_def dom_empty_cnode)
   apply (clarsimp simp: ex_nonz_cap_to_def)
   apply (rule_tac x="High_cnode_ptr" in exI)
   apply (rule_tac x="the_nat_to_bl_10 318" in exI)
   apply (force simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def s0_ptr_defs tcb_cap_cases_def High_caps_def the_nat_to_bl_def nat_to_bl_def well_formed_cnode_n_def dom_empty_cnode)
  apply (rule conjI)
   apply (simp add: Invariants_AI.cte_wp_at_caps_of_state zombies_final_def)
   apply (force dest: s0_caps_of_state simp: is_zombie_def)
  apply (rule conjI)
   apply (clarsimp simp: sym_refs_def state_refs_of_def state_hyp_refs_of_def s0_internal_def)
   apply (subst(asm) kh0_def)
   apply (clarsimp split: if_split_asm)
   apply (simp add: refs_of_def kh0_def s0_ptr_defs kh0_obj_def)+
  apply (clarsimp simp: sym_refs_def state_hyp_refs_of_def s0_internal_def)
  apply (subst(asm) kh0_def)
  apply (clarsimp split: if_split_asm)
             by (simp add: refs_of_def kh0_def s0_ptr_defs kh0_obj_def)+

lemma descendants_s0[simp]:
  "descendants_of (a, b) (cdt s0_internal) = {}"
  apply (rule set_eqI)
  apply clarsimp
  apply (drule descendants_of_NoneD[rotated])
   apply (simp add: s0_internal_def)+
   done

lemma valid_mdb_s0[simp]:
  "valid_mdb s0_internal"
  apply (simp add: valid_mdb_def reply_mdb_def)
  apply (intro conjI)
           apply (clarsimp simp: mdb_cte_at_def s0_internal_def)
          apply (force dest: s0_caps_of_state simp: untyped_mdb_def)
         apply (clarsimp simp: descendants_inc_def)
        apply (clarsimp simp: no_mloop_def s0_internal_def cdt_parent_defs)
       apply (clarsimp simp: untyped_inc_def)
       apply (drule s0_caps_of_state)+
       apply ((simp | erule disjE)+)[1]
      apply (force dest: s0_caps_of_state simp: ut_revocable_def)
     apply (force dest: s0_caps_of_state simp: irq_revocable_def)
    apply (clarsimp simp: reply_master_revocable_def)
    apply (drule s0_caps_of_state)
    apply ((simp add: is_master_reply_cap_def s0_internal_def s0_ptr_defs | erule disjE)+)[1]
   apply (force dest: s0_caps_of_state simp: reply_caps_mdb_def)
  apply (clarsimp simp: reply_masters_mdb_def)
  apply (simp add: s0_internal_def)
  done

lemma valid_ioc_s0[simp]:
  "valid_ioc s0_internal"
  by (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def valid_ioc_def
                        s0_internal_def kh0_def kh0_obj_def split: if_split_asm)+

lemma valid_idle_s0[simp]:
  "valid_idle s0_internal"
  apply (clarsimp simp: valid_idle_def st_tcb_at_tcb_states_of_state_eq
                        thread_bounds_of_state_s0
                        identity_eq[symmetric] tcb_states_of_state_s0
                        valid_arch_idle_def)
  by (simp add: s0_ptr_defs s0_internal_def idle_thread_ptr_def pred_tcb_at_def obj_at_def kh0_def idle_tcb_def)

lemma only_idle_s0[simp]:
  "only_idle s0_internal"
  apply (clarsimp simp: only_idle_def st_tcb_at_tcb_states_of_state_eq
                        identity_eq[symmetric] tcb_states_of_state_s0)
  apply (simp add: s0_ptr_defs s0_internal_def)
  done

lemma if_unsafe_then_cap_s0[simp]:
  "if_unsafe_then_cap s0_internal"
  apply (clarsimp simp: if_unsafe_then_cap_def ex_cte_cap_wp_to_def)
  apply (drule s0_caps_of_state)
  apply (case_tac "a=Low_cnode_ptr")
   apply (rule_tac x=Low_tcb_ptr in exI, rule_tac x="tcb_cnode_index 0" in exI)
   apply ((clarsimp simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def
                          tcb_cap_cases_def the_nat_to_bl_def nat_to_bl_def
                          Low_caps_def | erule disjE)+)[1]
  apply (case_tac "a=High_cnode_ptr")
   apply (rule_tac x=High_tcb_ptr in exI, rule_tac x="tcb_cnode_index 0" in exI)
   apply ((clarsimp simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def
                          tcb_cap_cases_def the_nat_to_bl_def nat_to_bl_def
                          High_caps_def | erule disjE)+)[1]
  apply (case_tac "a=Low_tcb_ptr")
   apply (rule_tac x=Low_cnode_ptr in exI, rule_tac x="the_nat_to_bl_10 1" in exI)
   apply ((clarsimp simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def
                          tcb_cap_cases_def the_nat_to_bl_def nat_to_bl_def
                          Low_caps_def well_formed_cnode_n_def dom_empty_cnode
         | erule disjE | force)+)[1]
  apply (case_tac "a=High_tcb_ptr")
   apply (rule_tac x=High_cnode_ptr in exI, rule_tac x="the_nat_to_bl_10 1" in exI)
   apply ((clarsimp simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def
                          tcb_cap_cases_def the_nat_to_bl_def nat_to_bl_def
                          High_caps_def well_formed_cnode_n_def dom_empty_cnode
         | erule disjE | force)+)[1]
  apply (rule_tac x=Silc_cnode_ptr in exI, rule_tac x="the_nat_to_bl_10 2" in exI)
  apply ((clarsimp simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def
                         tcb_cap_cases_def the_nat_to_bl_def nat_to_bl_def
                         Silc_caps_def well_formed_cnode_n_def dom_empty_cnode
        | erule disjE | force)+)[1]
  done

lemma valid_reply_caps_s0[simp]:
  "valid_reply_caps s0_internal"
  apply (clarsimp simp: valid_reply_caps_def)
  apply (rule conjI)
   apply (force  dest: s0_caps_of_state
                 simp: Invariants_AI.cte_wp_at_caps_of_state has_reply_cap_def is_reply_cap_to_def)
  apply (clarsimp simp: unique_reply_caps_def)
  apply (drule s0_caps_of_state)+
  apply (erule disjE | simp add: is_reply_cap_def)+
  done

lemma valid_reply_masters_s0[simp]:
  "valid_reply_masters s0_internal"
  apply (clarsimp simp: valid_reply_masters_def)
  apply (force dest: s0_caps_of_state
               simp: Invariants_AI.cte_wp_at_caps_of_state  is_master_reply_cap_to_def)
  done

lemma valid_global_refs_s0[simp]:
  "valid_global_refs s0_internal"
  apply (clarsimp simp: valid_global_refs_def valid_refs_def)
  apply (simp add: Invariants_AI.cte_wp_at_caps_of_state)
  apply clarsimp
  apply (drule s0_caps_of_state)
  apply (clarsimp simp: global_refs_def s0_internal_def arch_state0_def)
  apply (erule disjE | simp add: cap_range_def
                     | clarsimp simp: irq_node_offs_distinct[symmetric]
                     | simp only: s0_ptr_defs, force)+
  done

lemma valid_arch_state_s0[simp]:
  "valid_arch_state s0_internal"
  apply (clarsimp simp: valid_arch_state_def s0_internal_def arch_state0_def)
  apply (intro conjI)
      apply (clarsimp simp: obj_at_def kh0_def)
     apply (simp add: valid_asid_table_def)
    apply (clarsimp simp: obj_at_def kh0_def a_type_def)
   apply (simp add: valid_global_pts_def)
  apply (simp add: is_inv_def)
  done

lemma valid_irq_node_s0[simp]:
  "valid_irq_node s0_internal"
  apply (clarsimp simp: valid_irq_node_def)
  apply (rule conjI)
   apply (simp add: s0_internal_def)
   apply (rule injI)
   apply simp
   apply (rule ccontr)
   apply (rule_tac bnd="0x400" and 'a=32 in shift_distinct_helper[rotated 3])
        apply assumption
       apply (simp add: cte_level_bits_def)
      apply (simp add: cte_level_bits_def)
     apply (rule ucast_less[where 'b=10, simplified])
     apply simp
    apply (rule ucast_less[where 'b=10, simplified])
    apply simp
   apply (rule notI)
   apply (drule ucast_up_inj)
    apply simp
   apply simp
  apply (clarsimp simp: obj_at_def s0_internal_def)
  apply (force simp: kh0_def is_cap_table_def well_formed_cnode_n_def dom_empty_cnode)
  done

lemma valid_irq_handlers_s0[simp]:
  "valid_irq_handlers s0_internal"
  apply (clarsimp simp: valid_irq_handlers_def ran_def)
  apply (force dest: s0_caps_of_state)
  done

lemma valid_irq_state_s0[simp]:
  "valid_irq_states s0_internal"
  apply (clarsimp simp: valid_irq_states_def valid_irq_masks_def s0_internal_def machine_state0_def)
  done

lemma valid_machine_state_s0[simp]:
  "valid_machine_state s0_internal"
  apply (clarsimp simp: valid_machine_state_def s0_internal_def machine_state0_def in_user_frame_def obj_at_def const_def)
  done

lemma valid_arch_objs_s0[simp]:
  "valid_vspace_objs s0_internal"
  apply (clarsimp simp: valid_vspace_objs_def obj_at_def s0_internal_def)
  apply (drule kh0_SomeD)
  apply (erule disjE | clarsimp simp: addrFromPPtr_def
         | erule vs_lookupE, force simp: arch_state0_def vs_asid_refs_def)+
  done


lemma valid_arch_caps_s0[simp]:
  "valid_arch_caps s0_internal"
  apply (clarsimp simp: valid_arch_caps_def)
  apply (intro conjI)
     apply (clarsimp simp: valid_vs_lookup_def vs_lookup_pages_def vs_asid_refs_def
                           s0_internal_def arch_state0_def)
    apply (clarsimp simp: valid_table_caps_def is_pd_cap_def is_pt_cap_def)
    apply (drule s0_caps_of_state)
    apply (erule disjE | simp)+
   apply (clarsimp simp: unique_table_caps_def is_pd_cap_def is_pt_cap_def)
   apply (drule s0_caps_of_state)+
   apply (erule disjE | simp)+
  apply (clarsimp simp: unique_table_refs_def table_cap_ref_def)
  apply (drule s0_caps_of_state)+
  by auto

lemma valid_global_objs_s0[simp]:
  "valid_global_objs s0_internal"
  apply (clarsimp simp: valid_global_objs_def s0_internal_def arch_state0_def)
  apply (force simp: valid_vso_at_def obj_at_def kh0_def kh0_obj_def
                     is_aligned_addrFromPPtr kernel_base_aligned_pageBits
                     kernel_mapping_slots_def empty_table_def pde_ref_def valid_pde_mappings_def)
  done

lemma valid_kernel_mappings_s0[simp]:
  "valid_kernel_mappings s0_internal"
  apply (clarsimp simp: valid_kernel_mappings_def s0_internal_def ran_def
                 valid_kernel_mappings_if_pd_def split: kernel_object.splits
                                                        arch_kernel_obj.splits)
  apply (drule kh0_SomeD)
  apply (clarsimp simp: arch_state0_def kernel_mapping_slots_def)
  apply (erule disjE | simp add: pde_ref_def s0_ptr_defs kh0_obj_def High_pd'_def Low_pd'_def
                          split: if_split_asm pde.splits)+
  done

lemma equal_kernel_mappings_s0[simp]:
  "equal_kernel_mappings s0_internal"
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def s0_internal_def)
  apply (drule kh0_SomeD)+
  apply (force simp: kh0_obj_def High_pd'_def Low_pd'_def s0_ptr_defs kernel_mapping_slots_def)
  done

lemma valid_asid_map_s0[simp]:
  "valid_asid_map s0_internal"
  apply (clarsimp simp: valid_asid_map_def s0_internal_def arch_state0_def)
  done

lemma valid_global_pd_mappings_s0[simp]:
  "valid_global_vspace_mappings s0_internal"
  apply (clarsimp simp: valid_global_vspace_mappings_def s0_internal_def arch_state0_def
                        obj_at_def kh0_def kh0_obj_def s0_ptr_defs valid_pd_kernel_mappings_def
                        valid_pde_kernel_mappings_def pde_mapping_bits_def mask_def)
  apply (rule conjI)
   apply force
  apply clarsimp
  apply (subgoal_tac "xa - 0xFFFFF \<le> ucast x << 20")
   apply (case_tac "ucast x << 20 > (0xE0000000::32 word)")
    apply (subgoal_tac "(0xE0100000::32 word) \<le> ucast x << 20")
     apply ((drule(1) order_trans_rules(23))+, force)
    apply (simp add: shiftl_t2n)
    apply (cut_tac p="0xE0000000::32 word" and n=20 and m=20 and q="0x100000 * ucast x" in word_plus_power_2_offset_le)
         apply (simp add: is_aligned_def)
        apply (simp add: is_aligned_def unat_word_ariths)
        apply (subst mod_mult_mult1[where c="2^20" and b="2^12", simplified])
        apply simp
       apply simp
      apply simp
     apply simp
    apply simp
   apply (case_tac "ucast x << 20 < (0xE0000000::32 word)")
    apply (subgoal_tac "(0xE0000000::32 word) - 0x100000 \<ge> ucast x << 20")
     apply (subgoal_tac "0xFFFFF + (ucast x << 20) \<le> 0xDFFFFFFF")
      apply (drule_tac y="0xFFFFF + (ucast x << 20)" and z="0xDFFFFFFF::32 word" in order_trans_rules(23))
       apply simp
      apply ((drule(1) order_trans_rules(23))+, force)
     apply (simp add: add.commute)
     apply (simp add: word_plus_mono_left[where x="0xFFFFF" and z="0xDFF00000", simplified])
    apply (simp add: shiftl_t2n)
    apply (rule udvd_decr'[where K="0x100000" and q="0xE0000000" and ua=0, simplified])
       apply simp
      apply (simp add: uint_word_ariths)
      apply (subst mod_mult_mult1[where c="2^20" and b="2^12", simplified])
      apply simp
     apply simp
    apply simp
   apply (erule notE)
   apply (cut_tac x="ucast x::32 word" and n=20 in shiftl_shiftr_id)
     apply simp
    apply (simp add: ucast_less[where 'b=12, simplified])
   apply simp
   apply (rule ucast_up_inj[where 'b=32])
    apply simp
   apply simp
  apply (drule_tac c="0xFFFFF + (ucast x << 20)" and d="0xFFFFF" and b="0xFFFFF" in word_sub_mono)
     apply simp
    apply (rule word_sub_le)
    apply (rule order_trans_rules(23)[rotated], assumption)
    apply simp
   apply (simp add: add.commute)
   apply (rule no_plus_overflow_neg)
   apply simp
   apply (drule_tac x="ucast x << 20" in order_trans_rules(23), assumption)
   apply (simp add: le_less_trans)
  apply simp
  done

lemma pspace_in_kernel_window_s0[simp]:
  "pspace_in_kernel_window s0_internal"
  apply (clarsimp simp: pspace_in_kernel_window_def s0_internal_def)
  apply (drule kh0_SomeD)
  apply (erule disjE | simp add: arch_state0_def kh0_obj_def s0_ptr_defs mask_def
                                 irq_node_offs_range_def cte_level_bits_def | rule conjI
                     | rule order_trans_rules(23)[rotated] order_trans_rules(23), force, force)+
   apply (force intro: order_trans_rules(23)[rotated])
  apply clarsimp
  apply (drule_tac x=y in le_less_trans)
   apply (rule neq_le_trans[rotated])
    apply (rule word_plus_mono_right)
     apply (rule less_imp_le)
     apply simp+
  apply (force intro: less_imp_le less_le_trans)
  done

lemma cap_refs_in_kernel_window_s0[simp]:
  "cap_refs_in_kernel_window s0_internal"
  apply (clarsimp simp: cap_refs_in_kernel_window_def valid_refs_def cap_range_def
                        Invariants_AI.cte_wp_at_caps_of_state)
  apply (drule s0_caps_of_state)
  apply (erule disjE | simp add: arch_state0_def s0_internal_def s0_ptr_defs mask_def)+
  done

lemma cur_tcb_s0[simp]:
  "cur_tcb s0_internal"
  by (simp add: cur_tcb_def s0_ptr_defs s0_internal_def kh0_def kh0_obj_def obj_at_def is_tcb_def)

lemma valid_list_s0[simp]:
  "valid_list s0_internal"
  apply (simp add: valid_list_2_def s0_internal_def exst0_def const_def)
  done

lemma valid_sched_s0[simp]:
  "valid_sched s0_internal"
  apply (simp add: valid_sched_def s0_internal_def exst0_def)
  apply (intro conjI)
        apply (clarsimp simp: valid_etcbs_def s0_ptr_defs kh0_def kh0_obj_def is_etcb_at'_def
                              st_tcb_at_kh_def obj_at_kh_def obj_at_def)
       apply (clarsimp simp: const_def)
      apply (clarsimp simp: const_def)
     apply (clarsimp simp: valid_sched_action_def is_activatable_def st_tcb_at_kh_def
                           obj_at_kh_def obj_at_def kh0_def kh0_obj_def s0_ptr_defs)
    apply (clarsimp simp: ct_in_cur_domain_def in_cur_domain_def etcb_at'_def ekh0_obj_def
                          s0_ptr_defs)
   apply (clarsimp simp: const_def valid_blocked_def st_tcb_at_kh_def obj_at_kh_def obj_at_def
                         kh0_def kh0_obj_def split: if_split_asm)
  apply (clarsimp simp: valid_idle_etcb_def etcb_at'_def ekh0_obj_def s0_ptr_defs idle_thread_ptr_def)
  done

lemma respects_device_trivial:
  "pspace_respects_device_region s0_internal"
  "cap_refs_respects_device_region s0_internal"
  apply (clarsimp simp: s0_internal_def pspace_respects_device_region_def machine_state0_def device_mem_def
                        in_device_frame_def kh0_obj_def obj_at_kh_def obj_at_def kh0_def
                 split: if_splits)[1]
   apply fastforce
  apply (clarsimp simp: cap_refs_respects_device_region_def Invariants_AI.cte_wp_at_caps_of_state
                        cap_range_respects_device_region_def machine_state0_def)
  apply (intro conjI impI)
   apply (drule s0_caps_of_state)
   apply fastforce
  apply (clarsimp simp: s0_internal_def machine_state0_def)
  done

lemma einvs_s0:
  "einvs s0_internal"
  apply (simp add: valid_state_def invs_def respects_device_trivial)
  done

lemma obj_valid_pdpt_kh0:
  "x \<in> ran kh0 \<Longrightarrow> obj_valid_pdpt x"
  by (auto simp: kh0_def valid_entries_def obj_valid_pdpt_def idle_tcb_def High_tcb_def Low_tcb_def
                 High_pt_def High_pt'_def entries_align_def Low_pt_def High_pd_def Low_pt'_def High_pd'_def
                 Low_pd_def irq_cnode_def ntfn_def Silc_cnode_def High_cnode_def Low_cnode_def Low_pd'_def)

subsubsection \<open>Haskell state\<close>

text \<open>One invariant we need on s0 is that there exists
        an associated Haskell state satisfying the invariants.
        This does not yet exist.\<close>

lemma Sys1_valid_initial_state_noenabled:
  assumes extras_s0: "step_restrict s0"
  assumes utf_det: "\<forall>pl pr pxn tc ms s. det_inv InUserMode tc s \<and> einvs s \<and> context_matches_state pl pr pxn ms s \<and> ct_running s
                   \<longrightarrow> (\<exists>x. utf (cur_thread s) pl pr pxn (tc, ms) = {x})"
  assumes utf_non_empty: "\<forall>t pl pr pxn tc ms. utf t pl pr pxn (tc, ms) \<noteq> {}"
  assumes utf_non_interrupt: "\<forall>t pl pr pxn tc ms e f g. (e,f,g) \<in> utf t pl pr pxn (tc, ms) \<longrightarrow> e \<noteq> Some Interrupt"
  assumes det_inv_invariant: "invariant_over_ADT_if det_inv utf"
  assumes det_inv_s0: "det_inv KernelExit (cur_context s0_internal) s0_internal"
  shows "valid_initial_state_noenabled det_inv utf s0_internal Sys1PAS timer_irq s0_context"
  apply (unfold_locales, simp_all only: pasMaySendIrqs_Sys1PAS)
                     apply (insert det_inv_invariant)[9]
                     apply (erule(2) invariant_over_ADT_if.det_inv_abs_state)
                    apply ((erule invariant_over_ADT_if.det_inv_abs_state
                                  invariant_over_ADT_if.check_active_irq_if_Idle_det_inv
                                  invariant_over_ADT_if.check_active_irq_if_User_det_inv
                                  invariant_over_ADT_if.do_user_op_if_det_inv
                                  invariant_over_ADT_if.handle_preemption_if_det_inv
                                  invariant_over_ADT_if.kernel_entry_if_Interrupt_det_inv
                                  invariant_over_ADT_if.kernel_entry_if_det_inv
                                  invariant_over_ADT_if.kernel_exit_if_det_inv
                                  invariant_over_ADT_if.schedule_if_det_inv)+)[8]
            apply (rule Sys1_pas_cur_domain)
           apply (rule Sys1_pas_wellformed_noninterference)
          apply (simp only: einvs_s0)
          apply (simp add: Sys1_current_subject_idemp)
          apply (simp add: only_timer_irq_inv_s0 silc_inv_s0 Sys1_pas_cur_domain
                           domain_sep_inv_s0 Sys1_pas_refined Sys1_guarded_pas_domain
                           idle_equiv_refl)
          apply (clarsimp simp: obj_valid_pdpt_kh0 valid_domain_list_2_def s0_internal_def exst0_def)
         apply (simp add: det_inv_s0)
        apply (simp add: s0_internal_def exst0_def)
       apply (simp add: ct_in_state_def st_tcb_at_tcb_states_of_state_eq
                        identity_eq[symmetric] tcb_states_of_state_s0)
       apply (simp add: s0_ptr_defs s0_internal_def)
      apply (simp add: s0_internal_def exst0_def)
     apply (rule utf_det)
    apply (rule utf_non_empty)
   apply (rule utf_non_interrupt)
  apply (simp add: extras_s0[simplified s0_def])
  done

text \<open>the extra assumptions in valid_initial_state of being enabled,
        and a serial system, follow from ADT_IF_Refine\<close>

end

end
