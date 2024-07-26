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
  "AInvs.KernelInit_AI"
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
  irq_oracle_def: "RISCV64.irq_oracle \<equiv> \<lambda>pos. if pos mod 10 = 0 then 10 else 0"

context begin interpretation Arch . (*FIXME: arch-split*)

subsection \<open>We show that the authority graph does not let information flow from High to Low\<close>

datatype auth_graph_label = High | Low | IRQ0

abbreviation partition_label where
  "partition_label x \<equiv> OrdinaryLabel x"

definition Sys1AuthGraph :: "(auth_graph_label subject_label) auth_graph" where
  "Sys1AuthGraph \<equiv>
     {(partition_label High, Read, partition_label Low),
      (partition_label Low, Notify, partition_label High),
      (partition_label Low, Reset, partition_label High),
      (SilcLabel, Read, partition_label Low),
      (SilcLabel, Notify, partition_label High),
      (SilcLabel, Reset, partition_label High)}
   \<union> {(x, a, y). x = y}"

lemma subjectReads_Low:
  "subjectReads Sys1AuthGraph (partition_label Low) = {partition_label Low}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply (erule subjectReads.induct, (fastforce simp: Sys1AuthGraph_def)+)
  done

lemma Low_in_subjectReads_High:
  "partition_label Low \<in> subjectReads Sys1AuthGraph (partition_label High)"
  by (simp add: Sys1AuthGraph_def reads_read)

lemma subjectReads_High:
  "subjectReads Sys1AuthGraph (partition_label High) = {partition_label High, partition_label Low}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply (erule subjectReads.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply (auto intro: Low_in_subjectReads_High)
  done

lemma subjectReads_IRQ0:
  "subjectReads Sys1AuthGraph (partition_label IRQ0) = {partition_label IRQ0}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply (erule subjectReads.induct, (fastforce simp: Sys1AuthGraph_def)+)
  done

lemma High_in_subjectAffects_Low:
  "partition_label High \<in> subjectAffects Sys1AuthGraph (partition_label Low)"
  apply (rule affects_ep)
   apply (simp add: Sys1AuthGraph_def)
   apply (rule disjI1, simp+)
  done

lemma subjectAffects_Low:
  "subjectAffects Sys1AuthGraph (partition_label Low) = {partition_label Low, partition_label High}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply (erule subjectAffects.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply (auto intro: affects_lrefl High_in_subjectAffects_Low)
  done

lemma subjectAffects_High:
  "subjectAffects Sys1AuthGraph (partition_label High) = {partition_label High}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply (erule subjectAffects.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply (auto intro: affects_lrefl)
  done

lemma subjectAffects_IRQ0:
 "subjectAffects Sys1AuthGraph (partition_label IRQ0) = {partition_label IRQ0}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply (erule subjectAffects.induct, (fastforce simp: Sys1AuthGraph_def)+)
  apply (auto intro: affects_lrefl)
  done

lemmas subjectReads = subjectReads_High subjectReads_Low subjectReads_IRQ0

lemma partsSubjectAffects_Low:
  "partsSubjectAffects Sys1AuthGraph Low = {Partition Low, Partition High}"
  by (auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def
                 subjectReads subjectAffects_Low | case_tac xa, rename_tac xa)+

lemma partsSubjectAffects_High:
  "partsSubjectAffects Sys1AuthGraph High = {Partition High}"
  by (auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def
                 subjectReads subjectAffects_High | rename_tac xa, case_tac xa)+

lemma partsSubjectAffects_IRQ0:
  "partsSubjectAffects Sys1AuthGraph IRQ0 = {Partition IRQ0}"
  by (auto simp: partsSubjectAffects_def image_def label_can_affect_partition_def
                 subjectReads subjectAffects_IRQ0 | rename_tac xa, case_tac xa)+

lemmas partsSubjectAffects =
   partsSubjectAffects_High partsSubjectAffects_Low partsSubjectAffects_IRQ0

definition example_policy where
  "example_policy \<equiv>
     {(PSched, d) | d. True} \<union> {(d,e). d = e} \<union> {(Partition Low, Partition High)}"

lemma "policyFlows Sys1AuthGraph = example_policy"
  apply (rule equalityI)
   apply (rule subsetI)
   apply (clarsimp simp: example_policy_def)
   apply (erule policyFlows.cases)
    apply (case_tac l, auto simp: partsSubjectAffects)[1]
   apply assumption
  apply (rule subsetI)
  apply (clarsimp simp: example_policy_def)
  apply (elim disjE)
    apply (fastforce simp: partsSubjectAffects intro: policy_affects)
   apply (fastforce intro: policy_scheduler)
  apply (fastforce intro: policyFlows_refl refl_onD)
  done


subsection \<open>We show there exists a valid initial state associated to the
              above authority graph\<close>

text \<open>

This example (modified from ../access-control/ExampleSystem) is a system Sys1 made
of 2 main components Low and High, connected through an notification NTFN.
Both Low and High contains:

  . one TCB
  . one vspace made up of one top-level page table
  - one asid pool with a single entry for the corresponding vspace
  . each top-level pt contains a single page table, with access to a shared page in memory
     Low can read/write to this page, High can only read
  . one cspace made up of one cnode
  . each cspace contains 4 caps:
         one to the tcb
         one to the cnode itself
         one to the top level page table
         one to the asid pool
         one to the shared page
         one to the second level page table
         one to the ntfn

Low can send to the ntfn while High can receive from it.

Attempt to ASCII art:

          --------    ----                    ----   --------
          |       |   |  |                    |  |   |      |
          V       |   |  V    S         R     |  V   |      V
Low_tcb(3079)-->Low_cnode(6)--->ntfn(9)<---High_cnode(7)<--High_tcb(3080)
  |              |                               |          |
  V              |                               |          V
Low_pd(3063)<---------Low_pool      High_pool------------> High_pd(3065)
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

definition "ntfn_ptr \<equiv> pptr_base + 0x20"

definition "Low_tcb_ptr \<equiv> pptr_base + 0x400"
definition "High_tcb_ptr = pptr_base + 0x800"
definition "idle_tcb_ptr = pptr_base + 0x1000"

definition "Low_pt_ptr = pptr_base + 0x4000"
definition "High_pt_ptr = pptr_base + 0x5000"

definition "Low_pd_ptr = pptr_base + 0x7000"
definition "High_pd_ptr = pptr_base + 0x8000"

definition "Low_pool_ptr = pptr_base + 0x9000"
definition "High_pool_ptr = pptr_base + 0xA000"

definition "Low_cnode_ptr = pptr_base + 0x10000"
definition "High_cnode_ptr = pptr_base + 0x18000"
definition "Silc_cnode_ptr = pptr_base + 0x20000"
definition "irq_cnode_ptr = pptr_base + 0x28000"

definition "shared_page_ptr_virt = pptr_base + 0x200000"
definition "shared_page_ptr_phys = addrFromPPtr shared_page_ptr_virt"

definition "timer_irq \<equiv> 10" (* not sure exactly how this fits in *)

definition "Low_mcp \<equiv> 5 :: priority"
definition "Low_prio \<equiv> 5 :: priority"
definition "High_mcp \<equiv> 5 :: priority"
definition "High_prio \<equiv> 5 :: priority"
definition "Low_time_slice \<equiv> 0 :: nat"
definition "High_time_slice \<equiv> 5 :: nat"
definition "Low_domain \<equiv> 0 :: domain"
definition "High_domain \<equiv> 1 :: domain"

lemmas s0_ptr_defs =
  Low_pool_ptr_def High_pool_ptr_def Low_cnode_ptr_def High_cnode_ptr_def Silc_cnode_ptr_def
  ntfn_ptr_def irq_cnode_ptr_def Low_pd_ptr_def High_pd_ptr_def Low_pt_ptr_def High_pt_ptr_def
  Low_tcb_ptr_def High_tcb_ptr_def idle_tcb_ptr_def timer_irq_def Low_prio_def High_prio_def
  Low_time_slice_def Low_domain_def High_domain_def init_irq_node_ptr_def riscv_global_pt_ptr_def
  pptr_base_def pptrBase_def canonical_bit_def shared_page_ptr_virt_def

(* Distinctness proof of kernel pointers. *)

distinct ptrs_distinct[simp]:
  Low_tcb_ptr High_tcb_ptr idle_tcb_ptr ntfn_ptr
  Low_pt_ptr High_pt_ptr shared_page_ptr_virt Low_pd_ptr High_pd_ptr
  Low_cnode_ptr High_cnode_ptr Low_pool_ptr High_pool_ptr
  Silc_cnode_ptr irq_cnode_ptr riscv_global_pt_ptr
  by (auto simp: s0_ptr_defs)


text \<open>We need to define the asids of each pd and pt to ensure that
the object is included in the right ASID-label\<close>

definition Low_asid :: asid where
  "Low_asid \<equiv> 1 << asid_low_bits"

definition High_asid :: asid where
  "High_asid \<equiv> 2 << asid_low_bits"

definition Silc_asid :: asid where
  "Silc_asid \<equiv> 3 << asid_low_bits"

distinct asid_high_bits_distinct[simp]:
  "asid_high_bits_of Low_asid"
  "asid_high_bits_of High_asid"
  "asid_high_bits_of Silc_asid"
  by (auto simp: asid_high_bits_of_def asid_low_bits_def Low_asid_def High_asid_def Silc_asid_def)

distinct asids_distinct[simp]:
  High_asid Low_asid Silc_asid
  by (auto simp: Low_asid_def High_asid_def Silc_asid_def asid_low_bits_def)


text \<open>converting a nat to a bool list of size 10 - for the cnodes\<close>

definition nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list option" where
  "nat_to_bl bits n \<equiv>
    if n \<ge> 2^bits then None
    else Some $ bin_to_bl bits (of_nat n)"

lemma nat_to_bl_id [simp]: "nat_to_bl (size (x :: (('a::len) word))) (unat x) = Some (to_bl x)"
  by (clarsimp simp: nat_to_bl_def to_bl_def le_def word_size)

definition the_nat_to_bl :: "nat \<Rightarrow> nat \<Rightarrow> bool list" where
  "the_nat_to_bl sz n \<equiv> the (nat_to_bl sz (n mod 2^sz))"

abbreviation (input) the_nat_to_bl_10  :: "nat \<Rightarrow> bool list" where
  "the_nat_to_bl_10 n \<equiv> the_nat_to_bl 10 n"

lemma len_the_nat_to_bl[simp]:
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

lemma nat_to_bl_mod_n_eq[simp]:
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

lemma empty_cnode_eq_Some[simp]:
  "(empty_cnode n x = Some y) = (length x = n \<and> y = NullCap)"
  by (clarsimp simp: empty_cnode_def, metis)

lemma empty_cnode_eq_None[simp]:
  "(empty_cnode n x = None) = (length x \<noteq> n)"
  by (clarsimp simp: empty_cnode_def)


text \<open>Low's CSpace\<close>

definition Low_caps :: cnode_contents where
  "Low_caps \<equiv>
   (empty_cnode 10)
     ((the_nat_to_bl_10 1)
        \<mapsto> ThreadCap Low_tcb_ptr,
      (the_nat_to_bl_10 2)
        \<mapsto> CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2),
      (the_nat_to_bl_10 3)
        \<mapsto> ArchObjectCap (PageTableCap Low_pd_ptr (Some (Low_asid,0))),
      (the_nat_to_bl_10 4)
        \<mapsto> ArchObjectCap (ASIDPoolCap Low_pool_ptr Low_asid),
      (the_nat_to_bl_10 5)
        \<mapsto> ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_write RISCVLargePage False (Some (Low_asid,0))),
      (the_nat_to_bl_10 6)
        \<mapsto> ArchObjectCap (PageTableCap Low_pt_ptr (Some (Low_asid,0))),
      (the_nat_to_bl_10 318)
        \<mapsto> NotificationCap ntfn_ptr 0 {AllowSend})"

definition Low_cnode :: kernel_object where
  "Low_cnode \<equiv> CNode 10 Low_caps"

lemma ran_empty_cnode[simp]:
  "ran (empty_cnode C) = {NullCap}"
  by (auto simp: empty_cnode_def ran_def Ex_list_of_length intro: set_eqI)

lemma empty_cnode_app[simp]:
  "length x = n \<Longrightarrow> empty_cnode n x = Some NullCap"
  by (auto simp: empty_cnode_def)

lemma in_ran_If[simp]:
  "(x \<in> ran (\<lambda>n. if P n then A n else B n)) \<longleftrightarrow>
   (\<exists>n. P n \<and> A n = Some x) \<or> (\<exists>n. \<not> P n \<and> B n = Some x)"
  by (auto simp: ran_def)

lemma Low_caps_ran:
  "ran Low_caps =
     {ThreadCap Low_tcb_ptr,
      CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2),
      ArchObjectCap (PageTableCap Low_pd_ptr (Some (Low_asid,0))),
      ArchObjectCap (PageTableCap Low_pt_ptr (Some (Low_asid,0))),
      ArchObjectCap (ASIDPoolCap Low_pool_ptr Low_asid),
      ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_write RISCVLargePage False (Some (Low_asid,0))),
      NotificationCap ntfn_ptr 0 {AllowSend},
      NullCap}"
  apply (rule equalityI)
   apply (clarsimp simp: Low_caps_def fun_upd_def empty_cnode_def split: if_split_asm)
  apply (clarsimp simp: Low_caps_def fun_upd_def empty_cnode_def split: if_split_asm cong: conj_cong)
  apply (rule exI[where x="the_nat_to_bl_10 0"])
  apply simp
  done


text \<open>High's Cspace\<close>

definition High_caps :: cnode_contents where
  "High_caps \<equiv>
     (empty_cnode 10)
       ((the_nat_to_bl_10 1)
          \<mapsto> ThreadCap High_tcb_ptr,
        (the_nat_to_bl_10 2)
          \<mapsto> CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2),
        (the_nat_to_bl_10 3)
          \<mapsto> ArchObjectCap (PageTableCap High_pd_ptr (Some (High_asid,0))),
        (the_nat_to_bl_10 4)
          \<mapsto> ArchObjectCap (ASIDPoolCap High_pool_ptr High_asid),
        (the_nat_to_bl_10 5)
          \<mapsto> ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (High_asid,0))),
        (the_nat_to_bl_10 6)
          \<mapsto> ArchObjectCap (PageTableCap High_pt_ptr (Some (High_asid,0))),
        (the_nat_to_bl_10 318)
          \<mapsto> NotificationCap ntfn_ptr 0 {AllowRecv}) "

definition High_cnode :: kernel_object where
  "High_cnode \<equiv> CNode 10 High_caps"

lemma High_caps_ran:
  "ran High_caps =
     {ThreadCap High_tcb_ptr,
      CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2),
      ArchObjectCap (PageTableCap High_pd_ptr (Some (High_asid,0))),
      ArchObjectCap (PageTableCap High_pt_ptr (Some (High_asid,0))),
      ArchObjectCap (ASIDPoolCap High_pool_ptr High_asid),
      ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (High_asid,0))),
      NotificationCap ntfn_ptr 0 {AllowRecv},
      NullCap}"
  apply (rule equalityI)
   apply (clarsimp simp: High_caps_def ran_def empty_cnode_def split: if_split_asm)
  apply (clarsimp simp: High_caps_def ran_def empty_cnode_def split: if_split_asm cong: conj_cong)
  apply (rule exI [where x="the_nat_to_bl_10 0"])
  apply simp
  done


text \<open>We need a copy of boundary crossing caps owned by SilcLabel\<close>

definition Silc_caps :: cnode_contents where
  "Silc_caps \<equiv>
     (empty_cnode 10)
       ((the_nat_to_bl_10 2)
          \<mapsto> CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2),
        (the_nat_to_bl_10 5)
          \<mapsto> ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (Silc_asid,0))),
        (the_nat_to_bl_10 318)
          \<mapsto> NotificationCap ntfn_ptr 0 {AllowSend} )"

definition Silc_cnode :: kernel_object where
  "Silc_cnode \<equiv> CNode 10 Silc_caps"

lemma Silc_caps_ran:
  "ran Silc_caps =
     {CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2),
      ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (Silc_asid,0))),
      NotificationCap ntfn_ptr 0 {AllowSend},
      NullCap}"
  apply (rule equalityI)
   apply (clarsimp simp: Silc_caps_def ran_def empty_cnode_def)
  apply (clarsimp simp: ran_def Silc_caps_def empty_cnode_def cong: conj_cong)
  apply (rule_tac x="the_nat_to_bl_10 0" in exI)
  apply simp
  done


text \<open>notification between Low and High\<close>

definition ntfn :: kernel_object where
  "ntfn \<equiv> Notification \<lparr>ntfn_obj = WaitingNtfn [High_tcb_ptr], ntfn_bound_tcb=None\<rparr>"


text \<open>global page table is mapped into the top-level page tables of each vspace\<close>

abbreviation init_global_pt' where
  "init_global_pt' \<equiv> (\<lambda>idx. if idx \<in> kernel_mapping_slots then global_pte idx else InvalidPTE)"


text \<open>Low's VSpace (PageDirectory)\<close>

abbreviation ppn_from_addr :: "paddr \<Rightarrow> pte_ppn" where
  "ppn_from_addr addr \<equiv> ucast (addr >> pt_bits)"

abbreviation Low_pt' :: pt where
  "Low_pt' \<equiv>
     (\<lambda>_. InvalidPTE)
       (0 := PagePTE (ppn_from_addr shared_page_ptr_phys) {} vm_read_write)"

definition Low_pt :: kernel_object where
  "Low_pt \<equiv> ArchObj (PageTable Low_pt')"

abbreviation Low_pd' :: pt where
  "Low_pd' \<equiv>
     init_global_pt'
       (0 := PageTablePTE (ppn_from_addr (addrFromPPtr Low_pt_ptr)) {})"

definition Low_pd :: kernel_object where
  "Low_pd \<equiv> ArchObj (PageTable Low_pd')"


text \<open>High's VSpace (PageDirectory)\<close>

abbreviation High_pt' :: pt where
  "High_pt' \<equiv>
     (\<lambda>_. InvalidPTE)
       (0 := PagePTE (ppn_from_addr shared_page_ptr_phys) {} vm_read_only)"

definition High_pt :: kernel_object where
  "High_pt \<equiv> ArchObj (PageTable High_pt')"

abbreviation High_pd' :: pt where
  "High_pd' \<equiv>
     init_global_pt'
       (0 := PageTablePTE (ppn_from_addr (addrFromPPtr High_pt_ptr)) {})"

definition High_pd :: kernel_object where
  "High_pd \<equiv> ArchObj (PageTable High_pd')"


text \<open>Low's tcb\<close>

definition Low_tcb :: kernel_object where
  "Low_tcb \<equiv> TCB \<lparr>tcb_ctable = CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2),
                  tcb_vtable = ArchObjectCap (PageTableCap Low_pd_ptr (Some (Low_asid,0))),
                  tcb_reply = ReplyCap Low_tcb_ptr True {AllowGrant, AllowWrite},
                  tcb_caller = NullCap,
                  tcb_ipcframe = NullCap,
                  tcb_state = Running,
                  tcb_fault_handler = replicate word_bits False,
                  tcb_ipc_buffer = 0,
                  tcb_fault = None,
                  tcb_bound_notification = None,
                  tcb_mcpriority = Low_mcp,
                  tcb_arch = \<lparr>tcb_context = undefined\<rparr>\<rparr>"

definition Low_etcb :: etcb where
  "Low_etcb \<equiv> \<lparr>tcb_priority   = Low_prio,
               tcb_time_slice = Low_time_slice,
               tcb_domain     = Low_domain\<rparr>"


text \<open>High's tcb\<close>

definition High_tcb :: kernel_object where
  "High_tcb \<equiv> TCB \<lparr>tcb_ctable = CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2) ,
                   tcb_vtable = ArchObjectCap (PageTableCap High_pd_ptr (Some (High_asid,0))),
                   tcb_reply = ReplyCap High_tcb_ptr True {AllowGrant, AllowWrite},
                   tcb_caller = NullCap,
                   tcb_ipcframe = NullCap,
                   tcb_state = BlockedOnNotification ntfn_ptr,
                   tcb_fault_handler = replicate word_bits False,
                   tcb_ipc_buffer = 0,
                   tcb_fault = None,
                   tcb_bound_notification = None,
                   tcb_mcpriority = High_mcp,
                   tcb_arch = \<lparr>tcb_context = undefined\<rparr>\<rparr>"

definition High_etcb :: etcb where
  "High_etcb \<equiv> \<lparr>tcb_priority   = High_prio,
                tcb_time_slice = High_time_slice,
                tcb_domain     = High_domain\<rparr>"


text \<open>idle's tcb\<close>

definition idle_tcb :: kernel_object where
  "idle_tcb \<equiv> TCB \<lparr>tcb_ctable = NullCap,
                   tcb_vtable = NullCap,
                   tcb_reply = NullCap,
                   tcb_caller = NullCap,
                   tcb_ipcframe = NullCap,
                   tcb_state = IdleThreadState,
                   tcb_fault_handler = replicate word_bits False,
                   tcb_ipc_buffer = 0,
                   tcb_fault = None,
                   tcb_bound_notification = None,
                   tcb_mcpriority = default_priority,
                   tcb_arch = \<lparr>tcb_context = empty_context\<rparr>\<rparr>"

definition
  "irq_cnode \<equiv> CNode 0 (Map.empty([] \<mapsto> cap.NullCap))"

abbreviation
  "Low_pool' \<equiv> \<lambda>idx. if idx = asid_low_bits_of Low_asid then Some Low_pd_ptr else None"

definition
  "Low_pool \<equiv> ArchObj (ASIDPool Low_pool')"

abbreviation
  "High_pool' \<equiv> \<lambda>idx. if idx = asid_low_bits_of High_asid then Some High_pd_ptr else None"

definition
  "High_pool \<equiv> ArchObj (ASIDPool High_pool')"

definition
  "shared_page \<equiv> ArchObj (DataPage False RISCVLargePage)"

definition kh0 :: kheap where
  "kh0 \<equiv> (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << 5) = x
               then Some (CNode 0 (empty_cnode 0))
               else None)
         (Low_cnode_ptr  \<mapsto> Low_cnode,
          High_cnode_ptr \<mapsto> High_cnode,
          Low_pool_ptr   \<mapsto> Low_pool,
          High_pool_ptr  \<mapsto> High_pool,
          Silc_cnode_ptr \<mapsto> Silc_cnode,
          ntfn_ptr       \<mapsto> ntfn,
          irq_cnode_ptr  \<mapsto> irq_cnode,
          Low_pd_ptr     \<mapsto> Low_pd,
          High_pd_ptr    \<mapsto> High_pd,
          Low_pt_ptr     \<mapsto> Low_pt,
          High_pt_ptr    \<mapsto> High_pt,
          Low_tcb_ptr    \<mapsto> Low_tcb,
          High_tcb_ptr   \<mapsto> High_tcb,
          idle_tcb_ptr   \<mapsto> idle_tcb,
          shared_page_ptr_virt \<mapsto> shared_page,
          riscv_global_pt_ptr \<mapsto> init_global_pt)"

lemma irq_node_offs_min:
  "init_irq_node_ptr \<le> init_irq_node_ptr + (ucast (irq :: irq) << 5)"
  apply (rule_tac sz=59 in machine_word_plus_mono_right_split)
   apply (simp add: unat_word_ariths mask_def shiftl_t2n s0_ptr_defs)
   apply (cut_tac x=irq and 'a=64 in ucast_less)
    apply simp
   apply (simp add: word_less_nat_alt)
  apply (simp add: word_bits_def)
  done

lemma irq_node_offs_max:
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) < init_irq_node_ptr + 0x7E1"
  apply (simp add: s0_ptr_defs shiftl_t2n)
  apply (cut_tac x=irq and 'a=64 in ucast_less)
   apply simp
  apply (simp add: word_less_nat_alt unat_word_ariths)
  done

definition irq_node_offs_range where
  "irq_node_offs_range \<equiv> {x. init_irq_node_ptr \<le> x \<and> x < init_irq_node_ptr + 0x7E1}
                       \<inter> {x. is_aligned x 5}"

lemma irq_node_offs_in_range:
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<in> irq_node_offs_range"
  apply (clarsimp simp: irq_node_offs_min irq_node_offs_max irq_node_offs_range_def)
  apply (rule is_aligned_add[OF _ is_aligned_shift])
  apply (simp add: is_aligned_def s0_ptr_defs)
  done

lemma irq_node_offs_range_correct:
  "x \<in> irq_node_offs_range
   \<Longrightarrow> \<exists>irq. x = init_irq_node_ptr + (ucast (irq:: irq) << 5)"
  apply (clarsimp simp: irq_node_offs_min irq_node_offs_max irq_node_offs_range_def s0_ptr_defs)
  apply (rule_tac x="ucast ((x - 0xFFFFFFC000003000) >> 5)" in exI)
  apply (clarsimp simp: ucast_ucast_mask)
  apply (subst aligned_shiftr_mask_shiftl)
   apply (rule aligned_sub_aligned)
     apply assumption
    apply (simp add: is_aligned_def)
   apply simp
  apply simp
  apply (rule_tac n=11 in mask_eqI)
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
  apply (cut_tac x=x and y="0xFFFFFFC0000037E0" and n=14 in neg_mask_mono_le)
   apply (force dest: word_less_sub_1)
  apply (drule_tac n=11 in aligned_le_sharp)
   apply (simp add: is_aligned_def)
  apply (simp add: mask_def is_aligned_mask)
  apply word_bitwise
  apply fastforce
  done

lemma irq_node_offs_range_distinct[simp]:
  "Low_cnode_ptr \<notin> irq_node_offs_range"
  "High_cnode_ptr \<notin> irq_node_offs_range"
  "Low_pool_ptr \<notin> irq_node_offs_range"
  "High_pool_ptr \<notin> irq_node_offs_range"
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
  "riscv_global_pt_ptr \<notin> irq_node_offs_range"
  "shared_page_ptr_virt \<notin> irq_node_offs_range"
  by(simp add:irq_node_offs_range_def s0_ptr_defs)+

lemma irq_node_offs_distinct[simp]:
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> Low_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> High_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> Low_pool_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> High_pool_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> Silc_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> ntfn_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> irq_cnode_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> Low_pd_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> High_pd_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> Low_pt_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> High_pt_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> Low_tcb_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> High_tcb_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> idle_tcb_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> riscv_global_pt_ptr"
  "init_irq_node_ptr + (ucast (irq:: irq) << 5) \<noteq> shared_page_ptr_virt"
  by (simp add:not_inD[symmetric, OF _ irq_node_offs_in_range])+

lemma kh0_dom:
  "dom kh0 = {shared_page_ptr_virt, riscv_global_pt_ptr, idle_tcb_ptr, High_tcb_ptr, Low_tcb_ptr,
              High_pt_ptr, Low_pt_ptr, High_pd_ptr, Low_pd_ptr, irq_cnode_ptr, ntfn_ptr,
              Silc_cnode_ptr, High_pool_ptr, Low_pool_ptr, High_cnode_ptr, Low_cnode_ptr}
           \<union> irq_node_offs_range"
  apply (rule equalityI)
   apply (simp add: kh0_def dom_def)
   apply (clarsimp simp: irq_node_offs_in_range)
  apply (clarsimp simp: dom_def)
  apply (rule conjI, clarsimp simp: kh0_def)+
  apply (force simp: kh0_def dest: irq_node_offs_range_correct)
  done

lemmas kh0_SomeD' = set_mp[OF equalityD1[OF kh0_dom[simplified dom_def]], OF CollectI, simplified, OF exI]

lemma kh0_SomeD:
  "kh0 x = Some y \<Longrightarrow>
        x = shared_page_ptr_virt \<and> y = shared_page \<or>
        x = riscv_global_pt_ptr \<and> y = init_global_pt \<or>
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
        x = High_pool_ptr \<and> y = High_pool \<or>
        x = Low_pool_ptr \<and> y = Low_pool \<or>
        x = High_cnode_ptr \<and> y = High_cnode \<or>
        x = Low_cnode_ptr \<and> y = Low_cnode \<or>
        x \<in> irq_node_offs_range \<and> y = CNode 0 (empty_cnode 0)"
  apply (frule kh0_SomeD')
  apply (erule disjE, simp add: kh0_def | force simp: kh0_def split: if_split_asm)+
  done

lemmas kh0_obj_def =
  Low_cnode_def High_cnode_def Silc_cnode_def Low_pool_def High_pool_def Low_pd_def High_pd_def
  Low_pt_def High_pt_def  Low_tcb_def High_tcb_def idle_tcb_def irq_cnode_def ntfn_def
  init_global_pt_def global_pte_def vm_kernel_only_def shared_page_def


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
                     machine_state_rest = undefined\<rparr>"

definition arch_state0 :: "arch_state" where
  "arch_state0 \<equiv> \<lparr>
     riscv_asid_table = [asid_high_bits_of Low_asid \<mapsto> Low_pool_ptr,
                         asid_high_bits_of High_asid \<mapsto> High_pool_ptr],
     riscv_global_pts = (\<lambda>level. if level = max_pt_level then {riscv_global_pt_ptr} else {}),
     riscv_kernel_vspace = init_vspace_uses
   \<rparr>"

definition s0_internal :: "det_ext state" where
  "s0_internal \<equiv> \<lparr>
     kheap = kh0,
     cdt = Map.empty,
     is_original_cap = (\<lambda>_. False) ((Low_tcb_ptr, tcb_cnode_index 2) := True,
                                    (High_tcb_ptr, tcb_cnode_index 2) := True),
     cur_thread = Low_tcb_ptr,
     idle_thread = idle_tcb_ptr,
     machine_state = machine_state0,
     interrupt_irq_node = (\<lambda>irq. init_irq_node_ptr + (ucast irq << 5)),
     interrupt_states = (\<lambda>_. irq_state.IRQInactive) (timer_irq := irq_state.IRQTimer),
     arch_state = arch_state0,
     exst = exst0
   \<rparr>"

lemma kh_s0_def:
  "(kheap s0_internal x = Some y) = (
        x = shared_page_ptr_virt \<and> y = shared_page \<or>
        x = riscv_global_pt_ptr \<and> y = init_global_pt \<or>
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
        x = High_pool_ptr \<and> y = High_pool \<or>
        x = Low_pool_ptr \<and> y = Low_pool \<or>
        x = High_cnode_ptr \<and> y = High_cnode \<or>
        x = Low_cnode_ptr \<and> y = Low_cnode \<or>
        x \<in> irq_node_offs_range \<and> y = CNode 0 (empty_cnode 0))"
  apply (clarsimp simp: s0_internal_def kh0_def)
  apply (auto simp: irq_node_offs_in_range dest: irq_node_offs_range_correct)
  done


subsubsection \<open>Defining the policy graph\<close>

definition Sys1AgentMap :: "(auth_graph_label subject_label) agent_map" where
  "Sys1AgentMap \<equiv>
   \<comment> \<open>set the range of the shared_page to Low, default everything else to IRQ0\<close>
   (\<lambda>p. if p \<in> ptr_range shared_page_ptr_virt (pageBitsForSize RISCVLargePage)
        then partition_label Low
        else partition_label IRQ0)
   (Low_cnode_ptr := partition_label Low,
    High_cnode_ptr := partition_label High,
    Low_pool_ptr := partition_label Low,
    High_pool_ptr := partition_label High,
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
  "Sys1AgentMap Low_pool_ptr = partition_label Low"
  "Sys1AgentMap High_pool_ptr = partition_label High"
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
  "\<And>p. p \<in> ptr_range shared_page_ptr_virt (pageBitsForSize RISCVLargePage)
         \<Longrightarrow> Sys1AgentMap p = partition_label Low"
  unfolding Sys1AgentMap_def
  apply simp_all
  by (auto simp: s0_ptr_defs ptr_range_def)

definition Sys1ASIDMap :: "(auth_graph_label subject_label) agent_asid_map" where
  "Sys1ASIDMap \<equiv>
     (\<lambda>x. if asid_high_bits_of x = asid_high_bits_of Low_asid
          then partition_label Low
          else if asid_high_bits_of x = asid_high_bits_of High_asid
          then partition_label High
          else if asid_high_bits_of x = asid_high_bits_of Silc_asid
          then SilcLabel
          else undefined)"

(* We include 2 domains, Low is associated to domain 0, High to domain 1,
   we default the rest of the possible domains to High *)

definition Sys1PAS :: "(auth_graph_label subject_label) PAS" where
  "Sys1PAS \<equiv>
     \<lparr>pasObjectAbs = Sys1AgentMap,
      pasASIDAbs = Sys1ASIDMap,
      pasIRQAbs = (\<lambda>_. partition_label IRQ0),
      pasPolicy = Sys1AuthGraph,
      pasSubject = partition_label Low,
      pasMayActivate = True,
      pasMayEditReadyQueues = True, pasMaySendIrqs = False,
      pasDomainAbs = ((\<lambda>_. {partition_label High})(0 := {partition_label Low}))\<rparr>"


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
       { ((Low_cnode_ptr,(the_nat_to_bl_10 1)), ThreadCap Low_tcb_ptr),
         ((Low_cnode_ptr,(the_nat_to_bl_10 2)), CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((Low_cnode_ptr,(the_nat_to_bl_10 3)), ArchObjectCap (PageTableCap Low_pd_ptr (Some (Low_asid,0)))),
         ((Low_cnode_ptr,(the_nat_to_bl_10 6)), ArchObjectCap (PageTableCap Low_pt_ptr (Some (Low_asid,0)))),
         ((Low_cnode_ptr,(the_nat_to_bl_10 4)), ArchObjectCap (ASIDPoolCap Low_pool_ptr Low_asid)),
         ((Low_cnode_ptr,(the_nat_to_bl_10 5)), ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_write RISCVLargePage False (Some (Low_asid, 0)))),
         ((Low_cnode_ptr,(the_nat_to_bl_10 318)), NotificationCap ntfn_ptr 0 {AllowSend}),
         ((High_cnode_ptr,(the_nat_to_bl_10 1)), ThreadCap High_tcb_ptr),
         ((High_cnode_ptr,(the_nat_to_bl_10 2)), CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((High_cnode_ptr,(the_nat_to_bl_10 3)), ArchObjectCap (PageTableCap High_pd_ptr (Some (High_asid,0)))),
         ((High_cnode_ptr,(the_nat_to_bl_10 6)), ArchObjectCap (PageTableCap High_pt_ptr (Some (High_asid,0)))),
         ((High_cnode_ptr,(the_nat_to_bl_10 4)), ArchObjectCap (ASIDPoolCap High_pool_ptr High_asid)),
         ((High_cnode_ptr,(the_nat_to_bl_10 5)), ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (High_asid, 0)))),
         ((High_cnode_ptr,(the_nat_to_bl_10 318)), NotificationCap  ntfn_ptr 0 {AllowRecv}) ,
         ((Silc_cnode_ptr,(the_nat_to_bl_10 2)), CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((Silc_cnode_ptr,(the_nat_to_bl_10 5)), ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (Silc_asid, 0)))),
         ((Silc_cnode_ptr,(the_nat_to_bl_10 318)), NotificationCap ntfn_ptr 0 {AllowSend}),
         ((Low_tcb_ptr,(tcb_cnode_index 0)), CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((Low_tcb_ptr,(tcb_cnode_index 1)), ArchObjectCap (PageTableCap Low_pd_ptr (Some (Low_asid,0)))),
         ((Low_tcb_ptr,(tcb_cnode_index 2)), ReplyCap Low_tcb_ptr True {AllowGrant, AllowWrite}),
         ((Low_tcb_ptr,(tcb_cnode_index 3)), NullCap),
         ((Low_tcb_ptr,(tcb_cnode_index 4)), NullCap),
         ((High_tcb_ptr,(tcb_cnode_index 0)), CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2)),
         ((High_tcb_ptr,(tcb_cnode_index 1)), ArchObjectCap (PageTableCap High_pd_ptr (Some (High_asid,0)))),
         ((High_tcb_ptr,(tcb_cnode_index 2)), ReplyCap High_tcb_ptr True {AllowGrant, AllowWrite}),
         ((High_tcb_ptr,(tcb_cnode_index 3)), NullCap),
         ((High_tcb_ptr,(tcb_cnode_index 4)), NullCap)} "
  supply if_cong[cong]
  apply (insert High_caps_well_formed)
  apply (insert Low_caps_well_formed)
  apply (insert Silc_caps_well_formed)
  apply (simp add: caps_of_state_cte_wp_at cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def)
  apply (case_tac p, clarsimp)
  apply (clarsimp split: if_splits)
       apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def split: if_split_asm)+
    apply (clarsimp simp: Silc_caps_def split: if_splits)
   apply (clarsimp simp: High_caps_def split: if_splits)
  apply (clarsimp simp: Low_caps_def split: if_splits)
  done

lemma tcb_states_of_state_s0:
  "tcb_states_of_state s0_internal = [High_tcb_ptr \<mapsto> thread_state.BlockedOnNotification ntfn_ptr,
                                      Low_tcb_ptr \<mapsto> thread_state.Running,
                                      idle_tcb_ptr \<mapsto> thread_state.IdleThreadState ]"
  unfolding s0_internal_def tcb_states_of_state_def
  by (auto simp: get_tcb_def kh0_def kh0_obj_def)

lemma thread_bounds_of_state_s0:
  "thread_bound_ntfns s0_internal = Map.empty"
  unfolding s0_internal_def thread_bound_ntfns_def
  by (auto simp: get_tcb_def kh0_def kh0_obj_def)

lemma Sys1_wellformed':
  "policy_wellformed (pasPolicy Sys1PAS) False irqs x"
  by (clarsimp simp: Sys1PAS_def Sys1AgentMap_simps Sys1AuthGraph_def policy_wellformed_def)

corollary Sys1_wellformed:
  "x \<in> range (pasObjectAbs Sys1PAS) \<union> \<Union>(range (pasDomainAbs Sys1PAS)) - {SilcLabel}
   \<Longrightarrow> policy_wellformed (pasPolicy Sys1PAS) False irqs x"
  by (rule Sys1_wellformed')

lemma Sys1_pas_wellformed:
  "pas_wellformed Sys1PAS"
  by (clarsimp simp: Sys1PAS_def Sys1AgentMap_simps Sys1AuthGraph_def policy_wellformed_def)

lemma domains_of_state_s0[simp]:
  "domains_of_state s0_internal = {(High_tcb_ptr, High_domain),
                                   (Low_tcb_ptr, Low_domain),
                                   (idle_tcb_ptr, default_domain)}"
  apply (rule equalityI)
   apply (rule subsetI)
   apply clarsimp
   apply (erule domains_of_state_aux.cases)
   apply (clarsimp simp: s0_internal_def exst0_def ekh0_obj_def split: if_split_asm)
  apply (force simp: s0_internal_def exst0_def ekh0_obj_def intro: domains_of_state_aux.domtcbs)+
  done

lemma pool_for_asid_s0:
  "pool_for_asid asid s0_internal = (if asid_high_bits_of asid = asid_high_bits_of High_asid
                                     then Some High_pool_ptr
                                     else if asid_high_bits_of asid = asid_high_bits_of Low_asid
                                     then Some Low_pool_ptr
                                     else None)"
  by (clarsimp simp: pool_for_asid_def s0_internal_def arch_state0_def)

lemma asid_pools_of_s0:
  "asid_pools_of s0_internal = [Low_pool_ptr \<mapsto> Low_pool', High_pool_ptr \<mapsto> High_pool']"
  by (auto simp: asid_pools_of_ko_at obj_at_def s0_internal_def opt_map_def kh0_def kh0_obj_def
          split: option.splits)

lemma pts_of_s0:
  "pts_of s0_internal = [Low_pd_ptr \<mapsto> Low_pd',
                         High_pd_ptr \<mapsto> High_pd',
                         Low_pt_ptr \<mapsto> Low_pt',
                         High_pt_ptr \<mapsto> High_pt',
                         riscv_global_pt_ptr \<mapsto> init_global_pt']"
  by (auto simp: opt_map_def s0_internal_def kh0_def kh0_obj_def
          split: option.splits if_splits)+


lemma ptes_of_s0_PageTablePTE:
  "\<lbrakk> ptes_of s0_internal ptr = Some pte; is_PageTablePTE pte \<rbrakk>
     \<Longrightarrow> table_base ptr = Low_pd_ptr \<and> pte = PageTablePTE (ppn_from_addr (addrFromPPtr Low_pt_ptr)) {}
       \<or> table_base ptr = High_pd_ptr \<and> pte = PageTablePTE (ppn_from_addr (addrFromPPtr High_pt_ptr)) {}"
  by (auto simp: ptes_of_def pts_of_s0 obind_def kh0_obj_def split: option.splits if_splits)

lemma Low_pt_is_aligned[simp]:
  "is_aligned Low_pt_ptr pt_bits"
  by (clarsimp simp: s0_ptr_defs pt_bits_def table_size_def ptTranslationBits_def pte_bits_def word_size_bits_def is_aligned_def)

lemma High_pt_is_aligned[simp]:
  "is_aligned High_pt_ptr pt_bits"
  by (clarsimp simp: s0_ptr_defs pt_bits_def table_size_def ptTranslationBits_def pte_bits_def word_size_bits_def is_aligned_def)

lemma Low_pd_is_aligned[simp]:
  "is_aligned Low_pd_ptr pt_bits"
  by (clarsimp simp: s0_ptr_defs pt_bits_def table_size_def ptTranslationBits_def pte_bits_def word_size_bits_def is_aligned_def)

lemma High_pd_is_aligned[simp]:
  "is_aligned High_pd_ptr pt_bits"
  by (clarsimp simp: s0_ptr_defs pt_bits_def table_size_def ptTranslationBits_def pte_bits_def word_size_bits_def is_aligned_def)

lemma shared_page_ptr_is_aligned[simp]:
  "is_aligned shared_page_ptr_virt pt_bits"
  by (clarsimp simp: s0_ptr_defs pt_bits_def table_size_def ptTranslationBits_def pte_bits_def word_size_bits_def is_aligned_def)

lemma vs_lookup_s0_SomeD:
  "vs_lookup_table lvl asid vref s0_internal = Some (lvl', p)
   \<Longrightarrow> (asid_high_bits_of asid = asid_high_bits_of High_asid \<and> lvl' = asid_pool_level \<and> p = High_pool_ptr
      \<or> asid_high_bits_of asid = asid_high_bits_of Low_asid \<and> lvl' = asid_pool_level \<and> p = Low_pool_ptr
      \<or> asid = High_asid \<and> lvl' = max_pt_level \<and> p = High_pd_ptr
      \<or> asid = Low_asid \<and> lvl' = max_pt_level \<and> p = Low_pd_ptr
      \<or> asid = High_asid \<and> lvl' = max_pt_level - 1 \<and> p = High_pt_ptr
      \<or> asid = Low_asid \<and> lvl' = max_pt_level - 1 \<and> p = Low_pt_ptr)"
  apply (clarsimp simp: vs_lookup_table_def obind_def split: option.splits if_splits)
   apply (clarsimp simp: pool_for_asid_s0 split: if_splits)
  apply (case_tac "lvl = max_pt_level")
   apply (clarsimp simp: asid_pools_of_s0 pool_for_asid_s0 asid_high_low vspace_for_pool_def
                  split: if_splits)
  apply (case_tac "lvl = max_pt_level - 1")
   apply (clarsimp simp: pt_walk.simps split: if_splits)
    apply (drule (1) ptes_of_s0_PageTablePTE)
    apply (auto simp: pptr_from_pte_def ptrFromPAddr_addr_from_ppn' ptes_of_def asid_high_low
                      kh0_obj_def pts_of_s0 pool_for_asid_s0 asid_pools_of_s0 vspace_for_pool_def
               split: if_splits)[2]
  apply (clarsimp simp: pt_walk.simps)
  apply (clarsimp split: if_splits)
   apply (drule (1) ptes_of_s0_PageTablePTE)
   apply (erule disjE; clarsimp)
  by (clarsimp simp: pptr_from_pte_def ptrFromPAddr_addr_from_ppn' kh0_obj_def
                     pt_walk.simps ptes_of_def pts_of_s0 asid_high_low
                     pool_for_asid_s0 asid_pools_of_s0 vspace_for_pool_def
              split: if_splits)+

lemma pt_bits_left_max_minus_1_pageBitsForSize:
  "pt_bits_left (max_pt_level - 1) = pageBitsForSize RISCVLargePage"
  apply (clarsimp simp: pt_bits_left_def max_pt_level_def2)
  done

lemma Sys1_pas_refined:
  "pas_refined Sys1PAS s0_internal"
  apply (clarsimp simp: pas_refined_def)
  apply (intro conjI)
       apply (simp add: Sys1_pas_wellformed)
      apply (clarsimp simp: irq_map_wellformed_aux_def s0_internal_def Sys1AgentMap_def Sys1PAS_def)
      apply (clarsimp simp: s0_ptr_defs ptr_range_def)
      apply word_bitwise
     apply (clarsimp simp: tcb_domain_map_wellformed_aux_def minBound_word High_domain_def Low_domain_def
                           Sys1PAS_def Sys1AgentMap_def default_domain_def)
    apply (clarsimp simp: auth_graph_map_def Sys1PAS_def state_objs_to_policy_def state_bits_to_policy_def)
    apply (erule state_bits_to_policyp.cases; clarsimp)
          apply (drule s0_caps_of_state, clarsimp)
          apply (simp add: Sys1AuthGraph_def)
          apply (elim disjE; clarsimp simp: Sys1AgentMap_simps cap_auth_conferred_def ptr_range_def
                                            arch_cap_auth_conferred_def vspace_cap_rights_to_auth_def
                                            vm_read_write_def vm_read_only_def cap_rights_to_auth_def)
         apply (drule s0_caps_of_state, clarsimp)
         apply (elim disjE, simp_all)[1]
        apply (clarsimp simp: state_refs_of_def thread_st_auth_def tcb_states_of_state_s0
                              Sys1AuthGraph_def Sys1AgentMap_simps split: if_splits)
       apply (clarsimp simp: state_refs_of_def thread_st_auth_def thread_bounds_of_state_s0)
      apply (simp add: s0_internal_def) (* this is OK because cdt is empty..*)
     apply (simp add: s0_internal_def) (* this is OK because cdt is empty..*)
    apply (clarsimp simp: state_vrefs_def)
    apply (drule vs_lookup_s0_SomeD)
    apply (elim disjE; clarsimp)
         apply ((clarsimp simp: s0_internal_def kh0_obj_def opt_map_def vs_refs_aux_def
                                vm_read_only_def vspace_cap_rights_to_auth_def pte_ref2_def
                                Sys1AuthGraph_def Sys1AgentMap_simps graph_of_def ptrFromPAddr_addr_from_ppn'
                                shared_page_ptr_phys_def pt_bits_left_max_minus_1_pageBitsForSize
                         dest!: kh0_SomeD split: option.splits if_splits)+)[6]
   apply (rule subsetI, clarsimp)
   apply (erule state_asids_to_policy_aux.cases)
     apply (drule s0_caps_of_state, clarsimp)
     apply (fastforce simp: Sys1AuthGraph_def Sys1PAS_def Sys1ASIDMap_def Sys1AgentMap_def
                            Low_asid_def High_asid_def Silc_asid_def
                            asid_low_bits_def asid_high_bits_of_def)
    apply (clarsimp simp: state_vrefs_def)
    apply (drule vs_lookup_s0_SomeD)
    apply (clarsimp simp: vs_refs_aux_def s0_internal_def arch_state0_def kh0_def kh0_obj_def
                          Sys1PAS_def Sys1ASIDMap_def Sys1AgentMap_simps Sys1AuthGraph_def
                          opt_map_def graph_of_def split: if_splits)
   apply (clarsimp simp: Sys1PAS_def Sys1ASIDMap_def Sys1AgentMap_simps Sys1AuthGraph_def
                         s0_internal_def arch_state0_def split: if_splits)
  apply (fastforce elim: state_irqs_to_policy_aux.cases dest: s0_caps_of_state)
  done

lemma Sys1_pas_cur_domain:
  "pas_cur_domain Sys1PAS s0_internal"
  by (simp add: s0_internal_def exst0_def Sys1PAS_def)

lemma Sys1_current_subject_idemp:
  "Sys1PAS\<lparr>pasSubject := the_elem (pasDomainAbs Sys1PAS (cur_domain s0_internal))\<rparr> = Sys1PAS"
  by (simp add: Sys1PAS_def s0_internal_def exst0_def)

lemma pasMaySendIrqs_Sys1PAS[simp]:
  "pasMaySendIrqs Sys1PAS = False"
  by(auto simp: Sys1PAS_def)

lemma Sys1_pas_domains_distinct:
  "pas_domains_distinct Sys1PAS"
  by (clarsimp simp: Sys1PAS_def pas_domains_distinct_def)

lemma Sys1_pas_wellformed_noninterference:
  "pas_wellformed_noninterference Sys1PAS"
  apply (simp add: pas_wellformed_noninterference_def)
  apply (intro conjI ballI allI)
    apply (blast intro: Sys1_wellformed)
   apply (clarsimp simp: Sys1PAS_def policy_wellformed_def Sys1AuthGraph_def)
  apply (rule Sys1_pas_domains_distinct)
  done

lemma Sys1AgentMap_shared_page_ptr:
  "Sys1AgentMap shared_page_ptr_virt = partition_label Low"
  by (clarsimp simp: Sys1AgentMap_def s0_ptr_defs ptr_range_def bit_simps)

lemma silc_inv_s0:
  "silc_inv Sys1PAS s0_internal s0_internal"
  apply (clarsimp simp: silc_inv_def)
  apply (rule conjI, simp add: Sys1PAS_def)
  apply (rule conjI)
   apply (clarsimp simp: Sys1PAS_def Sys1AgentMap_def s0_internal_def kh0_def obj_at_def kh0_obj_def
                         is_cap_table_def Silc_caps_well_formed split: if_split_asm)
  apply (rule conjI)
   apply (clarsimp simp: Sys1PAS_def Sys1AuthGraph_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=Silc_cnode_ptr in exI)
   apply (rule conjI)
    apply (subgoal_tac "(Silc_cnode_ptr,the_nat_to_bl_10 318) \<in> slots_holding_overlapping_caps cap s0_internal
                      \<or> (Silc_cnode_ptr, the_nat_to_bl_10 5) \<in> slots_holding_overlapping_caps cap s0_internal")
     apply fastforce
    apply clarsimp
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
  apply (clarsimp simp: Sys1PAS_def Sys1AgentMap_def)
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
  by (clarsimp simp: guarded_pas_domain_def Sys1PAS_def s0_internal_def exst0_def Sys1AgentMap_simps)

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
  apply (simp add: High_caps_well_formed Low_caps_well_formed Silc_caps_well_formed)+
  apply (fastforce simp: well_formed_cnode_n_def dest: eqset_imp_iff[where x="[]"])
  done

lemma valid_caps_s0[simp]:
  "s0_internal \<turnstile> ThreadCap Low_tcb_ptr"
  "s0_internal \<turnstile> ThreadCap High_tcb_ptr"
  "s0_internal \<turnstile> CNodeCap Low_cnode_ptr 10 (the_nat_to_bl_10 2)"
  "s0_internal \<turnstile> CNodeCap High_cnode_ptr 10 (the_nat_to_bl_10 2)"
  "s0_internal \<turnstile> CNodeCap Silc_cnode_ptr 10 (the_nat_to_bl_10 2)"
  "s0_internal \<turnstile> ArchObjectCap (ASIDPoolCap Low_pool_ptr Low_asid)"
  "s0_internal \<turnstile> ArchObjectCap (ASIDPoolCap High_pool_ptr High_asid)"
  "s0_internal \<turnstile> ArchObjectCap (PageTableCap Low_pd_ptr (Some (Low_asid,0)))"
  "s0_internal \<turnstile> ArchObjectCap (PageTableCap High_pd_ptr (Some (High_asid,0)))"
  "s0_internal \<turnstile> ArchObjectCap (PageTableCap Low_pt_ptr (Some (Low_asid,0)))"
  "s0_internal \<turnstile> ArchObjectCap (PageTableCap High_pt_ptr (Some (High_asid,0)))"
  "s0_internal \<turnstile> ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_write RISCVLargePage False (Some (Low_asid,0)))"
  "s0_internal \<turnstile> ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (High_asid,0)))"
  "s0_internal \<turnstile> ArchObjectCap (FrameCap shared_page_ptr_virt vm_read_only RISCVLargePage False (Some (Silc_asid,0)))"
  "s0_internal \<turnstile> NotificationCap ntfn_ptr 0 {AllowWrite}"
  "s0_internal \<turnstile> NotificationCap ntfn_ptr 0 {AllowRead}"
  "s0_internal \<turnstile> ReplyCap Low_tcb_ptr True {AllowGrant,AllowWrite}"
  "s0_internal \<turnstile> ReplyCap High_tcb_ptr True {AllowGrant,AllowWrite}"
  by (auto simp: s0_internal_def s0_ptr_defs kh0_def kh0_obj_def bit_simps word_bits_def
                 valid_cap_def cap_aligned_def is_aligned_def obj_at_def cte_level_bits_def
                 is_ntfn_def is_tcb_def is_cap_table_def a_type_def the_nat_to_bl_def nat_to_bl_def
                 Low_asid_def High_asid_def Silc_asid_def asid_low_bits_def asid_bits_def
                 wellformed_mapdata_def valid_vm_rights_def vmsz_aligned_def)

lemma valid_obj_s0[simp]:
  "valid_obj Low_cnode_ptr       Low_cnode      s0_internal"
  "valid_obj High_cnode_ptr      High_cnode     s0_internal"
  "valid_obj High_pool_ptr       High_pool      s0_internal"
  "valid_obj Low_pool_ptr        Low_pool       s0_internal"
  "valid_obj Silc_cnode_ptr      Silc_cnode     s0_internal"
  "valid_obj ntfn_ptr            ntfn           s0_internal"
  "valid_obj irq_cnode_ptr       irq_cnode      s0_internal"
  "valid_obj Low_pd_ptr          Low_pd         s0_internal"
  "valid_obj High_pd_ptr         High_pd        s0_internal"
  "valid_obj Low_pt_ptr          Low_pt         s0_internal"
  "valid_obj High_pt_ptr         High_pt        s0_internal"
  "valid_obj Low_tcb_ptr         Low_tcb        s0_internal"
  "valid_obj High_tcb_ptr        High_tcb       s0_internal"
  "valid_obj idle_tcb_ptr        idle_tcb       s0_internal"
  "valid_obj riscv_global_pt_ptr init_global_pt s0_internal"
  "valid_obj shared_page_ptr_virt shared_page s0_internal"
                 apply (simp_all add: valid_obj_def kh0_obj_def)
              apply (simp add: valid_cs_def Low_caps_ran High_caps_ran Silc_caps_ran
                               valid_cs_size_def word_bits_def cte_level_bits_def)+
           apply (simp add: valid_ntfn_def obj_at_def s0_internal_def kh0_def High_tcb_def is_tcb_def)
          apply (simp add: valid_cs_def valid_cs_size_def word_bits_def
                           cte_level_bits_def well_formed_cnode_n_def)
         apply (clarsimp simp: valid_tcb_def tcb_cap_cases_def valid_tcb_state_def valid_arch_tcb_def
                               is_valid_vtable_root_def is_master_reply_cap_def is_ntfn_def obj_at_def
                               wellformed_pte_def valid_vm_rights_def vm_kernel_only_def
                | fastforce simp: s0_internal_def kh0_def kh0_obj_def)+
  done

lemma valid_objs_s0:
  "valid_objs s0_internal"
  apply (clarsimp simp: valid_objs_def)
  apply (subst (asm) s0_internal_def, clarsimp)
  apply (drule kh0_SomeD)
  apply (elim disjE; clarsimp)
  apply (fastforce simp: valid_obj_def valid_cs_def valid_cs_size_def
                         cte_level_bits_def word_bits_def well_formed_cnode_n_def)
  done

lemma pspace_aligned_s0:
  "pspace_aligned s0_internal"
  apply (clarsimp simp: pspace_aligned_def s0_internal_def)
  apply (drule kh0_SomeD)
  apply (auto simp: cte_level_bits_def irq_node_offs_range_def
                    is_aligned_def s0_ptr_defs kh0_obj_def bit_simps)
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
   apply word_bitwise
   apply auto[1]
  apply (elim disjE)
  (* slow *)
  by (simp | clarsimp simp: kh0_obj_def cte_level_bits_def s0_ptr_defs pte_bits_def bit_simps
           | fastforce
           | clarsimp simp: irq_node_offs_range_def s0_ptr_defs,
             drule_tac x="0x1F" in word_plus_strict_mono_right, simp, simp add: add.commute,
             drule(1) notE[rotated, OF less_trans, OF _ _ leD, rotated 2]
           | drule(1) notE[rotated, OF le_less_trans, OF _ _ leD, rotated 2], simp, assumption)+

lemma valid_pspace_s0[simp]:
  "valid_pspace s0_internal"
  apply (simp add: valid_pspace_def pspace_distinct_s0 pspace_aligned_s0 valid_objs_s0)
  apply (rule conjI)
   apply (clarsimp simp: if_live_then_nonz_cap_def)
   apply (subst (asm) s0_internal_def)
   apply (clarsimp simp: ex_nonz_cap_to_def live_def hyp_live_def obj_at_def kh0_def kh0_obj_def
                  split: if_splits)
     apply (rule_tac x="High_cnode_ptr" in exI)
     apply (rule_tac x="the_nat_to_bl_10 1" in exI)
     apply (force simp: s0_internal_def kh0_def kh0_obj_def High_caps_def
                        cte_wp_at_cases well_formed_cnode_n_def)
    apply (rule_tac x="Low_cnode_ptr" in exI)
    apply (rule_tac x="the_nat_to_bl_10 1" in exI)
    apply (force simp: s0_internal_def kh0_def kh0_obj_def Low_caps_def
                       cte_wp_at_cases well_formed_cnode_n_def)
   apply (rule_tac x="High_cnode_ptr" in exI)
   apply (rule_tac x="the_nat_to_bl_10 318" in exI)
   apply (force simp: s0_internal_def kh0_def kh0_obj_def High_caps_def
                      cte_wp_at_cases well_formed_cnode_n_def)
  apply (intro conjI)
    apply (force dest: s0_caps_of_state simp: cte_wp_at_caps_of_state zombies_final_def is_zombie_def)
   apply (clarsimp simp: sym_refs_def state_refs_of_def state_hyp_refs_of_def
                         refs_of_def s0_internal_def kh0_def kh0_obj_def)
  apply (clarsimp simp: sym_refs_def state_hyp_refs_of_def s0_internal_def kh0_def)
  done

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
  apply (clarsimp simp: valid_arch_mdb_def)
  done

lemma valid_ioc_s0[simp]:
  "valid_ioc s0_internal"
  by (clarsimp simp: cte_wp_at_cases valid_ioc_def s0_internal_def kh0_def kh0_obj_def)

lemma valid_idle_s0[simp]:
  "valid_idle s0_internal"
  by (clarsimp simp: valid_idle_def valid_arch_idle_def  pred_tcb_at_def obj_at_def
                     idle_thread_ptr_def idle_tcb_def kh0_def s0_ptr_defs s0_internal_def)

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
   apply (fastforce simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def)
  apply (case_tac "a=High_cnode_ptr")
   apply (rule_tac x=High_tcb_ptr in exI, rule_tac x="tcb_cnode_index 0" in exI)
   apply (fastforce simp: cte_wp_at_cases s0_internal_def kh0_def kh0_obj_def)
  apply (case_tac "a=Low_tcb_ptr")
   apply (rule_tac x=Low_cnode_ptr in exI, rule_tac x="the_nat_to_bl_10 1" in exI)
   apply (fastforce simp: s0_internal_def kh0_def kh0_obj_def Low_caps_def
                          cte_wp_at_cases well_formed_cnode_n_def)
  apply (case_tac "a=High_tcb_ptr")
   apply (rule_tac x=High_cnode_ptr in exI, rule_tac x="the_nat_to_bl_10 1" in exI)
   apply (fastforce simp: s0_internal_def kh0_def kh0_obj_def High_caps_def
                          cte_wp_at_cases well_formed_cnode_n_def)
  apply (rule_tac x=Silc_cnode_ptr in exI, rule_tac x="the_nat_to_bl_10 2" in exI)
  apply (fastforce simp: s0_internal_def kh0_def kh0_obj_def Silc_caps_def
                         cte_wp_at_cases well_formed_cnode_n_def)
  done

lemma valid_reply_caps_s0[simp]:
  "valid_reply_caps s0_internal"
  apply (clarsimp simp: valid_reply_caps_def)
  apply (rule conjI)
   apply (force dest: s0_caps_of_state
                simp: cte_wp_at_caps_of_state has_reply_cap_def is_reply_cap_to_def)
  apply (clarsimp simp: unique_reply_caps_def)
  apply (drule s0_caps_of_state)+
  apply (erule disjE | simp add: is_reply_cap_def)+
  done

lemma valid_reply_masters_s0[simp]:
  "valid_reply_masters s0_internal"
  apply (clarsimp simp: valid_reply_masters_def)
  apply (force dest: s0_caps_of_state simp: cte_wp_at_caps_of_state is_master_reply_cap_to_def)
  done

lemma valid_global_refs_s0[simp]:
  "valid_global_refs s0_internal"
  apply (clarsimp simp: valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)
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
    apply (auto simp: valid_asid_table_def kh0_def kh0_obj_def opt_map_def split: option.splits)[1]
   apply (fastforce simp: valid_global_arch_objs_def obj_at_def kh0_def a_type_def
                         init_global_pt_def max_pt_level_not_asid_pool_level[symmetric])
  apply (clarsimp simp: valid_global_tables_def pt_walk.simps obind_def)
  apply (fastforce dest: pt_walk_max_level
                   simp: obind_def opt_map_def asid_pool_level_eq geq_max_pt_level pte_of_def kh0_def
                         kh0_obj_def pte_rights_of_def
                  split: if_splits)
  done

lemma valid_irq_node_s0[simp]:
  "valid_irq_node s0_internal"
  apply (clarsimp simp: valid_irq_node_def)
  apply (rule conjI)
   apply (simp add: s0_internal_def)
   apply (rule injI)
   apply simp
   apply (rule ccontr)
   apply (rule_tac bnd="0x40" and 'a=64 in shift_distinct_helper[rotated 3])
        apply assumption
       apply simp
      apply simp
     apply (rule ucast_less[where 'b=6, simplified])
     apply simp
    apply (rule ucast_less[where 'b=6, simplified])
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
  by (clarsimp simp: valid_irq_states_def valid_irq_masks_def s0_internal_def machine_state0_def)

lemma valid_machine_state_s0[simp]:
  "valid_machine_state s0_internal"
  by (clarsimp simp: valid_machine_state_def s0_internal_def const_def
                     machine_state0_def in_user_frame_def obj_at_def)

lemma valid_arch_objs_s0[simp]:
  "valid_vspace_objs s0_internal"
  apply (clarsimp simp: valid_vspace_objs_def obj_at_def)
  apply (drule vs_lookup_s0_SomeD)
  apply (auto simp: aobjs_of_Some kh_s0_def kh0_obj_def data_at_def obj_at_def
                    ptrFromPAddr_addr_from_ppn' vmpage_size_of_level_def max_pt_level_def2
                    shared_page_ptr_phys_def)
  done

lemma valid_vs_lookup_s0_internal:
  "valid_vs_lookup s0_internal"
  supply pt_simps = pt_slot_offset_def pt_bits_left_def pt_index_def max_pt_level_def2
  supply user_region_simps = user_region_def canonical_user_def
  supply caps_of_state_simps = caps_of_state_def get_cap_def gets_def get_def get_object_def
                               assert_def assert_opt_def fail_def return_def bind_def
  apply (clarsimp simp: valid_vs_lookup_def vs_lookup_target_def vs_lookup_slot_def split: if_splits)
   \<comment> \<open>asid pool level\<close>
   apply (drule vs_lookup_level)
   apply (clarsimp simp: pool_for_asid_vs_lookup pool_for_asid_s0 asid_pools_of_s0
                         vspace_for_pool_def user_region_def vref_for_level_asid_pool
                  dest!: asid_high_low split: if_splits)
    \<comment> \<open>High asid\<close>
    apply (rule conjI, clarsimp simp: High_asid_def asid_low_bits_def)
    apply (rule_tac x=High_cnode_ptr in exI)
    apply (rule_tac x="(the_nat_to_bl_10 3)" in exI)
    apply (fastforce simp: High_cnode_def High_caps_def caps_of_state_def get_cap_def get_object_def
                           gets_def get_def assert_def assert_opt_def fail_def return_def bind_def
                           s0_internal_def kh0_def well_formed_cnode_n_def)
   \<comment> \<open>Low asid\<close>
   apply (rule conjI, clarsimp simp: Low_asid_def asid_low_bits_def)
   apply (rule_tac x=Low_cnode_ptr in exI)
   apply (rule_tac x="(the_nat_to_bl_10 3)" in exI)
   apply (fastforce simp: Low_cnode_def Low_caps_def caps_of_state_def get_cap_def get_object_def
                          gets_def get_def assert_def assert_opt_def fail_def return_def bind_def
                          s0_internal_def kh0_def well_formed_cnode_n_def)
  \<comment> \<open>below asid pool level\<close>
  apply (clarsimp simp: vs_lookup_table_def split: if_splits)
  apply (clarsimp simp: pt_walk.simps)
  apply (case_tac "bot_level < max_pt_level"; clarsimp)

   prefer 2
   \<comment> \<open>bot level = max pt level\<close>

   apply (clarsimp simp: pool_for_asid_s0 vspace_for_pool_def asid_pools_of_s0
                  dest!: asid_high_low split: if_splits)
    \<comment> \<open>High asid\<close>
    apply (rule conjI, clarsimp simp: High_asid_def asid_low_bits_def)
    apply (rule_tac x=High_cnode_ptr in exI)
    apply (rule_tac x="(the_nat_to_bl_10 6)" in exI)
    apply (rule_tac x="ArchObjectCap (PageTableCap High_pt_ptr (Some (High_asid,0)))" in exI)
    apply (subst (asm) s0_internal_def)
    apply (clarsimp simp: in_omonad ptes_of_def High_pd_def ptrFromPAddr_addr_from_ppn'
                   dest!: kh0_SomeD split: if_splits)
     apply (intro conjI)
      apply (fastforce simp: High_cnode_def High_caps_def caps_of_state_simps
                             s0_internal_def kh0_def well_formed_cnode_n_def)
     apply (clarsimp simp: vref_for_level_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
     apply (word_bitwise, fastforce)
    apply (clarsimp simp: kh0_obj_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
    apply (rule FalseE, word_bitwise, fastforce simp: elf_index_value)
   \<comment> \<open>Low asid\<close>
   apply (rule conjI, clarsimp simp: Low_asid_def asid_low_bits_def)
   apply (rule_tac x=Low_cnode_ptr in exI)
   apply (rule_tac x="(the_nat_to_bl_10 6)" in exI)
   apply (rule_tac x="ArchObjectCap (PageTableCap Low_pt_ptr (Some (Low_asid,0)))" in exI)
   apply (subst (asm) s0_internal_def)
   apply (clarsimp simp: in_omonad ptes_of_def Low_pd_def ptrFromPAddr_addr_from_ppn'
                  dest!: kh0_SomeD split: if_splits)
    apply (intro conjI)
     apply (fastforce simp: Low_cnode_def Low_caps_def caps_of_state_simps
                            s0_internal_def kh0_def well_formed_cnode_n_def)
    apply (clarsimp simp: vref_for_level_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
    apply (word_bitwise, fastforce)
   apply (clarsimp simp: kh0_obj_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
   apply (rule FalseE, word_bitwise, fastforce simp: elf_index_value)
  \<comment> \<open>bot level < max pt level\<close>
  apply (clarsimp simp: pool_for_asid_s0 vspace_for_pool_def asid_pools_of_s0
                 dest!: asid_high_low split: if_splits)
     \<comment> \<open>High asid\<close>
     apply (subst (asm) ptes_of_def)
     apply (clarsimp simp: pts_of_s0)
     apply (clarsimp simp: in_omonad kh0_obj_def pptr_from_pte_def ptrFromPAddr_addr_from_ppn'
                    split: if_splits)
     apply (rule conjI, clarsimp simp: High_asid_def asid_low_bits_def)
     apply (prop_tac "pt_walk (max_pt_level - 1) bot_level High_pt_ptr vref (ptes_of s0_internal) =
                      Some (max_pt_level - 1, High_pt_ptr)")
      apply (clarsimp simp: pt_walk.simps)
      apply (clarsimp simp: ptes_of_def pts_of_s0 in_omonad split: if_splits)
     apply (clarsimp simp: ptes_of_def pts_of_s0 shared_page_ptr_phys_def ptrFromPAddr_addr_from_ppn'
                    split: if_splits)
     apply (rule_tac x=High_cnode_ptr in exI)
     apply (rule_tac x="the_nat_to_bl_10 5" in exI)
     apply (rule exI, intro conjI)
       apply (fastforce simp: High_cnode_def High_caps_def caps_of_state_simps
                              s0_internal_def kh0_def well_formed_cnode_n_def)
      apply clarsimp
     apply (clarsimp simp: vref_for_level_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
     apply (word_bitwise, fastforce)
    \<comment> \<open>Low asid\<close>
    prefer 2
    apply (subst (asm) ptes_of_def)
    apply (clarsimp simp: pts_of_s0)
    apply (clarsimp simp: in_omonad kh0_obj_def pptr_from_pte_def ptrFromPAddr_addr_from_ppn'
                   split: if_splits)
    apply (rule conjI, clarsimp simp: Low_asid_def asid_low_bits_def)
    apply (prop_tac "pt_walk (max_pt_level - 1) bot_level Low_pt_ptr vref (ptes_of s0_internal) =
                     Some (max_pt_level - 1, Low_pt_ptr)")
     apply (clarsimp simp: pt_walk.simps)
     apply (clarsimp simp: ptes_of_def pts_of_s0 in_omonad split: if_splits)
    apply (clarsimp simp: ptes_of_def pts_of_s0 shared_page_ptr_phys_def ptrFromPAddr_addr_from_ppn'
                   split: if_splits)
    apply (rule_tac x=Low_cnode_ptr in exI)
    apply (rule_tac x="the_nat_to_bl_10 5" in exI)
    apply (rule exI, intro conjI)
      apply (fastforce simp: Low_cnode_def Low_caps_def caps_of_state_simps
                             s0_internal_def kh0_def well_formed_cnode_n_def)
     apply clarsimp
    apply (clarsimp simp: vref_for_level_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
    apply (word_bitwise, fastforce)
   \<comment> \<open>No lookups to other ptes\<close>
   apply (clarsimp simp: in_omonad ptes_of_def pts_of_s0  split: if_splits)
   apply (clarsimp simp: kh0_obj_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
   apply (rule FalseE, word_bitwise, fastforce simp: elf_index_value)
  apply (clarsimp simp: in_omonad ptes_of_def pts_of_s0  split: if_splits)
  apply (clarsimp simp: kh0_obj_def mask_def pt_simps user_region_simps bit_simps s0_ptr_defs)
  apply (rule FalseE, word_bitwise, fastforce simp: elf_index_value)
  done

lemma valid_arch_caps_s0[simp]:
  "valid_arch_caps s0_internal"
  supply if_split[split del]
  supply caps_of_state_simps = caps_of_state_def get_cap_def gets_def get_def get_object_def
                               assert_def assert_opt_def fail_def return_def bind_def
  apply (clarsimp simp: valid_arch_caps_def)
  apply (intro conjI)
      apply (simp add: valid_vs_lookup_s0_internal)
     apply (clarsimp simp: valid_asid_pool_caps_def s0_internal_def arch_state0_def)
     apply (clarsimp split: if_splits)
      apply (rule_tac x="High_cnode_ptr" in exI)
      apply (rule_tac x="the_nat_to_bl_10 4" in exI)
      apply (force simp: caps_of_state_simps well_formed_cnode_n_def s0_internal_def kh0_obj_def
                         kh0_def High_caps_def High_asid_def asid_high_bits_of_def asid_low_bits_def
                  split: if_splits)
     apply (rule_tac x="Low_cnode_ptr" in exI)
     apply (rule_tac x="the_nat_to_bl_10 4" in exI)
     apply (force simp: caps_of_state_simps well_formed_cnode_n_def s0_internal_def kh0_obj_def
                        kh0_def Low_caps_def Low_asid_def asid_high_bits_of_def asid_low_bits_def
                 split: if_splits)
    apply (clarsimp simp: valid_table_caps_def)
    apply (fastforce simp: caps_of_state_simps pts_of_s0 s0_internal_def kh0_obj_def
                           tcb_cnode_map_def Silc_caps_def High_caps_def Low_caps_def
                    dest!: kh0_SomeD split: if_splits kernel_object.splits option.splits)
   apply (clarsimp simp: unique_table_caps_def)
   apply (clarsimp simp: caps_of_state_simps split: if_splits kernel_object.splits option.splits)
      apply (subst (asm) s0_internal_def)
      apply (clarsimp simp: kh0_def kh0_obj_def Silc_caps_def High_caps_def Low_caps_def
                     split: if_splits)
     apply (subst (asm) s0_internal_def)
     apply (clarsimp simp: kh0_def kh0_obj_def Silc_caps_def High_caps_def Low_caps_def
                    split: if_splits)
    apply (clarsimp simp: s0_internal_def kh0_def kh0_obj_def split: if_splits;
           clarsimp simp: tcb_cnode_map_def split: if_splits)
   apply (clarsimp simp: s0_internal_def kh0_def kh0_obj_def split: if_splits;
          clarsimp simp: tcb_cnode_map_def split: if_splits)
  apply (clarsimp simp: unique_table_refs_def)
  apply (drule s0_caps_of_state)+
  apply clarsimp
  apply (elim disjE; clarsimp)
  done

lemma valid_global_objs_s0[simp]:
  "valid_global_objs s0_internal"
  by (clarsimp simp: valid_global_objs_def s0_internal_def arch_state0_def)

lemma valid_kernel_mappings_s0[simp]:
  "valid_kernel_mappings s0_internal"
  by (clarsimp simp: valid_kernel_mappings_def s0_internal_def ran_def
              split: kernel_object.splits arch_kernel_obj.splits)

lemma equal_kernel_mappings_s0[simp]:
  "equal_kernel_mappings s0_internal"
  supply misc = vref_for_level_def pt_bits_left_def asid_pool_level_size
                pageBits_def ptTranslationBits_def mask_def max_pt_level_def2
  apply (clarsimp simp: equal_kernel_mappings_def obj_at_def vspace_for_asid_def
                        vspace_for_pool_def pool_for_asid_s0 asid_pools_of_s0)
   apply (clarsimp simp: obind_def pts_of_s0)
   apply (clarsimp simp: has_kernel_mappings_def split: if_splits)
   apply (rule conjI; clarsimp)
    apply (clarsimp simp: kernel_mapping_slots_def s0_ptr_defs misc)
   apply (fastforce simp: pts_of_s0 s0_internal_def arch_state0_def
                          kh0_obj_def opt_map_def riscv_global_pt_def
                   dest!: kh0_SomeD split: if_splits option.splits)
  apply (clarsimp simp: pts_of_s0)
  apply (clarsimp simp: s0_internal_def riscv_global_pt_def arch_state0_def kh0_obj_def
                        kernel_mapping_slots_def s0_ptr_defs misc elf_index_value)+
  done

lemma valid_asid_map_s0[simp]:
  "valid_asid_map s0_internal"
  by (clarsimp simp: valid_asid_map_def s0_internal_def arch_state0_def)

lemma valid_global_pd_mappings_s0_helper:
  "\<lbrakk> pptr_base \<le> vref; vref < pptr_base + (1 << kernel_window_bits) \<rbrakk>
     \<Longrightarrow> \<exists>a b. pt_lookup_target 0 riscv_global_pt_ptr vref (ptes_of s0_internal) = Some (a, b) \<and>
               is_aligned b (pt_bits_left a) \<and>
               addrFromPPtr b + (vref && mask (pt_bits_left a)) = addrFromPPtr vref"
  supply misc = vref_for_level_def pt_bits_left_def asid_pool_level_size
                pageBits_def ptTranslationBits_def mask_def max_pt_level_def2
  apply (clarsimp simp: pt_lookup_target_def obind_def split: option.splits)
  apply (prop_tac "pt_lookup_slot_from_level max_pt_level 0 riscv_global_pt_ptr vref (ptes_of s0_internal) =
                   Some (max_pt_level, pt_slot_offset max_pt_level riscv_global_pt_ptr vref)")
   apply (clarsimp simp: pt_lookup_slot_from_level_def pt_walk.simps)
   apply (fastforce simp: ptes_of_def in_omonad s0_internal_def kh0_def init_global_pt_def
                          global_pte_def is_aligned_pt_slot_offset_pte)
  apply (clarsimp simp: pt_lookup_slot_from_level_def pt_walk.simps)
  apply (rule conjI; clarsimp dest!: pt_walk_max_level simp: max_pt_level_def2 split: if_splits)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: ptes_of_def pts_of_s0 global_pte_def kernel_window_bits_def
                         table_index_offset_pt_bits_left is_aligned_pt_slot_offset_pte
                  split: if_splits)
    apply (clarsimp simp: misc s0_ptr_defs)
    apply (word_bitwise, fastforce)
   apply (clarsimp simp: misc s0_ptr_defs kernel_mapping_slots_def)
   apply (word_bitwise, fastforce)
  apply (clarsimp simp: ptes_of_def pts_of_s0 is_aligned_pt_slot_offset_pte global_pte_def
                 split: if_splits)
   apply (clarsimp simp: addr_from_ppn_def ptrFromPAddr_def addrFromPPtr_def bit_simps
                         mask_def s0_ptr_defs pt_bits_left_def max_pt_level_def2
                         pptrBaseOffset_def paddrBase_def is_aligned_def kernel_window_bits_def)
   apply (word_bitwise, fastforce)
  apply (clarsimp simp: addr_from_ppn_def ptrFromPAddr_def addrFromPPtr_def bit_simps is_aligned_def
                        s0_ptr_defs pt_bits_left_def max_pt_level_def2 kernel_mapping_slots_def
                        mask_def pt_slot_offset_def pt_index_def pptrBaseOffset_def paddrBase_def
                        toplevel_bits_value elf_index_value kernel_window_bits_def)
  apply (word_bitwise, fastforce)
  done

lemma ptes_of_elf_window:
  "\<lbrakk>kernel_elf_base \<le> vref; vref < kernel_elf_base + 2 ^ pageBits\<rbrakk>
   \<Longrightarrow> ptes_of s0_internal (pt_slot_offset max_pt_level riscv_global_pt_ptr vref)
       = Some (global_pte elf_index)"
  unfolding ptes_of_def pts_of_s0
  apply (clarsimp simp: obind_def elf_window_4k is_aligned_pt_slot_offset_pte)
  done

lemma valid_global_pd_mappings_s0_helper':
  "\<lbrakk> kernel_elf_base \<le> vref; vref < kernel_elf_base + (1 << pageBits) \<rbrakk>
     \<Longrightarrow> \<exists>a b. pt_lookup_target 0 riscv_global_pt_ptr vref (ptes_of s0_internal) = Some (a, b) \<and>
               is_aligned b (pt_bits_left a) \<and>
               addrFromPPtr b + (vref && mask (pt_bits_left a)) = addrFromKPPtr vref"
  supply misc = vref_for_level_def pt_bits_left_def asid_pool_level_size
                pageBits_def ptTranslationBits_def mask_def max_pt_level_def2
  apply (clarsimp simp: pt_lookup_target_def obind_def split: option.splits)
  apply (prop_tac "pt_lookup_slot_from_level max_pt_level 0 riscv_global_pt_ptr vref (ptes_of s0_internal) =
                   Some (max_pt_level, pt_slot_offset max_pt_level riscv_global_pt_ptr vref)")
   apply (clarsimp simp: pt_lookup_slot_from_level_def pt_walk.simps)
   apply (fastforce simp: ptes_of_def in_omonad s0_internal_def kh0_def init_global_pt_def
                          global_pte_def is_aligned_pt_slot_offset_pte)
  apply (rule conjI; clarsimp)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: pt_lookup_slot_from_level_def pt_walk.simps)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: ptes_of_elf_window global_pte_def split: if_splits)
  apply (clarsimp simp: ptes_of_elf_window global_pte_def elf_index_value)
  apply (clarsimp simp: is_aligned_ptrFromPAddr_kernelELFPAddrBase kernelELFPAddrBase_addrFromKPPtr)
  done

lemma valid_global_pd_mappings_s0[simp]:
  "valid_global_vspace_mappings s0_internal"
  unfolding valid_global_vspace_mappings_def Let_def
  apply (intro conjI)
    apply (simp add: s0_internal_def arch_state0_def riscv_global_pt_def)
   apply (fastforce simp: s0_internal_def arch_state0_def in_omonad kernel_window_def
                          init_vspace_uses_def translate_address_def riscv_global_pt_def
                   dest!: valid_global_pd_mappings_s0_helper split: if_splits)
  apply (fastforce simp: translate_address_def in_omonad s0_internal_def arch_state0_def
                         riscv_global_pt_def kernel_elf_window_def init_vspace_uses_def
                  dest!: valid_global_pd_mappings_s0_helper' split: if_splits)
  done

lemma pspace_in_kernel_window_s0[simp]:
  "pspace_in_kernel_window s0_internal"
  apply (clarsimp simp: pspace_in_kernel_window_def kernel_window_def
                        init_vspace_uses_def s0_internal_def arch_state0_def)
  apply (subgoal_tac "x \<in> {pptr_base..<pptr_base + (1 << kernel_window_bits)}"; clarsimp)
  apply (drule kh0_SomeD)
  by (clarsimp simp: s0_ptr_defs kh0_obj_def cte_level_bits_def table_size pageBits_def
                     ptTranslationBits_def kernel_window_bits_def
              dest!: irq_node_offs_range_correct
      | erule disjE dual_order.strict_trans2[rotated] dual_order.trans
      | rule conjI | word_bitwise)+

lemma cap_refs_in_kernel_window_s0[simp]:
  "cap_refs_in_kernel_window s0_internal"
  apply (clarsimp simp: cap_refs_in_kernel_window_def valid_refs_def not_kernel_window_def
                        cap_range_def Invariants_AI.cte_wp_at_caps_of_state)
  apply (subgoal_tac "- kernel_window s0_internal \<inter> obj_refs cap = {}")
   apply (fastforce dest: s0_caps_of_state)
  apply (rule Int_emptyI, clarsimp)
  apply (erule swap, clarsimp)
  apply (drule s0_caps_of_state)
  apply (clarsimp simp: kernel_window_def init_vspace_uses_def s0_internal_def arch_state0_def)
  apply (subgoal_tac "x \<in> {pptr_base..<pptr_base + (1 << kernel_window_bits)}"; clarsimp)
  by (clarsimp simp: s0_ptr_defs kh0_obj_def table_size pageBits_def ptTranslationBits_def
                     kernel_window_bits_def
              dest!: irq_node_offs_range_correct
      | erule disjE dual_order.strict_trans2[rotated] dual_order.trans
      | rule conjI | word_bitwise)+

lemma cur_tcb_s0[simp]:
  "cur_tcb s0_internal"
  by (simp add: cur_tcb_def s0_ptr_defs s0_internal_def kh0_def kh0_obj_def obj_at_def is_tcb_def)

lemma valid_list_s0[simp]:
  "valid_list s0_internal"
  by (simp add: valid_list_2_def s0_internal_def exst0_def const_def)

lemma valid_sched_s0[simp]:
  "valid_sched s0_internal"
  apply (simp add: valid_sched_def s0_internal_def exst0_def)
  apply (intro conjI)
        apply (clarsimp simp: valid_etcbs_def is_etcb_at'_def kh0_def kh0_obj_def
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
   apply (clarsimp simp: s0_internal_def pspace_respects_device_region_def machine_state0_def kh0_def
                         kh0_obj_def device_mem_def in_device_frame_def obj_at_kh_def obj_at_def
                  split: if_splits)
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
  by (simp add: valid_state_def invs_def respects_device_trivial)


subsubsection \<open>Haskell state\<close>

text \<open>One invariant we need on s0 is that there exists
        an associated Haskell state satisfying the invariants.
        This does not yet exist.\<close>

lemma Sys1_valid_initial_state_noenabled:
  assumes extras_s0: "step_restrict s0"
  assumes utf_det: "\<forall>pl pr pxn tc ms s. det_inv InUserMode tc s \<and> einvs s \<and>
                                        context_matches_state pl pr pxn ms s \<and> ct_running s
                   \<longrightarrow> (\<exists>x. utf (cur_thread s) pl pr pxn (tc, ms) = {x})"
  assumes utf_non_empty: "\<forall>t pl pr pxn tc ms. utf t pl pr pxn (tc, ms) \<noteq> {}"
  assumes utf_non_interrupt: "\<forall>t pl pr pxn tc ms e f g. (e,f,g) \<in> utf t pl pr pxn (tc, ms)
                                                         \<longrightarrow> e \<noteq> Some Interrupt"
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
          apply (clarsimp simp: valid_domain_list_2_def s0_internal_def exst0_def)
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
