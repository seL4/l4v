(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Example_Valid_StateH
imports "InfoFlow.Example_Valid_State" ArchADT_IF_Refine
begin

context begin interpretation Arch .

section \<open>Haskell state\<close>

text \<open>One invariant we need on s0 is that there exists
        an associated Haskell state satisfying the invariants.
        This does not yet exist.\<close>

subsection \<open>Defining the State\<close>

definition empty_cte :: "nat \<Rightarrow> bool list \<Rightarrow> (capability \<times> mdbnode) option" where
  "empty_cte bits \<equiv> \<lambda>x. if length x = bits then Some (NullCap, MDB 0 0 False False) else None"

abbreviation (input) Null_mdb :: "mdbnode" where
  "Null_mdb \<equiv> MDB 0 0 False False"


text \<open>Low's CSpace\<close>

definition Low_capsH :: "cnode_index \<Rightarrow> (capability \<times> mdbnode) option" where
  "Low_capsH \<equiv>
     (empty_cte 10)
       ((the_nat_to_bl_10 1)
          \<mapsto> (ThreadCap Low_tcb_ptr, Null_mdb),
        (the_nat_to_bl_10 2)
          \<mapsto> (CNodeCap Low_cnode_ptr 10 2 10, MDB 0 Low_tcb_ptr False False),
        (the_nat_to_bl_10 3)
          \<mapsto> (ArchObjectCap (PageTableCap Low_pd_ptr (Some (ucast Low_asid, 0))),
              MDB 0 (Low_tcb_ptr + 0x20) False False),
        (the_nat_to_bl_10 4)
          \<mapsto> (ArchObjectCap (ASIDPoolCap Low_pool_ptr (ucast Low_asid)), Null_mdb),
        (the_nat_to_bl_10 5)
          \<mapsto> (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadWrite RISCVLargePage
                                      False (Some (ucast Low_asid, 0))),
              MDB 0 (Silc_cnode_ptr + 0xA0) False False),
        (the_nat_to_bl_10 6)
          \<mapsto> (ArchObjectCap (PageTableCap Low_pt_ptr (Some (ucast Low_asid, 0))), Null_mdb),
        (the_nat_to_bl_10 318)
          \<mapsto> (NotificationCap ntfn_ptr 0 True False, MDB (Silc_cnode_ptr + 318 * 0x20) 0 False False))"

definition Low_cte' :: "10 word \<Rightarrow> cte option" where
  "Low_cte' \<equiv> (map_option (\<lambda>(cap, mdb). CTE cap mdb)) \<circ> Low_capsH \<circ> to_bl"

definition Low_cte :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "Low_cte \<equiv> \<lambda>base offs.
     if is_aligned offs 5 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 15 - 1
     then map_option (\<lambda>cte. KOCTE cte) (Low_cte' (ucast (offs - base >> 5)))
     else None"


text \<open>High's Cspace\<close>

definition High_capsH :: "cnode_index \<Rightarrow> (capability \<times> mdbnode) option" where
  "High_capsH \<equiv>
     (empty_cte 10)
       ((the_nat_to_bl_10 1)
          \<mapsto> (ThreadCap High_tcb_ptr, Null_mdb),
        (the_nat_to_bl_10 2)
          \<mapsto> (CNodeCap High_cnode_ptr 10 2 10, MDB 0 High_tcb_ptr False False),
        (the_nat_to_bl_10 3)
          \<mapsto> (ArchObjectCap (PageTableCap High_pd_ptr (Some (ucast High_asid, 0))),
              MDB 0 (High_tcb_ptr + 0x20) False False),
        (the_nat_to_bl_10 4)
          \<mapsto> (ArchObjectCap (ASIDPoolCap High_pool_ptr (ucast High_asid)), Null_mdb),
        (the_nat_to_bl_10 5)
          \<mapsto> (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadOnly RISCVLargePage
                                      False (Some (ucast High_asid, 0))),
              MDB (Silc_cnode_ptr + 0xA0) 0 False False),
        (the_nat_to_bl_10 6)
          \<mapsto> (ArchObjectCap (PageTableCap High_pt_ptr (Some (ucast High_asid, 0))),
                  Null_mdb),
        (the_nat_to_bl_10 318)
          \<mapsto> (NotificationCap ntfn_ptr 0 False True, MDB 0 (Silc_cnode_ptr + 318 * 0x20) False False))"

definition High_cte' :: "10 word \<Rightarrow> cte option" where
  "High_cte' \<equiv> (map_option (\<lambda>(cap, mdb). CTE cap mdb)) \<circ> High_capsH \<circ> to_bl"

definition High_cte :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "High_cte \<equiv> \<lambda>base offs.
     if is_aligned offs 5 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 15 - 1
     then map_option (\<lambda>cte. KOCTE cte) (High_cte' (ucast (offs - base >> 5)))
     else None"


text \<open>We need a copy of boundary crossing caps owned by SilcLabel.\<close>

definition Silc_capsH :: "cnode_index \<Rightarrow> (capability \<times> mdbnode) option" where
  "Silc_capsH \<equiv>
     (empty_cte 10)
       ((the_nat_to_bl_10 2)
          \<mapsto> (CNodeCap Silc_cnode_ptr 10 2 10, Null_mdb),
        (the_nat_to_bl_10 5)
          \<mapsto> (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadOnly RISCVLargePage
                                      False (Some (ucast Silc_asid, 0))),
              MDB (Low_cnode_ptr + 0xA0) (High_cnode_ptr + 0xA0) False False),
        (the_nat_to_bl_10 318)
          \<mapsto> (NotificationCap ntfn_ptr 0 True False,
              MDB (High_cnode_ptr + 318 * 0x20) (Low_cnode_ptr + 318 * 0x20) False False))"

definition Silc_cte' :: "10 word \<Rightarrow> cte option" where
  "Silc_cte' \<equiv> (map_option (\<lambda>(cap, mdb). CTE cap mdb)) \<circ> Silc_capsH \<circ> to_bl"

definition Silc_cte :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "Silc_cte \<equiv> \<lambda>base offs.
     if is_aligned offs 5 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 15 - 1
     then map_option (\<lambda>cte. KOCTE cte) (Silc_cte' (ucast (offs - base >> 5)))
     else None"


text \<open>Notification between Low and High\<close>

definition ntfnH :: notification where
  "ntfnH \<equiv> NTFN (ntfn.WaitingNtfn [High_tcb_ptr]) None"


text \<open>Global page table\<close>

definition global_pteH' :: "pt_index \<Rightarrow> pte" where
  "global_pteH' idx \<equiv>
     if idx = 0x100
     then PagePTE ((ucast (idx && mask (ptTranslationBits - 1)) << ptTranslationBits * size max_pt_level))
                  False False False VMKernelOnly
     else if idx = elf_index
     then PagePTE (ucast ((kernelELFPAddrBase && ~~mask toplevel_bits) >> pageBits)) False False False VMKernelOnly
     else InvalidPTE"

definition global_pteH where
  "global_pteH \<equiv> (\<lambda>idx. if idx \<in> kernel_mapping_slots then global_pteH' idx else InvalidPTE)"

definition global_ptH :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "global_ptH \<equiv> \<lambda>base.
     (map_option (\<lambda>x. KOArch (KOPTE (global_pteH (x :: pt_index))))) \<circ>
     (\<lambda>offs. if is_aligned offs 3 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 12 - 1
             then Some (ucast (offs - base >> 3)) else None)"


text \<open>Low's page tables\<close>

definition Low_pt'H :: "pt_index \<Rightarrow> pte" where
  "Low_pt'H \<equiv>
     (\<lambda>_. InvalidPTE)
       (0 := PagePTE (shared_page_ptr_phys >> pt_bits) False False False VMReadWrite)"

definition Low_ptH :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "Low_ptH \<equiv>
     \<lambda>base. (map_option (\<lambda>x. KOArch (KOPTE (Low_pt'H x)))) \<circ>
            (\<lambda>offs. if is_aligned offs 3 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 12 - 1
                    then Some (ucast (offs - base >> 3)) else None)"

definition Low_pd'H :: "pt_index \<Rightarrow> pte" where
  "Low_pd'H \<equiv>
     global_pteH
       (0 := PageTablePTE (addrFromPPtr Low_pt_ptr >> pt_bits) False)"

definition Low_pdH :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "Low_pdH \<equiv>
     \<lambda>base. (map_option (\<lambda>x. KOArch (KOPTE (Low_pd'H x)))) \<circ>
            (\<lambda>offs. if is_aligned offs 3 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 12 - 1
                    then Some (ucast (offs - base >> 3)) else None)"


text \<open>High's page tables\<close>

definition High_pt'H :: "pt_index \<Rightarrow> pte" where
  "High_pt'H \<equiv>
     (\<lambda>_. InvalidPTE)
       (0 := PagePTE (shared_page_ptr_phys >> pt_bits) False False False VMReadOnly)"

definition High_ptH :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "High_ptH \<equiv>
     \<lambda>base. (map_option (\<lambda>x. KOArch (KOPTE (High_pt'H x)))) \<circ>
            (\<lambda>offs. if is_aligned offs 3 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 12 - 1
                    then Some (ucast (offs - base >> 3)) else None)"

definition High_pd'H :: "pt_index \<Rightarrow> pte" where
  "High_pd'H \<equiv>
     global_pteH
       (0 := PageTablePTE (addrFromPPtr High_pt_ptr >> pt_bits) False)"

definition High_pdH :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "High_pdH \<equiv>
     \<lambda>base. (map_option (\<lambda>x. KOArch (KOPTE (High_pd'H x)))) \<circ>
            (\<lambda>offs. if is_aligned offs 3 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 12 - 1
                    then Some (ucast (offs - base >> 3)) else None)"


text \<open>Low's tcb\<close>

definition Low_tcbH :: tcb where
  "Low_tcbH \<equiv> Thread
     \<comment> \<open>tcbCTable            =\<close> (CTE (CNodeCap Low_cnode_ptr 10 2 10)
                                      (MDB (Low_cnode_ptr + 0x40) 0 False False))
     \<comment> \<open>tcbVTable            =\<close> (CTE (ArchObjectCap (PageTableCap Low_pd_ptr (Some (ucast Low_asid, 0))))
                                      (MDB (Low_cnode_ptr + 0x60) 0 False False))
     \<comment> \<open>tcbReply             =\<close> (CTE (ReplyCap Low_tcb_ptr True True) (MDB 0 0 True True))
     \<comment> \<open>tcbCaller            =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbIPCBufferFrame    =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbDomain            =\<close> Low_domain
     \<comment> \<open>tcbState             =\<close> Running
     \<comment> \<open>tcbMCPriority        =\<close> Low_mcp
     \<comment> \<open>tcbPriority          =\<close> Low_prio
     \<comment> \<open>tcbQueued            =\<close> False
     \<comment> \<open>tcbFault             =\<close> None
     \<comment> \<open>tcbTimeSlice         =\<close> Low_time_slice
     \<comment> \<open>tcbFaultHandler      =\<close> 0
     \<comment> \<open>tcbIPCBuffer         =\<close> 0
     \<comment> \<open>tcbBoundNotification =\<close> None
     \<comment> \<open>tcbSchedPrev         =\<close> None
     \<comment> \<open>tcbSchedNext         =\<close> None
     \<comment> \<open>tcbContext           =\<close> (ArchThread undefined)"


text \<open>High's tcb\<close>

definition High_tcbH :: tcb where
  "High_tcbH \<equiv> Thread
     \<comment> \<open>tcbCTable            =\<close> (CTE (CNodeCap High_cnode_ptr 10 2 10)
                                      (MDB (High_cnode_ptr + 0x40) 0 False False))
     \<comment> \<open>tcbVTable            =\<close> (CTE (ArchObjectCap (PageTableCap High_pd_ptr (Some (ucast High_asid, 0))))
                                      (MDB (High_cnode_ptr + 0x60) 0 False False))
     \<comment> \<open>tcbReply             =\<close> (CTE (ReplyCap High_tcb_ptr True True) (MDB 0 0 True True))
     \<comment> \<open>tcbCaller            =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbIPCBufferFrame    =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbDomain            =\<close> High_domain
     \<comment> \<open>tcbState             =\<close> (BlockedOnNotification ntfn_ptr)
     \<comment> \<open>tcbMCPriority        =\<close> High_mcp
     \<comment> \<open>tcbPriority          =\<close> High_prio
     \<comment> \<open>tcbQueued            =\<close> False
     \<comment> \<open>tcbFault             =\<close> None
     \<comment> \<open>tcbTimeSlice         =\<close> High_time_slice
     \<comment> \<open>tcbFaultHandler      =\<close> 0
     \<comment> \<open>tcbIPCBuffer         =\<close> 0
     \<comment> \<open>tcbBoundNotification =\<close> None
     \<comment> \<open>tcbSchedPrev         =\<close> None
     \<comment> \<open>tcbSchedNext         =\<close> None
     \<comment> \<open>tcbContext           =\<close> (ArchThread undefined)"


text \<open>idle's tcb\<close>

definition idle_tcbH :: tcb where
  "idle_tcbH \<equiv> Thread
     \<comment> \<open>tcbCTable            =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbVTable            =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbReply             =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbCaller            =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbIPCBufferFrame    =\<close> (CTE NullCap Null_mdb)
     \<comment> \<open>tcbDomain            =\<close> default_domain
     \<comment> \<open>tcbState             =\<close> IdleThreadState
     \<comment> \<open>tcbMCPriority        =\<close> default_priority
     \<comment> \<open>tcbPriority          =\<close> default_priority
     \<comment> \<open>tcbQueued            =\<close> False
     \<comment> \<open>tcbFault             =\<close> None
     \<comment> \<open>tcbTimeSlice         =\<close> timeSlice
     \<comment> \<open>tcbFaultHandler      =\<close> 0
     \<comment> \<open>tcbIPCBuffer         =\<close> 0
     \<comment> \<open>tcbBoundNotification =\<close> None
     \<comment> \<open>tcbSchedPrev         =\<close> None
     \<comment> \<open>tcbSchedNext         =\<close> None
     \<comment> \<open>tcbContext           =\<close> (ArchThread empty_context)"


text \<open>Low's asid pool\<close>

abbreviation Low_poolH' :: "obj_ref \<rightharpoonup> obj_ref" where
  "Low_poolH' \<equiv> \<lambda>idx. if idx = ucast (asid_low_bits_of Low_asid) then Some Low_pd_ptr else None"

definition Low_poolH :: arch_kernel_object where
  "Low_poolH \<equiv> KOASIDPool (ASIDPool Low_poolH')"


text \<open>High's asid pool\<close>

abbreviation High_poolH' :: "obj_ref \<rightharpoonup> obj_ref" where
  "High_poolH' \<equiv> \<lambda>idx. if idx = ucast (asid_low_bits_of High_asid) then Some High_pd_ptr else None"

definition High_poolH :: arch_kernel_object where
  "High_poolH \<equiv> KOASIDPool (ASIDPool High_poolH')"


text \<open>Shared page\<close>

definition shared_pageH :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> kernel_object option" where
  "shared_pageH \<equiv> \<lambda>base.
     (\<lambda>offs. if is_aligned offs 12 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 21 - 1
             then Some KOUserData else None)"


text \<open>Initial ksPSpace\<close>

definition irq_cte :: cte where
  "irq_cte \<equiv> CTE NullCap Null_mdb"

definition option_update_range :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> 'b option)" where
  "option_update_range f g \<equiv> \<lambda>x. case f x of None \<Rightarrow> g x | Some y \<Rightarrow> Some y"

definition kh0H :: "(obj_ref \<rightharpoonup> kernel_object)" where
  "kh0H \<equiv> (option_update_range (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << 5) = x
                                     then Some (KOCTE (CTE NullCap Null_mdb)) else None) \<circ>
           option_update_range (Low_cte Low_cnode_ptr) \<circ>
           option_update_range (High_cte High_cnode_ptr) \<circ>
           option_update_range (Silc_cte Silc_cnode_ptr) \<circ>
           option_update_range [ntfn_ptr \<mapsto> KONotification ntfnH] \<circ>
           option_update_range [irq_cnode_ptr \<mapsto> KOCTE irq_cte] \<circ>
           option_update_range (Low_pdH Low_pd_ptr) \<circ>
           option_update_range (High_pdH High_pd_ptr) \<circ>
           option_update_range (Low_ptH Low_pt_ptr) \<circ>
           option_update_range (High_ptH High_pt_ptr) \<circ>
           option_update_range [Low_pool_ptr \<mapsto> KOArch Low_poolH] \<circ>
           option_update_range [High_pool_ptr \<mapsto> KOArch High_poolH] \<circ>
           option_update_range [Low_tcb_ptr \<mapsto> KOTCB Low_tcbH] \<circ>
           option_update_range [High_tcb_ptr \<mapsto> KOTCB High_tcbH] \<circ>
           option_update_range [idle_tcb_ptr \<mapsto> KOTCB idle_tcbH] \<circ>
           option_update_range (shared_pageH shared_page_ptr_virt) \<circ>
           option_update_range (global_ptH riscv_global_pt_ptr)
           ) Map.empty"


lemma s0_ptrs_aligned:
  "is_aligned riscv_global_pt_ptr 12"
  "is_aligned High_pd_ptr 12"
  "is_aligned Low_pd_ptr 12"
  "is_aligned High_pt_ptr 12"
  "is_aligned Low_pt_ptr 12"
  "is_aligned Silc_cnode_ptr 15"
  "is_aligned High_cnode_ptr 15"
  "is_aligned Low_cnode_ptr 15"
  "is_aligned High_tcb_ptr 10"
  "is_aligned Low_tcb_ptr 10"
  "is_aligned idle_tcb_ptr 10"
  "is_aligned ntfn_ptr 5"
  "is_aligned shared_page_ptr_virt 21"
  "is_aligned irq_cnode_ptr 10"
  "is_aligned Low_pool_ptr 12"
  "is_aligned High_pool_ptr 12"
  by (simp add: is_aligned_def s0_ptr_defs)+


text \<open>Page offset lemmas\<close>

lemma page_offs_min':
  "is_aligned ptr 21 \<Longrightarrow> (ptr :: obj_ref) \<le> ptr + (ucast (x :: pt_index) << 12)"
  apply (erule is_aligned_no_wrap')
  apply (word_bitwise, auto)
  done

lemma page_offs_min:
  "shared_page_ptr_virt \<le> shared_page_ptr_virt + (ucast (x:: pt_index) << 12)"
  by (simp_all add: page_offs_min' s0_ptrs_aligned)

lemma page_offs_max':
  "is_aligned ptr 21 \<Longrightarrow> (ptr :: obj_ref) + (ucast (x :: pt_index) << 12) \<le> ptr + 0x1FFFFF"
  apply (rule word_plus_mono_right)
   apply (simp add: shiftl_t2n mult.commute)
   apply (rule div_to_mult_word_lt)
   apply simp
   apply (rule plus_one_helper)
   apply simp
   apply (cut_tac ucast_less[where x=x])
    apply simp
   apply (fastforce elim: dual_order.strict_trans[rotated])
  apply (drule is_aligned_no_overflow)
  apply (simp add: add.commute)
  done

lemma page_offs_max:
  "shared_page_ptr_virt + (ucast (x :: pt_index) << 12) \<le> shared_page_ptr_virt + 0x1FFFFF"
  by (simp_all add: page_offs_max' s0_ptrs_aligned)

definition page_offs_range where
  "page_offs_range (ptr :: obj_ref) \<equiv> {x. ptr \<le> x \<and> x \<le> ptr + 2 ^ 21 - 1}
                                    \<inter> {x. is_aligned x 12}"

lemma page_offs_in_range':
  "is_aligned ptr 21 \<Longrightarrow> ptr + (ucast (x :: pt_index) << 12) \<in> page_offs_range ptr"
  apply (clarsimp simp: page_offs_min' page_offs_max' page_offs_range_def add.commute)
  apply (rule is_aligned_add[OF _ is_aligned_shift])
  apply (erule is_aligned_weaken)
  apply simp
  done

lemma page_offs_in_range:
  "shared_page_ptr_virt + (ucast (x :: pt_index) << 12) \<in> page_offs_range shared_page_ptr_virt"
  by (simp_all add: page_offs_in_range' s0_ptrs_aligned)

lemma page_offs_range_correct':
  "\<lbrakk> x \<in> page_offs_range ptr; is_aligned ptr 21 \<rbrakk>
     \<Longrightarrow> \<exists>y. x = ptr + (ucast (y :: pt_index) << 12)"
  apply (clarsimp simp: page_offs_range_def s0_ptr_defs)
  apply (rule_tac x="ucast ((x - ptr) >> 12)" in exI)
  apply (clarsimp simp: ucast_ucast_mask)
  apply (subst aligned_shiftr_mask_shiftl)
   apply (rule aligned_sub_aligned)
     apply assumption
    apply (erule is_aligned_weaken)
    apply simp
   apply simp
  apply simp
  apply (rule_tac n=21 in mask_eqI)
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_def)
   apply (simp add: mask_twice)
   apply (subst diff_conv_add_uminus)
   apply (subst add.commute[symmetric])
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_minus)
   apply simp
  apply (subst diff_conv_add_uminus)
  apply (subst add_mask_lower_bits)
    apply (simp add: is_aligned_def)
   apply clarsimp
  apply (cut_tac x=x and y="ptr + 0x1FFFFF" and n=21 in neg_mask_mono_le)
   apply (simp add: add.commute)
  apply (drule_tac n=21 in aligned_le_sharp)
   apply (simp add: is_aligned_def)
  apply (simp add: add.commute)
  apply (subst(asm) mask_out_add_aligned[symmetric])
   apply (erule is_aligned_weaken)
   apply simp
  apply (simp add: mask_def)
  done

lemma page_offs_range_correct:
  "x \<in> page_offs_range shared_page_ptr_virt
   \<Longrightarrow> \<exists>y. x = shared_page_ptr_virt + (ucast (y :: pt_index) << 12)"
  by (simp_all add: page_offs_range_correct' s0_ptrs_aligned)


text \<open>Page table offset lemmas\<close>

lemma pt_offs_min':
  "is_aligned ptr 12 \<Longrightarrow> (ptr :: obj_ref) \<le> ptr + (ucast (x :: pt_index) << 3)"
  apply (erule is_aligned_no_wrap')
  apply (word_bitwise, auto)
  done

lemma pt_offs_min:
  "Low_pd_ptr  \<le> Low_pd_ptr  + (ucast (x :: pt_index) << 3)"
  "High_pd_ptr \<le> High_pd_ptr + (ucast (x :: pt_index) << 3)"
  "Low_pt_ptr  \<le> Low_pt_ptr  + (ucast (x :: pt_index) << 3)"
  "High_pt_ptr \<le> High_pt_ptr + (ucast (x :: pt_index) << 3)"
  "riscv_global_pt_ptr \<le> riscv_global_pt_ptr + (ucast (x :: pt_index) << 3)"
  by (simp_all add: pt_offs_min' s0_ptrs_aligned)

lemma pt_offs_max':
  "is_aligned ptr 12 \<Longrightarrow> (ptr :: obj_ref) + (ucast (x :: pt_index) << 3) \<le> ptr + 0xFFF"
  apply (rule word_plus_mono_right)
   apply (simp add: shiftl_t2n mult.commute)
   apply (rule div_to_mult_word_lt)
   apply simp
   apply (rule plus_one_helper)
   apply simp
   apply (cut_tac ucast_less[where x=x])
    apply simp
   apply (fastforce elim: dual_order.strict_trans[rotated])
  apply (drule is_aligned_no_overflow)
  apply (simp add: add.commute)
  done

lemma pt_offs_max:
  "Low_pd_ptr  + (ucast (x :: pt_index) << 3) \<le> Low_pd_ptr  + 0xFFF"
  "High_pd_ptr + (ucast (x :: pt_index) << 3) \<le> High_pd_ptr + 0xFFF"
  "Low_pt_ptr  + (ucast (x :: pt_index) << 3) \<le> Low_pt_ptr  + 0xFFF"
  "High_pt_ptr + (ucast (x :: pt_index) << 3) \<le> High_pt_ptr + 0xFFF"
  "riscv_global_pt_ptr + (ucast (x :: pt_index) << 3) \<le> riscv_global_pt_ptr + 0xFFF"
  by (simp_all add: pt_offs_max' s0_ptrs_aligned)

definition pt_offs_range where
  "pt_offs_range (ptr :: obj_ref) \<equiv> {x. ptr \<le> x \<and> x \<le> ptr + 2 ^ 12 - 1}
                                  \<inter> {x. is_aligned x 3}"

lemma pt_offs_in_range':
  "is_aligned ptr 12
   \<Longrightarrow> ptr + (ucast (x :: pt_index) << 3) \<in> pt_offs_range ptr"
  apply (clarsimp simp: pt_offs_min' pt_offs_max' pt_offs_range_def add.commute)
  apply (rule is_aligned_add[OF _ is_aligned_shift])
  apply (erule is_aligned_weaken)
  apply simp
  done

lemma pt_offs_in_range:
  "Low_pd_ptr + (ucast (x :: pt_index) << 3) \<in> pt_offs_range Low_pd_ptr"
  "High_pd_ptr + (ucast (x :: pt_index) << 3) \<in> pt_offs_range High_pd_ptr"
  "Low_pt_ptr + (ucast (x :: pt_index) << 3) \<in> pt_offs_range Low_pt_ptr"
  "High_pt_ptr + (ucast (x :: pt_index) << 3) \<in> pt_offs_range High_pt_ptr"
  "riscv_global_pt_ptr + (ucast (x :: pt_index) << 3) \<in> pt_offs_range riscv_global_pt_ptr"
  by (simp_all add: pt_offs_in_range' s0_ptrs_aligned)

lemma pt_offs_range_correct':
  "\<lbrakk> x \<in> pt_offs_range ptr; is_aligned ptr 12 \<rbrakk>
     \<Longrightarrow> \<exists>y. x = ptr + (ucast (y :: pt_index) << 3)"
  apply (clarsimp simp: pt_offs_range_def s0_ptr_defs)
  apply (rule_tac x="ucast ((x - ptr) >> 3)" in exI)
  apply (clarsimp simp: ucast_ucast_mask)
  apply (subst aligned_shiftr_mask_shiftl)
   apply (rule aligned_sub_aligned)
     apply assumption
    apply (erule is_aligned_weaken)
    apply simp
   apply simp
  apply simp
  apply (rule_tac n=12 in mask_eqI)
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_def)
   apply (simp add: mask_twice)
   apply (subst diff_conv_add_uminus)
   apply (subst add.commute[symmetric])
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_minus)
   apply simp
  apply (subst diff_conv_add_uminus)
  apply (subst add_mask_lower_bits)
    apply (simp add: is_aligned_def)
   apply clarsimp
  apply (cut_tac x=x and y="ptr + 0xFFF" and n=12 in neg_mask_mono_le)
   apply (simp add: add.commute)
  apply (drule_tac n=12 in aligned_le_sharp)
   apply (simp add: is_aligned_def)
  apply (simp add: add.commute)
  apply (subst(asm) mask_out_add_aligned[symmetric])
   apply (erule is_aligned_weaken)
   apply simp
  apply (simp add: mask_def)
  done

lemma pt_offs_range_correct:
  "x \<in> pt_offs_range Low_pd_ptr  \<Longrightarrow> \<exists>y. x = Low_pd_ptr  + (ucast (y :: pt_index) << 3)"
  "x \<in> pt_offs_range High_pd_ptr \<Longrightarrow> \<exists>y. x = High_pd_ptr + (ucast (y :: pt_index) << 3)"
  "x \<in> pt_offs_range Low_pt_ptr  \<Longrightarrow> \<exists>y. x = Low_pt_ptr  + (ucast (y :: pt_index) << 3)"
  "x \<in> pt_offs_range High_pt_ptr \<Longrightarrow> \<exists>y. x = High_pt_ptr + (ucast (y :: pt_index) << 3)"
  "x \<in> pt_offs_range riscv_global_pt_ptr \<Longrightarrow> \<exists>y. x = riscv_global_pt_ptr + (ucast (y :: pt_index) << 3)"
  by (simp_all add: pt_offs_range_correct' s0_ptrs_aligned)


text \<open>CNode offset lemmas\<close>

lemma bl_to_bin_le2p_aux:
  "bl_to_bin_aux bs w \<le> (w + 1) * (2 ^ length bs) - 1"
  apply (induct bs arbitrary: w)
   apply clarsimp
  apply (clarsimp split del: split_of_bool)
  apply (drule meta_spec, erule xtr8 [rotated], simp)+
  done

lemma bl_to_bin_le2p:
  "bl_to_bin bs \<le> (2 ^ length bs) - 1"
  apply (unfold bl_to_bin_def)
  apply (rule xtr3)
   prefer 2
   apply (rule bl_to_bin_le2p_aux)
  apply simp
  done

lemma of_bl_length_le:
  "\<lbrakk> length x = k; k < len_of TYPE('a) \<rbrakk> \<Longrightarrow> (of_bl x :: 'a :: len word) \<le> 2 ^ k - 1"
  apply (unfold of_bl_def word_less_alt word_numeral_alt)
  apply safe
  apply (simp add: word_le_def take_bit_int_def uint_2p_alt uint_word_arith_bintrs(2))
  apply (subst mod_pos_pos_trivial)
    apply simp
   using not_le apply fastforce
  apply (subst uint_word_of_int)
  apply (subst mod_pos_pos_trivial)
    apply (rule bl_to_bin_ge0)
   apply (rule order_less_trans)
    apply (rule bl_to_bin_lt2p)
   apply simp
  apply (rule bl_to_bin_le2p)
  done

lemma cnode_offs_min':
  "\<lbrakk> is_aligned ptr 15; length x = 10 \<rbrakk> \<Longrightarrow> (ptr :: obj_ref) \<le> ptr + of_bl x * 0x20"
  apply (erule is_aligned_no_wrap')
  apply (rule div_lt_mult)
   apply (drule of_bl_length_less[where 'a=64])
    apply simp
   apply simp
  apply simp
  done

lemma cnode_offs_min:
  "length x = 10 \<Longrightarrow> Low_cnode_ptr  \<le> Low_cnode_ptr  + of_bl x * 0x20"
  "length x = 10 \<Longrightarrow> High_cnode_ptr \<le> High_cnode_ptr + of_bl x * 0x20"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr \<le> Silc_cnode_ptr + of_bl x * 0x20"
  by (simp_all add: cnode_offs_min' s0_ptrs_aligned)

lemma cnode_offs_max':
  "\<lbrakk> is_aligned ptr 15; length x = 10 \<rbrakk> \<Longrightarrow> (ptr :: obj_ref) + of_bl x * 0x20 \<le> ptr + 0x7fff"
  apply (rule word_plus_mono_right)
   apply (rule div_to_mult_word_lt)
   apply simp
   apply (rule plus_one_helper)
   apply simp
   apply (drule of_bl_length_less[where 'a=64])
    apply simp
   apply simp
  apply (drule is_aligned_no_overflow)
  apply (simp add: add.commute)
  done

lemma cnode_offs_max:
  "length x = 10 \<Longrightarrow> Low_cnode_ptr  + of_bl x * 0x20 \<le> Low_cnode_ptr  + 0x7fff"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<le> High_cnode_ptr + 0x7fff"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<le> Silc_cnode_ptr + 0x7fff"
  by (simp_all add: cnode_offs_max' s0_ptrs_aligned)

definition cnode_offs_range where
  "cnode_offs_range (ptr :: obj_ref) \<equiv> {x. ptr \<le> x \<and> x \<le> ptr + 2 ^ 15 - 1}
                                     \<inter> {x. is_aligned x 5}"

lemma cnode_offs_in_range':
  "\<lbrakk> is_aligned ptr 15; length x = 10 \<rbrakk> \<Longrightarrow> ptr + of_bl x * 0x20 \<in> cnode_offs_range ptr"
  apply (simp add: cnode_offs_min' cnode_offs_max' cnode_offs_range_def add.commute)
  apply (rule is_aligned_add)
   apply (erule is_aligned_weaken)
   apply simp
  apply (rule_tac is_aligned_mult_triv2[where x="of_bl x" and n=5, simplified])
  done

lemma cnode_offs_in_range:
  "length x = 10 \<Longrightarrow> Low_cnode_ptr  + of_bl x * 0x20 \<in> cnode_offs_range Low_cnode_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<in> cnode_offs_range High_cnode_ptr"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<in> cnode_offs_range Silc_cnode_ptr"
  by (simp_all add: cnode_offs_in_range' s0_ptrs_aligned)

lemma le_mask_eq:
  "x \<le> 2 ^ n - 1 \<Longrightarrow> x AND mask n = (x :: 'a :: len word)"
  apply (unfold word_less_alt word_numeral_alt)
  apply (simp add: word_of_int_power_hom mask_eq_exp_minus_1[symmetric])
  apply (erule word_le_mask_eq)
  done

lemma word_div_mult':
  fixes c :: obj_ref
  shows "\<lbrakk> 0 < c; a \<le> b * c \<rbrakk> \<Longrightarrow> a div c \<le> b"
  apply (simp add: word_le_nat_alt unat_div)
  apply (simp add: less_Suc_eq_le[symmetric])
  apply (subst td_gal_lt [symmetric])
   apply (simp add: word_less_nat_alt)
  apply (erule order_less_le_trans)
  apply (subst unat_word_ariths)
  apply (rule_tac y="Suc (unat b * unat c)" in order_trans)
   apply simp
  apply (simp add: word_less_nat_alt)
  done

lemma cnode_offs_range_correct':
  "\<lbrakk> x \<in> cnode_offs_range ptr; is_aligned ptr 15 \<rbrakk>
     \<Longrightarrow> \<exists>y. length y = 10 \<and> (x = ptr + of_bl y * 0x20)"
  apply (clarsimp simp: cnode_offs_range_def s0_ptr_defs)
  apply (rule_tac x="to_bl (ucast ((x - ptr) div 0x20) :: 10 word)" in exI)
  apply (clarsimp simp: to_bl_ucast of_bl_drop)
  apply (subst le_mask_eq)
   apply simp
   apply (rule word_div_mult')
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply (drule_tac a=x and n=5 in aligned_le_sharp)
     apply simp
    apply (simp add: add.commute)
    apply (subst(asm) mask_out_add_aligned[symmetric])
     apply (erule is_aligned_weaken)
     apply simp
    apply (simp add: mask_def)
   apply simp
  apply (clarsimp simp: neg_mask_is_div[where n=5, simplified, symmetric])
  apply (subst is_aligned_neg_mask_eq)
   apply (rule aligned_sub_aligned)
     apply assumption
    apply (erule is_aligned_weaken)
    apply simp
   apply simp
  apply simp
  done

lemma cnode_offs_range_correct:
  "x \<in> cnode_offs_range Low_cnode_ptr  \<Longrightarrow> \<exists>y. length y = 10 \<and> (x = Low_cnode_ptr  + of_bl y * 0x20)"
  "x \<in> cnode_offs_range High_cnode_ptr \<Longrightarrow> \<exists>y. length y = 10 \<and> (x = High_cnode_ptr + of_bl y * 0x20)"
  "x \<in> cnode_offs_range Silc_cnode_ptr \<Longrightarrow> \<exists>y. length y = 10 \<and> (x = Silc_cnode_ptr + of_bl y * 0x20)"
  by (simp_all add: cnode_offs_range_correct' s0_ptrs_aligned)


text \<open>TCB offset lemmas\<close>

lemma tcb_offs_min':
  "is_aligned ptr 10 \<Longrightarrow> (ptr :: obj_ref) \<le> ptr + ucast (x :: 10 word)"
  apply (erule is_aligned_no_wrap')
  apply (cut_tac x=x and 'a=64 in ucast_less)
   apply simp
  apply simp
  done

lemma tcb_offs_min:
  "Low_tcb_ptr  \<le> Low_tcb_ptr + ucast  (x :: 10 word)"
  "High_tcb_ptr \<le> High_tcb_ptr + ucast (x :: 10 word)"
  "idle_tcb_ptr \<le> idle_tcb_ptr + ucast (x :: 10 word)"
  by (simp_all add: tcb_offs_min' s0_ptrs_aligned)

lemma tcb_offs_max':
  "is_aligned ptr 10 \<Longrightarrow> (ptr :: obj_ref) + ucast (x :: 10 word) \<le> ptr + 0x3ff"
  apply (rule word_plus_mono_right)
   apply (rule plus_one_helper)
   apply (cut_tac ucast_less[where x=x and 'a=64])
    apply simp
   apply simp
  apply (drule is_aligned_no_overflow)
  apply (simp add: add.commute)
  done

lemma tcb_offs_max:
  "Low_tcb_ptr  + ucast (x :: 10 word) \<le> Low_tcb_ptr  + 0x3ff"
  "High_tcb_ptr + ucast (x :: 10 word) \<le> High_tcb_ptr + 0x3ff"
  "idle_tcb_ptr + ucast (x :: 10 word) \<le> idle_tcb_ptr + 0x3ff"
  by (simp_all add: tcb_offs_max' s0_ptrs_aligned)

definition tcb_offs_range where
  "tcb_offs_range (ptr :: obj_ref) \<equiv> {x. ptr \<le> x \<and> x \<le> ptr + 2 ^ 10 - 1}"

lemma tcb_offs_in_range':
  "is_aligned ptr 10 \<Longrightarrow> ptr + ucast (x :: 10 word) \<in> tcb_offs_range ptr"
  by (clarsimp simp: tcb_offs_min' tcb_offs_max' tcb_offs_range_def add.commute)

lemma tcb_offs_in_range:
  "Low_tcb_ptr  + ucast (x :: 10 word) \<in> tcb_offs_range Low_tcb_ptr"
  "High_tcb_ptr + ucast (x :: 10 word) \<in> tcb_offs_range High_tcb_ptr"
  "idle_tcb_ptr + ucast (x :: 10 word) \<in> tcb_offs_range idle_tcb_ptr"
  by (simp_all add: tcb_offs_in_range' s0_ptrs_aligned)

lemma tcb_offs_range_correct':
  "\<lbrakk> x \<in> tcb_offs_range ptr; is_aligned ptr 10 \<rbrakk>
     \<Longrightarrow> \<exists>y. x = ptr + ucast (y :: 10 word)"
  apply (clarsimp simp: tcb_offs_range_def s0_ptr_defs)
  apply (rule_tac x="ucast (x - ptr)" in exI)
  apply (clarsimp simp: ucast_ucast_mask)
  apply (rule_tac n=10 in mask_eqI)
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_def)
   apply (simp add: mask_twice)
   apply (subst diff_conv_add_uminus)
   apply (subst add.commute[symmetric])
   apply (subst mask_add_aligned)
    apply (simp add: is_aligned_minus)
   apply simp
  apply (subst diff_conv_add_uminus)
  apply (subst add_mask_lower_bits)
    apply (simp add: is_aligned_def)
   apply clarsimp
  apply (cut_tac x=x and y="ptr + 0x3FF" and n=10 in neg_mask_mono_le)
   apply (simp add: add.commute)
  apply (drule_tac n=10 in aligned_le_sharp)
   apply (simp add: is_aligned_def)
  apply (simp add: add.commute)
  apply (subst(asm) mask_out_add_aligned[symmetric])
   apply (erule is_aligned_weaken)
   apply simp
  apply (simp add: mask_def)
  done

lemma tcb_offs_range_correct:
  "x \<in> tcb_offs_range Low_tcb_ptr  \<Longrightarrow> \<exists>y. x = Low_tcb_ptr + ucast (y:: 10 word)"
  "x \<in> tcb_offs_range High_tcb_ptr \<Longrightarrow> \<exists>y. x = High_tcb_ptr + ucast (y:: 10 word)"
  "x \<in> tcb_offs_range idle_tcb_ptr \<Longrightarrow> \<exists>y. x = idle_tcb_ptr + ucast (y:: 10 word)"
  by (simp_all add: tcb_offs_range_correct' s0_ptrs_aligned)

lemma caps_dom_length_10:
  "Silc_caps x = Some y \<Longrightarrow> length x = 10"
  "High_caps x = Some y \<Longrightarrow> length x = 10"
  "Low_caps x  = Some y \<Longrightarrow> length x = 10"
  by (auto simp: Silc_caps_def High_caps_def Low_caps_def the_nat_to_bl_def nat_to_bl_def
          split: if_splits)

lemma dom_caps:
  "dom Silc_caps = {x. length x = 10}"
  "dom High_caps = {x. length x = 10}"
  "dom Low_caps = {x. length x = 10}"
  by (auto simp: Silc_caps_def High_caps_def Low_caps_def the_nat_to_bl_def nat_to_bl_def dom_def
          split: if_split_asm)

lemmas kh0H_obj_def =
  Low_cte_def High_cte_def Silc_cte_def ntfnH_def irq_cte_def Low_pdH_def
  High_pdH_def Low_ptH_def High_ptH_def Low_tcbH_def High_tcbH_def idle_tcbH_def
  global_ptH_def shared_pageH_def High_poolH_def Low_poolH_def

lemmas kh0H_all_obj_def =
  Low_pd'H_def High_pd'H_def Low_pt'H_def High_pt'H_def global_pteH_def global_pteH'_def
  Low_cte'_def Low_capsH_def High_cte'_def High_capsH_def
  Silc_cte'_def Silc_capsH_def empty_cte_def kh0H_obj_def

lemma not_in_range_None:
  "x \<notin> cnode_offs_range Low_cnode_ptr \<Longrightarrow> Low_cte Low_cnode_ptr x = None"
  "x \<notin> cnode_offs_range High_cnode_ptr \<Longrightarrow> High_cte High_cnode_ptr x = None"
  "x \<notin> cnode_offs_range Silc_cnode_ptr \<Longrightarrow> Silc_cte Silc_cnode_ptr x = None"
  "x \<notin> pt_offs_range Low_pd_ptr \<Longrightarrow> Low_pdH Low_pd_ptr x = None"
  "x \<notin> pt_offs_range High_pd_ptr \<Longrightarrow> High_pdH High_pd_ptr x = None"
  "x \<notin> pt_offs_range riscv_global_pt_ptr \<Longrightarrow> global_ptH riscv_global_pt_ptr x = None"
  "x \<notin> pt_offs_range Low_pt_ptr \<Longrightarrow> Low_ptH Low_pt_ptr x = None"
  "x \<notin> pt_offs_range High_pt_ptr \<Longrightarrow> High_ptH High_pt_ptr x = None"
  "x \<notin> page_offs_range shared_page_ptr_virt \<Longrightarrow> shared_pageH shared_page_ptr_virt x = None"
  by (auto simp: page_offs_range_def cnode_offs_range_def pt_offs_range_def s0_ptr_defs kh0H_obj_def)

lemma kh0H_dom_distinct:
  "idle_tcb_ptr \<notin> cnode_offs_range Silc_cnode_ptr"
  "High_tcb_ptr \<notin> cnode_offs_range Silc_cnode_ptr"
  "Low_tcb_ptr \<notin> cnode_offs_range Silc_cnode_ptr"
  "High_pool_ptr \<notin> cnode_offs_range Silc_cnode_ptr"
  "Low_pool_ptr \<notin> cnode_offs_range Silc_cnode_ptr"
  "irq_cnode_ptr \<notin> cnode_offs_range Silc_cnode_ptr"
  "ntfn_ptr \<notin> cnode_offs_range Silc_cnode_ptr"
  "idle_tcb_ptr \<notin> cnode_offs_range Low_cnode_ptr"
  "High_tcb_ptr \<notin> cnode_offs_range Low_cnode_ptr"
  "Low_tcb_ptr \<notin> cnode_offs_range Low_cnode_ptr"
  "High_pool_ptr \<notin> cnode_offs_range Low_cnode_ptr"
  "Low_pool_ptr \<notin> cnode_offs_range Low_cnode_ptr"
  "irq_cnode_ptr \<notin> cnode_offs_range Low_cnode_ptr"
  "ntfn_ptr \<notin> cnode_offs_range Low_cnode_ptr"
  "idle_tcb_ptr \<notin> cnode_offs_range High_cnode_ptr"
  "High_tcb_ptr \<notin> cnode_offs_range High_cnode_ptr"
  "Low_tcb_ptr \<notin> cnode_offs_range High_cnode_ptr"
  "High_pool_ptr \<notin> cnode_offs_range High_cnode_ptr"
  "Low_pool_ptr \<notin> cnode_offs_range High_cnode_ptr"
  "irq_cnode_ptr \<notin> cnode_offs_range High_cnode_ptr"
  "ntfn_ptr \<notin> cnode_offs_range High_cnode_ptr"
  "idle_tcb_ptr \<notin> pt_offs_range Low_pd_ptr"
  "High_tcb_ptr \<notin> pt_offs_range Low_pd_ptr"
  "Low_tcb_ptr \<notin> pt_offs_range Low_pd_ptr"
  "High_pool_ptr \<notin> pt_offs_range Low_pd_ptr"
  "Low_pool_ptr \<notin> pt_offs_range Low_pd_ptr"
  "irq_cnode_ptr \<notin> pt_offs_range Low_pd_ptr"
  "ntfn_ptr \<notin> pt_offs_range Low_pd_ptr"
  "idle_tcb_ptr \<notin> pt_offs_range High_pd_ptr"
  "High_tcb_ptr \<notin> pt_offs_range High_pd_ptr"
  "Low_tcb_ptr \<notin> pt_offs_range High_pd_ptr"
  "High_pool_ptr \<notin> pt_offs_range High_pd_ptr"
  "Low_pool_ptr \<notin> pt_offs_range High_pd_ptr"
  "irq_cnode_ptr \<notin> pt_offs_range High_pd_ptr"
  "ntfn_ptr \<notin> pt_offs_range High_pd_ptr"
  "idle_tcb_ptr \<notin> pt_offs_range riscv_global_pt_ptr"
  "High_tcb_ptr \<notin> pt_offs_range riscv_global_pt_ptr"
  "Low_tcb_ptr \<notin> pt_offs_range riscv_global_pt_ptr"
  "High_pool_ptr \<notin> pt_offs_range riscv_global_pt_ptr"
  "Low_pool_ptr \<notin> pt_offs_range riscv_global_pt_ptr"
  "irq_cnode_ptr \<notin> pt_offs_range riscv_global_pt_ptr"
  "ntfn_ptr \<notin> pt_offs_range riscv_global_pt_ptr"
  "idle_tcb_ptr \<notin> pt_offs_range Low_pt_ptr"
  "High_tcb_ptr \<notin> pt_offs_range Low_pt_ptr"
  "Low_tcb_ptr \<notin> pt_offs_range Low_pt_ptr"
  "High_pool_ptr \<notin> pt_offs_range Low_pt_ptr"
  "Low_pool_ptr \<notin> pt_offs_range Low_pt_ptr"
  "irq_cnode_ptr \<notin> pt_offs_range Low_pt_ptr"
  "ntfn_ptr \<notin> pt_offs_range Low_pt_ptr"
  "idle_tcb_ptr \<notin> pt_offs_range High_pt_ptr"
  "High_tcb_ptr \<notin> pt_offs_range High_pt_ptr"
  "Low_tcb_ptr \<notin> pt_offs_range High_pt_ptr"
  "High_pool_ptr \<notin> pt_offs_range High_pt_ptr"
  "Low_pool_ptr \<notin> pt_offs_range High_pt_ptr"
  "irq_cnode_ptr \<notin> pt_offs_range High_pt_ptr"
  "ntfn_ptr \<notin> pt_offs_range High_pt_ptr"
  "idle_tcb_ptr \<notin> tcb_offs_range Low_tcb_ptr"
  "High_tcb_ptr \<notin> tcb_offs_range Low_tcb_ptr"
  "High_pool_ptr \<notin> tcb_offs_range Low_tcb_ptr"
  "Low_pool_ptr \<notin> tcb_offs_range Low_tcb_ptr"
  "irq_cnode_ptr \<notin> tcb_offs_range Low_tcb_ptr"
  "ntfn_ptr \<notin> tcb_offs_range Low_tcb_ptr"
  "idle_tcb_ptr \<notin> tcb_offs_range High_tcb_ptr"
  "Low_tcb_ptr \<notin> tcb_offs_range High_tcb_ptr"
  "High_pool_ptr \<notin> tcb_offs_range High_tcb_ptr"
  "Low_pool_ptr \<notin> tcb_offs_range High_tcb_ptr"
  "irq_cnode_ptr \<notin> tcb_offs_range High_tcb_ptr"
  "ntfn_ptr \<notin> tcb_offs_range High_tcb_ptr"
  "High_tcb_ptr \<notin> tcb_offs_range idle_tcb_ptr"
  "Low_tcb_ptr \<notin> tcb_offs_range idle_tcb_ptr"
  "High_pool_ptr \<notin> tcb_offs_range idle_tcb_ptr"
  "Low_pool_ptr \<notin> tcb_offs_range idle_tcb_ptr"
  "irq_cnode_ptr \<notin> tcb_offs_range idle_tcb_ptr"
  "ntfn_ptr \<notin> tcb_offs_range idle_tcb_ptr"
  "idle_tcb_ptr \<notin> page_offs_range shared_page_ptr_virt"
  "High_tcb_ptr \<notin> page_offs_range shared_page_ptr_virt"
  "Low_tcb_ptr \<notin> page_offs_range shared_page_ptr_virt"
  "High_pool_ptr \<notin> page_offs_range shared_page_ptr_virt"
  "Low_pool_ptr \<notin> page_offs_range shared_page_ptr_virt"
  "irq_cnode_ptr \<notin> page_offs_range shared_page_ptr_virt"
  "ntfn_ptr \<notin> page_offs_range shared_page_ptr_virt"
  by (auto simp: tcb_offs_range_def pt_offs_range_def page_offs_range_def
                 cnode_offs_range_def kh0H_obj_def s0_ptr_defs)

lemma kh0H_dom_sets_distinct:
  "irq_node_offs_range \<inter> cnode_offs_range Silc_cnode_ptr = {}"
  "irq_node_offs_range \<inter> cnode_offs_range High_cnode_ptr = {}"
  "irq_node_offs_range \<inter> cnode_offs_range Low_cnode_ptr = {}"
  "irq_node_offs_range \<inter> pt_offs_range riscv_global_pt_ptr = {}"
  "irq_node_offs_range \<inter> pt_offs_range High_pd_ptr = {}"
  "irq_node_offs_range \<inter> pt_offs_range Low_pd_ptr = {}"
  "irq_node_offs_range \<inter> pt_offs_range High_pt_ptr = {}"
  "irq_node_offs_range \<inter> pt_offs_range Low_pt_ptr = {}"
  "irq_node_offs_range \<inter> tcb_offs_range High_tcb_ptr = {}"
  "irq_node_offs_range \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "irq_node_offs_range \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "irq_node_offs_range \<inter> page_offs_range shared_page_ptr_virt = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> cnode_offs_range High_cnode_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> cnode_offs_range Low_cnode_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> pt_offs_range riscv_global_pt_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> pt_offs_range High_pd_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> pt_offs_range Low_pd_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> pt_offs_range High_pt_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> pt_offs_range Low_pt_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "cnode_offs_range Silc_cnode_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "cnode_offs_range High_cnode_ptr \<inter> cnode_offs_range Low_cnode_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> pt_offs_range riscv_global_pt_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> pt_offs_range High_pd_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> pt_offs_range Low_pd_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> pt_offs_range High_pt_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> pt_offs_range Low_pt_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "cnode_offs_range High_cnode_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> pt_offs_range riscv_global_pt_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> pt_offs_range High_pd_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> pt_offs_range Low_pd_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> pt_offs_range High_pt_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> pt_offs_range Low_pt_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "cnode_offs_range Low_cnode_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> pt_offs_range High_pd_ptr = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> pt_offs_range Low_pd_ptr = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> pt_offs_range High_pt_ptr = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> pt_offs_range Low_pt_ptr = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "pt_offs_range riscv_global_pt_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "pt_offs_range High_pd_ptr \<inter> pt_offs_range Low_pd_ptr = {}"
  "pt_offs_range High_pd_ptr \<inter> pt_offs_range High_pt_ptr = {}"
  "pt_offs_range High_pd_ptr \<inter> pt_offs_range Low_pt_ptr = {}"
  "pt_offs_range High_pd_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "pt_offs_range High_pd_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "pt_offs_range High_pd_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "pt_offs_range High_pd_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "pt_offs_range Low_pd_ptr \<inter> pt_offs_range High_pt_ptr = {}"
  "pt_offs_range Low_pd_ptr \<inter> pt_offs_range Low_pt_ptr = {}"
  "pt_offs_range Low_pd_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "pt_offs_range Low_pd_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "pt_offs_range Low_pd_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "pt_offs_range Low_pd_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "pt_offs_range High_pt_ptr \<inter> pt_offs_range Low_pt_ptr = {}"
  "pt_offs_range High_pt_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "pt_offs_range High_pt_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "pt_offs_range High_pt_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "pt_offs_range High_pt_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "pt_offs_range Low_pt_ptr \<inter> tcb_offs_range High_tcb_ptr = {}"
  "pt_offs_range Low_pt_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "pt_offs_range Low_pt_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "pt_offs_range Low_pt_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "tcb_offs_range High_tcb_ptr \<inter> tcb_offs_range Low_tcb_ptr = {}"
  "tcb_offs_range High_tcb_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "tcb_offs_range High_tcb_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "tcb_offs_range Low_tcb_ptr \<inter> tcb_offs_range idle_tcb_ptr = {}"
  "tcb_offs_range Low_tcb_ptr \<inter> page_offs_range shared_page_ptr_virt = {}"
  "page_offs_range shared_page_ptr_virt \<inter> tcb_offs_range idle_tcb_ptr = {}"
  by (rule disjointI, clarsimp simp: tcb_offs_range_def pt_offs_range_def page_offs_range_def
                                     irq_node_offs_range_def cnode_offs_range_def s0_ptr_defs
                    , drule (1) order_trans le_less_trans, fastforce)+

lemmas offs_in_range =
  pt_offs_in_range page_offs_in_range tcb_offs_in_range cnode_offs_in_range irq_node_offs_in_range

lemmas offs_range_correct =
  pt_offs_range_correct page_offs_range_correct tcb_offs_range_correct
  cnode_offs_range_correct irq_node_offs_range_correct

lemma kh0H_dom_distinct':
  fixes y :: pt_index
  shows
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<noteq> idle_tcb_ptr"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<noteq> High_tcb_ptr"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<noteq> Low_tcb_ptr"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<noteq> High_pool_ptr"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<noteq> Low_pool_ptr"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<noteq> irq_cnode_ptr"
  "length x = 10 \<Longrightarrow> Silc_cnode_ptr + of_bl x * 0x20 \<noteq> ntfn_ptr"
  "length x = 10 \<Longrightarrow> Low_cnode_ptr + of_bl x * 0x20 \<noteq> idle_tcb_ptr"
  "length x = 10 \<Longrightarrow> Low_cnode_ptr + of_bl x * 0x20 \<noteq> High_tcb_ptr"
  "length x = 10 \<Longrightarrow> Low_cnode_ptr + of_bl x * 0x20 \<noteq> High_pool_ptr"
  "length x = 10 \<Longrightarrow> Low_cnode_ptr + of_bl x * 0x20 \<noteq> Low_pool_ptr"
  "length x = 10 \<Longrightarrow> Low_cnode_ptr + of_bl x * 0x20 \<noteq> Low_tcb_ptr"
  "length x = 10 \<Longrightarrow> Low_cnode_ptr + of_bl x * 0x20 \<noteq> irq_cnode_ptr"
  "length x = 10 \<Longrightarrow> Low_cnode_ptr + of_bl x * 0x20 \<noteq> ntfn_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<noteq> idle_tcb_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<noteq> High_tcb_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<noteq> Low_tcb_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<noteq> High_pool_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<noteq> Low_pool_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<noteq> irq_cnode_ptr"
  "length x = 10 \<Longrightarrow> High_cnode_ptr + of_bl x * 0x20 \<noteq> ntfn_ptr"
  "Low_pd_ptr + (ucast y << 3) \<noteq> idle_tcb_ptr"
  "Low_pd_ptr + (ucast y << 3) \<noteq> High_tcb_ptr"
  "Low_pd_ptr + (ucast y << 3) \<noteq> Low_tcb_ptr"
  "Low_pd_ptr + (ucast y << 3) \<noteq> High_pool_ptr"
  "Low_pd_ptr + (ucast y << 3) \<noteq> Low_pool_ptr"
  "Low_pd_ptr + (ucast y << 3) \<noteq> irq_cnode_ptr"
  "Low_pd_ptr + (ucast y << 3) \<noteq> ntfn_ptr"
  "High_pd_ptr + (ucast y << 3) \<noteq> idle_tcb_ptr"
  "High_pd_ptr + (ucast y << 3) \<noteq> High_tcb_ptr"
  "High_pd_ptr + (ucast y << 3) \<noteq> Low_tcb_ptr"
  "High_pd_ptr + (ucast y << 3) \<noteq> High_pool_ptr"
  "High_pd_ptr + (ucast y << 3) \<noteq> Low_pool_ptr"
  "High_pd_ptr + (ucast y << 3) \<noteq> irq_cnode_ptr"
  "High_pd_ptr + (ucast y << 3) \<noteq> ntfn_ptr"
  "Low_pt_ptr + (ucast y << 3) \<noteq> idle_tcb_ptr"
  "Low_pt_ptr + (ucast y << 3) \<noteq> High_tcb_ptr"
  "Low_pt_ptr + (ucast y << 3) \<noteq> Low_tcb_ptr"
  "Low_pt_ptr + (ucast y << 3) \<noteq> High_pool_ptr"
  "Low_pt_ptr + (ucast y << 3) \<noteq> Low_pool_ptr"
  "Low_pt_ptr + (ucast y << 3) \<noteq> irq_cnode_ptr"
  "Low_pt_ptr + (ucast y << 3) \<noteq> ntfn_ptr"
  "High_pt_ptr + (ucast y << 3) \<noteq> idle_tcb_ptr"
  "High_pt_ptr + (ucast y << 3) \<noteq> High_tcb_ptr"
  "High_pt_ptr + (ucast y << 3) \<noteq> Low_tcb_ptr"
  "High_pt_ptr + (ucast y << 3) \<noteq> High_pool_ptr"
  "High_pt_ptr + (ucast y << 3) \<noteq> Low_pool_ptr"
  "High_pt_ptr + (ucast y << 3) \<noteq> irq_cnode_ptr"
  "High_pt_ptr + (ucast y << 3) \<noteq> ntfn_ptr"
  "riscv_global_pt_ptr + (ucast y << 3) \<noteq> idle_tcb_ptr"
  "riscv_global_pt_ptr + (ucast y << 3) \<noteq> High_tcb_ptr"
  "riscv_global_pt_ptr + (ucast y << 3) \<noteq> Low_tcb_ptr"
  "riscv_global_pt_ptr + (ucast y << 3) \<noteq> High_pool_ptr"
  "riscv_global_pt_ptr + (ucast y << 3) \<noteq> Low_pool_ptr"
  "riscv_global_pt_ptr + (ucast y << 3) \<noteq> irq_cnode_ptr"
  "riscv_global_pt_ptr + (ucast y << 3) \<noteq> ntfn_ptr"
  "shared_page_ptr_virt + (ucast y << 12) \<noteq> idle_tcb_ptr"
  "shared_page_ptr_virt + (ucast y << 12) \<noteq> High_tcb_ptr"
  "shared_page_ptr_virt + (ucast y << 12) \<noteq> Low_tcb_ptr"
  "shared_page_ptr_virt + (ucast y << 12) \<noteq> High_pool_ptr"
  "shared_page_ptr_virt + (ucast y << 12) \<noteq> Low_pool_ptr"
  "shared_page_ptr_virt + (ucast y << 12) \<noteq> irq_cnode_ptr"
  "shared_page_ptr_virt + (ucast y << 12) \<noteq> ntfn_ptr"
  apply (drule offs_in_range, fastforce simp: kh0H_dom_distinct)+
  apply (cut_tac x=y in offs_in_range(1), fastforce simp: kh0H_dom_distinct)+
  apply (cut_tac x=y in offs_in_range(2), fastforce simp: kh0H_dom_distinct)+
  apply (cut_tac x=y in offs_in_range(3), fastforce simp: kh0H_dom_distinct)+
  apply (cut_tac x=y in offs_in_range(4), fastforce simp: kh0H_dom_distinct)+
  apply (cut_tac x=y in offs_in_range(5), fastforce simp: kh0H_dom_distinct)+
  apply (cut_tac x=y in offs_in_range(6), fastforce simp: kh0H_dom_distinct)+
  done

lemma not_disjointI:
  "\<lbrakk> x = y; x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> A \<inter> B \<noteq> {}"
  by fastforce

lemma shared_pageH_KOUserData[simp]:
  "shared_pageH shared_page_ptr_virt (shared_page_ptr_virt + (UCAST(9 \<rightarrow> 64) y << 12)) = Some KOUserData"
  apply (clarsimp simp: shared_pageH_def page_offs_min page_offs_max add.commute)
  apply (cut_tac shared_page_ptr_is_aligned)
  apply (clarsimp simp: is_aligned_mask mask_def s0_ptr_defs bit_simps)
  apply word_bitwise
  done

lemma kh0H_simps[simp]:
  fixes y :: pt_index
  shows
  "kh0H (init_irq_node_ptr + (ucast (irq :: irq) << 5)) = Some (KOCTE (CTE NullCap Null_mdb))"
  "kh0H ntfn_ptr      = Some (KONotification ntfnH)"
  "kh0H irq_cnode_ptr = Some (KOCTE irq_cte)"
  "kh0H Low_pool_ptr  = Some (KOArch Low_poolH)"
  "kh0H High_pool_ptr = Some (KOArch High_poolH)"
  "kh0H Low_tcb_ptr   = Some (KOTCB Low_tcbH)"
  "kh0H High_tcb_ptr  = Some (KOTCB High_tcbH)"
  "kh0H idle_tcb_ptr  = Some (KOTCB idle_tcbH)"
  "length x = 10 \<Longrightarrow> kh0H (Low_cnode_ptr  + of_bl x * 0x20) = Low_cte  Low_cnode_ptr  (Low_cnode_ptr  + of_bl x * 0x20)"
  "length x = 10 \<Longrightarrow> kh0H (High_cnode_ptr + of_bl x * 0x20) = High_cte High_cnode_ptr (High_cnode_ptr + of_bl x * 0x20)"
  "length x = 10 \<Longrightarrow> kh0H (Silc_cnode_ptr + of_bl x * 0x20) = Silc_cte Silc_cnode_ptr (Silc_cnode_ptr + of_bl x * 0x20)"
  "kh0H (Low_pd_ptr  + (ucast y << 3)) = Low_pdH  Low_pd_ptr  (Low_pd_ptr  + (ucast y << 3))"
  "kh0H (High_pd_ptr + (ucast y << 3)) = High_pdH High_pd_ptr (High_pd_ptr + (ucast y << 3))"
  "kh0H (Low_pt_ptr  + (ucast y << 3)) = Low_ptH  Low_pt_ptr  (Low_pt_ptr  + (ucast y << 3))"
  "kh0H (High_pt_ptr + (ucast y << 3)) = High_ptH High_pt_ptr (High_pt_ptr + (ucast y << 3))"
  "kh0H (riscv_global_pt_ptr + (ucast y << 3)) = global_ptH riscv_global_pt_ptr (riscv_global_pt_ptr + (ucast y << 3))"
  "kh0H (shared_page_ptr_virt + (ucast y << 12)) = Some KOUserData"
  supply option.case_cong[cong]
  apply (fastforce simp: kh0H_def option_update_range_def)
  by ((clarsimp simp: kh0H_def kh0H_dom_distinct kh0H_dom_distinct'
                       option_update_range_def not_in_range_None offs_in_range
       | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_None
       | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_None
       | rule conjI | clarsimp split: option.splits)+,
      drule not_disjointI,
      (erule offs_in_range | rule offs_in_range),
      (erule offs_in_range | rule offs_in_range),
      erule notE, rule kh0H_dom_sets_distinct)+

lemma kh0H_dom:
  "dom kh0H = {idle_tcb_ptr, High_tcb_ptr, Low_tcb_ptr,
               High_pool_ptr, Low_pool_ptr, irq_cnode_ptr, ntfn_ptr} \<union>
              irq_node_offs_range \<union>
              page_offs_range shared_page_ptr_virt \<union>
              cnode_offs_range Silc_cnode_ptr \<union>
              cnode_offs_range High_cnode_ptr \<union>
              cnode_offs_range Low_cnode_ptr \<union>
              pt_offs_range riscv_global_pt_ptr \<union>
              pt_offs_range High_pd_ptr \<union>
              pt_offs_range Low_pd_ptr \<union>
              pt_offs_range High_pt_ptr \<union>
              pt_offs_range Low_pt_ptr"
  apply (rule equalityI)
   apply (simp add: kh0H_def dom_def)
   apply (clarsimp simp: offs_in_range option_update_range_def not_in_range_None split: if_split_asm)
  apply (clarsimp simp: dom_def)
  apply (rule conjI)
   apply (force simp: kh0H_def kh0H_dom_distinct option_update_range_def not_in_range_None
                dest: irq_node_offs_range_correct split: option.splits)
  by (rule conjI
      | clarsimp simp: kh0H_def kh0H_dom_distinct option_update_range_def not_in_range_None
                split: option.splits
        , frule offs_range_correct
        , clarsimp simp: kh0H_all_obj_def cnode_offs_range_def page_offs_range_def pt_offs_range_def
                  split: if_split_asm)+

lemmas kh0H_SomeD' = set_mp[OF equalityD1[OF kh0H_dom[simplified dom_def]], OF CollectI, simplified, OF exI]

lemma kh0H_SomeD:
  "kh0H x = Some y
   \<Longrightarrow> x = ntfn_ptr \<and> y = KONotification ntfnH \<or>
       x = Low_tcb_ptr \<and> y = KOTCB Low_tcbH \<or>
       x = High_tcb_ptr \<and> y = KOTCB High_tcbH \<or>
       x = idle_tcb_ptr \<and> y = KOTCB idle_tcbH \<or>
       x \<in> pt_offs_range riscv_global_pt_ptr \<and> global_ptH riscv_global_pt_ptr x \<noteq> None
                                             \<and> y = the (global_ptH riscv_global_pt_ptr x) \<or>
       x \<in> irq_node_offs_range \<and> y = KOCTE (CTE NullCap Null_mdb) \<or>
       x \<in> pt_offs_range Low_pt_ptr \<and> Low_ptH Low_pt_ptr x \<noteq> None \<and> y = the (Low_ptH Low_pt_ptr x) \<or>
       x \<in> pt_offs_range High_pt_ptr \<and> High_ptH High_pt_ptr x \<noteq> None \<and> y = the (High_ptH High_pt_ptr x) \<or>
       x \<in> pt_offs_range Low_pd_ptr \<and> Low_pdH Low_pd_ptr x \<noteq> None \<and> y = the (Low_pdH Low_pd_ptr x) \<or>
       x \<in> pt_offs_range High_pd_ptr \<and> High_pdH High_pd_ptr x \<noteq> None \<and> y = the (High_pdH High_pd_ptr x) \<or>
       x = Low_pool_ptr \<and> y = KOArch Low_poolH \<or>
       x = High_pool_ptr \<and> y = KOArch High_poolH \<or>
       x \<in> cnode_offs_range Low_cnode_ptr \<and> Low_cte Low_cnode_ptr x \<noteq> None \<and> y = the (Low_cte Low_cnode_ptr x) \<or>
       x \<in> cnode_offs_range High_cnode_ptr \<and> High_cte High_cnode_ptr x \<noteq> None \<and> y = the (High_cte High_cnode_ptr x) \<or>
       x \<in> cnode_offs_range Silc_cnode_ptr \<and> Silc_cte Silc_cnode_ptr x \<noteq> None \<and> y = the (Silc_cte Silc_cnode_ptr x) \<or>
       x = irq_cnode_ptr \<and> y = KOCTE irq_cte \<or>
       x \<in> page_offs_range shared_page_ptr_virt \<and> y = KOUserData"
  apply (frule kh0H_SomeD')
  apply (elim disjE)
  by ((clarsimp | drule offs_range_correct)+)


definition arch_state0H :: Arch.kernel_state where
  "arch_state0H \<equiv>
     RISCVKernelState [ucast (asid_high_bits_of Low_asid) \<mapsto> Low_pool_ptr,
                       ucast (asid_high_bits_of High_asid) \<mapsto> High_pool_ptr]
                      (\<lambda>level. if level = maxPTLevel then [riscv_global_pt_ptr] else [])
                      init_vspace_uses"

definition s0H_internal :: "kernel_state" where
  "s0H_internal \<equiv> \<lparr>
     ksPSpace = kh0H,
     gsUserPages = [shared_page_ptr_virt \<mapsto> RISCVLargePage],
     gsCNodes = (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << 5) = x
                     then Some 0 else None)
                (Low_cnode_ptr  \<mapsto> 10,
                 High_cnode_ptr \<mapsto> 10,
                 Silc_cnode_ptr \<mapsto> 10,
                 irq_cnode_ptr  \<mapsto> 0),
     gsUntypedZeroRanges = ran (map_comp untypedZeroRange (option_map cteCap o map_to_ctes kh0H)),
     gsMaxObjectSize = card (UNIV :: obj_ref set),
     ksDomScheduleIdx = 0,
     ksDomSchedule = [(0, 10), (1, 10)],
     ksCurDomain = 0,
     ksDomainTime = 5,
     ksReadyQueues = const (TcbQueue None None),
     ksReadyQueuesL1Bitmap = const 0,
     ksReadyQueuesL2Bitmap = const 0,
     ksCurThread = Low_tcb_ptr,
     ksIdleThread = idle_tcb_ptr,
     ksSchedulerAction = ResumeCurrentThread,
     ksInterruptState = InterruptState init_irq_node_ptr ((\<lambda>_. IRQInactive) (timer_irq := IRQTimer)),
     ksWorkUnitsCompleted = undefined,
     ksArchState = arch_state0H,
     ksMachineState = machine_state0\<rparr>"


definition Low_cte_cte :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> cte option" where
  "Low_cte_cte \<equiv> \<lambda>base offs. if is_aligned offs 5 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 15 - 1
                              then Low_cte' (ucast (offs - base >> 5)) else None"

definition High_cte_cte :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> cte option" where
  "High_cte_cte \<equiv> \<lambda>base offs. if is_aligned offs 5 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 15 - 1
                               then High_cte' (ucast (offs - base >> 5)) else None"

definition Silc_cte_cte :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> cte option" where
  "Silc_cte_cte \<equiv> \<lambda>base offs. if is_aligned offs 5 \<and> base \<le> offs \<and> offs \<le> base + 2 ^ 15 - 1
                               then Silc_cte' (ucast (offs - base >> 5)) else None"

definition Low_tcb_cte :: "obj_ref \<Rightarrow> cte option" where
  "Low_tcb_cte \<equiv> [Low_tcb_ptr \<mapsto> tcbCTable Low_tcbH,
                  Low_tcb_ptr + 0x20 \<mapsto> tcbVTable Low_tcbH,
                  Low_tcb_ptr + 0x40 \<mapsto> tcbReply Low_tcbH,
                  Low_tcb_ptr + 0x60 \<mapsto> tcbCaller Low_tcbH,
                  Low_tcb_ptr + 0x80 \<mapsto> tcbIPCBufferFrame Low_tcbH]"

definition High_tcb_cte :: "obj_ref \<Rightarrow> cte option" where
  "High_tcb_cte \<equiv> [High_tcb_ptr \<mapsto> tcbCTable High_tcbH,
                   High_tcb_ptr + 0x20 \<mapsto> tcbVTable High_tcbH,
                   High_tcb_ptr + 0x40 \<mapsto> tcbReply High_tcbH,
                   High_tcb_ptr + 0x60 \<mapsto> tcbCaller High_tcbH,
                   High_tcb_ptr + 0x80 \<mapsto> tcbIPCBufferFrame High_tcbH]"

definition idle_tcb_cte :: "obj_ref \<Rightarrow> cte option" where
  "idle_tcb_cte \<equiv> [idle_tcb_ptr \<mapsto> tcbCTable idle_tcbH,
                   idle_tcb_ptr + 0x20 \<mapsto> tcbVTable idle_tcbH,
                   idle_tcb_ptr + 0x40 \<mapsto> tcbReply idle_tcbH,
                   idle_tcb_ptr + 0x60 \<mapsto> tcbCaller idle_tcbH,
                   idle_tcb_ptr + 0x80 \<mapsto> tcbIPCBufferFrame idle_tcbH]"


lemma not_in_range_cte_None:
  "x \<notin> cnode_offs_range Low_cnode_ptr \<Longrightarrow> Low_cte_cte Low_cnode_ptr x = None"
  "x \<notin> cnode_offs_range High_cnode_ptr \<Longrightarrow> High_cte_cte High_cnode_ptr x = None"
  "x \<notin> cnode_offs_range Silc_cnode_ptr \<Longrightarrow> Silc_cte_cte Silc_cnode_ptr x = None"
  "x \<notin> tcb_offs_range Low_tcb_ptr \<Longrightarrow> Low_tcb_cte x = None"
  "x \<notin> tcb_offs_range High_tcb_ptr \<Longrightarrow> High_tcb_cte x = None"
  "x \<notin> tcb_offs_range idle_tcb_ptr \<Longrightarrow> idle_tcb_cte x = None"
  by (fastforce simp: cnode_offs_range_def page_offs_range_def tcb_offs_range_def s0_ptr_defs Low_cte_cte_def
                      High_cte_cte_def Silc_cte_cte_def Low_tcb_cte_def High_tcb_cte_def idle_tcb_cte_def)+

lemma mask_neg_le:
  "x && ~~ mask n \<le> x"
  apply (clarsimp simp: neg_mask_is_div)
  apply (rule word_div_mult_le)
  done

lemma mask_in_tcb_offs_range:
  "x && ~~ mask 10 = ptr \<Longrightarrow> x \<in> tcb_offs_range ptr"
  apply (clarsimp simp: tcb_offs_range_def mask_neg_le objBitsKO_def)
  apply (cut_tac and_neg_mask_plus_mask_mono[where p=x and n=10])
  apply (simp add: add.commute mask_def)
  done

lemma set_mem_neq:
  "\<lbrakk> y \<notin> S; x \<in> S \<rbrakk> \<Longrightarrow> x \<noteq> y"
  by fastforce

lemma neg_mask_decompose:
  "x && ~~ mask n = ptr \<Longrightarrow> x = ptr + (x && mask n)"
  by (clarsimp simp: AND_NOT_mask_plus_AND_mask_eq)

lemma opt_None_not_dom:
  "m a = None \<Longrightarrow> a \<notin> dom m"
  by (simp add: dom_def)

lemma tcb_offs_range_mask_eq:
  "\<lbrakk> x \<in> tcb_offs_range ptr; is_aligned ptr 10 \<rbrakk> \<Longrightarrow> x && ~~ mask 10 = ptr"
  apply (drule(1) tcb_offs_range_correct')
  apply (clarsimp simp: objBitsKO_def)
  apply (drule_tac d="ucast y" in is_aligned_add_helper)
   apply (cut_tac x=y and 'a=64 in ucast_less)
    apply simp
   apply simp
  apply simp
  done

lemma not_in_tcb_offs:
  "\<forall>tcb. kh0H (x && ~~ mask 10) \<noteq> Some (KOTCB tcb)
   \<Longrightarrow> x \<notin> tcb_offs_range Low_tcb_ptr"
  "\<forall>tcb. kh0H (x && ~~ mask 10) \<noteq> Some (KOTCB tcb)
   \<Longrightarrow> x \<notin> tcb_offs_range High_tcb_ptr"
  "\<forall>tcb. kh0H (x && ~~ mask 10) \<noteq> Some (KOTCB tcb)
   \<Longrightarrow> x \<notin> tcb_offs_range idle_tcb_ptr"
  by (fastforce simp: s0_ptrs_aligned dest: tcb_offs_range_mask_eq)+

lemma range_tcb_not_kh0H_dom:
  "{(x && ~~ mask 10) + 1..(x && ~~ mask 10) + 2 ^ 10 - 1} \<inter> dom kh0H \<noteq> {} \<Longrightarrow> (x && ~~ mask 10) \<noteq> High_tcb_ptr"
  "{(x && ~~ mask 10) + 1..(x && ~~ mask 10) + 2 ^ 10 - 1} \<inter> dom kh0H \<noteq> {} \<Longrightarrow> (x && ~~ mask 10) \<noteq> Low_tcb_ptr"
  "{(x && ~~ mask 10) + 1..(x && ~~ mask 10) + 2 ^ 10 - 1} \<inter> dom kh0H \<noteq> {} \<Longrightarrow> (x && ~~ mask 10) \<noteq> idle_tcb_ptr"
    apply clarsimp
    apply (drule int_not_emptyD)
    apply (clarsimp simp: kh0H_dom)
    apply (subgoal_tac "xa \<in> tcb_offs_range High_tcb_ptr")
     prefer 2
     apply (clarsimp simp: tcb_offs_range_def objBitsKO_def)
     apply (rule_tac y="High_tcb_ptr + 1" in order_trans)
      apply (simp add: s0_ptr_defs)
     apply simp
    apply (clarsimp simp: kh0H_dom_distinct[THEN set_mem_neq])
    apply ((clarsimp simp: kh0H_dom_sets_distinct[THEN orthD2] |
            clarsimp simp: kh0H_dom_sets_distinct[THEN orthD1])+)[1]
    apply (clarsimp simp: s0_ptr_defs tcb_offs_range_def)
   apply clarsimp
   apply (drule int_not_emptyD)
   apply (clarsimp simp: kh0H_dom)
   apply (subgoal_tac "xa \<in> tcb_offs_range Low_tcb_ptr")
    prefer 2
    apply (clarsimp simp: tcb_offs_range_def objBitsKO_def)
    apply (rule_tac y="Low_tcb_ptr + 1" in order_trans)
     apply (simp add: s0_ptr_defs)
    apply simp
   apply (clarsimp simp: kh0H_dom_distinct[THEN set_mem_neq])
   apply ((clarsimp simp: kh0H_dom_sets_distinct[THEN orthD2] |
           clarsimp simp: kh0H_dom_sets_distinct[THEN orthD1])+)[1]
   apply (clarsimp simp: s0_ptr_defs tcb_offs_range_def)
  apply clarsimp
  apply (drule int_not_emptyD)
  apply (clarsimp simp: kh0H_dom)
  apply (subgoal_tac "xa \<in> tcb_offs_range idle_tcb_ptr")
   prefer 2
   apply (clarsimp simp: tcb_offs_range_def objBitsKO_def)
   apply (rule_tac y="idle_tcb_ptr + 1" in order_trans)
    apply (simp add: s0_ptr_defs)
   apply simp
  apply (clarsimp simp: kh0H_dom_distinct[THEN set_mem_neq])
  apply ((clarsimp simp: kh0H_dom_sets_distinct[THEN orthD2] |
          clarsimp simp: kh0H_dom_sets_distinct[THEN orthD1])+)[1]
  apply (clarsimp simp: s0_ptr_defs tcb_offs_range_def)
  done

lemma kh0H_dom_tcb:
  "kh0H x = Some (KOTCB tcb)
   \<Longrightarrow> x = Low_tcb_ptr \<or> x = High_tcb_ptr \<or> x = idle_tcb_ptr"
  apply (frule domI[where m="kh0H"])
  apply (simp add: kh0H_dom)
  apply (elim disjE)
  by (auto dest: offs_range_correct simp: kh0H_all_obj_def s0_ptrs_aligned split: if_split_asm)

lemma map_to_ctes_kh0H:
  "map_to_ctes kh0H =
     (option_update_range
        (\<lambda>x. if \<exists>irq :: irq. init_irq_node_ptr + (ucast irq << 5) = x
             then Some (CTE NullCap Null_mdb) else None) \<circ>
      option_update_range (Low_cte_cte Low_cnode_ptr) \<circ>
      option_update_range (High_cte_cte High_cnode_ptr) \<circ>
      option_update_range (Silc_cte_cte Silc_cnode_ptr) \<circ>
      option_update_range [irq_cnode_ptr \<mapsto> CTE NullCap Null_mdb] \<circ>
      option_update_range Low_tcb_cte \<circ>
      option_update_range High_tcb_cte \<circ>
      option_update_range idle_tcb_cte
      ) Map.empty"
  supply option.case_cong[cong] if_cong[cong]
  supply objBits_defs[simp]
  apply (rule ext)
  apply (case_tac "kh0H x")
   apply (clarsimp simp add: map_to_ctes_def Let_def objBitsKO_def)
   apply (rule conjI)
    apply clarsimp
    apply (thin_tac "x \<inter> y = {}" for x y)
    apply (frule kh0H_dom_tcb)
    apply (elim disjE)
      apply (clarsimp simp: option_update_range_def)
      apply (frule mask_in_tcb_offs_range)
      apply (clarsimp simp: kh0H_dom_distinct[THEN set_mem_neq])
      apply (simp add: kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None
             | simp add: kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None)+
      apply (rule conjI, clarsimp)
      apply (clarsimp split: option.splits)
      apply (rule conjI)
       apply (fastforce simp: tcb_cte_cases_def Low_tcb_cte_def dest: neg_mask_decompose)
      subgoal by (fastforce simp: Low_tcb_cte_def tcb_cte_cases_def
                           split: if_split_asm dest: neg_mask_decompose)
     apply (clarsimp simp: option_update_range_def)
     apply (frule mask_in_tcb_offs_range)
     apply (clarsimp simp: kh0H_dom_distinct[THEN set_mem_neq])
     apply (simp add: kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None
            | simp add: kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None)+
     apply (rule conjI, clarsimp)
     apply clarsimp
     apply (clarsimp split: option.splits)
     apply (rule conjI)
      apply (fastforce simp: tcb_cte_cases_def High_tcb_cte_def dest: neg_mask_decompose)
     subgoal by (fastforce simp: High_tcb_cte_def tcb_cte_cases_def
                          split: if_split_asm dest: neg_mask_decompose)
    apply (clarsimp simp: option_update_range_def)
    apply (frule mask_in_tcb_offs_range)
    apply (clarsimp simp: kh0H_dom_distinct[THEN set_mem_neq])
    apply (simp add: kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None
           | simp add: kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None)+
    apply (rule conjI, clarsimp)
    apply clarsimp
    apply (clarsimp split: option.splits)
    apply (rule conjI)
     apply (fastforce simp: tcb_cte_cases_def idle_tcb_cte_def dest: neg_mask_decompose)
    subgoal by (fastforce simp: idle_tcb_cte_def tcb_cte_cases_def
                         split: if_split_asm dest: neg_mask_decompose)
   apply (drule_tac m="kh0H" in opt_None_not_dom)
   apply (rule conjI)
    apply (clarsimp simp: kh0H_dom option_update_range_def)
    apply ((clarsimp simp: kh0H_dom_sets_distinct[THEN orthD2] not_in_tcb_offs not_in_range_cte_None offs_in_range
          | clarsimp simp: kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None)+)[1]
   apply (rule impI)
   apply (frule range_tcb_not_kh0H_dom(1)[simplified])
   apply (frule range_tcb_not_kh0H_dom(2)[simplified])
   apply (drule range_tcb_not_kh0H_dom(3)[simplified])
   apply (clarsimp simp: kh0H_dom split del: if_split)
   apply (clarsimp simp: option_update_range_def)
   apply ((clarsimp simp: kh0H_dom_sets_distinct[THEN orthD2] not_in_tcb_offs not_in_range_cte_None offs_in_range
         | clarsimp simp: kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None)+)[1]
   apply (subst not_in_range_cte_None,
          clarsimp simp: tcb_offs_range_mask_eq s0_ptrs_aligned)+
   apply (clarsimp simp: irq_node_offs_in_range)
  apply (frule kh0H_SomeD)
  apply (elim disjE)
                  defer
                  apply ((clarsimp simp: map_to_ctes_def Let_def split del: if_split,
                          subst if_split_eq1, rule conjI, rule impI,
                          (subst is_aligned_neg_mask_eq, simp add: is_aligned_def s0_ptr_defs objBitsKO_def)+,
                          ((clarsimp simp: option_update_range_def kh0H_dom_distinct not_in_range_cte_None |
                            clarsimp simp: idle_tcb_cte_def High_tcb_cte_def Low_tcb_cte_def)+)[1],
                         rule impI,
                         (subst (asm) is_aligned_neg_mask_eq, simp add: is_aligned_def s0_ptr_defs objBitsKO_def)+,
                         clarsimp,
                         clarsimp simp: kh0H_dom objBitsKO_def s0_ptr_defs irq_node_offs_range_def
                                        cnode_offs_range_def pt_offs_range_def page_offs_range_def,
                         rule FalseE, drule int_not_emptyD, clarsimp,
                         (elim disjE, (clarsimp | drule(1) order_trans le_less_trans, fastforce)+)[1])+)[3]
               defer 2
               apply ((clarsimp simp: map_to_ctes_def Let_def split del: if_split,
                       subst if_split_eq1, rule conjI, rule impI, drule pt_offs_range_correct,
                       clarsimp simp: kh0H_obj_def kh0H_dom_distinct option_update_range_def not_in_range_cte_None,
                       rule impI, subst if_split_eq1, rule conjI, rule impI, rule FalseE,
                       drule pt_offs_range_correct, clarsimp, cut_tac x=ya and 'a=64 in ucast_less,
                       simp, drule shiftl_less_t2n'[where n=3], simp, simp,
                       drule plus_one_helper[where n="0xFFF", simplified], drule kh0H_dom_tcb,
                       (elim disjE, (clarsimp simp: s0_ptr_defs objBitsKO_def,
                                     erule notE[rotated],
                                     rule_tac a="x::obj_ref" for x in dual_order.strict_implies_not_eq,
                                     rule less_le_trans[rotated, OF aligned_le_sharp],
                                     erule word_plus_mono_right2[rotated],
                                     simp, simp add: is_aligned_def, simp)+)[1],
                       rule impI,
                       clarsimp simp: option_update_range_def kh0H_dom_distinct[THEN set_mem_neq] not_in_range_cte_None,
                       ((clarsimp simp: kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None irq_node_offs_in_range |
                         clarsimp simp: kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1])+)[5]
          prefer 8
          apply ((clarsimp simp: map_to_ctes_def Let_def kh0H_obj_def split del: if_split,
                  subst if_split_eq1, rule conjI,
                  clarsimp, drule kh0H_dom_tcb, fastforce simp: s0_ptr_defs mask_def objBitsKO_def,
                  fastforce simp: option_update_range_def kh0H_dom_distinct not_in_range_cte_None)+)[3]
       apply ((clarsimp simp: map_to_ctes_def Let_def kh0H_obj_def objBitsKO_def
                       split: if_split_asm split del: if_split,
               subst if_split_eq1, rule conjI, rule impI,
               clarsimp simp: option_update_range_def kh0H_dom_distinct not_in_range_cte_None,
               (clarsimp simp: option_update_range_def kh0H_dom_distinct[THEN set_mem_neq]
                               kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
                | simp add: kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+,
               rule conjI, clarsimp, drule offs_range_correct,
               fastforce simp: Low_cte_cte_def High_cte_cte_def Silc_cte_cte_def,
               rule impI, rule FalseE, drule offs_range_correct,
               clarsimp simp: Low_cte_def High_cte_def Silc_cte_def cnode_offs_min cnode_offs_max,
               cut_tac x="of_bl y" and z="0x20::obj_ref" and y="2 ^ 15 - 1" in div_to_mult_word_lt,
               frule_tac 'a=64 in of_bl_length_le, simp, simp, drule int_not_emptyD,
               clarsimp simp: kh0H_dom s0_ptr_defs cnode_offs_range_def page_offs_range_def
                              pt_offs_range_def irq_node_offs_range_def,
               (elim disjE, (clarsimp simp: s0_ptr_defs,
                             drule_tac b="x + y * 0x20" and n=5 for x y in aligned_le_sharp,
                             fastforce simp: is_aligned_def, clarsimp simp: add.commute,
                             subst (asm) mask_out_add_aligned[symmetric],
                             simp add: is_aligned_mult_triv2[where n=5, simplified],
                             simp add: mask_def, drule word_leq_le_minus_one,
                             subst add.commute, rule neq_0_no_wrap,
                             erule word_plus_mono_right2[rotated],
                             fastforce, fastforce, fastforce simp: add.commute | unat_arith)+)[1])+)[3]
    apply (clarsimp simp: map_to_ctes_def Let_def kh0H_obj_def split del: if_split,
           subst if_split_eq1, rule conjI, rule impI,
           clarsimp simp: option_update_range_def kh0H_dom_distinct not_in_range_cte_None, rule impI,
           clarsimp simp: kh0H_dom objBitsKO_def s0_ptr_defs is_aligned_def page_offs_range_def
                          cnode_offs_range_def pt_offs_range_def irq_node_offs_range_def,
           rule FalseE, drule int_not_emptyD, clarsimp,
           (elim disjE, (clarsimp | drule(1) order_trans le_less_trans, fastforce)+)[1])
   apply (clarsimp simp: map_to_ctes_def Let_def kh0H_obj_def split del: if_split)
   apply (subst if_split_eq1)
   apply (rule conjI, clarsimp)
    apply (fastforce dest: kh0H_dom_tcb simp: page_offs_range_def objBitsKO_def)
   apply (clarsimp simp: option_update_range_def kh0H_dom_distinct not_in_range_cte_None)
   apply (rule conjI; clarsimp)
   apply (rule conjI; clarsimp)
   apply (subst is_aligned_neg_mask_eq, clarsimp simp: objBitsKO_def page_offs_range_def is_aligned_weaken)+
   apply (clarsimp split: option.splits)
   apply (intro conjI impI; drule kh0H_dom_sets_distinct[THEN orthD2]
                                  kh0H_dom_sets_distinct[THEN orthD1],
                            drule not_in_range_cte_None, solves clarsimp)
  apply (clarsimp simp: map_to_ctes_def Let_def kh0H_obj_def split del: if_split)
  apply (frule irq_node_offs_range_correct)
  apply (subst if_split_eq1)
  apply (rule conjI)
   apply (rule impI)
   apply (clarsimp simp: option_update_range_def kh0H_dom_distinct not_in_range_cte_None)
   apply fastforce
  apply (rule impI)
  apply clarsimp
  apply (erule impE)
   apply (rule is_aligned_add)
    apply (simp add: is_aligned_def s0_ptr_defs objBitsKO_def)
   apply (rule is_aligned_shiftl)
   apply (clarsimp simp: objBitsKO_def)
  apply (rule FalseE)
  apply (clarsimp simp: s0_ptr_defs cnode_offs_range_def page_offs_range_def pt_offs_range_def
                        irq_node_offs_range_def objBitsKO_def kh0H_dom)
  apply (cut_tac x=irq and 'a=64 in ucast_less)
   apply simp
  apply (drule shiftl_less_t2n'[where n=5])
   apply simp
  apply simp
  apply (drule plus_one_helper[where n="0x7FF", simplified])
  apply (elim disjE)
         apply (unat_arith+)[7]
  apply (drule int_not_emptyD)
  apply clarsimp
  apply (elim disjE,
         ((clarsimp,
          drule(1) aligned_le_sharp,
          clarsimp simp: add.commute,
          subst(asm) mask_out_add_aligned[symmetric],
           simp add: is_aligned_shiftl,
          simp add: mask_def,
          drule word_leq_le_minus_one,
           subst add.commute,
           rule neq_0_no_wrap,
            erule word_plus_mono_right2[rotated],
            fastforce,
           fastforce,
          fastforce simp: add.commute)
          | unat_arith)+)[1]
  done

lemma option_update_range_map_comp:
  "option_update_range m m' = map_add m' m"
  by (simp add: fun_eq_iff option_update_range_def map_comp_def map_add_def split: option.split)

lemma tcb_offs_in_rangeI:
  "\<lbrakk> ptr \<le> ptr + x; ptr + x \<le> ptr + 2 ^ 10 - 1 \<rbrakk> \<Longrightarrow> ptr + x \<in> tcb_offs_range ptr"
  by (simp add: tcb_offs_range_def)

lemma map_to_ctes_kh0H_simps[simp]:
  "map_to_ctes kh0H (init_irq_node_ptr + (ucast (irq :: irq) << 5)) = Some (CTE NullCap Null_mdb)"
  "map_to_ctes kh0H irq_cnode_ptr = Some (CTE NullCap Null_mdb)"
  "length x = 10 \<Longrightarrow> map_to_ctes kh0H (Low_cnode_ptr + of_bl x * 0x20) =
                     Low_cte_cte Low_cnode_ptr (Low_cnode_ptr + of_bl x * 0x20)"
  "length x = 10 \<Longrightarrow> map_to_ctes kh0H (High_cnode_ptr + of_bl x * 0x20) =
                     High_cte_cte High_cnode_ptr (High_cnode_ptr + of_bl x * 0x20)"
  "length x = 10 \<Longrightarrow> map_to_ctes kh0H (Silc_cnode_ptr + of_bl x * 0x20) =
                     Silc_cte_cte Silc_cnode_ptr (Silc_cnode_ptr + of_bl x * 0x20)"
  "map_to_ctes kh0H Low_tcb_ptr = Low_tcb_cte Low_tcb_ptr"
  "map_to_ctes kh0H (Low_tcb_ptr + 0x20) = Low_tcb_cte (Low_tcb_ptr + 0x20)"
  "map_to_ctes kh0H (Low_tcb_ptr + 0x40) = Low_tcb_cte (Low_tcb_ptr + 0x40)"
  "map_to_ctes kh0H (Low_tcb_ptr + 0x60) = Low_tcb_cte (Low_tcb_ptr + 0x60)"
  "map_to_ctes kh0H (Low_tcb_ptr + 0x80) = Low_tcb_cte (Low_tcb_ptr + 0x80)"
  "map_to_ctes kh0H High_tcb_ptr = High_tcb_cte High_tcb_ptr"
  "map_to_ctes kh0H (High_tcb_ptr + 0x20) = High_tcb_cte (High_tcb_ptr + 0x20)"
  "map_to_ctes kh0H (High_tcb_ptr + 0x40) = High_tcb_cte (High_tcb_ptr + 0x40)"
  "map_to_ctes kh0H (High_tcb_ptr + 0x60) = High_tcb_cte (High_tcb_ptr + 0x60)"
  "map_to_ctes kh0H (High_tcb_ptr + 0x80) = High_tcb_cte (High_tcb_ptr + 0x80)"
  "map_to_ctes kh0H idle_tcb_ptr = idle_tcb_cte idle_tcb_ptr"
  "map_to_ctes kh0H (idle_tcb_ptr + 0x20) = idle_tcb_cte (idle_tcb_ptr + 0x20)"
  "map_to_ctes kh0H (idle_tcb_ptr + 0x40) = idle_tcb_cte (idle_tcb_ptr + 0x40)"
  "map_to_ctes kh0H (idle_tcb_ptr + 0x60) = idle_tcb_cte (idle_tcb_ptr + 0x60)"
  "map_to_ctes kh0H (idle_tcb_ptr + 0x80) = idle_tcb_cte (idle_tcb_ptr + 0x80)"
  supply option.case_cong[cong] if_cong[cong]
     apply (clarsimp simp: map_to_ctes_kh0H option_update_range_def)
     apply fastforce
    apply (clarsimp simp: map_to_ctes_kh0H option_update_range_def kh0H_dom_distinct not_in_range_cte_None)
   apply ((clarsimp simp: option_update_range_def not_in_range_cte_None cnode_offs_in_range
                          kh0H_dom_distinct kh0H_dom_distinct' map_to_ctes_kh0H s0_ptrs_aligned,
           ((clarsimp simp: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None |
             clarsimp simp: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1],
           intro conjI,
           (clarsimp, drule not_disjointI,
            (erule offs_in_range | rule offs_in_range),
            (erule offs_in_range | rule offs_in_range),
            erule notE, rule kh0H_dom_sets_distinct)+,
           clarsimp split: option.splits)+)[3]
  apply (clarsimp simp: option_update_range_def not_in_range_cte_None
                        map_to_ctes_kh0H kh0H_dom_distinct split: option.splits)
  apply (cut_tac ptr="Low_tcb_ptr" and x="0x20" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: not_in_range_cte_None option_update_range_def
                        map_to_ctes_kh0H  kh0H_dom_distinct kh0H_dom_distinct'
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="Low_tcb_ptr" and x="0x40" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="Low_tcb_ptr" and x="0x60" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="Low_tcb_ptr" and x="0x80" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (clarsimp simp: map_to_ctes_kh0H option_update_range_def kh0H_dom_distinct not_in_range_cte_None split: option.splits)
  apply (cut_tac ptr="High_tcb_ptr" and x="0x20" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="High_tcb_ptr" and x="0x40" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="High_tcb_ptr" and x="0x60" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="High_tcb_ptr" and x="0x80" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (clarsimp simp: map_to_ctes_kh0H option_update_range_def kh0H_dom_distinct not_in_range_cte_None split: option.splits)
  apply (cut_tac ptr="idle_tcb_ptr" and x="0x20" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="idle_tcb_ptr" and x="0x40" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="idle_tcb_ptr" and x="0x60" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  apply (drule not_disjointI,
           rule irq_node_offs_in_range,
          assumption,
         erule notE,
         rule kh0H_dom_sets_distinct)
  apply (cut_tac ptr="idle_tcb_ptr" and x="0x80" in tcb_offs_in_rangeI, simp add: s0_ptr_defs, simp add: s0_ptr_defs)
  apply (clarsimp simp: map_to_ctes_kh0H kh0H_dom_distinct kh0H_dom_distinct'
                        option_update_range_def not_in_range_cte_None
                 split: option.splits)
  apply ((simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD1] not_in_range_cte_None
        | simp add: offs_in_range kh0H_dom_sets_distinct[THEN orthD2] not_in_range_cte_None)+)[1]
  apply (intro conjI impI allI)
     apply (simp add: s0_ptr_defs)
    apply clarsimp
    apply (drule not_disjointI,
             rule irq_node_offs_in_range,
            assumption,
           erule notE,
           rule kh0H_dom_sets_distinct)
   apply (clarsimp simp: kh0H_dom_distinct)
  apply clarsimp
  by (drule not_disjointI,
        rule irq_node_offs_in_range,
       assumption,
      erule notE,
      rule kh0H_dom_sets_distinct)

lemma map_to_ctes_kh0H_dom:
  "dom (map_to_ctes kh0H) = {idle_tcb_ptr, idle_tcb_ptr + 0x20, idle_tcb_ptr + 0x40,
                             idle_tcb_ptr + 0x60, idle_tcb_ptr + 0x80,
                             Low_tcb_ptr, Low_tcb_ptr + 0x20, Low_tcb_ptr + 0x40,
                             Low_tcb_ptr + 0x60, Low_tcb_ptr + 0x80,
                             High_tcb_ptr, High_tcb_ptr + 0x20, High_tcb_ptr + 0x40,
                             High_tcb_ptr + 0x60, High_tcb_ptr + 0x80,
                             irq_cnode_ptr}
                           \<union> irq_node_offs_range
                           \<union> cnode_offs_range Silc_cnode_ptr
                           \<union> cnode_offs_range High_cnode_ptr
                           \<union> cnode_offs_range Low_cnode_ptr"
  supply option.case_cong[cong] if_cong[cong]
  apply (rule equalityI)
   apply (simp add: map_to_ctes_kh0H dom_def)
   apply clarsimp
   apply (clarsimp simp: offs_in_range option_update_range_def split: option.splits if_split_asm)
        apply (clarsimp simp: idle_tcb_cte_def)
       apply (clarsimp simp: High_tcb_cte_def)
      apply (clarsimp simp: Low_tcb_cte_def)
     apply (clarsimp simp: Silc_cte_cte_def cnode_offs_range_def split: if_split_asm)
    apply (clarsimp simp: High_cte_cte_def cnode_offs_range_def split: if_split_asm)
   apply (clarsimp simp: Low_cte_cte_def cnode_offs_range_def split: if_split_asm)
  apply (clarsimp simp: dom_def)
  apply (clarsimp simp: idle_tcb_cte_def Low_tcb_cte_def High_tcb_cte_def)
  apply (rule conjI)
   apply (fastforce dest: irq_node_offs_range_correct)
  apply (rule conjI)
   apply clarsimp
   apply (frule cnode_offs_range_correct)
   apply (clarsimp simp: Silc_cte_cte_def Silc_cte'_def Silc_capsH_def empty_cte_def cnode_offs_range_def)
  apply (rule conjI)
   apply clarsimp
   apply (frule cnode_offs_range_correct)
   apply (clarsimp simp: High_cte_cte_def High_cte'_def High_capsH_def empty_cte_def cnode_offs_range_def)
  apply clarsimp
  apply (frule cnode_offs_range_correct)
  apply (clarsimp simp: Low_cte_cte_def Low_cte'_def Low_capsH_def empty_cte_def cnode_offs_range_def)
  done

lemmas map_to_ctes_kh0H_SomeD' =
  set_mp[OF equalityD1[OF map_to_ctes_kh0H_dom[simplified dom_def]], OF CollectI, simplified, OF exI]

lemma map_to_ctes_kh0H_SomeD:
  "map_to_ctes kh0H x = Some y
   \<Longrightarrow> x = idle_tcb_ptr \<and> y = (CTE NullCap Null_mdb) \<or>
       x = idle_tcb_ptr + 0x20 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = idle_tcb_ptr + 0x40 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = idle_tcb_ptr + 0x60 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = idle_tcb_ptr + 0x80 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = Low_tcb_ptr \<and> y = (CTE (CNodeCap Low_cnode_ptr 10 2 10) (MDB (Low_cnode_ptr + 0x40) 0 False False)) \<or>
       x = Low_tcb_ptr + 0x20 \<and> y = (CTE (ArchObjectCap (PageTableCap Low_pd_ptr (Some (ucast Low_asid,0))))
                                         (MDB (Low_cnode_ptr + 0x60) 0 False False)) \<or>
       x = Low_tcb_ptr + 0x40 \<and> y = (CTE (ReplyCap Low_tcb_ptr True True) (MDB 0 0 True True)) \<or>
       x = Low_tcb_ptr + 0x60 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = Low_tcb_ptr + 0x80 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = High_tcb_ptr \<and> y = (CTE (CNodeCap High_cnode_ptr 10 2 10) (MDB (High_cnode_ptr + 0x40) 0 False False)) \<or>
       x = High_tcb_ptr + 0x20 \<and> y = (CTE (ArchObjectCap (PageTableCap High_pd_ptr (Some (ucast High_asid, 0))))
                                          (MDB (High_cnode_ptr + 0x60) 0 False False)) \<or>
       x = High_tcb_ptr + 0x40 \<and> y = (CTE (ReplyCap High_tcb_ptr True True) (MDB 0 0 True True)) \<or>
       x = High_tcb_ptr + 0x60 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = High_tcb_ptr + 0x80 \<and> y = (CTE NullCap Null_mdb) \<or>
       x = irq_cnode_ptr \<and> y = (CTE NullCap Null_mdb) \<or>
       x \<in> irq_node_offs_range \<and> y = (CTE NullCap Null_mdb) \<or>
       x \<in> cnode_offs_range Silc_cnode_ptr \<and> Silc_cte_cte Silc_cnode_ptr x \<noteq> None
                                           \<and> y = the (Silc_cte_cte Silc_cnode_ptr x) \<or>
       x \<in> cnode_offs_range High_cnode_ptr \<and> High_cte_cte High_cnode_ptr x \<noteq> None \<and> y = the (High_cte_cte High_cnode_ptr x) \<or>
       x \<in> cnode_offs_range Low_cnode_ptr \<and> Low_cte_cte Low_cnode_ptr x \<noteq> None \<and> y = the (Low_cte_cte Low_cnode_ptr x)"
  apply (frule map_to_ctes_kh0H_SomeD')
  apply (erule disjE, rule disjI1, clarsimp simp: idle_tcb_cte_def idle_tcbH_def
                                                  Low_tcb_cte_def Low_tcbH_def Low_capsH_def
                                                  High_tcb_cte_def High_tcbH_def High_capsH_def
                                                  the_nat_to_bl_def nat_to_bl_def, rule disjI2)+
  apply ((erule disjE)?, drule offs_range_correct, clarsimp simp: offs_in_range)+
  done

lemma mask_neg_add_aligned:
  "is_aligned q n \<Longrightarrow> p + q && ~~ mask n = (p && ~~ mask n) + q"
  apply (subst add.commute)
  apply (simp add: mask_out_add_aligned[symmetric])
  done

lemma mask_neg_add_aligned':
  "is_aligned q n \<Longrightarrow> q + p && ~~ mask n = (p && ~~ mask n) + q"
  by (simp add: mask_out_add_aligned[symmetric])

lemma kh_s0H[simp]:
  "ksPSpace s0H_internal = kh0H"
  by (simp add: s0H_internal_def)

lemma pspace_distinct'_split:
  notes less_1_simp[simp del] shows
  "(\<forall>(y, ko) \<in> graph_of (ksPSpace ks). (x \<le> y \<or> y + (1 << objBitsKO ko) - 1 < x)
                                     \<and> y \<le> y + (1 << objBitsKO ko) - 1)
   \<Longrightarrow> pspace_distinct' (ks \<lparr>ksPSpace := restrict_map (ksPSpace ks) {..< x}\<rparr>)
   \<Longrightarrow> pspace_distinct' (ks \<lparr>ksPSpace := restrict_map (ksPSpace ks) {x ..}\<rparr>)
   \<Longrightarrow> pspace_distinct' ks"
  apply (clarsimp simp: pspace_distinct'_def)
  apply (drule bspec, erule graph_ofI, clarsimp)
  apply (simp add: Ball_def)
  apply (drule_tac x=xa in spec)+
  apply (erule disjE)
   apply (simp add: domI)
   apply (thin_tac "P \<longrightarrow> Q" for P Q)
   apply (simp add: ps_clear_def)
   apply (erule trans[rotated])
   apply auto[1]
  apply (clarsimp simp add: domI)
  apply (drule mp, erule(1) order_le_less_trans)
  apply (thin_tac "P \<longrightarrow> Q" for P Q)
  apply (simp add: ps_clear_def)
  apply (erule trans[rotated])
  apply (fastforce simp: mask_eq_exp_minus_1 add_diff_eq)
  done

lemma irq_node_offs_range_def2:
  "irq_node_offs_range = {x. init_irq_node_ptr \<le> x \<and> x \<le> init_irq_node_ptr + 0x7E0} \<inter>
                         {x. is_aligned x 5}"
  apply (safe, simp_all add: irq_node_offs_range_def add.commute)
  by (auto dest: word_less_sub_1 simp: s0_ptr_defs elim: dual_order.strict_trans2[rotated])

(* FIXME IF: fix repetitiveness *)
lemma s0H_pspace_distinct':
  notes pteBits_def[simp] objBits_defs[simp]
  shows "pspace_distinct' s0H_internal"
  supply option.case_cong[cong] if_cong[cong]
  apply (clarsimp simp: pspace_distinct'_def ps_clear_def mask_eq_exp_minus_1)
  apply (rule disjointI)
  apply clarsimp
  apply (drule kh0H_SomeD)+
  \<comment> \<open>ntfn_ptr\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
  subgoal by ((elim disjE; clarsimp),
              (thin_tac "_ \<le> _", clarsimp simp: pt_offs_range_def page_offs_range_def
                                                 cnode_offs_range_def irq_node_offs_range_def2
                               , drule dual_order.trans, assumption
                               , clarsimp simp: s0_ptr_defs objBitsKO_def
               | solves \<open>clarsimp simp: s0_ptr_defs objBitsKO_def\<close>)+)
  \<comment> \<open>Low_tcb_ptr\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
  subgoal by ((elim disjE; clarsimp),
              (thin_tac "_ \<le> _", clarsimp simp: pt_offs_range_def page_offs_range_def
                                                 cnode_offs_range_def irq_node_offs_range_def2
                               , drule dual_order.trans, assumption
                               , clarsimp simp: s0_ptr_defs objBitsKO_def
               | solves \<open>clarsimp simp: s0_ptr_defs objBitsKO_def\<close>)+)
  \<comment> \<open>High_tcb_ptr\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
  subgoal by ((elim disjE; clarsimp),
              (thin_tac "_ \<le> _", clarsimp simp: pt_offs_range_def page_offs_range_def
                                                 cnode_offs_range_def irq_node_offs_range_def2
                               , drule dual_order.trans, assumption
                               , clarsimp simp: s0_ptr_defs objBitsKO_def
               | solves \<open>clarsimp simp: s0_ptr_defs objBitsKO_def\<close>)+)
  \<comment> \<open>Idle_tcb_ptr\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
  subgoal by ((elim disjE; clarsimp),
              (thin_tac "_ \<le> _", clarsimp simp: pt_offs_range_def page_offs_range_def
                                                 cnode_offs_range_def irq_node_offs_range_def2
                               , drule dual_order.trans, assumption
                               , clarsimp simp: s0_ptr_defs objBitsKO_def
               | solves \<open>clarsimp simp: s0_ptr_defs objBitsKO_def\<close>)+)
  \<comment> \<open>riscv_global_pt_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
   apply (elim disjE; clarsimp)
                   apply ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def objBitsKO_def,
                           drule dual_order.trans, assumption,
                           (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                            drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                           simp add: s0_ptr_defs)+)[4]
             apply (clarsimp simp: pt_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def bit_simps
                            split: if_split_asm;
                    (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def2 cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>irq_node_offs_range\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
   apply (elim disjE; clarsimp)
                   apply ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def objBitsKO_def,
                           drule dual_order.trans, assumption,
                           (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                            drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                           simp add: s0_ptr_defs)+)[5]
              apply (clarsimp simp: irq_node_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def
                             split: if_split_asm;
                     (drule(1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def2 cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>Low_pt_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
   apply (elim disjE; clarsimp)
                   apply ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def objBitsKO_def,
                           drule dual_order.trans, assumption,
                           (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                            drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                           simp add: s0_ptr_defs)+)[6]
             apply (clarsimp simp: pt_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def bit_simps
                            split: if_split_asm;
                    (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def2 cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>High_pt_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
   apply (elim disjE; clarsimp)
                   apply ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def objBitsKO_def,
                           drule dual_order.trans, assumption,
                           (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                            drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                           simp add: s0_ptr_defs)+)[7]
             apply (clarsimp simp: pt_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def bit_simps
                            split: if_split_asm;
                    (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def2 cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>Low_pd_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
   apply (elim disjE; clarsimp)
                   apply ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def objBitsKO_def,
                           drule dual_order.trans, assumption,
                           (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                            drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                           simp add: s0_ptr_defs)+)[8]
             apply (clarsimp simp: pt_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def bit_simps
                            split: if_split_asm;
                    (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def2 cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>High_pd_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
   apply (elim disjE; clarsimp)
                   apply ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def objBitsKO_def,
                           drule dual_order.trans, assumption,
                           (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                            drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                           simp add: s0_ptr_defs)+)[9]
             apply (clarsimp simp: pt_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def bit_simps
                            split: if_split_asm;
                    (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>Low_pool_ptr\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
   subgoal for x y ya yb
   by ((elim disjE; clarsimp),
       ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def cnode_offs_range_def
                        page_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def,
         (thin_tac "ya \<le> _", drule dual_order.trans, assumption |
          thin_tac "_ \<le> ya", drule dual_order.trans, assumption)?,
         solves \<open>clarsimp simp: s0_ptr_defs bit_simps\<close>)+))
  \<comment> \<open>High_pool_ptr\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
   subgoal for x y ya yb
   by ((elim disjE; clarsimp),
       ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def cnode_offs_range_def
                        page_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def,
         (thin_tac "ya \<le> _", drule dual_order.trans, assumption |
          thin_tac "_ \<le> ya", drule dual_order.trans, assumption)?,
         solves \<open>clarsimp simp: s0_ptr_defs bit_simps\<close>)+))
  \<comment> \<open>Low_cnode_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
  apply (elim disjE; clarsimp)
                  apply ((clarsimp simp: cnode_offs_range_def irq_node_offs_range_def2
                                         pt_offs_range_def objBitsKO_def,
                          drule dual_order.trans, assumption,
                          (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                           drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                          simp add: s0_ptr_defs)+)[12]
      apply (clarsimp simp: objBitsKO_def kh0H_obj_def Low_cte'_def Low_capsH_def cnode_offs_range_def
                     split: if_split_asm;
             (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>High_cnode_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
  apply (elim disjE; clarsimp)
                  apply ((clarsimp simp: cnode_offs_range_def irq_node_offs_range_def2
                                         pt_offs_range_def objBitsKO_def,
                          drule dual_order.trans, assumption,
                          (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                           drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                          simp add: s0_ptr_defs)+)[13]
      apply (clarsimp simp: objBitsKO_def kh0H_obj_def High_cte'_def High_capsH_def cnode_offs_range_def
                     split: if_split_asm;
             (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>Silc_cnode_ptr\<close>
  apply (erule_tac P="_ \<and> _ \<and> y = _" in disjE)
  apply (elim disjE; clarsimp)
                  apply ((clarsimp simp: cnode_offs_range_def irq_node_offs_range_def2
                                         pt_offs_range_def objBitsKO_def,
                          drule dual_order.trans, assumption,
                          (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                           drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                          simp add: s0_ptr_defs)+)[14]
      apply (clarsimp simp: objBitsKO_def kh0H_obj_def Silc_cte'_def Silc_capsH_def cnode_offs_range_def
                     split: if_split_asm;
             (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def))
             apply (thin_tac "_ \<le> _",
                    clarsimp simp: kh0H_obj_def objBitsKO_def archObjSize_def bit_simps pt_offs_range_def
                                   irq_node_offs_range_def cnode_offs_range_def page_offs_range_def,
                    drule_tac a=x and b="_ + _" in aligned_le_sharp, assumption,
                    drule dual_order.trans[rotated],
                    erule word_plus_mono_left, simp add: s0_ptr_defs mask_def,
                    (drule_tac b=ya and a="(_ && ~~ mask _) + _" in dual_order.trans, assumption)?,
                    simp add: s0_ptr_defs mask_def)+
  \<comment> \<open>irq_cnode_ptr\<close>
  apply (erule_tac P="_ \<and> y = _" in disjE)
   subgoal for x y ya yb
   by ((elim disjE; clarsimp),
       ((clarsimp simp: irq_node_offs_range_def2 pt_offs_range_def cnode_offs_range_def
                        page_offs_range_def objBitsKO_def archObjSize_def kh0H_obj_def,
         (thin_tac "ya \<le> _", drule dual_order.trans, assumption |
          thin_tac "_ \<le> ya", drule dual_order.trans, assumption)?,
         solves \<open>clarsimp simp: s0_ptr_defs bit_simps\<close>)+))
  \<comment> \<open>shared_page_ptr\<close>
  apply (elim disjE; clarsimp)
                 apply ((clarsimp simp: cnode_offs_range_def irq_node_offs_range_def2
                                        page_offs_range_def pt_offs_range_def objBitsKO_def,
                         drule dual_order.trans, assumption,
                         (thin_tac "ya \<le> _", thin_tac "_ \<le> ya",
                          drule_tac b=ya and a="_ + _" in dual_order.trans, assumption)?,
                         simp add: s0_ptr_defs)+)[16]
  apply (clarsimp simp: page_offs_range_def objBitsKO_def archObjSize_def bit_simps)
  apply (drule (1) aligned_le_sharp, simp add: mask_neg_add_aligned', fastforce simp: mask_def)
  done

lemma pspace_distinctD'':
  "\<lbrakk> \<exists>v. ksPSpace s x = Some v \<and> objBitsKO v = n; pspace_distinct' s \<rbrakk>
     \<Longrightarrow> ps_clear x n s"
  apply clarsimp
  apply (drule(1) pspace_distinctD')
  apply simp
  done

lemma cnode_offs_min2':
  "is_aligned ptr 15 \<Longrightarrow> (ptr :: obj_ref) \<le> ptr + 0x20 * (x && mask 10)"
  apply (erule is_aligned_no_wrap')
  apply (subst mult.commute)
  apply (rule div_lt_mult)
   apply (cut_tac and_mask_less'[where n=10])
    apply simp
   apply simp
  apply simp
  done

lemma cnode_offs_min2:
  "Low_cnode_ptr \<le> Low_cnode_ptr + 0x20 * (x && mask 10)"
  "High_cnode_ptr \<le> High_cnode_ptr + 0x20 * (x && mask 10)"
  "Silc_cnode_ptr \<le> Silc_cnode_ptr + 0x20 * (x && mask 10)"
  by (simp_all add: cnode_offs_min2' s0_ptrs_aligned)

lemma cnode_offs_max2':
  "is_aligned ptr 15 \<Longrightarrow> (ptr::obj_ref) + 0x20 * (x && mask 10) \<le> ptr + 0x7fff"
  apply (rule word_plus_mono_right)
   apply (subst mult.commute)
   apply (rule div_to_mult_word_lt)
   apply simp
   apply (rule plus_one_helper)
   apply simp
   apply (cut_tac and_mask_less'[where n=10])
    apply simp
   apply simp
  apply (drule is_aligned_no_overflow)
  apply (simp add: add.commute)
  done

lemma cnode_offs_max2:
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<le> Low_cnode_ptr + 0x7fff"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<le> High_cnode_ptr + 0x7fff"
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<le> Silc_cnode_ptr + 0x7fff"
  by (simp_all add: cnode_offs_max2' s0_ptrs_aligned)

lemma cnode_offs_in_range2':
  "is_aligned ptr 15 \<Longrightarrow> ptr + 0x20 * (x && mask 10) \<in> cnode_offs_range ptr"
  apply (clarsimp simp: cnode_offs_min2' cnode_offs_max2' cnode_offs_range_def add.commute)
  apply (rule is_aligned_add)
   apply (erule is_aligned_weaken)
   apply simp
  apply (rule_tac is_aligned_mult_triv1[where n=5, simplified])
  done

lemma cnode_offs_in_range2:
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<in> cnode_offs_range Silc_cnode_ptr"
  "Low_cnode_ptr  + 0x20 * (x && mask 10) \<in> cnode_offs_range Low_cnode_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<in> cnode_offs_range High_cnode_ptr"
  by (simp_all add: cnode_offs_in_range2' s0_ptrs_aligned)+

lemma kh0H_dom_distinct2:
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<noteq> idle_tcb_ptr"
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<noteq> High_tcb_ptr"
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<noteq> Low_tcb_ptr"
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<noteq> High_pool_ptr"
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<noteq> Low_pool_ptr"
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<noteq> irq_cnode_ptr"
  "Silc_cnode_ptr + 0x20 * (x && mask 10) \<noteq> ntfn_ptr"
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<noteq> idle_tcb_ptr"
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<noteq> High_tcb_ptr"
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<noteq> Low_tcb_ptr"
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<noteq> High_pool_ptr"
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<noteq> Low_pool_ptr"
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<noteq> irq_cnode_ptr"
  "Low_cnode_ptr + 0x20 * (x && mask 10) \<noteq> ntfn_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<noteq> idle_tcb_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<noteq> High_tcb_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<noteq> Low_tcb_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<noteq> High_pool_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<noteq> Low_pool_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<noteq> irq_cnode_ptr"
  "High_cnode_ptr + 0x20 * (x && mask 10) \<noteq> ntfn_ptr"
  by (cut_tac x=x in cnode_offs_in_range2(1), fastforce simp: kh0H_dom_distinct
      | cut_tac x=x in cnode_offs_in_range2(2), fastforce simp: kh0H_dom_distinct
      | cut_tac x=x in cnode_offs_in_range2(3), fastforce simp: kh0H_dom_distinct)+

lemma kh0H_cnode_simps2[simp]:
  "kh0H (Low_cnode_ptr + 0x20 * (x && mask 10)) = Low_cte Low_cnode_ptr (Low_cnode_ptr + 0x20 * (x && mask 10))"
  "kh0H (High_cnode_ptr + 0x20 * (x && mask 10)) = High_cte High_cnode_ptr (High_cnode_ptr + 0x20 * (x && mask 10))"
  "kh0H (Silc_cnode_ptr + 0x20 * (x && mask 10)) = Silc_cte Silc_cnode_ptr (Silc_cnode_ptr + 0x20 * (x && mask 10))"
  supply option.case_cong[cong] if_cong[cong]
  by (clarsimp simp: kh0H_def option_update_range_def cnode_offs_in_range' s0_ptrs_aligned
                     kh0H_dom_distinct kh0H_dom_distinct2 not_in_range_None,
      ((clarsimp simp: cnode_offs_in_range2 kh0H_dom_sets_distinct[THEN orthD1] not_in_range_None
        | clarsimp simp: cnode_offs_in_range2 kh0H_dom_sets_distinct[THEN orthD2] not_in_range_None)+),
      intro conjI,
      (clarsimp, drule not_disjointI,
                 (rule irq_node_offs_in_range cnode_offs_in_range2 | erule offs_in_range),
                 (rule irq_node_offs_in_range cnode_offs_in_range2 | erule offs_in_range),
                 erule notE, rule kh0H_dom_sets_distinct)+,
      clarsimp split: option.splits)+

lemma cnode_offs_aligned2:
  "is_aligned (Low_cnode_ptr  + 0x20 * (addr && mask 10)) 5"
  "is_aligned (High_cnode_ptr + 0x20 * (addr && mask 10)) 5"
  "is_aligned (Silc_cnode_ptr + 0x20 * (addr && mask 10)) 5"
  by (rule is_aligned_add, rule is_aligned_weaken, rule s0_ptrs_aligned,
      simp, rule is_aligned_mult_triv1[where n=5, simplified])+

lemma less_t2n_ex_ucast:
  "\<lbrakk> (x::'a::len word) < 2 ^ n; len_of TYPE('b) = n \<rbrakk> \<Longrightarrow> \<exists>y. x = ucast (y::'b::len word)"
  apply (rule_tac x="ucast x" in exI)
  apply (rule ucast_ucast_len[symmetric])
  apply simp
  done

lemma pd_offs_aligned:
  "is_aligned (Low_pd_ptr  + (ucast (x :: pt_index) << 3)) 3"
  "is_aligned (High_pd_ptr + (ucast (x :: pt_index) << 3)) 3"
  by (rule is_aligned_add[OF _ is_aligned_shift], simp add: s0_ptr_defs is_aligned_def)+

lemma less_0x200_exists_ucast:
  "p < 0x200 \<Longrightarrow> \<exists>p'. p = UCAST(9 \<rightarrow> 64) p'"
  apply (rule_tac x="UCAST(64 \<rightarrow> 9) p" in exI)
  apply word_bitwise
  apply clarsimp
  done

lemma valid_caps_s0H[simp]:
  notes pteBits_def[simp] objBits_defs[simp]
  shows
  "valid_cap' NullCap s0H_internal"
  "valid_cap' (ThreadCap Low_tcb_ptr) s0H_internal"
  "valid_cap' (ThreadCap High_tcb_ptr) s0H_internal"
  "valid_cap' (CNodeCap Low_cnode_ptr 10 2 10) s0H_internal"
  "valid_cap' (CNodeCap High_cnode_ptr 10 2 10) s0H_internal"
  "valid_cap' (CNodeCap Silc_cnode_ptr 10 2 10) s0H_internal"
  "valid_cap' (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadWrite RISCVLargePage False (Some (ucast Low_asid, 0)))) s0H_internal"
  "valid_cap' (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadOnly RISCVLargePage False (Some (ucast High_asid, 0)))) s0H_internal"
  "valid_cap' (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadOnly RISCVLargePage False (Some (ucast Silc_asid, 0)))) s0H_internal"
  "valid_cap' (ArchObjectCap (PageTableCap Low_pt_ptr (Some (ucast Low_asid, 0)))) s0H_internal"
  "valid_cap' (ArchObjectCap (PageTableCap High_pt_ptr (Some (ucast High_asid, 0)))) s0H_internal"
  "valid_cap' (ArchObjectCap (PageTableCap Low_pd_ptr (Some (ucast Low_asid, 0)))) s0H_internal"
  "valid_cap' (ArchObjectCap (PageTableCap High_pd_ptr (Some (ucast High_asid, 0)))) s0H_internal"
  "valid_cap' (ArchObjectCap (ASIDPoolCap Low_pool_ptr (ucast Low_asid))) s0H_internal"
  "valid_cap' (ArchObjectCap (ASIDPoolCap High_pool_ptr (ucast High_asid))) s0H_internal"
  "valid_cap' (NotificationCap ntfn_ptr 0 True False) s0H_internal"
  "valid_cap' (NotificationCap ntfn_ptr 0 False True) s0H_internal"
  "valid_cap' (ReplyCap Low_tcb_ptr True True) s0H_internal"
  "valid_cap' (ReplyCap High_tcb_ptr True True) s0H_internal"
  supply option.case_cong[cong] if_cong[cong]
  apply (simp | simp add: valid_cap'_def s0H_internal_def capAligned_def word_bits_def
                          objBits_def s0_ptrs_aligned obj_at'_def,
                intro conjI, simp add: objBitsKO_def s0_ptrs_aligned, simp add: objBitsKO_def,
                simp add: objBitsKO_def s0_ptrs_aligned mask_def,
                rule pspace_distinctD'[OF _ s0H_pspace_distinct', simplified s0H_internal_def],
                simp)+
   apply (simp add: valid_cap'_def capAligned_def word_bits_def objBits_def s0_ptrs_aligned obj_at'_def)
   apply (intro conjI)
      apply (simp add: objBitsKO_def s0_ptrs_aligned)
     apply (simp add: objBitsKO_def)
    apply (simp add: objBitsKO_def s0_ptrs_aligned mask_def)
   apply (clarsimp simp: Low_cte_def Low_cte'_def Low_capsH_def cnode_offs_min2 objBitsKO_def
                         cnode_offs_max2 cnode_offs_aligned2 add.commute s0_ptrs_aligned empty_cte_def)
   apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct'])
   apply (simp add: Low_cte_def Low_cte'_def Low_capsH_def empty_cte_def objBitsKO_def
                    cnode_offs_min2 cnode_offs_max2 cnode_offs_aligned2 add.commute s0_ptrs_aligned)
   apply (simp add: valid_cap'_def capAligned_def word_bits_def objBits_def s0_ptrs_aligned obj_at'_def)
   apply (intro conjI)
      apply (simp add: objBitsKO_def s0_ptrs_aligned)
     apply (simp add: objBitsKO_def)
    apply (simp add: objBitsKO_def s0_ptrs_aligned mask_def)
   apply (clarsimp simp: High_cte_def High_cte'_def High_capsH_def cnode_offs_min2 cnode_offs_max2
                         cnode_offs_aligned2 add.commute s0_ptrs_aligned objBitsKO_def empty_cte_def)
   apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct'])
   apply (simp add: High_cte_def High_cte'_def High_capsH_def empty_cte_def objBitsKO_def
                    cnode_offs_min2 cnode_offs_max2 cnode_offs_aligned2 add.commute s0_ptrs_aligned)
   apply (simp add: valid_cap'_def capAligned_def word_bits_def objBits_def s0_ptrs_aligned obj_at'_def)
   apply (intro conjI)
      apply (simp add: objBitsKO_def s0_ptrs_aligned)
     apply (simp add: objBitsKO_def)
    apply (simp add: objBitsKO_def s0_ptrs_aligned mask_def)
   apply (clarsimp simp: Silc_cte_def Silc_cte'_def Silc_capsH_def cnode_offs_min2 objBitsKO_def
                         empty_cte_def cnode_offs_max2 cnode_offs_aligned2 add.commute s0_ptrs_aligned)
   apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct'])
   apply (simp add: Silc_cte_def Silc_cte'_def Silc_capsH_def empty_cte_def objBitsKO_def
                    cnode_offs_min2 cnode_offs_max2 cnode_offs_aligned2 add.commute s0_ptrs_aligned)
  apply ((clarsimp simp: valid_cap'_def capAligned_def word_bits_def s0_ptrs_aligned bit_simps
                         Low_asid_def High_asid_def Silc_asid_def asid_bits_defs
                         vmsz_aligned_def frame_at'_def typ_at'_def ko_wp_at'_def
                         wellformed_mapdata'_def asid_wf_def mask_def,
          drule less_0x200_exists_ucast, clarsimp, clarsimp simp: objBitsKO_def,
          rule conjI, clarsimp simp: s0_ptr_defs is_aligned_mask bit_simps mask_def, word_bitwise,
          rule pspace_distinctD''[OF _ s0H_pspace_distinct'],
          simp add: objBitsKO_def)+)[3]
  apply ((simp add: valid_cap'_def capAligned_def word_bits_def Low_asid_def High_asid_def
                    asid_bits_defs asid_wf_def s0_ptrs_aligned wellformed_mapdata'_def
                    bit_simps mask_def archObjSize_def pt_offs_min objBitsKO_def
                    page_table_at'_def typ_at'_def ko_wp_at'_def kh0H_obj_def, safe,
          rule pspace_distinctD''[OF _ s0H_pspace_distinct'],
          simp add: pt_offs_min kh0H_obj_def archObjSize_def bit_simps objBitsKO_def,
          clarsimp simp: is_aligned_mask mask_def s0_ptr_defs, word_bitwise,
          fastforce simp: pt_offs_max add.commute)+)[4]
  apply ((simp add: valid_cap'_def capAligned_def word_bits_def Low_asid_def High_asid_def
                    asid_bits_defs asid_wf_def s0_ptrs_aligned bit_simps wellformed_mapdata'_def
                    mask_def page_table_at'_def typ_at'_def ko_wp_at'_def kh0H_obj_def
                    objBitsKO_def archObjSize_def pt_offs_min,
          intro conjI, clarsimp simp: is_aligned_mask mask_def s0_ptr_defs,
          rule pspace_distinctD''[OF _ s0H_pspace_distinct'],
          simp add: kh0H_obj_def archObjSize_def bit_simps objBitsKO_def)+)[2]
  by (simp add: valid_cap'_def s0H_internal_def capAligned_def word_bits_def objBits_def obj_at'_def,
      intro conjI, simp add: objBitsKO_def s0_ptrs_aligned, simp add: objBitsKO_def,
      simp add: objBitsKO_def s0_ptrs_aligned mask_def,
      rule pspace_distinctD'[OF _ s0H_pspace_distinct', simplified s0H_internal_def], simp)+

text \<open>We can only instantiate our example state (featuring high and low domains) if the number
  of configured domains is > 1, i.e. that maxDomain is 1 or greater. When seL4 is configured for a
  single domain only, none of the state instantiation proofs below are relevant.\<close>

lemma s0H_valid_objs':
  "1 \<le> maxDomain \<Longrightarrow> valid_objs' s0H_internal"
  supply objBits_defs[simp]
  apply (clarsimp simp: valid_objs'_def ran_def)
  apply (drule kh0H_SomeD)
  apply (elim disjE)
                  apply (clarsimp simp: valid_obj'_def ntfnH_def valid_ntfn'_def obj_at'_def)
                  apply (rule conjI)
                   apply (clarsimp simp: is_aligned_def s0_ptr_defs objBitsKO_def)
                  apply (clarsimp simp: pspace_distinctD'[OF _ s0H_pspace_distinct'])
                 apply (clarsimp simp: valid_obj'_def valid_tcb'_def valid_tcb_state'_def
                                       Low_domain_def minBound_word valid_arch_tcb'_def
                                       Low_mcp_def Low_prio_def maxPriority_def numPriorities_def
                                       tcb_cte_cases_def Low_capsH_def kh0H_obj_def)
                apply (clarsimp simp: valid_obj'_def valid_tcb'_def  valid_tcb_state'_def
                                      High_domain_def minBound_word valid_arch_tcb'_def
                                      High_mcp_def High_prio_def maxPriority_def numPriorities_def
                                      tcb_cte_cases_def High_capsH_def obj_at'_def kh0H_obj_def)
                apply (rule conjI)
                 apply (simp add: is_aligned_def s0_ptr_defs objBitsKO_def)
                apply (clarsimp simp: ntfnH_def pspace_distinctD'[OF _ s0H_pspace_distinct'])
               apply (clarsimp simp: valid_obj'_def valid_tcb'_def kh0H_obj_def valid_tcb_state'_def
                                     default_domain_def minBound_word valid_arch_tcb'_def
                                     default_priority_def tcb_cte_cases_def)
              defer 2
              apply (auto simp: is_aligned_def addrFromPPtr_def ptrFromPAddr_def pptrBaseOffset_def
                                valid_obj'_def s0_ptr_defs kh0H_obj_def valid_arch_obj'_def)[5]
         apply (auto simp: valid_obj'_def valid_cte'_def empty_cte_def irq_cte_def
                           valid_arch_obj'_def
                           Low_cte_def Low_cte'_def Low_capsH_def
                           High_cte_def High_cte'_def High_capsH_def
                           Silc_cte_def Silc_cte'_def Silc_capsH_def)
  done

lemmas the_nat_to_bl_simps = the_nat_to_bl_def nat_to_bl_def

lemma ucast_shiftr_13E:
  "\<lbrakk> ucast (p - ptr >> 5) = (0x13E :: 10 word); p \<le> 0x7FFF + ptr; ptr \<le> p;
     is_aligned ptr 15; is_aligned p 5 \<rbrakk>
     \<Longrightarrow> p = (ptr :: obj_ref) + 0x27C0"
  apply (subst(asm) up_ucast_inj_eq[symmetric, where 'b=64])
   apply simp
  apply simp
  apply (subst(asm) ucast_ucast_len)
   apply simp
   apply (rule shiftr_less_t2n[where m=10, simplified])
   apply simp
   apply (rule word_leq_minus_one_le)
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply simp
   apply simp
  apply (drule shiftr_eqD[where y="0x27C0" and n=5 and 'a=64, simplified])
    apply (erule(1) aligned_sub_aligned[OF _ is_aligned_weaken])
     apply simp
    apply simp
   apply (simp add: is_aligned_def)
  apply (simp add: diff_eq_eq)
  done

lemma ucast_shiftr_6:
  "\<lbrakk> ucast (p - ptr >> 5) = (0x6 :: 10 word); p \<le> 0x7FFF + ptr; ptr \<le> p;
     is_aligned ptr 15; is_aligned p 5\<rbrakk>
     \<Longrightarrow> p = (ptr :: obj_ref) + 0xC0"
  apply (subst(asm) up_ucast_inj_eq[symmetric, where 'b=64])
   apply simp
  apply simp
  apply (subst(asm) ucast_ucast_len)
   apply simp
   apply (rule shiftr_less_t2n[where m=10, simplified])
   apply simp
   apply (rule word_leq_minus_one_le)
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply simp
   apply simp
  apply (drule shiftr_eqD[where y="0xC0" and n=5 and 'a=64, simplified])
    apply (erule(1) aligned_sub_aligned[OF _ is_aligned_weaken])
     apply simp
    apply simp
   apply (simp add: is_aligned_def)
  apply (simp add: diff_eq_eq)
  done

lemma ucast_shiftr_5:
  "\<lbrakk> ucast (p - ptr >> 5) = (5 :: 10 word); p \<le> 0x7FFF + ptr; ptr \<le> p;
     is_aligned ptr 15; is_aligned p 5\<rbrakk>
     \<Longrightarrow> p = (ptr :: obj_ref) + 0xA0"
  apply (subst(asm) up_ucast_inj_eq[symmetric, where 'b=64])
   apply simp
  apply simp
  apply (subst(asm) ucast_ucast_len)
   apply simp
   apply (rule shiftr_less_t2n[where m=10, simplified])
   apply simp
   apply (rule word_leq_minus_one_le)
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply simp
   apply simp
  apply (drule shiftr_eqD[where y="0xA0" and n=5 and 'a=64, simplified])
    apply (erule(1) aligned_sub_aligned[OF _ is_aligned_weaken])
     apply simp
    apply simp
   apply (simp add: is_aligned_def)
  apply (simp add: diff_eq_eq)
  done

lemma ucast_shiftr_4:
  "\<lbrakk> ucast (p - ptr >> 5) = (4 :: 10 word); p \<le> 0x7FFF + ptr; ptr \<le> p;
     is_aligned ptr 15; is_aligned p 5\<rbrakk>
     \<Longrightarrow> p = (ptr :: obj_ref) + 0x80"
  apply (subst(asm) up_ucast_inj_eq[symmetric, where 'b=64])
   apply simp
  apply simp
  apply (subst(asm) ucast_ucast_len)
   apply simp
   apply (rule shiftr_less_t2n[where m=10, simplified])
   apply simp
   apply (rule word_leq_minus_one_le)
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply simp
   apply simp
  apply (drule shiftr_eqD[where y="0x80" and n=5 and 'a=64, simplified])
    apply (erule(1) aligned_sub_aligned[OF _ is_aligned_weaken])
     apply simp
    apply simp
   apply (simp add: is_aligned_def)
  apply (simp add: diff_eq_eq)
  done

lemma ucast_shiftr_3:
  "\<lbrakk>ucast (p - ptr >> 5) = (3 :: 10 word); p \<le> 0x7FFF + ptr; ptr \<le> p;
    is_aligned ptr 15; is_aligned p 5\<rbrakk>
    \<Longrightarrow> p = (ptr :: obj_ref) + 0x60"
  apply (subst(asm) up_ucast_inj_eq[symmetric, where 'b=64])
   apply simp
  apply simp
  apply (subst(asm) ucast_ucast_len)
   apply simp
   apply (rule shiftr_less_t2n[where m=10, simplified])
   apply simp
   apply (rule word_leq_minus_one_le)
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply simp
   apply simp
  apply (drule shiftr_eqD[where y="0x60" and n=5 and 'a=64, simplified])
    apply (erule(1) aligned_sub_aligned[OF _ is_aligned_weaken])
     apply simp
    apply simp
   apply (simp add: is_aligned_def)
  apply (simp add: diff_eq_eq)
  done

lemma ucast_shiftr_2:
  "\<lbrakk>ucast (p - ptr >> 5) = (2 :: 10 word); p \<le> 0x7FFF + ptr; ptr \<le> p;
    is_aligned ptr 15; is_aligned p 5\<rbrakk>
    \<Longrightarrow> p = (ptr :: obj_ref) + 0x40"
  apply (subst(asm) up_ucast_inj_eq[symmetric, where 'b=64])
   apply simp
  apply simp
  apply (subst(asm) ucast_ucast_len)
   apply simp
   apply (rule shiftr_less_t2n[where m=10, simplified])
   apply simp
   apply (rule word_leq_minus_one_le)
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply simp
   apply simp
  apply (drule shiftr_eqD[where y="0x40" and n=5 and 'a=64, simplified])
    apply (erule(1) aligned_sub_aligned[OF _ is_aligned_weaken])
     apply simp
    apply simp
   apply (simp add: is_aligned_def)
  apply (simp add: diff_eq_eq)
  done

lemma ucast_shiftr_1:
  "\<lbrakk>ucast (p - ptr >> 5) = (1 :: 10 word); p \<le> 0x7FFF + ptr; ptr \<le> p;
    is_aligned ptr 15; is_aligned p 5\<rbrakk>
    \<Longrightarrow> p = (ptr :: obj_ref) + 0x20"
  apply (subst(asm) up_ucast_inj_eq[symmetric, where 'b=64])
   apply simp
  apply simp
  apply (subst(asm) ucast_ucast_len)
   apply simp
   apply (rule shiftr_less_t2n[where m=10, simplified])
   apply simp
   apply (rule word_leq_minus_one_le)
    apply simp
   apply simp
   apply (rule word_diff_ls')
    apply simp
   apply simp
  apply (drule shiftr_eqD[where y="0x20" and n=5 and 'a=64, simplified])
    apply (erule(1) aligned_sub_aligned[OF _ is_aligned_weaken])
     apply simp
    apply simp
   apply (simp add: is_aligned_def)
  apply (simp add: diff_eq_eq)
  done

lemmas kh0H_all_obj_def' = Low_cte_cte_def High_cte_cte_def Silc_cte_cte_def
                           Low_tcb_cte_def High_tcb_cte_def idle_tcb_cte_def kh0H_all_obj_def

lemma map_to_ctes_kh0H_simps'[simp]:
  "map_to_ctes kh0H (Low_cnode_ptr + 0x20) = Some (CTE (ThreadCap Low_tcb_ptr) Null_mdb)"
  "map_to_ctes kh0H (Low_cnode_ptr + 0x40) = Some (CTE (CNodeCap Low_cnode_ptr 10 2 10)
                                                       (MDB 0 Low_tcb_ptr False False))"
  "map_to_ctes kh0H (Low_cnode_ptr + 0x60) = Some (CTE (ArchObjectCap (PageTableCap Low_pd_ptr (Some (ucast Low_asid, 0))))
                                                       (MDB 0 (Low_tcb_ptr + 0x20) False False))"
  "map_to_ctes kh0H (Low_cnode_ptr + 0x80) = Some (CTE (ArchObjectCap (ASIDPoolCap Low_pool_ptr (ucast Low_asid))) Null_mdb)"
  "map_to_ctes kh0H (Low_cnode_ptr + 0xA0) = Some (CTE (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadWrite RISCVLargePage
                                                                                False (Some (ucast Low_asid, 0))))
                                                       (MDB 0 (Silc_cnode_ptr + 0xA0) False False))"
  "map_to_ctes kh0H (Low_cnode_ptr + 0xC0) = Some (CTE (ArchObjectCap (PageTableCap Low_pt_ptr (Some (ucast Low_asid, 0)))) Null_mdb)"
  "map_to_ctes kh0H (Low_cnode_ptr + 0x27C0) = Some (CTE (NotificationCap ntfn_ptr 0 True False)
                                                         (MDB (Silc_cnode_ptr + 0x27C0) 0 False False))"
  "map_to_ctes kh0H (High_cnode_ptr + 0x20) = Some (CTE (ThreadCap High_tcb_ptr) Null_mdb)"
  "map_to_ctes kh0H (High_cnode_ptr + 0x40) = Some (CTE (CNodeCap High_cnode_ptr 10 2 10) (MDB 0 High_tcb_ptr False False))"
  "map_to_ctes kh0H (High_cnode_ptr + 0x60) = Some (CTE (ArchObjectCap (PageTableCap High_pd_ptr (Some (ucast High_asid, 0))))
                                                        (MDB 0 (High_tcb_ptr + 0x20) False False))"
  "map_to_ctes kh0H (High_cnode_ptr + 0x80) = Some (CTE (ArchObjectCap (ASIDPoolCap High_pool_ptr (ucast High_asid))) Null_mdb)"
  "map_to_ctes kh0H (High_cnode_ptr + 0xA0) = Some (CTE (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadOnly RISCVLargePage
                                                                                 False (Some (ucast High_asid, 0))))
                                                        (MDB (Silc_cnode_ptr + 0xA0) 0 False False))"
  "map_to_ctes kh0H (High_cnode_ptr + 0xC0) = Some (CTE (ArchObjectCap (PageTableCap High_pt_ptr (Some (ucast High_asid, 0)))) Null_mdb)"
  "map_to_ctes kh0H (High_cnode_ptr + 0x27C0) = Some (CTE (NotificationCap ntfn_ptr 0 False True)
                                                          (MDB 0 (Silc_cnode_ptr + 0x27C0) False False))"
  "map_to_ctes kh0H (Silc_cnode_ptr + 0x40) = Some (CTE (CNodeCap Silc_cnode_ptr 10 2 10) Null_mdb)"
  "map_to_ctes kh0H (Silc_cnode_ptr + 0xA0) = Some (CTE (ArchObjectCap (FrameCap shared_page_ptr_virt VMReadOnly RISCVLargePage
                                                                                 False (Some (ucast Silc_asid, 0))))
                                                        (MDB (Low_cnode_ptr + 0xA0) (High_cnode_ptr + 0xA0) False False))"
  "map_to_ctes kh0H (Silc_cnode_ptr + 0x27C0) = Some (CTE (NotificationCap ntfn_ptr 0 True False)
                                                          (MDB (High_cnode_ptr + 318 * 0x20) (Low_cnode_ptr + 318 * 0x20) False False))"
                  apply (clarsimp simp: map_to_ctes_kh0H_simps(3)[where x="the_nat_to_bl_10 1", simplified the_nat_to_bl_simps, simplified]
                                        kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
                 apply (clarsimp simp: map_to_ctes_kh0H_simps(3)[where x="the_nat_to_bl_10 2", simplified the_nat_to_bl_simps, simplified]
                                       kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
                apply (clarsimp simp: map_to_ctes_kh0H_simps(3)[where x="the_nat_to_bl_10 3", simplified the_nat_to_bl_simps, simplified]
                                      kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
               apply (clarsimp simp: map_to_ctes_kh0H_simps(3)[where x="the_nat_to_bl_10 4", simplified the_nat_to_bl_simps, simplified]
                                     kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
              apply (clarsimp simp: map_to_ctes_kh0H_simps(3)[where x="the_nat_to_bl_10 5", simplified the_nat_to_bl_simps, simplified]
                                    kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
             apply (clarsimp simp: map_to_ctes_kh0H_simps(3)[where x="the_nat_to_bl_10 6", simplified the_nat_to_bl_simps, simplified]
                                   kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
            apply (clarsimp simp: map_to_ctes_kh0H_simps(3)[where x="the_nat_to_bl_10 318", simplified the_nat_to_bl_simps, simplified]
                                  kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
           apply (clarsimp simp: map_to_ctes_kh0H_simps(4)[where x="the_nat_to_bl_10 1", simplified the_nat_to_bl_simps, simplified]
                                 kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
          apply (clarsimp simp: map_to_ctes_kh0H_simps(4)[where x="the_nat_to_bl_10 2", simplified the_nat_to_bl_simps, simplified]
                                kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
         apply (clarsimp simp: map_to_ctes_kh0H_simps(4)[where x="the_nat_to_bl_10 3", simplified the_nat_to_bl_simps, simplified]
                               kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
        apply (clarsimp simp: map_to_ctes_kh0H_simps(4)[where x="the_nat_to_bl_10 4", simplified the_nat_to_bl_simps, simplified]
                              kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
       apply (clarsimp simp: map_to_ctes_kh0H_simps(4)[where x="the_nat_to_bl_10 5", simplified the_nat_to_bl_simps, simplified]
                             kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
      apply (clarsimp simp: map_to_ctes_kh0H_simps(4)[where x="the_nat_to_bl_10 6", simplified the_nat_to_bl_simps, simplified]
                            kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
     apply (clarsimp simp: map_to_ctes_kh0H_simps(4)[where x="the_nat_to_bl_10 318", simplified the_nat_to_bl_simps, simplified]
                           kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
    apply (clarsimp simp: map_to_ctes_kh0H_simps(5)[where x="the_nat_to_bl_10 2", simplified the_nat_to_bl_simps, simplified]
                          kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
   apply (clarsimp simp: map_to_ctes_kh0H_simps(5)[where x="the_nat_to_bl_10 5", simplified the_nat_to_bl_simps, simplified]
                         kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
  apply (clarsimp simp: map_to_ctes_kh0H_simps(5)[where x="the_nat_to_bl_10 318", simplified the_nat_to_bl_simps, simplified]
                        kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps, fastforce simp: s0_ptr_defs is_aligned_def)
  done

lemma mdb_next_s0H:
  "p' \<noteq> 0
   \<Longrightarrow> map_to_ctes kh0H \<turnstile> p \<leadsto> p' =
       (p = Low_cnode_ptr + 0x27C0 \<and> p' = Silc_cnode_ptr + 0x27C0 \<or>
        p = Silc_cnode_ptr + 0x27C0 \<and> p' = High_cnode_ptr + 0x27C0 \<or>
        p = High_cnode_ptr + 0xA0 \<and> p' = Silc_cnode_ptr + 0xA0 \<or>
        p = Silc_cnode_ptr + 0xA0 \<and> p' = Low_cnode_ptr + 0xA0 \<or>
        p = Low_tcb_ptr \<and> p' = Low_cnode_ptr + 0x40 \<or>
        p = Low_tcb_ptr + 0x20 \<and> p' = Low_cnode_ptr + 0x60 \<or>
        p = High_tcb_ptr \<and> p' = High_cnode_ptr + 0x40 \<or>
        p = High_tcb_ptr + 0x20 \<and> p' = High_cnode_ptr + 0x60)"
  apply (rule iffI)
   apply (simp add: next_unfold')
   apply (elim exE conjE)
   apply (frule map_to_ctes_kh0H_SomeD)
   apply (elim disjE, simp_all)[1]
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                           ucast_shiftr_13E ucast_shiftr_5 s0_ptrs_aligned
                    split: if_split_asm)
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                          ucast_shiftr_5 s0_ptrs_aligned
                   split: if_split_asm)
   apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                         ucast_shiftr_13E ucast_shiftr_5 s0_ptrs_aligned
                  split: if_split_asm)
  apply (clarsimp simp: next_unfold' map_to_ctes_kh0H_dom)
  apply (elim disjE, simp_all add: kh0H_all_obj_def')
  done

lemma mdb_prev_s0H:
  "p \<noteq> 0
   \<Longrightarrow> map_to_ctes kh0H \<turnstile> p \<leftarrow> p' =
       (p = Low_cnode_ptr + 0x27C0 \<and> p' = Silc_cnode_ptr + 0x27C0 \<or>
        p = Silc_cnode_ptr + 0x27C0 \<and> p' = High_cnode_ptr + 0x27C0 \<or>
        p = High_cnode_ptr + 0xA0 \<and> p' = Silc_cnode_ptr + 0xA0 \<or>
        p = Silc_cnode_ptr + 0xA0 \<and> p' = Low_cnode_ptr + 0xA0 \<or>
        p = Low_tcb_ptr \<and> p' = Low_cnode_ptr + 0x40 \<or>
        p = Low_tcb_ptr + 0x20 \<and> p' = Low_cnode_ptr + 0x60 \<or>
        p = High_tcb_ptr \<and> p' = High_cnode_ptr + 0x40 \<or>
        p = High_tcb_ptr + 0x20 \<and> p' = High_cnode_ptr + 0x60)"
  apply (rule iffI)
   apply (simp add: mdb_prev_def)
   apply (elim exE conjE)
   apply (frule map_to_ctes_kh0H_SomeD)
   apply (elim disjE, simp_all)[1]
     apply clarsimp
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                           ucast_shiftr_13E ucast_shiftr_5 s0_ptrs_aligned
                    split: if_split_asm)
    apply clarsimp
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                          ucast_shiftr_13E ucast_shiftr_3 ucast_shiftr_2 s0_ptrs_aligned
                   split: if_split_asm)
   apply clarsimp
   apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                         ucast_shiftr_5 ucast_shiftr_3 ucast_shiftr_2 s0_ptrs_aligned
                  split: if_split_asm)
  apply (clarsimp simp: mdb_prev_def map_to_ctes_kh0H_dom)
  apply (elim disjE, simp_all add: kh0H_all_obj_def')
  done

lemma mdb_next_trancl_s0H:
  "p' \<noteq> 0
   \<Longrightarrow> map_to_ctes kh0H \<turnstile> p \<leadsto>\<^sup>+ p' =
       (p = Low_cnode_ptr + 0x27C0 \<and> p' = Silc_cnode_ptr + 0x27C0 \<or>
        p = Silc_cnode_ptr + 0x27C0 \<and> p' = High_cnode_ptr + 0x27C0 \<or>
        p = Low_cnode_ptr + 0x27C0 \<and> p' = High_cnode_ptr + 0x27C0 \<or>
        p = High_cnode_ptr + 0xA0 \<and> p' = Silc_cnode_ptr + 0xA0 \<or>
        p = Silc_cnode_ptr + 0xA0 \<and> p' = Low_cnode_ptr + 0xA0 \<or>
        p = High_cnode_ptr + 0xA0 \<and> p' = Low_cnode_ptr + 0xA0 \<or>
        p = Low_tcb_ptr \<and> p' = Low_cnode_ptr + 0x40 \<or>
        p = Low_tcb_ptr + 0x20 \<and> p' = Low_cnode_ptr + 0x60 \<or>
        p = High_tcb_ptr \<and> p' = High_cnode_ptr + 0x40 \<or>
        p = High_tcb_ptr + 0x20 \<and> p' = High_cnode_ptr + 0x60)"
  apply (rule iffI)
   apply (erule converse_trancl_induct)
    apply (clarsimp simp: mdb_next_s0H)
   apply (subst (asm) mdb_next_s0H)
    apply (clarsimp simp: s0_ptr_defs)
   apply (clarsimp simp: s0_ptr_defs del: disjCI)
   apply ((erule_tac P="y = _ \<and> _" in disjE | clarsimp)+)[1]
  apply (elim disjE)
           apply (rule r_into_trancl, simp add: mdb_next_s0H)
          apply (rule r_into_trancl, simp add: mdb_next_s0H)
         apply (rule r_r_into_trancl[where b="Silc_cnode_ptr + 0x27C0"])
          apply (simp add: mdb_next_s0H s0_ptr_defs)
         apply (simp add: mdb_next_s0H)
        apply (rule r_into_trancl, simp add: mdb_next_s0H)
       apply (rule r_into_trancl, simp add: mdb_next_s0H)
      apply (rule r_r_into_trancl[where b="Silc_cnode_ptr + 0xA0"])
       apply (simp add: mdb_next_s0H s0_ptr_defs)
      apply (simp add: mdb_next_s0H)
     apply (rule r_into_trancl, simp add: mdb_next_s0H)
    apply (rule r_into_trancl, simp add: mdb_next_s0H)
   apply (rule r_into_trancl, simp add: mdb_next_s0H)
  apply (rule r_into_trancl, simp add: mdb_next_s0H)
  done

lemma mdb_next_rtrancl_not_0_s0H:
  "\<lbrakk> map_to_ctes kh0H \<turnstile> p \<leadsto>\<^sup>* p'; p' \<noteq> 0 \<rbrakk> \<Longrightarrow> p \<noteq> 0"
  apply (drule rtranclD)
  apply (clarsimp simp: mdb_next_trancl_s0H s0_ptr_defs)
  done

lemma sameRegionAs_s0H:
  "\<lbrakk> map_to_ctes kh0H p = Some (CTE cap mdb); map_to_ctes kh0H p' = Some (CTE cap' mdb');
     sameRegionAs cap cap'; p \<noteq> p' \<rbrakk>
     \<Longrightarrow> (p = Low_cnode_ptr + 0x27C0 \<and> (p' = Silc_cnode_ptr + 0x27C0 \<or> p' = High_cnode_ptr + 0x27C0) \<or>
          p = Silc_cnode_ptr + 0x27C0 \<and> (p' = Low_cnode_ptr + 0x27C0 \<or> p' = High_cnode_ptr + 0x27C0) \<or>
          p = High_cnode_ptr + 0x27C0 \<and> (p' = Low_cnode_ptr + 0x27C0 \<or> p' = Silc_cnode_ptr + 0x27C0) \<or>
          p = Low_cnode_ptr + 0xA0 \<and> (p' = Silc_cnode_ptr + 0xA0 \<or> p' = High_cnode_ptr + 0xA0) \<or>
          p = Silc_cnode_ptr + 0xA0 \<and> (p' = Low_cnode_ptr + 0xA0 \<or> p' = High_cnode_ptr + 0xA0) \<or>
          p = High_cnode_ptr + 0xA0 \<and> (p' = Low_cnode_ptr + 0xA0 \<or> p' = Silc_cnode_ptr + 0xA0) \<or>
          p = Low_tcb_ptr \<and> p' = Low_cnode_ptr + 0x40 \<or>
          p = Low_cnode_ptr + 0x40 \<and> p' = Low_tcb_ptr \<or>
          p = Low_tcb_ptr + 0x20 \<and> p' = Low_cnode_ptr + 0x60 \<or>
          p = Low_cnode_ptr + 0x60 \<and> p' = Low_tcb_ptr + 0x20 \<or>
          p = High_tcb_ptr \<and> p' = High_cnode_ptr + 0x40 \<or>
          p = High_cnode_ptr + 0x40 \<and> p' = High_tcb_ptr \<or>
          p = High_tcb_ptr + 0x20 \<and> p' = High_cnode_ptr + 0x60 \<or>
          p = High_cnode_ptr + 0x60 \<and> p' = High_tcb_ptr + 0x20)"
  supply option.case_cong[cong] if_cong[cong] s0_ptrs_aligned[simp]
  apply (frule_tac x=p in map_to_ctes_kh0H_SomeD)
  apply (elim disjE, simp_all)
          apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
          apply (elim disjE, simp_all add: sameRegionAs_def isCap_simps)[1]
            apply (clarsimp simp: kh0H_all_obj_def' s0_ptr_defs split: if_split_asm)
           apply (clarsimp simp: kh0H_all_obj_def' s0_ptr_defs split: if_split_asm)
          apply (clarsimp simp: to_bl_use_of_bl the_nat_to_bl_simps kh0H_all_obj_def' ucast_shiftr_2
                         split: if_split_asm)
         apply ((frule_tac x=p' in map_to_ctes_kh0H_SomeD,
                (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps)[1],
                ((clarsimp simp: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps to_bl_use_of_bl
                                 the_nat_to_bl_simps kh0H_all_obj_def' ucast_shiftr_2 ucast_shiftr_3
                          split: if_split_asm)+)[3])+)[5]
    apply (clarsimp simp: kh0H_all_obj_def' split: if_split_asm)
      apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
      apply (elim disjE, simp_all add: sameRegionAs_def isCap_simps)[1]
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                       split: if_split_asm)
        apply (drule(2) ucast_shiftr_13E; clarsimp)
        apply (drule(2) ucast_shiftr_13E; clarsimp)
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_13E
                      split: if_split_asm)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_13E
                     split: if_split_asm)
     apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
     apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                               split: if_split_asm)[1]
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
       apply (drule(2) ucast_shiftr_5; clarsimp)
       apply (drule(2) ucast_shiftr_5; clarsimp)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
      apply (drule(2) ucast_shiftr_5; clarsimp)
      apply (drule(2) ucast_shiftr_5; clarsimp)
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
     apply (drule(2) ucast_shiftr_5; clarsimp)
     apply (drule(2) ucast_shiftr_5; clarsimp)
    apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
    apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                              split: if_split_asm)[1]
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
      apply (drule(2) ucast_shiftr_2; clarsimp)
      apply (drule(2) ucast_shiftr_2; clarsimp)
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
   apply (clarsimp simp: kh0H_all_obj_def' split: if_split_asm)
         apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
         apply (elim disjE, simp_all add: sameRegionAs_def isCap_simps)[1]
           apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_13E
                          split: if_split_asm)
          apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
          apply (drule(2) ucast_shiftr_13E; clarsimp)
          apply (drule(2) ucast_shiftr_13E; clarsimp)
         apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_13E
                        split: if_split_asm)
        apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
        apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                                  split: if_split_asm)[1]
          apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                         split: if_split_asm)
         apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                        split: if_split_asm)
         apply (drule(2) ucast_shiftr_6; clarsimp)
         apply (drule(2) ucast_shiftr_6; clarsimp)
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
       apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
       apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                                 split: if_split_asm)[1]
         apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                        split: if_split_asm)
         apply (drule(2) ucast_shiftr_5; clarsimp)
         apply (drule(2) ucast_shiftr_5; clarsimp)
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
        apply (drule(2) ucast_shiftr_5; clarsimp)
        apply (drule(2) ucast_shiftr_5; clarsimp)
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
       apply (drule(2) ucast_shiftr_5; clarsimp)
       apply (drule(2) ucast_shiftr_5; clarsimp)
      apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
      apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                                split: if_split_asm)[1]
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                       split: if_split_asm)
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
       apply (drule(2) ucast_shiftr_4; clarsimp)
       apply (drule(2) ucast_shiftr_4; clarsimp)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
     apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
     apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                               split: if_split_asm)[1]
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                       split: if_split_asm)
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
      apply (drule(2) ucast_shiftr_3; clarsimp)
      apply (drule(2) ucast_shiftr_3; clarsimp)
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
    apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
    apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                              split: if_split_asm)[1]
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                      split: if_split_asm)
       apply (drule(2) ucast_shiftr_2; clarsimp)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
     apply (drule(2) ucast_shiftr_2; clarsimp)
     apply (drule(2) ucast_shiftr_2; clarsimp)
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
   apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
   apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                             split: if_split_asm)[1]
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                    split: if_split_asm)
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
    apply (drule(2) ucast_shiftr_1; clarsimp)
    apply (drule(2) ucast_shiftr_1; clarsimp)
   apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
  apply (clarsimp simp: kh0H_all_obj_def' split: if_split_asm)
        apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
        apply (elim disjE, simp_all add: sameRegionAs_def isCap_simps)[1]
          apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_13E
                         split: if_split_asm)
         apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
         apply (drule(2) ucast_shiftr_13E; clarsimp)
         apply (drule(2) ucast_shiftr_13E; clarsimp)
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_13E
                       split: if_split_asm)
        apply (drule(2) ucast_shiftr_13E; clarsimp)
        apply (drule(2) ucast_shiftr_13E; clarsimp)
       apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
       apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                                 split: if_split_asm)[1]
         apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                        split: if_split_asm)
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
       apply (drule(2) ucast_shiftr_6; clarsimp)
       apply (drule(2) ucast_shiftr_6; clarsimp)
      apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
      apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                                split: if_split_asm)[1]
        apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                       split: if_split_asm)
        apply (drule(2) ucast_shiftr_5; clarsimp)
        apply (drule(2) ucast_shiftr_5; clarsimp)
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                      split: if_split_asm)
       apply (drule(2) ucast_shiftr_5; clarsimp)
       apply (drule(2) ucast_shiftr_5; clarsimp)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps
                     split: if_split_asm)
      apply (drule(2) ucast_shiftr_5; clarsimp)
      apply (drule(2) ucast_shiftr_5; clarsimp)
     apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
     apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                               split: if_split_asm)[1]
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                      split: if_split_asm)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
     apply (drule(2) ucast_shiftr_4; clarsimp)
     apply (drule(2) ucast_shiftr_4; clarsimp)
    apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
    apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                              split: if_split_asm)[1]
       apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                      split: if_split_asm)
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
    apply (drule(2) ucast_shiftr_3; clarsimp)
    apply (drule(2) ucast_shiftr_3; clarsimp)
   apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
   apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                             split: if_split_asm)[1]
      apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                     split: if_split_asm)
      apply (drule(2) ucast_shiftr_2; clarsimp)
     apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
   apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
   apply (drule(2) ucast_shiftr_2; clarsimp)
   apply (drule(2) ucast_shiftr_2; clarsimp)
  apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
  apply (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def isCap_simps
                            split: if_split_asm)[1]
    apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps ucast_shiftr_3
                   split: if_split_asm)
   apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
  apply (clarsimp simp: kh0H_all_obj_def' to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
  apply (drule(2) ucast_shiftr_1; clarsimp)
  apply (drule(2) ucast_shiftr_1; clarsimp)
  done

lemma mdb_prevI:
  "m p = Some c \<Longrightarrow> m \<turnstile> mdbPrev (cteMDBNode c) \<leftarrow> p"
  by (simp add: mdb_prev_def)

lemma mdb_nextI:
  "m p = Some c \<Longrightarrow> m \<turnstile> p \<leadsto> mdbNext (cteMDBNode c)"
  by (simp add: mdb_next_unfold)

lemma s0H_valid_pspace':
  notes pteBits_def[simp] objBits_defs[simp]
  assumes "1 \<le> maxDomain"
  shows "valid_pspace' s0H_internal"
  using assms
  supply option.case_cong[cong] if_cong[cong]
  apply (clarsimp simp: valid_pspace'_def s0H_pspace_distinct' s0H_valid_objs')
  apply (intro conjI)
      apply (clarsimp simp: pspace_aligned'_def)
      apply (drule kh0H_SomeD)
      apply (elim disjE; clarsimp simp: s0_ptr_defs kh0H_all_obj_def objBitsKO_def archObjSize_def
                                        cnode_offs_range_def page_offs_range_def pt_offs_range_def
                                        irq_node_offs_range_def is_aligned_mask mask_def bit_simps
                                 split: if_splits)
     apply (clarsimp simp: pspace_canonical'_def)
     apply (drule kh0H_SomeD')
     apply (fastforce elim: dual_order.trans
                     intro: above_pptr_base_canonical
                      simp: irq_node_offs_range_def cnode_offs_range_def
                            pt_offs_range_def page_offs_range_def s0_ptr_defs)
    apply (clarsimp simp: pspace_in_kernel_mappings'_def)
    apply (clarsimp simp: kernel_mappings_def)
    apply (drule kh0H_SomeD')
    apply (fastforce elim: dual_order.trans
                     simp: s0_ptr_defs irq_node_offs_range_def cnode_offs_range_def
                           pt_offs_range_def page_offs_range_def kernel_mappings_def)
   apply (clarsimp simp: no_0_obj'_def)
   apply (rule ccontr, clarsimp)
   apply (drule kh0H_SomeD)
   apply (simp add: irq_node_offs_range_def cnode_offs_range_def
                    page_offs_range_def pt_offs_range_def s0_ptr_defs)
  apply (simp add: valid_mdb'_def)
  apply (clarsimp simp: valid_mdb_ctes_def)
  apply (intro conjI)
               apply (clarsimp simp: valid_dlist_def3)
               apply (rule conjI)
                apply (clarsimp simp: mdb_next_s0H)
                apply (subst mdb_prev_s0H)
                 apply (fastforce simp: s0_ptr_defs)
                apply simp
               apply (clarsimp simp: mdb_prev_s0H)
               apply (subst mdb_next_s0H)
                apply (fastforce simp: s0_ptr_defs)
               apply simp
              apply (clarsimp simp: no_0_def)
              apply (rule ccontr)
              apply clarsimp
              apply (drule map_to_ctes_kh0H_SomeD)
              apply (elim disjE, (clarsimp simp: irq_node_offs_range_def
                                                 cnode_offs_range_def s0_ptr_defs)+)[1]
             apply (clarsimp simp: mdb_chain_0_def)
             apply (frule map_to_ctes_kh0H_SomeD)
             apply (elim disjE)
                                apply ((erule r_into_trancl[OF next_fold], clarsimp)+)[5]
                           apply ((rule r_r_into_trancl[OF next_fold next_fold], simp+)+)[2]
                         apply ((erule r_into_trancl[OF next_fold], clarsimp)+)[3]
                      apply ((rule r_r_into_trancl[OF next_fold next_fold], simp+)+)[2]
                    apply ((erule r_into_trancl[OF next_fold], clarsimp)+)[5]
               apply (clarsimp simp: kh0H_all_obj_def Silc_cte_cte_def cnode_offs_range_def
                              split: if_split_asm)
                  apply ((rule r_r_into_trancl[OF next_fold next_fold], simp+)+)[2]
                apply (erule r_into_trancl[OF next_fold], simp)
               apply (erule r_into_trancl[OF next_fold], simp)
              apply (clarsimp simp: kh0H_all_obj_def High_cte_cte_def cnode_offs_range_def
                             split: if_split_asm)
                     apply ((erule r_into_trancl[OF next_fold], clarsimp)+)[2]
                   apply (rule trancl_into_trancl2[OF next_fold], simp+)[1]
                   apply (rule r_r_into_trancl[OF next_fold next_fold], simp+)[1]
                  apply ((erule r_into_trancl[OF next_fold], clarsimp)+)[5]
             apply (clarsimp simp: kh0H_all_obj_def Low_cte_cte_def cnode_offs_range_def
                            split: if_split_asm)
                    apply (rule trancl_into_trancl2[OF next_fold], simp+)[1]
                    apply (rule r_r_into_trancl[OF next_fold next_fold], simp+)[1]
                   apply (erule r_into_trancl[OF next_fold], simp)+
            apply (clarsimp simp: valid_badges_def)
            apply (frule_tac x=p in map_to_ctes_kh0H_SomeD)
            apply (elim disjE, (clarsimp simp: Low_cte_cte_def High_cte_cte_def Silc_cte_cte_def
                                               kh0H_all_obj_def isCap_simps
                                        split: if_split_asm)+)[1]
              apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
              apply (elim disjE, (clarsimp simp: Low_cte_cte_def High_cte_cte_def Silc_cte_cte_def
                                                 kh0H_all_obj_def isCap_simps sameRegionAs_def
                                          split: if_split_asm)+)[1]
             apply (intro conjI impI)
              apply (clarsimp simp: High_cte_cte_def kh0H_all_obj_def isCap_simps split: if_split_asm)
             apply (drule(1) sameRegion_ntfn)
             apply (clarsimp simp: High_cte_cte_def kh0H_all_obj_def isCap_simps split: if_split_asm)
             apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
             apply (elim disjE, (clarsimp simp: High_cte_cte_def Low_cte_cte_def
                                                Silc_cte_cte_def kh0H_all_obj_def
                                         split: if_split_asm)+)[1]
            apply (intro conjI impI)
             apply (clarsimp simp: Low_cte_cte_def kh0H_all_obj_def isCap_simps split: if_split_asm)
            apply (drule(1) sameRegion_ntfn)
            apply (clarsimp simp: Low_cte_cte_def kh0H_all_obj_def isCap_simps split: if_split_asm)
            apply (frule_tac x=p' in map_to_ctes_kh0H_SomeD)
            apply (elim disjE, (clarsimp simp: High_cte_cte_def Low_cte_cte_def
                                               Silc_cte_cte_def kh0H_all_obj_def
                                        split: if_split_asm)+)[1]
           apply (clarsimp simp: caps_contained'_def)
           apply (drule_tac x=p in map_to_ctes_kh0H_SomeD)
           apply (elim disjE, simp_all)[1]
             apply (clarsimp simp: Silc_cte_cte_def kh0H_all_obj_def split: if_split_asm)
            apply (clarsimp simp: High_cte_cte_def kh0H_all_obj_def split: if_split_asm)
           apply (clarsimp simp: Low_cte_cte_def kh0H_all_obj_def split: if_split_asm)
          apply (clarsimp simp: mdb_chunked_def)
          apply (frule(3) sameRegionAs_s0H)
          apply (clarsimp simp: conj_disj_distribL)
          apply (prop_tac "p \<noteq> 0 \<and> p' \<noteq> 0")
           apply (elim disjE; clarsimp simp: s0_ptr_defs)
          apply (intro conjI; clarsimp)
            apply (simp add: mdb_next_trancl_s0H)
            apply (elim disjE, simp_all)[1]
           apply (thin_tac "_ \<or> _")
           apply (clarsimp simp: mdb_next_trancl_s0H)
           apply (elim disjE)
                    apply ((clarsimp simp: is_chunk_def,
                            drule mdb_next_rtrancl_not_0_s0H, fastforce simp: s0_ptr_defs,
                            clarsimp simp: mdb_next_trancl_s0H,
                            (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def
                                                       isCap_simps kh0H_all_obj_def'
                                       , (fastforce simp: s0_ptr_defs)+)[1])+)[10]
          apply (thin_tac "_ \<or> _")
          apply (clarsimp simp: mdb_next_trancl_s0H)
          apply (elim disjE)
                   apply ((clarsimp simp: is_chunk_def,
                           drule mdb_next_rtrancl_not_0_s0H, fastforce simp: s0_ptr_defs,
                           clarsimp simp: mdb_next_trancl_s0H,
                           (elim disjE, simp_all add: sameRegionAs_def RISCV64_H.sameRegionAs_def
                                                      isCap_simps kh0H_all_obj_def'
                                      , (fastforce simp: s0_ptr_defs)+)[1])+)[10]
         apply (clarsimp simp: untyped_mdb'_def)
         apply (drule_tac x=p in map_to_ctes_kh0H_SomeD)
         apply (elim disjE, simp_all add: isCap_simps kh0H_all_obj_def')[1]
           apply ((clarsimp split: if_split_asm)+)[3]
        apply (clarsimp simp: untyped_inc'_def)
        apply (rule FalseE)
        apply (drule_tac x=p in map_to_ctes_kh0H_SomeD)
        apply (elim disjE, simp_all add: isCap_simps kh0H_all_obj_def')[1]
          apply ((clarsimp split: if_split_asm)+)[3]
       apply (clarsimp simp: valid_nullcaps_def)
       apply (drule map_to_ctes_kh0H_SomeD)
       apply (elim disjE, simp_all add: kh0H_all_obj_def' nullMDBNode_def)
         apply ((clarsimp split: if_split_asm)+)[3]
      apply (clarsimp simp: ut_revocable'_def)
      apply (drule map_to_ctes_kh0H_SomeD)
      apply (elim disjE, simp_all add: isCap_simps kh0H_all_obj_def')[1]
        apply ((clarsimp split: if_split_asm)+)[3]
     apply (clarsimp simp: class_links_def)
     apply (subst(asm) mdb_next_s0H)
      apply (drule_tac x=p' in map_to_ctes_kh0H_SomeD)
      apply (elim disjE, (clarsimp simp: s0_ptr_defs irq_node_offs_range_def cnode_offs_range_def)+)[1]
     apply (elim disjE, (clarsimp simp: kh0H_all_obj_def')+)[1]
    apply (clarsimp simp: distinct_zombies_def distinct_zombie_caps_def)
    apply (drule_tac x=ptr in map_to_ctes_kh0H_SomeD)
    apply (elim disjE, simp_all add: isCap_simps kh0H_all_obj_def')[1]
      apply ((clarsimp split: if_split_asm)+)[3]
   apply (clarsimp simp: irq_control_def)
   apply (drule map_to_ctes_kh0H_SomeD)
   apply (elim disjE, simp_all add: isCap_simps kh0H_all_obj_def')[1]
     apply ((clarsimp split: if_split_asm)+)[3]
  apply (clarsimp simp: reply_masters_rvk_fb_def ran_def)
  apply (frule map_to_ctes_kh0H_SomeD)
  apply (elim disjE, simp_all add: isCap_simps kh0H_all_obj_def')[1]
    apply ((clarsimp split: if_split_asm)+)[3]
  done

end


(* Instantiate the current, abstract domain scheduler into the
   concrete scheduler required for this example *)
axiomatization  where
  newKSDomSched: "newKSDomSchedule = [(0,0xA), (1, 0xA)]"

axiomatization where
  newKSDomainTime: "newKSDomainTime = 5"

(* kernel_data_refs is an undefined constant at the moment, and therefore
   cannot be referred to in valid_global_refs' and pspace_domain_valid.
   We use an axiomatization for the moment. *)
axiomatization  where
  kdr_valid_global_refs': "valid_global_refs' s0H_internal" and
  kdr_pspace_domain_valid: "pspace_domain_valid s0H_internal"


context begin interpretation Arch .

lemma ksArchState0H[simp]:
  "ksArchState s0H_internal = arch_state0H"
  by (simp add: s0H_internal_def)

lemma valid_arch_state_s0H:
  "valid_arch_state' s0H_internal"
  apply (clarsimp simp: valid_arch_state'_def)
  apply (intro conjI)
    apply (clarsimp simp: valid_asid_table'_def s0H_internal_def arch_state0H_def asid_bits_defs
                          asid_high_bits_of_def Low_asid_def High_asid_def mask_def s0_ptr_defs)
   apply (clarsimp simp: valid_global_pts'_def is_aligned_riscv_global_pt_ptr[simplified bit_simps]
                         arch_state0H_def page_table_at'_def typ_at'_def ko_wp_at'_def
                         bit_simps global_ptH_def pt_offs_min)
   apply (subst objBitsKO_def)
   apply (clarsimp simp: archObjSize_def bit_simps)
   apply (intro conjI)
     apply (fastforce intro: pspace_distinctD'[OF _ s0H_pspace_distinct']
                       simp: global_ptH_def pt_offs_min)
    apply (clarsimp simp: is_aligned_mask mask_def s0_ptr_defs)
    apply word_bitwise
   apply (clarsimp simp: s0_ptr_defs)
   apply word_bitwise
  apply (clarsimp simp: arch_state0H_def)
  done

lemma s0H_invs:
  assumes "1 \<le> maxDomain"
  notes pteBits_def[simp] objBits_defs[simp]
  shows "invs' s0H_internal"
  using assms
  supply option.case_cong[cong] if_cong[cong]
  supply raw_tcb_cte_cases_simps[simp] (* FIXME arch-split: legacy, try use tcb_cte_cases_neqs *)
  apply (clarsimp simp: invs'_def valid_state'_def s0H_valid_pspace')
  apply (rule conjI)
   apply (clarsimp simp: sch_act_wf_def ct_in_state'_def st_tcb_at'_def obj_at'_def
                         s0H_internal_def s0_ptrs_aligned objBitsKO_def Low_tcbH_def)
   apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct', simplified s0H_internal_def])
   apply (simp add: objBitsKO_def)
  apply (rule conjI)
   apply (clarsimp simp: sym_refs_def state_refs_of'_def refs_of'_def split: option.splits)
   apply (frule kh0H_SomeD)
   apply (elim disjE, simp_all)[1]
              apply (clarsimp simp: ntfnH_def ntfn_q_refs_of'_def)
              apply (rule conjI)
               apply (clarsimp simp: tcb_st_refs_of'_def High_tcbH_def)
              apply (clarsimp simp: objBitsKO_def s0_ptrs_aligned)
              apply (erule notE, rule pspace_distinctD''[OF _ s0H_pspace_distinct'])
              apply (simp add: objBitsKO_def)
             apply (clarsimp simp: tcb_st_refs_of'_def Low_tcbH_def)
            apply (clarsimp simp: tcb_st_refs_of'_def High_tcbH_def)
            apply (rule conjI)
             apply (clarsimp simp: ntfnH_def)
            apply (clarsimp simp: objBitsKO_def ntfnH_def)
            apply (erule impE, simp add: is_aligned_def s0_ptr_defs)
            apply (erule notE, rule pspace_distinctD''[OF _ s0H_pspace_distinct'])
            apply (simp add: objBitsKO_def ntfnH_def)
           apply (clarsimp simp: tcb_st_refs_of'_def idle_tcbH_def)
          apply (clarsimp simp: global_ptH_def)
         apply (clarsimp simp: Low_ptH_def)
        apply (clarsimp simp: High_ptH_def)
       apply (clarsimp simp: Low_pdH_def)
      apply (clarsimp simp: High_pdH_def)
     apply (clarsimp simp: Low_cte_def Low_cte'_def split: if_split_asm)
    apply (clarsimp simp: High_cte_def High_cte'_def split: if_split_asm)
   apply (clarsimp simp: Silc_cte_def Silc_cte'_def split: if_split_asm)
  apply (rule conjI)
   apply (clarsimp simp: if_live_then_nonz_cap'_def ko_wp_at'_def)
   apply (drule kh0H_SomeD)
   apply (elim disjE, simp_all add: kh0H_all_obj_def' objBitsKO_def live'_def hyp_live'_def)[1]
             apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
             apply (rule_tac x="Silc_cnode_ptr + 0x27C0" in exI)
             apply (clarsimp simp: kh0H_all_obj_def')
            apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
            apply (rule_tac x="Low_cnode_ptr + 0x20" in exI)
            apply (clarsimp simp: kh0H_all_obj_def')
           apply (clarsimp simp: ex_nonz_cap_to'_def cte_wp_at_ctes_of)
           apply (rule_tac x="High_cnode_ptr + 0x20" in exI)
           apply (clarsimp simp: kh0H_all_obj_def')
          apply (clarsimp split: if_split_asm simp: live'_def hyp_live'_def)+
  apply (rule conjI)
   apply (clarsimp simp: if_unsafe_then_cap'_def ex_cte_cap_wp_to'_def cte_wp_at_ctes_of)
   apply (frule map_to_ctes_kh0H_SomeD)
   apply (elim disjE, simp_all add: kh0H_all_obj_def')[1]
           apply (rule_tac x="Low_cnode_ptr + 0x20" in exI)
           apply (clarsimp simp: kh0H_all_obj_def' image_def)
          apply (rule_tac x="Low_cnode_ptr + 0x20" in exI)
          apply (clarsimp simp: kh0H_all_obj_def' image_def)
         apply (rule_tac x="Low_cnode_ptr + 0x20" in exI)
         apply (clarsimp simp: kh0H_all_obj_def' image_def)
        apply (rule_tac x="High_cnode_ptr + 0x20" in exI)
        apply (clarsimp simp: kh0H_all_obj_def' image_def)
       apply (rule_tac x="High_cnode_ptr + 0x20" in exI)
       apply (clarsimp simp: kh0H_all_obj_def' image_def)
      apply (rule_tac x="High_cnode_ptr + 0x20" in exI)
      apply (clarsimp simp: kh0H_all_obj_def' image_def)
     apply (rule_tac x="Silc_cnode_ptr + 0x40" in exI)
     apply (clarsimp simp: kh0H_all_obj_def' image_def to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
       apply (drule(2) ucast_shiftr_13E, rule s0_ptrs_aligned, simp)
       apply (rule_tac x="(0x27C0 >> 5)" in bexI)
        apply simp
       apply (simp add: mask_def)
      apply (drule(2) ucast_shiftr_5, rule s0_ptrs_aligned, simp)
      apply (rule_tac x=5 in bexI)
       apply simp
      apply (simp add: mask_def)
     apply (drule(2) ucast_shiftr_2, rule s0_ptrs_aligned, simp)
     apply (rule_tac x=2 in bexI)
      apply simp
     apply (simp add: mask_def)
    apply (rule_tac x="High_cnode_ptr + 0x40" in exI)
    apply (clarsimp simp: kh0H_all_obj_def' image_def to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
          apply (drule(2) ucast_shiftr_13E, rule s0_ptrs_aligned, simp)
          apply (rule_tac x="0x13E" in bexI)
           apply simp
          apply (simp add: mask_def)
         apply (drule(2) ucast_shiftr_6, rule s0_ptrs_aligned, simp)
         apply (rule_tac x=6 in bexI)
          apply simp
         apply (simp add: mask_def)
        apply (drule(2) ucast_shiftr_5, rule s0_ptrs_aligned, simp)
        apply (rule_tac x=5 in bexI)
         apply simp
        apply (simp add: mask_def)
       apply (drule(2) ucast_shiftr_4, rule s0_ptrs_aligned, simp)
       apply (rule_tac x=4 in bexI)
        apply simp
       apply (simp add: mask_def)
      apply (drule(2) ucast_shiftr_3, rule s0_ptrs_aligned, simp)
      apply (rule_tac x=3 in bexI)
       apply simp
      apply (simp add: mask_def)
     apply (drule(2) ucast_shiftr_2, rule s0_ptrs_aligned, simp)
     apply (rule_tac x=2 in bexI)
      apply simp
     apply (simp add: mask_def)
    apply (drule(2) ucast_shiftr_1, rule s0_ptrs_aligned, simp)
    apply (rule_tac x=1 in bexI)
     apply simp
    apply (simp add: mask_def)
   apply (rule_tac x="Low_cnode_ptr + 0x40" in exI)
   apply (clarsimp simp: kh0H_all_obj_def' image_def to_bl_use_of_bl the_nat_to_bl_simps split: if_split_asm)
         apply (drule(2) ucast_shiftr_13E, rule s0_ptrs_aligned, simp)
         apply (rule_tac x="0x13E" in bexI)
          apply simp
         apply (simp add: mask_def)
        apply (drule(2) ucast_shiftr_6, rule s0_ptrs_aligned, simp)
        apply (rule_tac x=6 in bexI)
         apply simp
        apply (simp add: mask_def)
       apply (drule(2) ucast_shiftr_5, rule s0_ptrs_aligned, simp)
       apply (rule_tac x=5 in bexI)
        apply simp
       apply (simp add: mask_def)
      apply (drule(2) ucast_shiftr_4, rule s0_ptrs_aligned, simp)
      apply (rule_tac x=4 in bexI)
       apply simp
      apply (simp add: mask_def)
     apply (drule(2) ucast_shiftr_3, rule s0_ptrs_aligned, simp)
     apply (rule_tac x=3 in bexI)
      apply simp
     apply (simp add: mask_def)
    apply (drule(2) ucast_shiftr_2, rule s0_ptrs_aligned, simp)
    apply (rule_tac x=2 in bexI)
     apply simp
    apply (simp add: mask_def)
   apply (drule(2) ucast_shiftr_1, rule s0_ptrs_aligned, simp)
   apply (rule_tac x=1 in bexI)
    apply simp
   apply (simp add: mask_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def objBitsKO_def idle_tcb'_def)
   apply (clarsimp simp: s0H_internal_def s0_ptrs_aligned idle_tcbH_def)
   apply (rule conjI)
    apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct', simplified s0H_internal_def])
    apply (simp add: objBitsKO_def)
   apply (clarsimp simp: idle_tcb_ptr_def idle_thread_ptr_def)
  apply (rule conjI)
   apply (clarsimp simp: kdr_valid_global_refs') (* use axiomatization for now *)
  apply (rule conjI)
   apply (clarsimp simp: valid_arch_state_s0H)
  apply (rule conjI)
   apply (clarsimp simp: valid_irq_node'_def)
   apply (rule conjI)
    apply (clarsimp simp: s0H_internal_def is_aligned_def s0_ptr_defs word_size)
   apply (clarsimp simp: obj_at'_def objBitsKO_def s0H_internal_def
                         shiftl_t2n[where n=4, simplified, symmetric])
   apply (rule conjI)
    apply (rule is_aligned_add)
     apply (simp add: is_aligned_def s0_ptr_defs)
    apply (rule is_aligned_shift)
   apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct', simplified s0H_internal_def])
   apply (simp add: objBitsKO_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_irq_handlers'_def cteCaps_of_def ran_def)
   apply (drule_tac map_to_ctes_kh0H_SomeD)
   apply (elim disjE, simp_all add: kh0H_all_obj_def')[1]
     apply ((clarsimp split: if_split_asm)+)[3]
  apply (rule conjI)
   apply (clarsimp simp: valid_irq_states'_def s0H_internal_def machine_state0_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_machine_state'_def s0H_internal_def machine_state0_def)
  apply (rule conjI)
   apply (clarsimp simp: irqs_masked'_def s0H_internal_def maxIRQ_def timer_irq_def irqInvalid_def)
  apply (rule conjI)
   apply (clarsimp simp: sym_heap_def opt_map_def projectKOs split: option.splits)
   using kh0H_dom_tcb
   apply (fastforce simp: kh0H_obj_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_sched_pointers_def opt_map_def projectKOs split: option.splits)
   using kh0H_dom_tcb
   apply (fastforce simp: kh0H_obj_def)
  apply (rule conjI)
   apply (clarsimp simp: valid_bitmaps_def valid_bitmapQ_def bitmapQ_def s0H_internal_def
                         tcbQueueEmpty_def bitmapQ_no_L1_orphans_def bitmapQ_no_L2_orphans_def)
  apply (rule conjI)
   apply (clarsimp simp: ct_not_inQ_def obj_at'_def objBitsKO_def
                         s0H_internal_def s0_ptrs_aligned Low_tcbH_def)
   apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct', simplified s0H_internal_def])
   apply (simp add: objBitsKO_def)
  apply (rule conjI)
   apply (clarsimp simp: ct_idle_or_in_cur_domain'_def obj_at'_def tcb_in_cur_domain'_def
                         s0H_internal_def Low_tcbH_def Low_domain_def objBitsKO_def s0_ptrs_aligned)
   apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct', simplified s0H_internal_def])
   apply (simp add: objBitsKO_def)
  apply (rule conjI)
   apply (clarsimp simp: kdr_pspace_domain_valid) (* use axiomatization for now *)
  apply (clarsimp simp: s0H_internal_def cteCaps_of_def untyped_ranges_zero_inv_def
                        dschDomain_def dschLength_def)
  apply (clarsimp simp: newKernelState_def newKSDomSched)
  apply (clarsimp simp: cur_tcb'_def obj_at'_def  s0H_internal_def objBitsKO_def s0_ptrs_aligned)
  apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct', simplified s0H_internal_def])
  apply (simp add: objBitsKO_def)
  done

lemma kh0_pspace_dom:
  "pspace_dom kh0 = {idle_tcb_ptr, High_tcb_ptr, Low_tcb_ptr,
                     High_pool_ptr, Low_pool_ptr, irq_cnode_ptr, ntfn_ptr} \<union>
                    irq_node_offs_range \<union>
                    page_offs_range shared_page_ptr_virt \<union>
                    cnode_offs_range Silc_cnode_ptr \<union>
                    cnode_offs_range High_cnode_ptr \<union>
                    cnode_offs_range Low_cnode_ptr \<union>
                    pt_offs_range riscv_global_pt_ptr \<union>
                    pt_offs_range High_pd_ptr \<union>
                    pt_offs_range Low_pd_ptr \<union>
                    pt_offs_range High_pt_ptr \<union>
                    pt_offs_range Low_pt_ptr"
  apply (rule equalityI)
   apply (simp add: dom_def pspace_dom_def)
   apply clarsimp
   apply (clarsimp simp: kh0_def obj_relation_cuts_def page_offs_in_range pt_offs_in_range
                         cnode_offs_in_range irq_node_offs_in_range s0_ptrs_aligned bit_simps
                         kh0_obj_def cte_map_def' caps_dom_length_10
                   dest!: less_0x200_exists_ucast split: if_split_asm)
  apply (clarsimp simp: pspace_dom_def dom_def)
  apply (rule conjI)
   apply (rule_tac x=idle_tcb_ptr in exI)
   apply (clarsimp simp: kh0_def kh0_obj_def s0_ptr_defs image_def)
  apply (rule conjI)
   apply (rule_tac x=High_tcb_ptr in exI)
   apply (clarsimp simp: kh0_def kh0_obj_def s0_ptr_defs image_def)
  apply (rule conjI)
   apply (rule_tac x=Low_tcb_ptr in exI)
   apply (clarsimp simp: kh0_def kh0_obj_def s0_ptr_defs image_def)
  apply (rule conjI)
   apply (rule_tac x=High_pool_ptr in exI)
   apply (clarsimp simp: kh0_def kh0_obj_def s0_ptr_defs image_def)
  apply (rule conjI)
   apply (rule_tac x=Low_pool_ptr in exI)
   apply (clarsimp simp: kh0_def kh0_obj_def s0_ptr_defs image_def)
  apply (rule conjI)
   apply (rule_tac x=irq_cnode_ptr in exI)
   apply (clarsimp simp: kh0_def kh0_obj_def s0_ptr_defs image_def cte_map_def)
  apply (rule conjI)
   apply (rule_tac x=ntfn_ptr in exI)
   apply (clarsimp simp: kh0_def kh0_obj_def s0_ptr_defs image_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=x in exI)
   apply (drule offs_range_correct)
   apply clarsimp
   apply (force simp: kh0_def kh0_obj_def image_def cte_map_def')
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=shared_page_ptr_virt in exI)
   apply (drule offs_range_correct)
   apply (clarsimp simp: kh0_def kh0_obj_def image_def s0_ptr_defs cte_map_def' dom_caps bit_simps)
   apply (rule_tac x="UCAST (9 \<rightarrow> 64) y" in exI)
   apply clarsimp
   apply word_bitwise
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=Silc_cnode_ptr in exI)
   apply (drule offs_range_correct)
   apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs cte_map_def' dom_caps)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=High_cnode_ptr in exI)
   apply (drule offs_range_correct)
   apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs cte_map_def' dom_caps)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=Low_cnode_ptr in exI)
   apply (drule offs_range_correct)
   apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs cte_map_def' dom_caps)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=riscv_global_pt_ptr in exI)
   apply (drule offs_range_correct)
   apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs bit_simps)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=High_pd_ptr in exI)
   apply (drule offs_range_correct)
   apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs bit_simps)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=Low_pd_ptr in exI)
   apply (drule offs_range_correct)
   apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs bit_simps)
  apply (rule conjI)
   apply clarsimp
   apply (rule_tac x=High_pt_ptr in exI)
   apply (drule offs_range_correct)
   apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs bit_simps)
  apply clarsimp
  apply (rule_tac x=Low_pt_ptr in exI)
  apply (drule offs_range_correct)
  apply (force simp: kh0_def kh0_obj_def image_def s0_ptr_defs bit_simps)
  done


lemma shiftl_shiftr_3_pt_index[simp]:
  "ucast (((ucast (x :: pt_index) << 3) :: obj_ref) >> 3) = x"
  apply (subst shiftl_shiftr_id)
    apply simp
   apply (cut_tac ucast_less[where x=x])
    apply (erule less_trans)
    apply simp
   apply simp
  apply (rule ucast_ucast_id)
  apply simp
  done

lemma mult_shiftr_id[simp]:
  "length x = 10 \<Longrightarrow> of_bl x * (0x20 :: obj_ref) >> 5 = of_bl x"
  apply (simp add: shiftl_t2n[symmetric, where n=5, simplified mult.commute, simplified] )
  apply (subst shiftl_shiftr_id)
    apply simp
   apply (rule less_trans)
    apply (rule of_bl_length_less)
     apply assumption
    apply simp
   apply simp
  apply simp
  done

lemma to_bl_ucast_of_bl[simp]:
  "length x = 10 \<Longrightarrow> to_bl ((ucast (of_bl x :: obj_ref)) :: 10 word) = x"
  apply (subst ucast_of_bl_up)
   apply (simp add: word_size)
  apply (simp add: word_rep_drop)
  done

lemma is_aligned_shiftr_3[simp]:
  "is_aligned (riscv_global_pt_ptr + (n << 3)) 3"
  "is_aligned (High_pd_ptr + (n << 3)) 3"
  "is_aligned (Low_pd_ptr + (n << 3)) 3"
  "is_aligned (High_pt_ptr + (n << 3)) 3"
  "is_aligned (Low_pt_ptr + (n << 3)) 3"
      apply (rule is_aligned_add[OF is_aligned_weaken[OF s0_ptrs_aligned(1), where y=3, simplified bit_simps]]; fastforce)
     apply (rule is_aligned_add[OF is_aligned_weaken[OF s0_ptrs_aligned(2), where y=3, simplified bit_simps]]; fastforce)
    apply (rule is_aligned_add[OF is_aligned_weaken[OF s0_ptrs_aligned(3), where y=3, simplified bit_simps]]; fastforce)
   apply (rule is_aligned_add[OF is_aligned_weaken[OF s0_ptrs_aligned(4), where y=3, simplified bit_simps]]; fastforce)
  apply (rule is_aligned_add[OF is_aligned_weaken[OF s0_ptrs_aligned(5), where y=3, simplified bit_simps]]; fastforce)
  done

lemma s0_pspace_rel:
  "pspace_relation (kheap s0_internal) kh0H"
  apply (simp add: pspace_relation_def s0_internal_def s0H_internal_def kh0H_dom kh0_pspace_dom)
  apply clarsimp
  apply (drule kh0_SomeD)
  apply (elim disjE)
                  apply (clarsimp simp: kh0_obj_def bit_simps dest!: less_0x200_exists_ucast)
                 defer
                 apply ((clarsimp simp: kh0_obj_def kh0H_obj_def bit_simps word_bits_def
                                        fault_rel_optionation_def tcb_relation_cut_def
                                        tcb_relation_def arch_tcb_relation_def the_nat_to_bl_simps
                             split del: if_split)+)[3]
              prefer 13
              apply ((clarsimp simp: kh0_obj_def kh0H_all_obj_def bit_simps add.commute
                                     pt_offs_max pt_offs_min pte_relation_def
                          split del: if_split,
                      clarsimp simp: s0_ptr_defs shared_page_ptr_phys_def addrFromPPtr_def pptrBaseOffset_def paddrBase_def
                                     vmrights_map_def vm_read_only_def vm_read_write_def
                                     kh0_obj_def kh0H_all_obj_def elf_index_value,
                      (clarsimp simp: bit_simps mask_def)?)+)[5]
         apply (clarsimp simp: kh0_obj_def kh0H_obj_def well_formed_cnode_n_def
                               cte_relation_def cte_map_def bit_simps)
        apply (clarsimp simp: kh0H_obj_def bit_simps ntfn_def other_obj_relation_def ntfn_relation_def)
       defer
       apply ((clarsimp simp: kh0_obj_def kh0H_obj_def other_obj_relation_def
                              asid_pool_relation_def comp_def inv_into_def2, rule ext,
               clarsimp simp: asid_low_bits_of_def asid_low_bits_def High_asid_def,
               word_bitwise, fastforce)+)[2]
     apply (clarsimp simp: kh0H_obj_def kh0_obj_def cte_relation_def cte_map_def')
     apply (cut_tac dom_caps(2))[1]
     apply (frule_tac m=High_caps in domI)
     apply (cut_tac x=y in cnode_offs_in_range(2), simp)
     apply (clarsimp simp: cnode_offs_range_def kh0H_all_obj_def High_caps_def
                           the_nat_to_bl_simps vmrights_map_def vm_read_only_def
                    split: if_split_asm)
    apply (clarsimp simp: kh0H_obj_def kh0_obj_def cte_relation_def cte_map_def')
    apply (cut_tac dom_caps(3))[1]
    apply (frule_tac m=Low_caps in domI)
    apply (cut_tac x=y in cnode_offs_in_range(1), simp)
    apply (clarsimp simp: cnode_offs_range_def kh0H_all_obj_def Low_caps_def
                          the_nat_to_bl_simps vmrights_map_def vm_read_write_def
                   split: if_split_asm)
   apply (fastforce simp: kh0H_obj_def cte_map_def cte_relation_def well_formed_cnode_n_def
                    dest: irq_node_offs_range_correct split: if_split_asm)
  apply (clarsimp simp: kh0H_obj_def kh0_obj_def cte_relation_def cte_map_def')
  apply (cut_tac dom_caps(1))[1]
  apply (frule_tac m=Silc_caps in domI)
  apply (cut_tac x=y in cnode_offs_in_range(3), simp)
  apply (clarsimp simp: cnode_offs_range_def kh0H_all_obj_def Silc_caps_def
                        the_nat_to_bl_simps vmrights_map_def vm_read_only_def
                 split: if_split_asm)
  done

lemma subtree_node_Some:
  "m \<turnstile> a \<rightarrow> b \<Longrightarrow> m a \<noteq> None"
  by (erule subtree.cases) (auto simp: parentOf_def)

lemma s0_srel:
  "1 \<le> maxDomain \<Longrightarrow> (s0_internal, s0H_internal) \<in> state_relation"
  apply (simp add: state_relation_def)
  apply (intro conjI)
                  apply (simp add: s0_pspace_rel)
                 apply (simp add: s0_internal_def exst0_def s0H_internal_def sched_act_relation_def)
                apply (clarsimp simp: s0_internal_def exst0_def s0H_internal_def
                                      ready_queues_relation_def ready_queue_relation_def
                                      list_queue_relation_def queue_end_valid_def
                                      prev_queue_head_def inQ_def tcbQueueEmpty_def
                                      projectKOs opt_map_def opt_pred_def
                               split: option.splits)
                using kh0H_dom_tcb
                apply (fastforce simp: kh0H_obj_def)
               apply (clarsimp simp: s0_internal_def exst0_def s0H_internal_def ghost_relation_def)
               apply (rule conjI)
                apply (fastforce simp: kh0_def kh0_obj_def dest: kh0_SomeD)
               apply clarsimp
               apply (rule conjI)
                apply clarsimp
                apply (rule iffI)
                 apply clarsimp
                 apply (drule kh0_SomeD)
                 apply (clarsimp simp: irq_node_offs_in_range)
                apply (fastforce simp: kh0_def well_formed_cnode_n_def empty_cnode_def dom_def)
               apply clarsimp
               apply (clarsimp simp: s0_ptr_defs)
               apply (subgoal_tac "a \<notin> irq_node_offs_range")
                prefer 2
                apply (clarsimp simp: irq_node_offs_range_def s0_ptr_defs)
                apply (erule_tac x="ucast (a - 0xFFFFFFC000003000 >> 5)" in allE)
                apply (subst (asm) ucast_ucast_len)
                 apply (rule shiftr_less_t2n)
                 apply (rule word_less_sub_right)
                  apply (erule dual_order.strict_trans[rotated], clarsimp)
                 apply clarsimp
                apply (simp add: shiftr_shiftl1)
                apply (subst(asm) is_aligned_neg_mask_eq)
                 apply (rule aligned_sub_aligned[where n=5])
                   apply simp
                  apply (simp add: is_aligned_def)
                 apply simp
                apply simp
               apply (intro conjI impI)
                   apply clarsimp
                   apply (rule iffI)
                    apply clarsimp
                    apply (drule kh0_SomeD)
                    apply (clarsimp simp: s0_ptr_defs kh0_obj_def)
                   apply (fastforce simp: kh0_def kh0_obj_def dom_def s0_ptr_defs Low_caps_def
                                          well_formed_cnode_n_def empty_cnode_def)
                  apply clarsimp
                  apply (rule iffI)
                   apply clarsimp
                   apply (drule kh0_SomeD)
                   apply (clarsimp simp: s0_ptr_defs kh0_obj_def)
                  apply (fastforce simp: kh0_def kh0_obj_def dom_def s0_ptr_defs High_caps_def
                                         well_formed_cnode_n_def empty_cnode_def)
                 apply clarsimp
                 apply (rule iffI)
                  apply clarsimp
                  apply (drule kh0_SomeD)
                  apply (clarsimp simp: s0_ptr_defs kh0_obj_def)
                 apply (fastforce simp: kh0_def kh0_obj_def dom_def s0_ptr_defs Silc_caps_def
                                        well_formed_cnode_n_def empty_cnode_def)
                apply clarsimp
                apply (rule iffI)
                 apply clarsimp
                 apply (drule kh0_SomeD)
                 apply (clarsimp simp: s0_ptr_defs kh0_obj_def)
                apply (fastforce simp: kh0_def kh0_obj_def dom_def s0_ptr_defs Silc_caps_def
                                       well_formed_cnode_n_def empty_cnode_def)
               apply clarsimp
               apply (drule kh0_SomeD)
               apply (clarsimp simp: s0_ptr_defs kh0_obj_def)
              apply (clarsimp simp: s0H_internal_def cdt_relation_def)
              apply (clarsimp simp: descendants_of'_def)
              apply (frule subtree_parent)
              apply (drule subtree_mdb_next)
              apply (case_tac "x = 0")
               apply (cut_tac s0H_valid_pspace')
                apply (simp add: valid_pspace'_def valid_mdb'_def valid_mdb_ctes_def
                                 parentOf_def isMDBParentOf_def kh0H_all_obj_def')
               apply simp
              apply (clarsimp simp: mdb_next_trancl_s0H)
              apply (elim disjE, (clarsimp simp: parentOf_def isMDBParentOf_def kh0H_all_obj_def')+)[1]
             apply (clarsimp simp: cdt_list_relation_def s0_internal_def exst0_def split: option.splits)
             apply (clarsimp simp: next_slot_def)
             apply (cut_tac p="(a, b)" and t="(const [])" and m="Map.empty" in next_not_child_NoneI)
                apply fastforce
               apply (simp add: next_sib_def)
              apply (simp add: finite_depth_def)
             apply simp
            apply (clarsimp simp: revokable_relation_def)
            apply (clarsimp simp: null_filter_def split: if_split_asm)
            apply (drule s0_caps_of_state)
            apply clarsimp
            apply (elim disjE)
                                  apply (clarsimp simp: s0H_internal_def s0_internal_def
                                                        cte_map_def' kh0H_all_obj_def'
                                                 split: if_split_asm)+
                 apply (clarsimp simp: tcb_cnode_index_def ucast_bl[symmetric]
                                       Low_tcb_cte_def Low_tcbH_def High_tcb_cte_def High_tcbH_def)
                apply ((clarsimp simp: cte_map_def' s0H_internal_def s0_internal_def,
                        clarsimp simp: tcb_cnode_index_def ucast_bl[symmetric]
                                       Low_tcb_cte_def Low_tcbH_def High_tcb_cte_def High_tcbH_def)+)[5]
           apply (clarsimp simp: s0_internal_def s0H_internal_def arch_state0_def arch_state0H_def
                                 arch_state_relation_def asid_high_bits_of_def asid_low_bits_def
                                 High_asid_def Low_asid_def max_pt_level_def2 maxPTLevel_def comp_def
                          split: if_splits)
           apply safe
            apply (rule ext)
            apply clarsimp
            apply (word_bitwise, fastforce)
           apply (rule ext)
           apply (clarsimp split: if_splits)
           subgoal for level
           by (induct level; simp only: size_maxPTLevel[simplified maxPTLevel_def, symmetric]
                                        bit0.size_inj max_pt_level_def2)
          apply (clarsimp simp: s0_internal_def s0H_internal_def exst0_def cte_level_bits_def
                                interrupt_state_relation_def irq_state_relation_def)
         apply (clarsimp simp: s0_internal_def exst0_def s0H_internal_def)+
  done

definition
  "s0H \<equiv> ((if ct_idle' s0H_internal then idle_context s0_internal else s0_context, s0H_internal), KernelExit)"

lemma step_restrict_s0:
  "1 \<le> maxDomain \<Longrightarrow> step_restrict s0"
  supply option.case_cong[cong] if_cong[cong]
  apply (clarsimp simp: step_restrict_def has_srel_state_def)
  apply (rule_tac x="fst (fst s0H)" in exI)
  apply (rule_tac x="snd (fst s0H)" in exI)
  apply (rule_tac x="snd s0H" in exI)
  apply (simp add: s0H_def lift_fst_rel_def lift_snd_rel_def s0_srel s0_def split del: if_split)
  apply (rule conjI)
   apply (clarsimp split: if_split_asm)
   apply (rule conjI)
    apply clarsimp
    apply (frule ct_idle'_related[OF s0_srel s0H_invs]; solves simp)
   apply clarsimp
   apply (drule ct_idle_related[OF s0_srel]; simp)
  apply (clarsimp simp: full_invs_if'_def s0H_invs)
  apply (rule conjI)
   apply (simp only: ex_abs_def)
   apply (rule_tac x="s0_internal" in exI)
   apply (simp only: einvs_s0 s0_srel)
  apply (simp add: s0H_internal_def valid_domain_list'_def)
  apply (clarsimp simp: ct_in_state'_def st_tcb_at'_def obj_at'_def
                        s0H_internal_def objBits_simps' s0_ptrs_aligned Low_tcbH_def)
  apply (rule pspace_distinctD''[OF _ s0H_pspace_distinct', simplified s0H_internal_def])
  apply (simp add: objBits_simps')
  done

lemma Sys1_valid_initial_state_noenabled:
  assumes domains: "1 \<le> maxDomain"
  assumes utf_det: "\<forall>pl pr pxn tc ms s. det_inv InUserMode tc s \<and> einvs s \<and> context_matches_state pl pr pxn ms s \<and> ct_running s
                                        \<longrightarrow> (\<exists>x. utf (cur_thread s) pl pr pxn (tc, ms) = {x})"
  assumes utf_non_empty: "\<forall>t pl pr pxn tc ms. utf t pl pr pxn (tc, ms) \<noteq> {}"
  assumes utf_non_interrupt: "\<forall>t pl pr pxn tc ms e f g. (e,f,g) \<in> utf t pl pr pxn (tc, ms) \<longrightarrow> e \<noteq> Some Interrupt"
  assumes det_inv_invariant: "invariant_over_ADT_if det_inv utf"
  assumes det_inv_s0: "det_inv KernelExit (cur_context s0_internal) s0_internal"
  shows "valid_initial_state_noenabled det_inv utf s0_internal Sys1PAS timer_irq s0_context"
  by (rule Sys1_valid_initial_state_noenabled[OF step_restrict_s0 utf_det utf_non_empty
                                                 utf_non_interrupt det_inv_invariant det_inv_s0
                                                 ],
      rule domains)

end

end
