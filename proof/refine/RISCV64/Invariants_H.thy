(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory Invariants_H
imports
  LevityCatch
  "AInvs.Deterministic_AI"
  "AInvs.AInvs"
  "Lib.AddUpdSimps"
begin

context Arch begin

lemmas haskell_crunch_def [crunch_def] =
  deriveCap_def finaliseCap_def
  hasCancelSendRights_def sameRegionAs_def isPhysicalCap_def
  sameObjectAs_def updateCapData_def maskCapRights_def
  createObject_def capUntypedPtr_def capUntypedSize_def
  performInvocation_def decodeInvocation_def

context begin global_naming global
requalify_facts
  Retype_H.deriveCap_def Retype_H.finaliseCap_def
  Retype_H.hasCancelSendRights_def Retype_H.sameRegionAs_def Retype_H.isPhysicalCap_def
  Retype_H.sameObjectAs_def Retype_H.updateCapData_def Retype_H.maskCapRights_def
  Retype_H.createObject_def Retype_H.capUntypedPtr_def Retype_H.capUntypedSize_def
  Retype_H.performInvocation_def Retype_H.decodeInvocation_def
end

end

\<comment> \<open>---------------------------------------------------------------------------\<close>

section "Invariants on Executable Spec"

(* FIXME RISCV: move up, use everywhere *)
abbreviation ptr_range :: "obj_ref \<Rightarrow> nat \<Rightarrow> machine_word set" where
  "ptr_range p n \<equiv> {p .. p + mask n}"

context begin interpretation Arch .

definition ps_clear :: "obj_ref \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ps_clear p n s \<equiv> (ptr_range p n - {p}) \<inter> dom (ksPSpace s) = {}"

definition pspace_no_overlap' :: "obj_ref \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pspace_no_overlap' ptr bits \<equiv>
     \<lambda>s. \<forall>x ko. ksPSpace s x = Some ko \<longrightarrow>
                (ptr_range x (objBitsKO ko)) \<inter> {ptr .. (ptr && ~~ mask bits) + mask bits} = {}"

definition ko_wp_at' :: "(kernel_object \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ko_wp_at' P p s \<equiv> \<exists>ko. ksPSpace s p = Some ko \<and> is_aligned p (objBitsKO ko) \<and> P ko \<and>
                           ps_clear p (objBitsKO ko) s"

definition obj_at' :: "('a::pspace_storable \<Rightarrow> bool) \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  obj_at'_real_def:
  "obj_at' P p s \<equiv> ko_wp_at' (\<lambda>ko. \<exists>obj. projectKO_opt ko = Some obj \<and> P obj) p s"

definition typ_at' :: "kernel_object_type \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "typ_at' T \<equiv> ko_wp_at' (\<lambda>ko. koTypeOf ko = T)"

abbreviation ep_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ep_at' \<equiv> obj_at' ((\<lambda>x. True) :: endpoint \<Rightarrow> bool)"

abbreviation ntfn_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ntfn_at' \<equiv> obj_at' ((\<lambda>x. True) :: notification \<Rightarrow> bool)"

abbreviation tcb_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "tcb_at' \<equiv> obj_at' ((\<lambda>x. True) :: tcb \<Rightarrow> bool)"

abbreviation real_cte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "real_cte_at' \<equiv> obj_at' ((\<lambda>x. True) :: cte \<Rightarrow> bool)"

abbreviation ko_at' :: "'a::pspace_storable \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ko_at' v \<equiv> obj_at' (\<lambda>k. k = v)"

abbreviation pte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pte_at' \<equiv> typ_at' (ArchT PTET)"

end

record itcb' =
  itcbState             :: thread_state
  itcbFaultHandler      :: cptr
  itcbIPCBuffer         :: vptr
  itcbBoundNotification :: "machine_word option"
  itcbPriority          :: priority
  itcbFault             :: "fault option"
  itcbTimeSlice         :: nat
  itcbMCP               :: priority

definition tcb_to_itcb' :: "tcb \<Rightarrow> itcb'" where
  "tcb_to_itcb' tcb \<equiv> \<lparr> itcbState             = tcbState tcb,
                        itcbFaultHandler      = tcbFaultHandler tcb,
                        itcbIPCBuffer         = tcbIPCBuffer tcb,
                        itcbBoundNotification = tcbBoundNotification tcb,
                        itcbPriority          = tcbPriority tcb,
                        itcbFault             = tcbFault tcb,
                        itcbTimeSlice         = tcbTimeSlice tcb,
                        itcbMCP               = tcbMCP tcb\<rparr>"

lemma itcb_simps[simp]:
  "itcbState (tcb_to_itcb' tcb) = tcbState tcb"
  "itcbFaultHandler (tcb_to_itcb' tcb) = tcbFaultHandler tcb"
  "itcbIPCBuffer (tcb_to_itcb' tcb) = tcbIPCBuffer tcb"
  "itcbBoundNotification (tcb_to_itcb' tcb) = tcbBoundNotification tcb"
  "itcbPriority (tcb_to_itcb' tcb) = tcbPriority tcb"
  "itcbFault (tcb_to_itcb' tcb) = tcbFault tcb"
  "itcbTimeSlice (tcb_to_itcb' tcb) = tcbTimeSlice tcb"
  "itcbMCP (tcb_to_itcb' tcb) = tcbMCP tcb"
  by (auto simp: tcb_to_itcb'_def)

definition pred_tcb_at' :: "(itcb' \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> machine_word \<Rightarrow> kernel_state \<Rightarrow> bool"
  where
  "pred_tcb_at' proj test \<equiv> obj_at' (\<lambda>ko. test (proj (tcb_to_itcb' ko)))"

abbreviation st_tcb_at' :: "(thread_state \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "st_tcb_at' \<equiv> pred_tcb_at' itcbState"

abbreviation bound_tcb_at' :: "(obj_ref option \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "bound_tcb_at' \<equiv> pred_tcb_at' itcbBoundNotification"

abbreviation mcpriority_tcb_at' :: "(priority \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "mcpriority_tcb_at' \<equiv> pred_tcb_at' itcbMCP"

lemma st_tcb_at'_def:
  "st_tcb_at' test \<equiv> obj_at' (test \<circ> tcbState)"
  by (simp add: pred_tcb_at'_def o_def)

text \<open> cte with property at \<close>
definition cte_wp_at' :: "(cte \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "cte_wp_at' P p s \<equiv> \<exists>cte::cte. fst (getObject p s) = {(cte,s)} \<and> P cte"

abbreviation cte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "cte_at' \<equiv> cte_wp_at' \<top>"

definition tcb_cte_cases :: "machine_word \<rightharpoonup> ((tcb \<Rightarrow> cte) \<times> ((cte \<Rightarrow> cte) \<Rightarrow> tcb \<Rightarrow> tcb))" where
 "tcb_cte_cases \<equiv> [ 0 << cteSizeBits \<mapsto> (tcbCTable, tcbCTable_update),
                    1 << cteSizeBits \<mapsto> (tcbVTable, tcbVTable_update),
                    2 << cteSizeBits \<mapsto> (tcbReply, tcbReply_update),
                    3 << cteSizeBits \<mapsto> (tcbCaller, tcbCaller_update),
                    4 << cteSizeBits \<mapsto> (tcbIPCBufferFrame, tcbIPCBufferFrame_update) ]"

definition max_ipc_words :: machine_word where
  "max_ipc_words \<equiv> capTransferDataSize + msgMaxLength + msgMaxExtraCaps + 2"

definition tcb_st_refs_of' :: "thread_state \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_st_refs_of' st \<equiv> case st of
     (BlockedOnReceive x _)     => {(x, TCBBlockedRecv)}
   | (BlockedOnSend x _ _ _ _)  => {(x, TCBBlockedSend)}
   | (BlockedOnNotification x)  => {(x, TCBSignal)}
   | _                          => {}"

definition ep_q_refs_of' :: "endpoint \<Rightarrow> (obj_ref \<times> reftype) set" where
  "ep_q_refs_of' ep \<equiv> case ep of
     IdleEP     => {}
   | (RecvEP q) => set q \<times> {EPRecv}
   | (SendEP q) => set q \<times> {EPSend}"

definition ntfn_q_refs_of' :: "Structures_H.ntfn \<Rightarrow> (obj_ref \<times> reftype) set" where
  "ntfn_q_refs_of' ntfn \<equiv> case ntfn of
     IdleNtfn        => {}
   | (WaitingNtfn q) => set q \<times> {NTFNSignal}
   | (ActiveNtfn b)  => {}"

definition ntfn_bound_refs' :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "ntfn_bound_refs' t \<equiv> set_option t \<times> {NTFNBound}"

definition tcb_bound_refs' :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set" where
  "tcb_bound_refs' a \<equiv> set_option a \<times> {TCBBound}"

definition refs_of' :: "kernel_object \<Rightarrow> (obj_ref \<times> reftype) set" where
  "refs_of' ko \<equiv> case ko of
     (KOTCB tcb)           => tcb_st_refs_of' (tcbState tcb) \<union> tcb_bound_refs' (tcbBoundNotification tcb)
   | (KOEndpoint ep)       => ep_q_refs_of' ep
   | (KONotification ntfn) => ntfn_q_refs_of' (ntfnObj ntfn) \<union> ntfn_bound_refs' (ntfnBoundTCB ntfn)
   | _                     => {}"

definition state_refs_of' :: "kernel_state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set" where
  "state_refs_of' s \<equiv> \<lambda>x.
     case ksPSpace s x of
       None \<Rightarrow> {}
     | Some ko \<Rightarrow> if is_aligned x (objBitsKO ko) \<and> ps_clear x (objBitsKO ko) s
                  then refs_of' ko else {}"

fun live' :: "kernel_object \<Rightarrow> bool" where
  "live' (KOTCB tcb) =
     (bound (tcbBoundNotification tcb) \<or>
     (tcbState tcb \<noteq> Inactive \<and> tcbState tcb \<noteq> IdleThreadState) \<or>  tcbQueued tcb)"
| "live' (KOEndpoint ep)       = (ep \<noteq> IdleEP)"
| "live' (KONotification ntfn) = (bound (ntfnBoundTCB ntfn) \<or> (\<exists>ts. ntfnObj ntfn = WaitingNtfn ts))"
| "live' _                     = False"

fun zobj_refs' :: "capability \<Rightarrow> obj_ref set" where
  "zobj_refs' (EndpointCap r _ _ _ _ _)  = {r}"
| "zobj_refs' (NotificationCap r _ _ _)  = {r}"
| "zobj_refs' (ThreadCap r)              = {r}"
| "zobj_refs' _                          = {}"

definition ex_nonz_cap_to' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ex_nonz_cap_to' ref \<equiv> \<lambda>s. \<exists>cref. cte_wp_at' (\<lambda>c. ref \<in> zobj_refs' (cteCap c)) cref s"

definition if_live_then_nonz_cap' :: "kernel_state \<Rightarrow> bool" where
  "if_live_then_nonz_cap' s \<equiv> \<forall>ptr. ko_wp_at' live' ptr s \<longrightarrow> ex_nonz_cap_to' ptr s"

fun cte_refs' :: "capability \<Rightarrow> obj_ref \<Rightarrow> obj_ref set" where
  "cte_refs' (CNodeCap ref bits _ _) x = (\<lambda>x. ref + x << cteSizeBits) ` {0 .. mask bits}"
| "cte_refs' (ThreadCap ref) x         = (\<lambda>x. ref + x) ` dom tcb_cte_cases"
| "cte_refs' (Zombie ref _ n) x        = (\<lambda>x. ref + x << cteSizeBits) ` {0 ..< of_nat n}"
| "cte_refs' (IRQHandlerCap irq) x     = {x + ucast irq << cteSizeBits}"
| "cte_refs' _ _                       = {}"


abbreviation irq_node' :: "kernel_state \<Rightarrow> obj_ref" where
  "irq_node' s \<equiv> intStateIRQNode (ksInterruptState s)"

definition ex_cte_cap_wp_to' :: "(capability \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ex_cte_cap_wp_to' P ptr \<equiv>
     \<lambda>s. \<exists>cref. cte_wp_at' (\<lambda>c. P (cteCap c) \<and> ptr \<in> cte_refs' (cteCap c) (irq_node' s)) cref s"

abbreviation ex_cte_cap_to' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ex_cte_cap_to' \<equiv> ex_cte_cap_wp_to' \<top>"

definition if_unsafe_then_cap' :: "kernel_state \<Rightarrow> bool" where
  "if_unsafe_then_cap' s \<equiv>
     \<forall>cref. cte_wp_at' (\<lambda>c. cteCap c \<noteq> NullCap) cref s \<longrightarrow> ex_cte_cap_to' cref s"


section "Valid caps and objects (design spec)"

context begin interpretation Arch .

primrec acapBits :: "arch_capability \<Rightarrow> nat" where
  "acapBits (ASIDPoolCap _ _)     = asidLowBits + word_size_bits"
| "acapBits ASIDControlCap        = asidHighBits + word_size_bits"
| "acapBits (FrameCap _ _ sz _ _) = pageBitsForSize sz"
| "acapBits (PageTableCap _ _)    = table_size"

end

primrec zBits :: "zombie_type \<Rightarrow> nat" where
  "zBits (ZombieCNode n) = objBits (undefined::cte) + n"
| "zBits (ZombieTCB)     = tcbBlockSizeBits"

primrec capBits :: "capability \<Rightarrow> nat" where
  "capBits NullCap                   = 0"
| "capBits DomainCap                 = 0"
| "capBits (UntypedCap _ _ b _)      = b"
| "capBits (EndpointCap _ _ _ _ _ _) = objBits (undefined::endpoint)"
| "capBits (NotificationCap _ _ _ _) = objBits (undefined::Structures_H.notification)"
| "capBits (CNodeCap _ b _ _)        = objBits (undefined::cte) + b"
| "capBits (ThreadCap _)             = objBits (undefined::tcb)"
| "capBits (Zombie _ z _)            = zBits z"
| "capBits (IRQControlCap)           = 0"
| "capBits (IRQHandlerCap _)         = 0"
| "capBits (ReplyCap _ _ _)          = objBits (undefined :: tcb)"
| "capBits (ArchObjectCap x)         = acapBits x"

definition capAligned :: "capability \<Rightarrow> bool" where
  "capAligned c \<equiv> is_aligned (capUntypedPtr c) (capBits c) \<and> capBits c < word_bits"

definition obj_range' :: "machine_word \<Rightarrow> kernel_object \<Rightarrow> machine_word set" where
  "obj_range' p ko \<equiv> ptr_range p (objBitsKO ko)"

primrec (nonexhaustive) usableUntypedRange :: "capability \<Rightarrow> machine_word set" where
 "usableUntypedRange (UntypedCap _ p n f) = (if f < 2^n then {p+of_nat f .. p + mask n} else {})"

definition valid_untyped' :: "bool \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_untyped' d ptr bits idx s \<equiv>
     \<forall>ptr'. \<not> ko_wp_at' (\<lambda>ko. ptr_range ptr bits \<subset> obj_range' ptr' ko
                              \<or> obj_range' ptr' ko \<inter>
                                  usableUntypedRange (UntypedCap d ptr bits idx) \<noteq> {}) ptr' s"

primrec zombieCTEs :: "zombie_type \<Rightarrow> nat" where
  "zombieCTEs ZombieTCB = 5"
| "zombieCTEs (ZombieCNode n) = 2 ^ n"

context begin interpretation Arch .

definition page_table_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
 "page_table_at' x \<equiv> \<lambda>s.
    is_aligned x ptBits \<and>
    (\<forall>y < 2 ^ ptTranslationBits. typ_at' (ArchT PTET) (x + (y << word_size_bits)) s)"

lemmas vspace_table_at'_defs = page_table_at'_def

abbreviation asid_pool_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "asid_pool_at' \<equiv> typ_at' (ArchT ASIDPoolT)"

definition asid_wf :: "asid \<Rightarrow> bool" where
  "asid_wf asid \<equiv> asid \<le> mask asid_bits"

(* FIXME RISCV: complete design spec invariants *)

end

end
