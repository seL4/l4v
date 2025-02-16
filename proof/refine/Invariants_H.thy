(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Invariants_H
imports
  ArchInvsDefs_H
begin

arch_requalify_consts
  refs_of_a'
  hyp_live'
  azobj_refs'
  acapBits
  tcb_hyp_refs'
  valid_arch_cap'
  canonical_address
  valid_arch_tcb'
  valid_arch_obj'
  isArchFrameCap
  acapClass
  global_refs'
  valid_arch_state'
  archMakeObjectT
  valid_arch_mdb_ctes
  pspace_in_kernel_mappings'
  kernel_data_refs
  kernel_mappings

(* FIXME arch-split: review section titles *)
section "Invariants on Executable Spec"

abbreviation ep_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ep_at' \<equiv> obj_at' ((\<lambda>x. True) :: endpoint \<Rightarrow> bool)"

abbreviation ntfn_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ntfn_at' \<equiv> obj_at' ((\<lambda>x. True) :: notification \<Rightarrow> bool)"

abbreviation tcb_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "tcb_at' \<equiv> obj_at' ((\<lambda>x. True) :: tcb \<Rightarrow> bool)"

abbreviation real_cte_at' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "real_cte_at' \<equiv> obj_at' ((\<lambda>x. True) :: cte \<Rightarrow> bool)"

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

abbreviation tcb_of' :: "kernel_object \<Rightarrow> tcb option" where
  "tcb_of' \<equiv> projectKO_opt"

abbreviation tcbs_of' :: "kernel_state \<Rightarrow> obj_ref \<Rightarrow> tcb option" where
  "tcbs_of' s \<equiv> ksPSpace s |> tcb_of'"

abbreviation tcbSchedPrevs_of :: "kernel_state \<Rightarrow> obj_ref \<Rightarrow> obj_ref option" where
   "tcbSchedPrevs_of s \<equiv> tcbs_of' s |> tcbSchedPrev"

abbreviation tcbSchedNexts_of :: "kernel_state \<Rightarrow> obj_ref \<Rightarrow> obj_ref option" where
  "tcbSchedNexts_of s \<equiv> tcbs_of' s |> tcbSchedNext"

abbreviation sym_heap_sched_pointers :: "global.kernel_state \<Rightarrow> bool" where
  "sym_heap_sched_pointers s \<equiv> sym_heap (tcbSchedNexts_of s) (tcbSchedPrevs_of s)"

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

(* the non-hyp, non-arch part of live' *)
primrec live0' :: "Structures_H.kernel_object \<Rightarrow> bool" where
  "live0' (KOTCB tcb) =
     (bound (tcbBoundNotification tcb)
      \<or> tcbSchedPrev tcb \<noteq> None \<or> tcbSchedNext tcb \<noteq> None
      \<or> tcbQueued tcb
      \<or> (tcbState tcb \<noteq> Inactive \<and> tcbState tcb \<noteq> IdleThreadState))"
| "live0' (KOCTE cte)           = False"
| "live0' (KOEndpoint ep)       = (ep \<noteq> IdleEP)"
| "live0' (KONotification ntfn) = (bound (ntfnBoundTCB ntfn) \<or> (\<exists>ts. ntfnObj ntfn = WaitingNtfn ts))"
| "live0' (KOUserData)          = False"
| "live0' (KOUserDataDevice)    = False"
| "live0' (KOKernelData)        = False"
| "live0' (KOArch ako)          = False"

(* hyp_refs *)

definition hyp_refs_of' :: "kernel_object \<Rightarrow> (obj_ref \<times> reftype) set" where
  "hyp_refs_of' x \<equiv> case x of
     (KOTCB tcb)           \<Rightarrow> tcb_hyp_refs' (tcbArch tcb)
   | (KOCTE cte)           \<Rightarrow> {}
   | (KOEndpoint ep)       \<Rightarrow> {}
   | (KONotification ntfn) \<Rightarrow> {}
   | (KOUserData)          \<Rightarrow> {}
   | (KOUserDataDevice)    \<Rightarrow> {}
   | (KOKernelData)        \<Rightarrow> {}
   | (KOArch ako)          \<Rightarrow> refs_of_a' ako"

definition state_hyp_refs_of' :: "kernel_state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set" where
  "state_hyp_refs_of' s \<equiv>
     (\<lambda>p. case (ksPSpace s p) of
            None \<Rightarrow> {}
          | Some ko \<Rightarrow> (if is_aligned p (objBitsKO ko) \<and> ps_clear p (objBitsKO ko) s
                       then hyp_refs_of' ko
                       else {}))"

definition live' :: "kernel_object \<Rightarrow> bool" where
 "live' ko \<equiv> case ko of
    KOTCB tcb           => live0' ko \<or> hyp_live' ko
  | KOCTE cte           => False
  | KOEndpoint ep       => live0' ko
  | KONotification ntfn => live0' ko
  | KOUserData          => False
  | KOUserDataDevice    => False
  | KOKernelData        => False
  | KOArch ako          => hyp_live' ko"

fun zobj_refs' :: "capability \<Rightarrow> obj_ref set" where
  "zobj_refs' NullCap                        = {}"
| "zobj_refs' DomainCap                      = {}"
| "zobj_refs' (UntypedCap d r n f)           = {}"
| "zobj_refs' (EndpointCap r badge x y z t)  = {r}"
| "zobj_refs' (NotificationCap r badge x y)  = {r}"
| "zobj_refs' (CNodeCap r b g gsz)           = {}"
| "zobj_refs' (ThreadCap r)                  = {r}"
| "zobj_refs' (Zombie r b n)                 = {}"
| "zobj_refs' (ArchObjectCap ac)             = azobj_refs' ac"
| "zobj_refs' (IRQControlCap)                = {}"
| "zobj_refs' (IRQHandlerCap irq)            = {}"
| "zobj_refs' (ReplyCap tcb m x)             = {}"

definition ex_nonz_cap_to' :: "obj_ref \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ex_nonz_cap_to' ref \<equiv> \<lambda>s. \<exists>cref. cte_wp_at' (\<lambda>c. ref \<in> zobj_refs' (cteCap c)) cref s"

definition if_live_then_nonz_cap' :: "kernel_state \<Rightarrow> bool" where
  "if_live_then_nonz_cap' s \<equiv> \<forall>ptr. ko_wp_at' live' ptr s \<longrightarrow> ex_nonz_cap_to' ptr s"

fun cte_refs' :: "capability \<Rightarrow> obj_ref \<Rightarrow> obj_ref set" where
  "cte_refs' (CNodeCap ref bits _ _) x = (\<lambda>x. ref + (x << cteSizeBits)) ` {0 .. mask bits}"
| "cte_refs' (ThreadCap ref) x         = (\<lambda>x. ref + x) ` dom tcb_cte_cases"
| "cte_refs' (Zombie ref _ n) x        = (\<lambda>x. ref + (x << cteSizeBits)) ` {0 ..< of_nat n}"
| "cte_refs' (IRQHandlerCap irq) x     = {x + (ucast irq << cteSizeBits)}"
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
  "obj_range' p ko \<equiv> mask_range p (objBitsKO ko)"

primrec (nonexhaustive) usableUntypedRange :: "capability \<Rightarrow> machine_word set" where
 "usableUntypedRange (UntypedCap _ p n f) = (if f < 2^n then {p+of_nat f .. p + mask n} else {})"

definition valid_untyped' :: "bool \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_untyped' d ptr bits idx s \<equiv>
     \<forall>ptr'. \<not> ko_wp_at' (\<lambda>ko. mask_range ptr bits \<subset> obj_range' ptr' ko
                              \<or> obj_range' ptr' ko \<inter>
                                  usableUntypedRange (UntypedCap d ptr bits idx) \<noteq> {}) ptr' s"

primrec zombieCTEs :: "zombie_type \<Rightarrow> nat" where
  "zombieCTEs ZombieTCB = 5"
| "zombieCTEs (ZombieCNode n) = 2 ^ n"

definition
  valid_cap' :: "capability \<Rightarrow> kernel_state \<Rightarrow> bool"
where valid_cap'_def:
  "valid_cap' c s \<equiv> capAligned c \<and>
  (case c of
    NullCap \<Rightarrow> True
  | DomainCap \<Rightarrow> True
  | UntypedCap d r n f \<Rightarrow>
      valid_untyped' d r n f s \<and> r \<noteq> 0 \<and> minUntypedSizeBits \<le> n \<and> n \<le> maxUntypedSizeBits
        \<and> f \<le> 2^n \<and> is_aligned (of_nat f :: machine_word) minUntypedSizeBits
        \<and> canonical_address r \<and> r \<in> kernel_mappings
  | EndpointCap r badge x y z t \<Rightarrow> ep_at' r s
  | NotificationCap r badge x y \<Rightarrow> ntfn_at' r s
  | CNodeCap r bits guard guard_sz \<Rightarrow>
      bits \<noteq> 0 \<and> bits + guard_sz \<le> word_bits \<and> guard && mask guard_sz = guard \<and>
      (\<forall>addr. real_cte_at' (r + 2^cteSizeBits * (addr && mask bits)) s)
  | ThreadCap r \<Rightarrow> tcb_at' r s
  | ReplyCap r m x \<Rightarrow> tcb_at' r s
  | IRQControlCap \<Rightarrow> True
  | IRQHandlerCap irq \<Rightarrow> irq \<le> maxIRQ
  | Zombie r b n \<Rightarrow> n \<le> zombieCTEs b \<and> zBits b < word_bits
                    \<and> (case b of ZombieTCB \<Rightarrow> tcb_at' r s | ZombieCNode n \<Rightarrow> n \<noteq> 0
                    \<and> (\<forall>addr. real_cte_at' (r + 2^cteSizeBits * (addr && mask n)) s))
  | ArchObjectCap ac \<Rightarrow> valid_arch_cap' ac s)"

definition arch_cap'_fun_lift :: "(arch_capability \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> capability \<Rightarrow> 'a" where
  "arch_cap'_fun_lift P F c \<equiv> case c of ArchObjectCap ac \<Rightarrow> P ac | _ \<Rightarrow> F"

lemmas arch_cap'_fun_lift_simps[simp] = arch_cap'_fun_lift_def[split_simps capability.split]

(* Use abbreviation, not syntax, so that it can be input-only *)
abbreviation (input) valid_cap'_syn ::
  "kernel_state \<Rightarrow> capability \<Rightarrow> bool" ("_ \<turnstile>'' _" [60, 60] 61) where
  "s \<turnstile>' c \<equiv> valid_cap' c s"

definition valid_cte' :: "cte \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_cte' cte s \<equiv> s \<turnstile>' (cteCap cte)"

definition valid_tcb_state' :: "thread_state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_tcb_state' ts s \<equiv> case ts of
    BlockedOnReceive ref a \<Rightarrow> ep_at' ref s
  | BlockedOnSend ref a b d c \<Rightarrow> ep_at' ref s
  | BlockedOnNotification ref \<Rightarrow> ntfn_at' ref s
  | _ \<Rightarrow> True"

definition valid_ipc_buffer_ptr' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_ipc_buffer_ptr' a s \<equiv>
     is_aligned a msg_align_bits \<and> typ_at' UserDataT (a && ~~ mask pageBits) s"

definition valid_bound_ntfn' :: "machine_word option \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_bound_ntfn' ntfn_opt s \<equiv>
     case ntfn_opt of None \<Rightarrow> True | Some a \<Rightarrow> ntfn_at' a s"

abbreviation opt_tcb_at' :: "machine_word option \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "opt_tcb_at' \<equiv> none_top tcb_at'"

lemmas opt_tcb_at'_def = none_top_def

definition valid_tcb' :: "tcb \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_tcb' t s \<equiv> (\<forall>(getF, setF) \<in> ran tcb_cte_cases. s \<turnstile>' cteCap (getF t))
                  \<and> valid_tcb_state' (tcbState t) s
                  \<and> is_aligned (tcbIPCBuffer t) msg_align_bits
                  \<and> valid_bound_ntfn' (tcbBoundNotification t) s
                  \<and> tcbDomain t \<le> maxDomain
                  \<and> tcbPriority t \<le> maxPriority
                  \<and> tcbMCP t \<le> maxPriority
                  \<and> opt_tcb_at' (tcbSchedPrev t) s
                  \<and> opt_tcb_at' (tcbSchedNext t) s
                  \<and> valid_arch_tcb' (tcbArch t) s"

definition valid_ep' :: "Structures_H.endpoint \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_ep' ep s \<equiv> case ep of
     IdleEP \<Rightarrow> True
   | SendEP ts \<Rightarrow> (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at' t s) \<and> distinct ts)
   | RecvEP ts \<Rightarrow> (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at' t s) \<and> distinct ts)"

definition valid_bound_tcb' :: "machine_word option \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_bound_tcb' tcb_opt s \<equiv> case tcb_opt of None \<Rightarrow> True | Some t \<Rightarrow> tcb_at' t s"

definition valid_ntfn' :: "Structures_H.notification \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_ntfn' ntfn s \<equiv> (case ntfnObj ntfn of
    IdleNtfn \<Rightarrow> True
  | WaitingNtfn ts \<Rightarrow>
      (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at' t s) \<and> distinct ts
     \<and> (case ntfnBoundTCB ntfn of Some tcb \<Rightarrow> ts = [tcb] | _ \<Rightarrow> True))
  | ActiveNtfn b \<Rightarrow> True)
  \<and> valid_bound_tcb' (ntfnBoundTCB ntfn) s"

definition valid_obj' :: "Structures_H.kernel_object \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_obj' ko s \<equiv> case ko of
    KOEndpoint endpoint \<Rightarrow> valid_ep' endpoint s
  | KONotification notification \<Rightarrow> valid_ntfn' notification s
  | KOKernelData \<Rightarrow> False
  | KOUserData \<Rightarrow> True
  | KOUserDataDevice \<Rightarrow> True
  | KOTCB tcb \<Rightarrow> valid_tcb' tcb s
  | KOCTE cte \<Rightarrow> valid_cte' cte s
  | KOArch ako \<Rightarrow> valid_arch_obj' ako s"

definition
  pspace_aligned' :: "kernel_state \<Rightarrow> bool"
where
 "pspace_aligned' s \<equiv>
  \<forall>x \<in> dom (ksPSpace s). is_aligned x (objBitsKO (the (ksPSpace s x)))"

definition
  pspace_distinct' :: "kernel_state \<Rightarrow> bool"
where
  "pspace_distinct' s \<equiv>
   \<forall>x \<in> dom (ksPSpace s). ps_clear x (objBitsKO (the (ksPSpace s x))) s"

definition pspace_canonical' :: "kernel_state \<Rightarrow> bool" where
  "pspace_canonical' s \<equiv> \<forall>p \<in> dom (ksPSpace s). canonical_address p"

definition
  valid_objs' :: "kernel_state \<Rightarrow> bool"
where
  "valid_objs' s \<equiv> \<forall>obj \<in> ran (ksPSpace s). valid_obj' obj s"


type_synonym cte_heap = "machine_word \<Rightarrow> cte option"

definition
  map_to_ctes :: "(machine_word \<rightharpoonup> kernel_object) \<Rightarrow> cte_heap"
where
 "map_to_ctes m \<equiv> \<lambda>x.
      let cte_bits = objBitsKO (KOCTE undefined);
        tcb_bits = objBitsKO (KOTCB undefined);
        y = (x && (~~ mask tcb_bits))
      in
      if \<exists>cte. m x = Some (KOCTE cte) \<and> is_aligned x cte_bits
            \<and> {x + 1 .. x + (1 << cte_bits) - 1} \<inter> dom m = {}
      then case m x of Some (KOCTE cte) \<Rightarrow> Some cte
      else if \<exists>tcb. m y = Some (KOTCB tcb)
            \<and> {y + 1 .. y + (1 << tcb_bits) - 1} \<inter> dom m = {}
      then case m y of Some (KOTCB tcb) \<Rightarrow>
             option_map (\<lambda>(getF, setF). getF tcb) (tcb_cte_cases (x - y))
      else None"

abbreviation
  "ctes_of s \<equiv> map_to_ctes (ksPSpace s)"

definition
  mdb_next :: "cte_heap \<Rightarrow> machine_word \<Rightarrow> machine_word option"
where
  "mdb_next s c \<equiv> option_map (mdbNext o cteMDBNode) (s c)"

definition
  mdb_next_rel :: "cte_heap \<Rightarrow> (machine_word \<times> machine_word) set"
where
  "mdb_next_rel m \<equiv> {(x, y). mdb_next m x = Some y}"

abbreviation
  mdb_next_direct :: "cte_heap \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto> _" [60,0,60] 61)
where
  "m \<turnstile> a \<leadsto> b \<equiv> (a, b) \<in> mdb_next_rel m"

abbreviation
  mdb_next_trans :: "cte_heap \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto>\<^sup>+ _" [60,0,60] 61)
where
  "m \<turnstile> a \<leadsto>\<^sup>+ b \<equiv> (a,b) \<in> (mdb_next_rel m)\<^sup>+"

abbreviation
  mdb_next_rtrans :: "cte_heap \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> bool" ("_ \<turnstile> _ \<leadsto>\<^sup>* _" [60,0,60] 61)
where
  "m \<turnstile> a \<leadsto>\<^sup>* b \<equiv> (a,b) \<in> (mdb_next_rel m)\<^sup>*"

definition
  "valid_badges m \<equiv>
  \<forall>p p' cap node cap' node'.
    m p = Some (CTE cap node) \<longrightarrow>
    m p' = Some (CTE cap' node') \<longrightarrow>
    (m \<turnstile> p \<leadsto> p') \<longrightarrow>
    (sameRegionAs cap cap') \<longrightarrow>
    (isEndpointCap cap \<longrightarrow>
     capEPBadge cap \<noteq> capEPBadge cap' \<longrightarrow>
     capEPBadge cap' \<noteq> 0 \<longrightarrow>
     mdbFirstBadged node')
    \<and>
    (isNotificationCap cap \<longrightarrow>
     capNtfnBadge cap \<noteq> capNtfnBadge cap' \<longrightarrow>
     capNtfnBadge cap' \<noteq> 0 \<longrightarrow>
     mdbFirstBadged node')"

fun (sequential)
  untypedRange :: "capability \<Rightarrow> machine_word set"
where
   "untypedRange (UntypedCap d p n f) = {p .. p + 2 ^ n - 1}"
|  "untypedRange c = {}"

primrec
  capClass :: "capability \<Rightarrow> capclass"
where
  "capClass (NullCap)                          = NullClass"
| "capClass (DomainCap)                        = DomainClass"
| "capClass (UntypedCap d p n f)               = PhysicalClass"
| "capClass (EndpointCap ref badge s r g gr)   = PhysicalClass"
| "capClass (NotificationCap ref badge s r)    = PhysicalClass"
| "capClass (CNodeCap ref bits g gs)           = PhysicalClass"
| "capClass (ThreadCap ref)                    = PhysicalClass"
| "capClass (Zombie r b n)                     = PhysicalClass"
| "capClass (IRQControlCap)                    = IRQClass"
| "capClass (IRQHandlerCap irq)                = IRQClass"
| "capClass (ReplyCap tcb m g)                 = ReplyClass tcb"
| "capClass (ArchObjectCap cap)                = acapClass cap"

definition
  "capRange cap \<equiv>
  if capClass cap \<noteq> PhysicalClass then {}
  else {capUntypedPtr cap .. capUntypedPtr cap + 2 ^ capBits cap - 1}"

definition
  "caps_contained' m \<equiv>
  \<forall>p p' c n c' n'.
  m p = Some (CTE c n) \<longrightarrow>
  m p' = Some (CTE c' n') \<longrightarrow>
  \<not>isUntypedCap c' \<longrightarrow>
  capRange c' \<inter> untypedRange c \<noteq> {} \<longrightarrow>
  capRange c' \<subseteq> untypedRange c"

definition
  valid_dlist :: "cte_heap \<Rightarrow> bool"
where
  "valid_dlist m \<equiv>
  \<forall>p cte. m p = Some cte \<longrightarrow>
    (let prev = mdbPrev (cteMDBNode cte);
         next = mdbNext (cteMDBNode cte)
    in (prev \<noteq> 0 \<longrightarrow> (\<exists>cte'. m prev = Some cte' \<and> mdbNext (cteMDBNode cte') = p)) \<and>
       (next \<noteq> 0 \<longrightarrow> (\<exists>cte'. m next = Some cte' \<and> mdbPrev (cteMDBNode cte') = p)))"

definition
  "no_0 m \<equiv> m 0 = None"
definition
  "no_loops m \<equiv> \<forall>c. \<not> m \<turnstile> c \<leadsto>\<^sup>+ c"
definition
  "mdb_chain_0 m \<equiv> \<forall>x \<in> dom m. m \<turnstile> x \<leadsto>\<^sup>+ 0"

definition
  "class_links m \<equiv> \<forall>p p' cte cte'.
     m p = Some cte \<longrightarrow>
     m p' = Some cte' \<longrightarrow>
     m \<turnstile> p \<leadsto> p' \<longrightarrow>
     capClass (cteCap cte) = capClass (cteCap cte')"

definition
  "is_chunk m cap p p' \<equiv>
  \<forall>p''. m \<turnstile> p \<leadsto>\<^sup>+ p'' \<longrightarrow> m \<turnstile> p'' \<leadsto>\<^sup>* p' \<longrightarrow>
  (\<exists>cap'' n''. m p'' = Some (CTE cap'' n'') \<and> sameRegionAs cap cap'')"

definition
  "mdb_chunked m \<equiv> \<forall>p p' cap cap' n n'.
  m p = Some (CTE cap n) \<longrightarrow>
  m p' = Some (CTE cap' n') \<longrightarrow>
  sameRegionAs cap cap' \<longrightarrow>
  p \<noteq> p' \<longrightarrow>
  (m \<turnstile> p \<leadsto>\<^sup>+ p' \<or> m \<turnstile> p' \<leadsto>\<^sup>+ p) \<and>
  (m \<turnstile> p \<leadsto>\<^sup>+ p' \<longrightarrow> is_chunk m cap p p') \<and>
  (m \<turnstile> p' \<leadsto>\<^sup>+ p \<longrightarrow> is_chunk m cap' p' p)"

definition
  parentOf :: "cte_heap \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> bool" ("_ \<turnstile> _ parentOf _" [60,0,60] 61)
where
  "s \<turnstile> c' parentOf c \<equiv>
  \<exists>cte' cte. s c = Some cte \<and> s c' = Some cte' \<and> isMDBParentOf cte' cte"


context
notes [[inductive_internals =true]]
begin

inductive
  subtree :: "cte_heap \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> bool" ("_ \<turnstile> _ \<rightarrow> _" [60,0,60] 61)
  for s :: cte_heap and c :: machine_word
where
  direct_parent:
  "\<lbrakk> s \<turnstile> c \<leadsto> c'; c' \<noteq> 0; s \<turnstile> c parentOf c'\<rbrakk> \<Longrightarrow> s \<turnstile> c \<rightarrow> c'"
 |
  trans_parent:
  "\<lbrakk> s \<turnstile> c \<rightarrow> c'; s \<turnstile> c' \<leadsto> c''; c'' \<noteq> 0; s \<turnstile> c parentOf c'' \<rbrakk> \<Longrightarrow> s \<turnstile> c \<rightarrow> c''"

end

definition
  "descendants_of' c s \<equiv> {c'. s \<turnstile> c \<rightarrow> c'}"


definition
 "untyped_mdb' m \<equiv>
  \<forall>p p' c n c' n'.
      m p = Some (CTE c n) \<longrightarrow> isUntypedCap c \<longrightarrow>
      m p' = Some (CTE c' n') \<longrightarrow> \<not> isUntypedCap c' \<longrightarrow>
      capRange c' \<inter> untypedRange c \<noteq> {} \<longrightarrow>
      p' \<in> descendants_of' p m"

definition
  "untyped_inc' m \<equiv>
  \<forall>p p' c c' n n'.
     m p = Some (CTE c n) \<longrightarrow> isUntypedCap c \<longrightarrow>
     m p' = Some (CTE c' n') \<longrightarrow> isUntypedCap c' \<longrightarrow>
     (untypedRange c \<subseteq> untypedRange c' \<or>
      untypedRange c' \<subseteq> untypedRange c \<or>
      untypedRange c \<inter> untypedRange c' = {}) \<and>
     (untypedRange c \<subset> untypedRange c' \<longrightarrow> (p \<in> descendants_of' p' m \<and> untypedRange c \<inter> usableUntypedRange c' ={})) \<and>
     (untypedRange c' \<subset> untypedRange c \<longrightarrow> (p' \<in> descendants_of' p m \<and> untypedRange c' \<inter> usableUntypedRange c ={})) \<and>
     (untypedRange c = untypedRange c' \<longrightarrow> (p' \<in> descendants_of' p m \<and> usableUntypedRange c={}
     \<or> p \<in> descendants_of' p' m \<and> usableUntypedRange c' = {} \<or> p = p'))"

definition
  "valid_nullcaps m \<equiv> \<forall>p n. m p = Some (CTE NullCap n) \<longrightarrow> n = nullMDBNode"

definition
  "ut_revocable' m \<equiv> \<forall>p cap n. m p = Some (CTE cap n) \<longrightarrow> isUntypedCap cap \<longrightarrow> mdbRevocable n"

definition
  "irq_control m \<equiv>
  \<forall>p n. m p = Some (CTE IRQControlCap n) \<longrightarrow>
        mdbRevocable n \<and>
        (\<forall>p' n'. m p' = Some (CTE IRQControlCap n') \<longrightarrow> p' = p)"

definition
  distinct_zombie_caps :: "(machine_word \<Rightarrow> capability option) \<Rightarrow> bool"
where
 "distinct_zombie_caps caps \<equiv> \<forall>ptr ptr' cap cap'. caps ptr = Some cap
         \<and> caps ptr' = Some cap' \<and> ptr \<noteq> ptr' \<and> isZombie cap
         \<and> capClass cap' = PhysicalClass \<and> \<not> isUntypedCap cap' \<and> \<not> isArchFrameCap cap'
         \<and> capBits cap = capBits cap' \<longrightarrow> capUntypedPtr cap \<noteq> capUntypedPtr cap'"

definition
  distinct_zombies :: "cte_heap \<Rightarrow> bool"
where
 "distinct_zombies m \<equiv> distinct_zombie_caps (option_map cteCap \<circ> m)"

definition
  reply_masters_rvk_fb :: "cte_heap \<Rightarrow> bool"
where
 "reply_masters_rvk_fb ctes \<equiv> \<forall>cte \<in> ran ctes.
        isReplyCap (cteCap cte) \<and> capReplyMaster (cteCap cte)
    \<longrightarrow> mdbRevocable (cteMDBNode cte) \<and> mdbFirstBadged (cteMDBNode cte)"

definition
  valid_mdb_ctes :: "cte_heap \<Rightarrow> bool"
where
  "valid_mdb_ctes \<equiv> \<lambda>m. valid_dlist m \<and> no_0 m \<and> mdb_chain_0 m \<and>
                        valid_badges m \<and> caps_contained' m \<and>
                        mdb_chunked m \<and> untyped_mdb' m \<and>
                        untyped_inc' m \<and> valid_nullcaps m \<and>
                        ut_revocable' m \<and> class_links m \<and> distinct_zombies m
                        \<and> irq_control m \<and> reply_masters_rvk_fb m
                        \<and> valid_arch_mdb_ctes m"

definition
  valid_mdb' :: "kernel_state \<Rightarrow> bool"
where
  "valid_mdb' \<equiv> \<lambda>s. valid_mdb_ctes (ctes_of s)"

definition
  "no_0_obj' \<equiv> \<lambda>s. ksPSpace s 0 = None"

definition
  valid_pspace' :: "kernel_state \<Rightarrow> bool"
where
  "valid_pspace' \<equiv> valid_objs' and
                   pspace_aligned' and
                   pspace_canonical' and
                   pspace_in_kernel_mappings' and
                   pspace_distinct' and
                   no_0_obj' and
                   valid_mdb'"

primrec
  runnable' :: "Structures_H.thread_state \<Rightarrow> bool"
where
  "runnable' (Structures_H.Running)                 = True"
| "runnable' (Structures_H.Inactive)                = False"
| "runnable' (Structures_H.Restart)                 = True"
| "runnable' (Structures_H.IdleThreadState)         = False"
| "runnable' (Structures_H.BlockedOnReceive a b)    = False"
| "runnable' (Structures_H.BlockedOnReply)          = False"
| "runnable' (Structures_H.BlockedOnSend a b c d e) = False"
| "runnable' (Structures_H.BlockedOnNotification x) = False"

definition inQ :: "domain \<Rightarrow> priority \<Rightarrow> tcb \<Rightarrow> bool" where
  "inQ d p tcb \<equiv> tcbQueued tcb \<and> tcbPriority tcb = p \<and> tcbDomain tcb = d"

lemma inQ_implies_tcbQueueds_of:
  "(inQ domain priority |< tcbs_of' s') tcbPtr \<Longrightarrow> (tcbQueued |< tcbs_of' s') tcbPtr"
  by (clarsimp simp: opt_map_def opt_pred_def inQ_def split: option.splits)

defs ready_qs_runnable_def:
  "ready_qs_runnable s \<equiv> \<forall>t. obj_at' tcbQueued t s \<longrightarrow> st_tcb_at' runnable' t s"

definition
  (* for given domain and priority, the scheduler bitmap indicates a thread is in the queue *)
  (* second level of the bitmap is stored in reverse for better cache locality in common case *)
  bitmapQ :: "domain \<Rightarrow> priority \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "bitmapQ d p s \<equiv> ksReadyQueuesL1Bitmap s d !! prioToL1Index p
                     \<and> ksReadyQueuesL2Bitmap s (d, invertL1Index (prioToL1Index p))
                         !! unat (p && mask wordRadix)"
definition
  (* A priority is used as a two-part key into the bitmap structure. If an L2 bitmap entry
     is set without an L1 entry, updating the L1 entry (shared by many priorities) may make
     unexpected threads schedulable *)
  bitmapQ_no_L2_orphans :: "kernel_state \<Rightarrow> bool"
where
  "bitmapQ_no_L2_orphans \<equiv> \<lambda>s.
    \<forall>d i j. ksReadyQueuesL2Bitmap s (d, invertL1Index i) !! j \<and> i < l2BitmapSize
            \<longrightarrow> (ksReadyQueuesL1Bitmap s d !! i)"

definition
  (* If the scheduler finds a set bit in L1 of the bitmap, it must find some bit set in L2
     when it looks there. This lets it omit a check.
     L2 entries have wordBits bits each. That means the L1 word only indexes
     a small number of L2 entries, despite being stored in a wordBits word.
     We allow only bits corresponding to L2 indices to be set.
  *)
  bitmapQ_no_L1_orphans :: "kernel_state \<Rightarrow> bool"
where
  "bitmapQ_no_L1_orphans \<equiv> \<lambda>s.
    \<forall>d i. ksReadyQueuesL1Bitmap s d !! i \<longrightarrow> ksReadyQueuesL2Bitmap s (d, invertL1Index i) \<noteq> 0 \<and>
                                             i < l2BitmapSize"

definition valid_bitmapQ :: "kernel_state \<Rightarrow> bool" where
  "valid_bitmapQ \<equiv> \<lambda>s. \<forall>d p. bitmapQ d p s \<longleftrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (d,p))"

definition valid_bitmaps :: "kernel_state \<Rightarrow> bool" where
  "valid_bitmaps \<equiv> \<lambda>s. valid_bitmapQ s \<and> bitmapQ_no_L2_orphans s \<and> bitmapQ_no_L1_orphans s"

lemma valid_bitmaps_valid_bitmapQ[elim!]:
  "valid_bitmaps s \<Longrightarrow> valid_bitmapQ s"
  by (simp add: valid_bitmaps_def)

lemma valid_bitmaps_bitmapQ_no_L2_orphans[elim!]:
  "valid_bitmaps s \<Longrightarrow> bitmapQ_no_L2_orphans s"
  by (simp add: valid_bitmaps_def)

lemma valid_bitmaps_bitmapQ_no_L1_orphans[elim!]:
  "valid_bitmaps s \<Longrightarrow> bitmapQ_no_L1_orphans s"
  by (simp add: valid_bitmaps_def)

lemma valid_bitmaps_lift:
  assumes prq: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueues s)\<rbrace>"
  assumes prqL1: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL1Bitmap s)\<rbrace>"
  assumes prqL2: "\<And>P. f \<lbrace>\<lambda>s. P (ksReadyQueuesL2Bitmap s)\<rbrace>"
  shows "f \<lbrace>valid_bitmaps\<rbrace>"
  unfolding valid_bitmaps_def valid_bitmapQ_def bitmapQ_def
            bitmapQ_no_L1_orphans_def bitmapQ_no_L2_orphans_def
  apply (rule hoare_pre)
   apply (wps assms | wpsimp)+
  done

(* when a thread gets added to / removed from a queue, but before bitmap updated *)
definition valid_bitmapQ_except :: "domain \<Rightarrow> priority \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_bitmapQ_except d' p' \<equiv> \<lambda>s.
    \<forall>d p. (d \<noteq> d' \<or> p \<noteq> p') \<longrightarrow> (bitmapQ d p s \<longleftrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (d,p)))"

lemmas bitmapQ_defs = valid_bitmapQ_def valid_bitmapQ_except_def bitmapQ_def
                       bitmapQ_no_L2_orphans_def bitmapQ_no_L1_orphans_def

\<comment> \<open>
  The tcbSchedPrev and tcbSchedNext fields of a TCB are used only to indicate membership in
  one of the ready queues. \<close>
definition valid_sched_pointers_2 ::
  "(obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<rightharpoonup> obj_ref) \<Rightarrow> (obj_ref \<Rightarrow> bool) \<Rightarrow> bool "
  where
  "valid_sched_pointers_2 prevs nexts ready \<equiv>
     \<forall>ptr. prevs ptr \<noteq> None \<or> nexts ptr \<noteq> None \<longrightarrow> ready ptr"

abbreviation valid_sched_pointers :: "kernel_state \<Rightarrow> bool" where
  "valid_sched_pointers s \<equiv>
     valid_sched_pointers_2 (tcbSchedPrevs_of s) (tcbSchedNexts_of s) (tcbQueued |< tcbs_of' s)"

lemmas valid_sched_pointers_def = valid_sched_pointers_2_def

lemma valid_sched_pointersD:
  "\<lbrakk>valid_sched_pointers s; \<not> (tcbQueued |< tcbs_of' s) t\<rbrakk>
   \<Longrightarrow> tcbSchedPrevs_of s t = None \<and> tcbSchedNexts_of s t = None"
  by (fastforce simp: valid_sched_pointers_def in_opt_pred opt_map_red)

definition tcb_in_cur_domain' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "tcb_in_cur_domain' t \<equiv> \<lambda>s. obj_at' (\<lambda>tcb. ksCurDomain s = tcbDomain tcb) t s"

definition
  ct_idle_or_in_cur_domain' :: "kernel_state \<Rightarrow> bool" where
  "ct_idle_or_in_cur_domain' \<equiv> \<lambda>s. ksSchedulerAction s = ResumeCurrentThread \<longrightarrow>
    ksCurThread s = ksIdleThread s \<or> tcb_in_cur_domain' (ksCurThread s) s"

definition
 "ct_in_state' test \<equiv> \<lambda>s. st_tcb_at' test (ksCurThread s) s"

definition
 "ct_not_inQ \<equiv> \<lambda>s. ksSchedulerAction s = ResumeCurrentThread
                     \<longrightarrow> obj_at' (Not \<circ> tcbQueued) (ksCurThread s) s"

abbreviation
  "idle' \<equiv> \<lambda>st. st = Structures_H.IdleThreadState"

abbreviation
  "activatable' st \<equiv> runnable' st \<or> idle' st"

primrec
  sch_act_wf :: "scheduler_action \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "sch_act_wf ResumeCurrentThread = ct_in_state' activatable'"
| "sch_act_wf ChooseNewThread     = \<top>"
| "sch_act_wf (SwitchToThread t)  = (\<lambda>s. st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s)"

definition sch_act_simple :: "kernel_state \<Rightarrow> bool" where
  "sch_act_simple \<equiv> \<lambda>s. (ksSchedulerAction s = ResumeCurrentThread) \<or>
                         (ksSchedulerAction s = ChooseNewThread)"

definition sch_act_sane :: "kernel_state \<Rightarrow> bool" where
  "sch_act_sane \<equiv> \<lambda>s. \<forall>t. ksSchedulerAction s = SwitchToThread t \<longrightarrow> t \<noteq> ksCurThread s"

abbreviation
  "sch_act_not t \<equiv> \<lambda>s. ksSchedulerAction s \<noteq> SwitchToThread t"

definition idle_tcb'_2 :: "Structures_H.thread_state \<times> machine_word option \<Rightarrow> bool" where
  "idle_tcb'_2 \<equiv> \<lambda>(st, ntfn_opt). (idle' st \<and> ntfn_opt = None)"

abbreviation
  "idle_tcb' tcb \<equiv> idle_tcb'_2 (tcbState tcb, tcbBoundNotification tcb)"

lemmas idle_tcb'_def = idle_tcb'_2_def

definition valid_idle' :: "kernel_state \<Rightarrow> bool" where
  "valid_idle' \<equiv> \<lambda>s. obj_at' idle_tcb' (ksIdleThread s) s \<and> idle_thread_ptr = ksIdleThread s"

lemma valid_idle'_tcb_at':
  "valid_idle' s \<Longrightarrow> obj_at' idle_tcb' (ksIdleThread s) s"
  by (clarsimp simp: valid_idle'_def)

definition valid_irq_node' :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "valid_irq_node' x \<equiv>
   \<lambda>s. is_aligned x (size (0::irq) + cteSizeBits) \<and>
       (\<forall>irq :: irq. real_cte_at' (x + (ucast irq << cteSizeBits)) s)"

definition valid_refs' :: "machine_word set \<Rightarrow> cte_heap \<Rightarrow> bool" where
  "valid_refs' R \<equiv> \<lambda>m. \<forall>c \<in> ran m. R \<inter> capRange (cteCap c) = {}"

definition valid_cap_sizes' :: "nat \<Rightarrow> cte_heap \<Rightarrow> bool" where
  "valid_cap_sizes' n hp \<equiv> \<forall>cte \<in> ran hp. 2 ^ capBits (cteCap cte) \<le> n"

definition valid_global_refs' :: "kernel_state \<Rightarrow> bool" where
  "valid_global_refs' \<equiv> \<lambda>s.
      valid_refs' kernel_data_refs (ctes_of s)
    \<and> global_refs' s \<subseteq> kernel_data_refs
    \<and> valid_cap_sizes' (gsMaxObjectSize s) (ctes_of s)"

definition pspace_domain_valid :: "kernel_state \<Rightarrow> bool" where
  "pspace_domain_valid \<equiv> \<lambda>s.
     \<forall>x ko. ksPSpace s x = Some ko \<longrightarrow> mask_range x (objBitsKO ko) \<inter> kernel_data_refs = {}"

definition irq_issued' :: "irq \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "irq_issued' irq \<equiv> \<lambda>s. intStateIRQTable (ksInterruptState s) irq = IRQSignal"

definition cteCaps_of :: "kernel_state \<Rightarrow> machine_word \<Rightarrow> capability option" where
 "cteCaps_of s \<equiv> option_map cteCap \<circ> ctes_of s"

definition valid_irq_handlers' :: "kernel_state \<Rightarrow> bool" where
  "valid_irq_handlers' \<equiv> \<lambda>s. \<forall>cap \<in> ran (cteCaps_of s). \<forall>irq.
                                 cap = IRQHandlerCap irq \<longrightarrow> irq_issued' irq s"

definition
  "irqs_masked' \<equiv> \<lambda>s. \<forall>irq > maxIRQ. intStateIRQTable (ksInterruptState s) irq = IRQInactive"

definition
  "valid_irq_masks' table masked \<equiv> \<forall>irq. table irq = IRQInactive \<longrightarrow> masked irq"

abbreviation
  "valid_irq_states' s \<equiv>
  valid_irq_masks' (intStateIRQTable (ksInterruptState s)) (irq_masks (ksMachineState s))"

defs pointerInUserData_def:
  "pointerInUserData p \<equiv> typ_at' UserDataT (p && ~~ mask pageBits)"

(* pointerInDeviceData is not defined in spec but is necessary for valid_machine_state' *)
definition pointerInDeviceData :: "machine_word \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "pointerInDeviceData p \<equiv> typ_at' UserDataDeviceT (p && ~~ mask pageBits)"

definition
  "valid_machine_state' \<equiv>
   \<lambda>s. \<forall>p. pointerInUserData p s \<or> pointerInDeviceData p s \<or> underlying_memory (ksMachineState s) p = 0"

definition
  "untyped_ranges_zero_inv cps urs \<equiv> urs = ran (untypedZeroRange \<circ>\<^sub>m cps)"

abbreviation
  "untyped_ranges_zero' s \<equiv> untyped_ranges_zero_inv (cteCaps_of s) (gsUntypedZeroRanges s)"

(* FIXME: this really should be a definition like the above. *)
(* The schedule is invariant. *)
abbreviation
  "valid_dom_schedule' \<equiv>
   \<lambda>s. ksDomSchedule s \<noteq> [] \<and> (\<forall>x\<in>set (ksDomSchedule s). dschDomain x \<le> maxDomain \<and> 0 < dschLength x)
       \<and> ksDomSchedule s = ksDomSchedule (newKernelState undefined)
       \<and> ksDomScheduleIdx s < length (ksDomSchedule (newKernelState undefined))"

definition valid_state' :: "kernel_state \<Rightarrow> bool" where
  "valid_state' \<equiv> \<lambda>s. valid_pspace' s \<and> sch_act_wf (ksSchedulerAction s) s
                      \<and> sym_refs (state_refs_of' s) \<and> sym_refs (state_hyp_refs_of' s)
                      \<and> if_live_then_nonz_cap' s \<and> if_unsafe_then_cap' s
                      \<and> valid_idle' s
                      \<and> valid_global_refs' s \<and> valid_arch_state' s
                      \<and> valid_irq_node' (irq_node' s) s
                      \<and> valid_irq_handlers' s
                      \<and> valid_irq_states' s
                      \<and> valid_machine_state' s
                      \<and> irqs_masked' s
                      \<and> sym_heap_sched_pointers s
                      \<and> valid_sched_pointers s
                      \<and> valid_bitmaps s
                      \<and> ct_not_inQ s
                      \<and> ct_idle_or_in_cur_domain' s
                      \<and> pspace_domain_valid s
                      \<and> ksCurDomain s \<le> maxDomain
                      \<and> valid_dom_schedule' s
                      \<and> untyped_ranges_zero' s"

definition
  "cur_tcb' s \<equiv> tcb_at' (ksCurThread s) s"

definition
  invs' :: "kernel_state \<Rightarrow> bool" where
  "invs' \<equiv> valid_state' and cur_tcb'"


subsection "Derived concepts"

abbreviation
  "awaiting_reply' ts \<equiv> ts = Structures_H.BlockedOnReply"

  (* x-symbol doesn't have a reverse leadsto.. *)
definition
  mdb_prev :: "cte_heap \<Rightarrow> machine_word \<Rightarrow> machine_word \<Rightarrow> bool" ("_ \<turnstile> _ \<leftarrow> _" [60,0,60] 61)
where
  "m \<turnstile> c \<leftarrow> c' \<equiv> (\<exists>z. m c' = Some z \<and> c = mdbPrev (cteMDBNode z))"

definition
  makeObjectT :: "kernel_object_type \<Rightarrow> kernel_object"
  where
  "makeObjectT tp \<equiv> case tp of
                      EndpointT \<Rightarrow> injectKO (makeObject :: endpoint)
                    | NotificationT \<Rightarrow> injectKO (makeObject :: Structures_H.notification)
                    | CTET \<Rightarrow> injectKO (makeObject :: cte)
                    | TCBT \<Rightarrow> injectKO (makeObject :: tcb)
                    | UserDataT \<Rightarrow> injectKO (makeObject :: user_data)
                    | UserDataDeviceT \<Rightarrow> injectKO (makeObject :: user_data_device)
                    | KernelDataT \<Rightarrow> KOKernelData
                    | ArchT atp \<Rightarrow> archMakeObjectT atp"

definition
  objBitsT :: "kernel_object_type \<Rightarrow> nat"
  where
  "objBitsT tp \<equiv> objBitsKO (makeObjectT tp)"


abbreviation
  "active' st \<equiv> st = Structures_H.Running \<or> st = Structures_H.Restart"

lemma runnable_eq_active': "runnable' = active'"
  apply (rule ext)
  apply (case_tac st, simp_all)
  done

abbreviation
  "simple' st \<equiv> st = Structures_H.Inactive \<or>
                st = Structures_H.Running \<or>
                st = Structures_H.Restart \<or>
                idle' st \<or> awaiting_reply' st"

abbreviation
  "ct_active' \<equiv> ct_in_state' active'"

abbreviation
  "ct_running' \<equiv> ct_in_state' (\<lambda>st. st = Structures_H.Running)"

abbreviation(input)
 "all_invs_but_sym_refs_ct_not_inQ'
    \<equiv> \<lambda>s. valid_pspace' s \<and> sch_act_wf (ksSchedulerAction s) s
           \<and> if_live_then_nonz_cap' s \<and> if_unsafe_then_cap' s
           \<and> valid_idle' s \<and> valid_global_refs' s \<and> valid_arch_state' s
           \<and> valid_irq_node' (irq_node' s) s \<and> valid_irq_handlers' s
           \<and> valid_irq_states' s \<and> irqs_masked' s
           \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s \<and> valid_bitmaps s
           \<and> valid_machine_state' s
           \<and> cur_tcb' s \<and> ct_idle_or_in_cur_domain' s
           \<and> pspace_domain_valid s
           \<and> ksCurDomain s \<le> maxDomain
           \<and> valid_dom_schedule' s \<and> untyped_ranges_zero' s"

abbreviation(input)
 "all_invs_but_ct_not_inQ'
    \<equiv> \<lambda>s. valid_pspace' s \<and> sch_act_wf (ksSchedulerAction s) s
           \<and> sym_refs (state_refs_of' s) \<and> sym_refs (state_hyp_refs_of' s)
           \<and> if_live_then_nonz_cap' s \<and> if_unsafe_then_cap' s
           \<and> valid_idle' s \<and> valid_global_refs' s \<and> valid_arch_state' s
           \<and> valid_irq_node' (irq_node' s) s \<and> valid_irq_handlers' s
           \<and> valid_irq_states' s \<and> irqs_masked' s
           \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s \<and> valid_bitmaps s
           \<and> valid_machine_state' s
           \<and> cur_tcb' s \<and> ct_idle_or_in_cur_domain' s
           \<and> pspace_domain_valid s
           \<and> ksCurDomain s \<le> maxDomain
           \<and> valid_dom_schedule' s \<and> untyped_ranges_zero' s"

lemma all_invs_but_sym_refs_not_ct_inQ_check':
  "(all_invs_but_sym_refs_ct_not_inQ' and sym_refs \<circ> state_refs_of' and sym_refs \<circ> state_hyp_refs_of' and ct_not_inQ) = invs'"
  by (simp add: pred_conj_def conj_commute conj_left_commute invs'_def valid_state'_def)

lemma all_invs_but_not_ct_inQ_check':
  "(all_invs_but_ct_not_inQ' and ct_not_inQ) = invs'"
  by (simp add: pred_conj_def conj_commute conj_left_commute invs'_def valid_state'_def)

definition
  "all_invs_but_ct_idle_or_in_cur_domain'
    \<equiv> \<lambda>s. valid_pspace' s \<and> sch_act_wf (ksSchedulerAction s) s
           \<and> sym_refs (state_refs_of' s) \<and> sym_refs (state_hyp_refs_of' s)
           \<and> if_live_then_nonz_cap' s \<and> if_unsafe_then_cap' s
           \<and> valid_idle' s \<and> valid_global_refs' s \<and> valid_arch_state' s
           \<and> valid_irq_node' (irq_node' s) s \<and> valid_irq_handlers' s
           \<and> valid_irq_states' s \<and> irqs_masked' s
           \<and> sym_heap_sched_pointers s \<and> valid_sched_pointers s \<and> valid_bitmaps s
           \<and> valid_machine_state' s
           \<and> cur_tcb' s \<and> ct_not_inQ s
           \<and> pspace_domain_valid s
           \<and> ksCurDomain s \<le> maxDomain
           \<and> valid_dom_schedule' s \<and> untyped_ranges_zero' s"

lemmas invs_no_cicd'_def = all_invs_but_ct_idle_or_in_cur_domain'_def

lemma all_invs_but_ct_idle_or_in_cur_domain_check':
  "(all_invs_but_ct_idle_or_in_cur_domain' and ct_idle_or_in_cur_domain') = invs'"
  by (simp add: all_invs_but_ct_idle_or_in_cur_domain'_def pred_conj_def
                conj_left_commute conj_commute invs'_def valid_state'_def)

abbreviation (input)
  "invs_no_cicd' \<equiv> all_invs_but_ct_idle_or_in_cur_domain'"

lemma invs'_to_invs_no_cicd'_def:
  "invs' = (all_invs_but_ct_idle_or_in_cur_domain' and ct_idle_or_in_cur_domain')"
  by (fastforce simp: invs'_def all_invs_but_ct_idle_or_in_cur_domain'_def valid_state'_def )

locale mdb_next =
  fixes m :: cte_heap

  fixes greater_eq
  defines "greater_eq a b \<equiv> m \<turnstile> a \<leadsto>\<^sup>* b"

  fixes greater
  defines "greater a b \<equiv> m \<turnstile> a \<leadsto>\<^sup>+ b"

locale mdb_order = mdb_next +
  assumes no_0: "no_0 m"
  assumes chain: "mdb_chain_0 m"

\<comment> \<open>---------------------------------------------------------------------------\<close>
section "Alternate split rules for preserving subgoal order"

lemma ntfn_splits[split]:
  " P (case ntfn of Structures_H.ntfn.IdleNtfn \<Rightarrow> f1
     | Structures_H.ntfn.ActiveNtfn x \<Rightarrow> f2 x
     | Structures_H.ntfn.WaitingNtfn x \<Rightarrow> f3 x) =
  ((ntfn = Structures_H.ntfn.IdleNtfn \<longrightarrow> P f1) \<and>
   (\<forall>x2. ntfn = Structures_H.ntfn.ActiveNtfn x2 \<longrightarrow>
         P (f2 x2)) \<and>
   (\<forall>x3. ntfn = Structures_H.ntfn.WaitingNtfn x3 \<longrightarrow>
         P (f3 x3)))"
  "P (case ntfn of Structures_H.ntfn.IdleNtfn \<Rightarrow> f1
     | Structures_H.ntfn.ActiveNtfn x \<Rightarrow> f2 x
     | Structures_H.ntfn.WaitingNtfn x \<Rightarrow> f3 x) =
  (\<not> (ntfn = Structures_H.ntfn.IdleNtfn \<and> \<not> P f1 \<or>
       (\<exists>x2. ntfn = Structures_H.ntfn.ActiveNtfn x2 \<and>
             \<not> P (f2 x2)) \<or>
       (\<exists>x3. ntfn = Structures_H.ntfn.WaitingNtfn x3 \<and>
             \<not> P (f3 x3))))"
  by (rule ntfn.splits)+

\<comment> \<open>---------------------------------------------------------------------------\<close>

section "Lemmas"

lemma valid_bound_ntfn'_None[simp]:
  "valid_bound_ntfn' None = \<top>"
  by (auto simp: valid_bound_ntfn'_def)

lemma valid_bound_ntfn'_Some[simp]:
  "valid_bound_ntfn' (Some x) = ntfn_at' x"
  by (auto simp: valid_bound_ntfn'_def)

lemma valid_bound_tcb'_None[simp]:
  "valid_bound_tcb' None = \<top>"
  by (auto simp: valid_bound_tcb'_def)

lemma valid_bound_tcb'_Some[simp]:
  "valid_bound_tcb' (Some x) = tcb_at' x"
  by (auto simp: valid_bound_tcb'_def)

lemma objBitsKO_Data:
  "objBitsKO (if dev then KOUserDataDevice else KOUserData) = pageBits"
  by (simp add: objBits_def objBitsKO_def word_size_def)

(* non-gen versions are in Arch *)
lemmas gen_objBits_simps = objBits_def objBitsKO_def

lemma ps_clear_def2:
  "p \<le> p + 1 \<Longrightarrow> ps_clear p n s = ({p + 1 .. p + (1 << n) - 1} \<inter> dom (ksPSpace s) = {})"
  apply (simp add: ps_clear_def mask_def add_diff_eq)
  apply safe
   apply (drule_tac a=x in equals0D)
   apply clarsimp
   apply (drule mp, simp)
   apply (erule disjE)
    apply simp
   apply clarsimp
  apply (drule_tac a=x in equals0D)
  apply clarsimp
  apply (case_tac "p + 1 \<le> x")
   apply clarsimp
  apply (simp add: linorder_not_le)
  apply (drule plus_one_helper, simp)
  done

lemma projectKO_stateI:
  "fst (projectKO e s) = {(obj, s)} \<Longrightarrow> fst (projectKO e s') = {(obj, s')}"
  unfolding projectKO_def
  by (auto simp: fail_def return_def valid_def split: option.splits)

lemma singleton_in_magnitude_check:
  "(x, s) \<in> fst (magnitudeCheck a b c s') \<Longrightarrow> \<forall>s'. fst (magnitudeCheck a b c s') = {(x, s')}"
  by (simp add: magnitudeCheck_def when_def in_monad return_def
         split: if_split_asm option.split_asm)

lemma projectKO_eq:
  "(fst (projectKO ko c) = {(obj, c)}) = (projectKO_opt ko = Some obj)"
  by (simp add: projectKO_def fail_def return_def split: option.splits)

lemma obj_at'_def':
  "obj_at' P p s = (\<exists>ko obj. ksPSpace s p = Some ko \<and> is_aligned p (objBitsKO ko)
                   \<and> fst (projectKO ko s) = {(obj,s)} \<and> P obj
                   \<and> ps_clear p (objBitsKO ko) s)"
  apply (simp add: obj_at'_real_def ko_wp_at'_def projectKO_eq
                   True_notin_set_replicate_conv objBits_def)
  apply fastforce
  done

lemma obj_at'_def:
  "obj_at' P p s \<equiv> \<exists>ko obj. ksPSpace s p = Some ko \<and> is_aligned p (objBitsKO ko)
                   \<and> fst (projectKO ko s) = {(obj,s)} \<and> P obj
                   \<and> ps_clear p (objBitsKO ko) s"
  by (simp add: obj_at'_def')

lemma obj_atE' [elim?]:
  assumes objat: "obj_at' P ptr s"
  and        rl: "\<And>ko obj.
  \<lbrakk> ksPSpace s ptr = Some ko; is_aligned ptr (objBitsKO ko);
     fst (projectKO ko s) = {(obj,s)}; P obj;
     ps_clear ptr (objBitsKO ko) s \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using objat unfolding obj_at'_def by (auto intro!: rl)

lemma obj_atI' [intro?]:
  "\<lbrakk> ksPSpace s ptr = Some ko; is_aligned ptr (objBitsKO ko);
       fst (projectKO ko s) = {(obj, s)}; P obj;
       ps_clear ptr (objBitsKO ko) s \<rbrakk>
  \<Longrightarrow> obj_at' P ptr s"
  unfolding obj_at'_def by (auto)

lemma cte_at'_def:
  "cte_at' p s \<equiv> \<exists>cte::cte. fst (getObject p s) = {(cte,s)}"
  by (simp add: cte_wp_at'_def)

lemma refs_of'_simps[simp]:
 "refs_of' (KOTCB tcb)           = tcb_st_refs_of' (tcbState tcb) \<union> tcb_bound_refs' (tcbBoundNotification tcb)"
 "refs_of' (KOCTE cte)           = {}"
 "refs_of' (KOEndpoint ep)       = ep_q_refs_of' ep"
 "refs_of' (KONotification ntfn)     = ntfn_q_refs_of' (ntfnObj ntfn) \<union> ntfn_bound_refs' (ntfnBoundTCB ntfn)"
 "refs_of' (KOUserData)          = {}"
 "refs_of' (KOUserDataDevice)          = {}"
 "refs_of' (KOKernelData)        = {}"
 "refs_of' (KOArch ako)          = {}"
  by (auto simp: refs_of'_def)

lemma tcb_st_refs_of'_simps[simp]:
 "tcb_st_refs_of' (Running)                  = {}"
 "tcb_st_refs_of' (Inactive)                 = {}"
 "tcb_st_refs_of' (Restart)                  = {}"
 "tcb_st_refs_of' (BlockedOnReceive x'' a')  = {(x'', TCBBlockedRecv)}"
 "tcb_st_refs_of' (BlockedOnSend x a b c d)  = {(x, TCBBlockedSend)}"
 "tcb_st_refs_of' (BlockedOnNotification x') = {(x', TCBSignal)}"
 "tcb_st_refs_of' (BlockedOnReply)           = {}"
 "tcb_st_refs_of' (IdleThreadState)          = {}"
  by (auto simp: tcb_st_refs_of'_def)

lemma ep_q_refs_of'_simps[simp]:
 "ep_q_refs_of'  IdleEP    = {}"
 "ep_q_refs_of' (RecvEP q) = set q \<times> {EPRecv}"
 "ep_q_refs_of' (SendEP q) = set q \<times> {EPSend}"
  by (auto simp: ep_q_refs_of'_def)

lemma ntfn_q_refs_of'_simps[simp]:
 "ntfn_q_refs_of'  IdleNtfn         = {}"
 "ntfn_q_refs_of' (WaitingNtfn q)      = set q \<times> {NTFNSignal}"
 "ntfn_q_refs_of' (ActiveNtfn b)  = {}"
  by (auto simp: ntfn_q_refs_of'_def)

lemma ntfn_bound_refs'_simps[simp]:
  "ntfn_bound_refs' (Some t) = {(t, NTFNBound)}"
  "ntfn_bound_refs' None = {}"
  by (auto simp: ntfn_bound_refs'_def)

lemma tcb_bound_refs'_simps[simp]:
  "tcb_bound_refs' (Some a) = {(a, TCBBound)}"
  "tcb_bound_refs' None = {}"
  by (auto simp: tcb_bound_refs'_def)

lemma refs_of_rev':
 "(x, TCBBlockedRecv) \<in> refs_of' ko =
    (\<exists>tcb. ko = KOTCB tcb \<and> (\<exists>a. tcbState tcb = BlockedOnReceive x a))"
 "(x, TCBBlockedSend) \<in> refs_of' ko =
    (\<exists>tcb. ko = KOTCB tcb \<and> (\<exists>a b c d. tcbState tcb = BlockedOnSend x a b c d))"
 "(x, TCBSignal) \<in> refs_of' ko =
    (\<exists>tcb. ko = KOTCB tcb \<and> tcbState tcb = BlockedOnNotification x)"
 "(x, EPRecv) \<in> refs_of' ko =
    (\<exists>ep. ko = KOEndpoint ep \<and> (\<exists>q. ep = RecvEP q \<and> x \<in> set q))"
 "(x, EPSend) \<in> refs_of' ko =
    (\<exists>ep. ko = KOEndpoint ep \<and> (\<exists>q. ep = SendEP q \<and> x \<in> set q))"
 "(x, NTFNSignal) \<in> refs_of' ko =
    (\<exists>ntfn. ko = KONotification ntfn \<and> (\<exists>q. ntfnObj ntfn = WaitingNtfn q \<and> x \<in> set q))"
 "(x, TCBBound) \<in>  refs_of' ko =
    (\<exists>tcb. ko = KOTCB tcb \<and> (tcbBoundNotification tcb = Some x))"
 "(x, NTFNBound) \<in> refs_of' ko =
    (\<exists>ntfn. ko = KONotification ntfn \<and> (ntfnBoundTCB ntfn = Some x))"
  by (auto simp: refs_of'_def
                 tcb_st_refs_of'_def
                 ep_q_refs_of'_def
                 ntfn_q_refs_of'_def
                 ntfn_bound_refs'_def
                 tcb_bound_refs'_def
          split: Structures_H.kernel_object.splits
                 Structures_H.thread_state.splits
                 Structures_H.endpoint.splits
                 Structures_H.notification.splits
                 Structures_H.ntfn.splits)+

lemma hyp_refs_of'_simps[simp]:
  "hyp_refs_of' (KOCTE cte) = {}"
  "hyp_refs_of' (KOTCB tcb) = tcb_hyp_refs' (tcbArch tcb)"
  "hyp_refs_of' (KOEndpoint ep) = {}"
  "hyp_refs_of' (KONotification ntfn) = {}"
  "hyp_refs_of' (KOUserData) = {}"
  "hyp_refs_of' (KOUserDataDevice) = {}"
  "hyp_refs_of' (KOKernelData) = {}"
  "hyp_refs_of' (KOArch ao) = refs_of_a' ao"
  by (auto simp: hyp_refs_of'_def)

lemma ko_wp_at'_weakenE:
  "\<lbrakk> ko_wp_at' P p s; \<And>ko. P ko \<Longrightarrow> Q ko \<rbrakk> \<Longrightarrow> ko_wp_at' Q p s"
  by (clarsimp simp: ko_wp_at'_def)

lemma projectKO_opt_tcbD:
  "projectKO_opt ko = Some (tcb :: tcb) \<Longrightarrow> ko = KOTCB tcb"
  by (cases ko, simp_all add: projectKO_opt_tcb)

lemma st_tcb_at_refs_of_rev':
  "ko_wp_at' (\<lambda>ko. (x, TCBBlockedRecv) \<in> refs_of' ko) t s
     = st_tcb_at' (\<lambda>ts. \<exists>a. ts = BlockedOnReceive x a) t s"
  "ko_wp_at' (\<lambda>ko. (x, TCBBlockedSend) \<in> refs_of' ko) t s
     = st_tcb_at' (\<lambda>ts. \<exists>a b c d. ts = BlockedOnSend x a b c d) t s"
  "ko_wp_at' (\<lambda>ko. (x, TCBSignal) \<in> refs_of' ko) t s
     = st_tcb_at' (\<lambda>ts. ts = BlockedOnNotification x) t s"
  by (fastforce simp: refs_of_rev' pred_tcb_at'_def obj_at'_real_def
                     projectKO_opt_tcb[where e="KOTCB y" for y]
              elim!: ko_wp_at'_weakenE
              dest!: projectKO_opt_tcbD)+

lemma state_refs_of'_elemD:
  "\<lbrakk> ref \<in> state_refs_of' s x \<rbrakk> \<Longrightarrow> ko_wp_at' (\<lambda>obj. ref \<in> refs_of' obj) x s"
  by (clarsimp simp add: state_refs_of'_def ko_wp_at'_def
                  split: option.splits if_split_asm)

lemma obj_at_state_refs_ofD':
  "obj_at' P p s \<Longrightarrow> \<exists>obj. P obj \<and> state_refs_of' s p = refs_of' (injectKO obj)"
  apply (clarsimp simp: obj_at'_real_def project_inject ko_wp_at'_def conj_commute)
  apply (rule exI, erule conjI)
  apply (clarsimp simp: state_refs_of'_def)
  done

lemma ko_at_state_refs_ofD':
  "ko_at' ko p s \<Longrightarrow> state_refs_of' s p = refs_of' (injectKO ko)"
  by (clarsimp dest!: obj_at_state_refs_ofD')

definition
  tcb_ntfn_is_bound' :: "machine_word option \<Rightarrow> tcb \<Rightarrow> bool"
where
  "tcb_ntfn_is_bound' ntfn tcb \<equiv> tcbBoundNotification tcb = ntfn"

lemma st_tcb_at_state_refs_ofD':
  "st_tcb_at' P t s \<Longrightarrow> \<exists>ts ntfnptr. P ts \<and> obj_at' (tcb_ntfn_is_bound' ntfnptr) t s
          \<and> state_refs_of' s t = (tcb_st_refs_of' ts \<union> tcb_bound_refs' ntfnptr)"
  by (auto simp: pred_tcb_at'_def tcb_ntfn_is_bound'_def obj_at'_def projectKO_eq
                 project_inject state_refs_of'_def)

lemma bound_tcb_at_state_refs_ofD':
  "bound_tcb_at' P t s \<Longrightarrow> \<exists>ts ntfnptr. P ntfnptr \<and> obj_at' (tcb_ntfn_is_bound' ntfnptr) t s
          \<and> state_refs_of' s t = (tcb_st_refs_of' ts \<union> tcb_bound_refs' ntfnptr)"
  by (auto simp: pred_tcb_at'_def obj_at'_def tcb_ntfn_is_bound'_def projectKO_eq
                 project_inject state_refs_of'_def)

lemma sym_refs_obj_atD':
  "\<lbrakk> obj_at' P p s; sym_refs (state_refs_of' s) \<rbrakk> \<Longrightarrow>
     \<exists>obj. P obj \<and> state_refs_of' s p = refs_of' (injectKO obj)
        \<and> (\<forall>(x, tp)\<in>refs_of' (injectKO obj). ko_wp_at' (\<lambda>ko. (p, symreftype tp) \<in> refs_of' ko) x s)"
  apply (drule obj_at_state_refs_ofD')
  apply (erule exEI, clarsimp)
  apply (drule sym, simp)
  apply (drule(1) sym_refsD)
  apply (erule state_refs_of'_elemD)
  done

lemma sym_refs_ko_atD':
  "\<lbrakk> ko_at' ko p s; sym_refs (state_refs_of' s) \<rbrakk> \<Longrightarrow>
     state_refs_of' s p = refs_of' (injectKO ko) \<and>
     (\<forall>(x, tp)\<in>refs_of' (injectKO ko). ko_wp_at' (\<lambda>ko. (p, symreftype tp) \<in> refs_of' ko) x s)"
  by (drule(1) sym_refs_obj_atD', simp)

lemma sym_refs_st_tcb_atD':
  "\<lbrakk> st_tcb_at' P t s; sym_refs (state_refs_of' s) \<rbrakk> \<Longrightarrow>
     \<exists>ts ntfnptr. P ts \<and> obj_at' (tcb_ntfn_is_bound' ntfnptr) t s
        \<and> state_refs_of' s t = tcb_st_refs_of' ts \<union> tcb_bound_refs' ntfnptr
        \<and> (\<forall>(x, tp)\<in>tcb_st_refs_of' ts \<union> tcb_bound_refs' ntfnptr. ko_wp_at' (\<lambda>ko. (t, symreftype tp) \<in> refs_of' ko) x s)"
  apply (drule st_tcb_at_state_refs_ofD')
  apply (erule exE)+
  apply (rule_tac x=ts in exI)
  apply (rule_tac x=ntfnptr in exI)
  apply clarsimp
  apply (frule obj_at_state_refs_ofD')
  apply (drule (1)sym_refs_obj_atD')
  apply auto
  done

lemma sym_refs_bound_tcb_atD':
  "\<lbrakk> bound_tcb_at' P t s; sym_refs (state_refs_of' s) \<rbrakk> \<Longrightarrow>
     \<exists>ts ntfnptr. P ntfnptr \<and> obj_at' (tcb_ntfn_is_bound' ntfnptr) t s
        \<and> state_refs_of' s t = tcb_st_refs_of' ts \<union> tcb_bound_refs' ntfnptr
        \<and> (\<forall>(x, tp)\<in>tcb_st_refs_of' ts \<union> tcb_bound_refs' ntfnptr. ko_wp_at' (\<lambda>ko. (t, symreftype tp) \<in> refs_of' ko) x s)"
  apply (drule bound_tcb_at_state_refs_ofD')
  apply (erule exE)+
  apply (rule_tac x=ts in exI)
  apply (rule_tac x=ntfnptr in exI)
  apply clarsimp
  apply (frule obj_at_state_refs_ofD')
  apply (drule (1)sym_refs_obj_atD')
  apply auto
  done

lemma state_hyp_refs_of'_elemD:
  "\<lbrakk> ref \<in> state_hyp_refs_of' s x \<rbrakk> \<Longrightarrow> ko_wp_at' (\<lambda>obj. ref \<in> hyp_refs_of' obj) x s"
  by (clarsimp simp add: state_hyp_refs_of'_def ko_wp_at'_def
                  split: option.splits if_split_asm)

lemma obj_at_state_hyp_refs_ofD':
  "obj_at' P p s \<Longrightarrow> \<exists>ko. P ko \<and> state_hyp_refs_of' s p = hyp_refs_of' (injectKO ko)"
  apply (clarsimp simp: obj_at'_real_def project_inject ko_wp_at'_def conj_commute)
  apply (rule exI, erule conjI)
  apply (clarsimp simp: state_hyp_refs_of'_def)
  done

lemma ko_at_state_hyp_refs_ofD':
  "ko_at' ko p s \<Longrightarrow> state_hyp_refs_of' s p = hyp_refs_of' (injectKO ko)"
  by (clarsimp dest!: obj_at_state_hyp_refs_ofD')

lemma hyp_sym_refs_obj_atD':
  "\<lbrakk> obj_at' P p s; sym_refs (state_hyp_refs_of' s) \<rbrakk> \<Longrightarrow>
     \<exists>ko. P ko \<and> state_hyp_refs_of' s p = hyp_refs_of' (injectKO ko) \<and>
        (\<forall>(x, tp)\<in>hyp_refs_of' (injectKO ko). ko_wp_at' (\<lambda>ko. (p, symreftype tp) \<in> hyp_refs_of' ko) x s)"
  apply (drule obj_at_state_hyp_refs_ofD')
  apply (erule exEI, clarsimp)
  apply (drule sym, simp)
  apply (drule(1) sym_refsD)
  apply (erule state_hyp_refs_of'_elemD)
  done

lemma refs_of_live':
  "refs_of' ko \<noteq> {} \<Longrightarrow> live' ko"
  apply (cases ko, simp_all add: live'_def)
    apply clarsimp
   apply (rename_tac notification)
   apply (case_tac "ntfnObj notification"; simp)
    apply fastforce+
  done

lemma if_live_then_nonz_capE':
  "\<lbrakk> if_live_then_nonz_cap' s; ko_wp_at' live' p s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to' p s"
  by (fastforce simp: if_live_then_nonz_cap'_def)

lemma if_live_then_nonz_capD':
  assumes x: "if_live_then_nonz_cap' s" "ko_wp_at' P p s"
  assumes y: "\<And>obj. \<lbrakk> P obj; ksPSpace s p = Some obj; is_aligned p (objBitsKO obj) \<rbrakk> \<Longrightarrow> live' obj"
  shows "ex_nonz_cap_to' p s" using x
  by (clarsimp elim!: if_live_then_nonz_capE' y
                simp: ko_wp_at'_def)

lemma if_live_state_refsE:
  "\<lbrakk> if_live_then_nonz_cap' s;
     state_refs_of' s p \<noteq> {} \<rbrakk> \<Longrightarrow> ex_nonz_cap_to' p s"
  by (clarsimp simp: state_refs_of'_def ko_wp_at'_def
              split: option.splits if_split_asm
              elim!: refs_of_live' if_live_then_nonz_capE')

lemmas ex_cte_cap_to'_def = ex_cte_cap_wp_to'_def

lemma if_unsafe_then_capD':
  "\<lbrakk> cte_wp_at' P p s; if_unsafe_then_cap' s; \<And>cte. P cte \<Longrightarrow> cteCap cte \<noteq> NullCap \<rbrakk>
     \<Longrightarrow> ex_cte_cap_to' p s"
  unfolding if_unsafe_then_cap'_def
  apply (erule allE, erule mp)
  apply (clarsimp simp: cte_wp_at'_def)
  done

lemma max_ipc_words:
  "max_ipc_words = 0x80"
  unfolding max_ipc_words_def
  by (simp add: msgMaxLength_def msgLengthBits_def msgMaxExtraCaps_def msgExtraCapBits_def capTransferDataSize_def)

lemma valid_objsE' [elim]:
  "\<lbrakk> valid_objs' s; ksPSpace s x = Some obj; valid_obj' obj s \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding valid_objs'_def by auto

lemma pspace_distinctD':
  "\<lbrakk> ksPSpace s x = Some v; pspace_distinct' s \<rbrakk> \<Longrightarrow> ps_clear x (objBitsKO v) s"
  apply (simp add: pspace_distinct'_def)
  apply (drule bspec, erule domI)
  apply simp
  done

lemma pspace_alignedD':
  "\<lbrakk> ksPSpace s x = Some v; pspace_aligned' s \<rbrakk> \<Longrightarrow> is_aligned x (objBitsKO v)"
  apply (simp add: pspace_aligned'_def)
  apply (drule bspec, erule domI)
  apply simp
  done

lemma next_unfold:
  "mdb_next s c =
   (case s c of Some cte \<Rightarrow> Some (mdbNext (cteMDBNode cte)) | None \<Rightarrow> None)"
  by (simp add: mdb_next_def split: option.split)

lemma sch_act_sane_not:
  "sch_act_sane s = sch_act_not (ksCurThread s) s"
  by (auto simp: sch_act_sane_def)

lemmas valid_irq_states'_def = valid_irq_masks'_def

lemma valid_pspaceE' [elim]:
  "\<lbrakk>valid_pspace' s;
    \<lbrakk> valid_objs' s; pspace_aligned' s; pspace_distinct' s; pspace_canonical' s; no_0_obj' s;
      valid_mdb' s \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding valid_pspace'_def by simp

lemma idle'_no_refs:
  "valid_idle' s \<Longrightarrow> state_refs_of' s (ksIdleThread s) = {}"
  by (clarsimp simp: valid_idle'_def pred_tcb_at'_def obj_at'_def tcb_ntfn_is_bound'_def
                     projectKO_eq project_inject state_refs_of'_def idle_tcb'_def)

lemma idle'_not_queued':
  "\<lbrakk>valid_idle' s; sym_refs (state_refs_of' s);
    state_refs_of' s ptr = insert t queue \<times> {rt}\<rbrakk>\<Longrightarrow>
   ksIdleThread s \<notin> queue"
  by (frule idle'_no_refs, fastforce simp: valid_idle'_def sym_refs_def)

lemma idle'_not_queued:
  "\<lbrakk>valid_idle' s; sym_refs (state_refs_of' s);
    state_refs_of' s ptr = queue \<times> {rt}\<rbrakk> \<Longrightarrow>
   ksIdleThread s \<notin> queue"
  by (frule idle'_no_refs, fastforce simp: valid_idle'_def sym_refs_def)


lemma obj_at_conj':
  "\<lbrakk> obj_at' P p s; obj_at' Q p s \<rbrakk> \<Longrightarrow> obj_at' (\<lambda>k. P k \<and> Q k) p s"
  by (auto simp: obj_at'_def)

lemma pred_tcb_at_conj':
  "\<lbrakk> pred_tcb_at' proj P t s; pred_tcb_at' proj Q t s \<rbrakk> \<Longrightarrow> pred_tcb_at' proj (\<lambda>a. P a \<and> Q a) t s"
  apply (simp add: pred_tcb_at'_def)
  apply (erule (1) obj_at_conj')
  done

lemma obj_at_False' [simp]:
  "obj_at' (\<lambda>k. False) t s = False"
  by (simp add: obj_at'_def)

lemma pred_tcb_at_False' [simp]:
  "pred_tcb_at' proj (\<lambda>st. False) t s = False"
  by (simp add: pred_tcb_at'_def obj_at'_def)

lemma obj_at'_pspaceI:
  "obj_at' t ref s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow>  obj_at' t ref s'"
  by (auto intro!: projectKO_stateI simp: obj_at'_def ps_clear_def)

lemma valid_untyped'_pspaceI:
  "\<lbrakk>ksPSpace s = ksPSpace s'; valid_untyped' d p n idx s\<rbrakk>
  \<Longrightarrow> valid_untyped' d p n idx s'"
  by (simp add: valid_untyped'_def ko_wp_at'_def ps_clear_def)

lemma typ_at'_pspaceI:
  "typ_at' T p s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> typ_at' T p s'"
  by (simp add: typ_at'_def ko_wp_at'_def ps_clear_def)

(* all architectures have same slots, only cteSizeBits will vary *)
lemma (in Arch) tcb_cte_cases_distinct_n:
  "distinct [
     0 << cteSizeBits :: machine_word,
     1 << cteSizeBits,
     2 << cteSizeBits,
     3 << cteSizeBits,
     4 << cteSizeBits]"
  by (simp add: cteSizeBits_def wordSizeCase_def wordBits_def word_size)

requalify_facts Arch.tcb_cte_cases_distinct_n

lemmas tcb_cte_cases_neqs_n =
  conjI[OF
    tcb_cte_cases_distinct_n[simplified]
    distinct_rev[THEN iffD2, OF tcb_cte_cases_distinct_n, simplified],
    simplified conj_ac, simplified] (* remove duplicates from 0/1 simplification *)

lemma tcb_cte_cases_simps[simp]:
  "tcb_cte_cases 0  = Some (tcbCTable, tcbCTable_update)"
  "tcb_cte_cases (1 << cteSizeBits) = Some (tcbVTable, tcbVTable_update)"
  "tcb_cte_cases (2 << cteSizeBits) = Some (tcbReply, tcbReply_update)"
  "tcb_cte_cases (3 << cteSizeBits) = Some (tcbCaller, tcbCaller_update)"
  "tcb_cte_cases (4 << cteSizeBits) = Some (tcbIPCBufferFrame, tcbIPCBufferFrame_update)"
  by (simp add: tcb_cte_cases_neqs_n tcb_cte_cases_def)+

lemmas tcbSlot_defs = tcbCTableSlot_def tcbVTableSlot_def tcbReplySlot_def tcbCallerSlot_def
                      tcbIPCBufferSlot_def

lemma tcb_cte_cases_distinct:
  "distinct [
     tcbCTableSlot << cteSizeBits :: machine_word,
     tcbVTableSlot << cteSizeBits,
     tcbReplySlot << cteSizeBits,
     tcbCallerSlot << cteSizeBits,
     tcbIPCBufferSlot << cteSizeBits]"
  by (simp add: tcbSlot_defs tcb_cte_cases_neqs_n)

lemmas tcb_cte_cases_neqs =
  tcb_cte_cases_neqs_n
  tcb_cte_cases_distinct[simplified]
  distinct_rev[THEN iffD2, OF tcb_cte_cases_distinct, simplified]

lemma objBits_cte_conv: "objBits (cte :: cte) = cteSizeBits"
  by (simp add: gen_objBits_simps word_size)

lemma in_alignCheck[simp]:
  "((v, s') \<in> fst (alignCheck x n s)) = (s' = s \<and> is_aligned x n)"
  by (simp add: alignCheck_def in_monad is_aligned_mask[symmetric]
                alignError_def conj_comms
          cong: conj_cong)

lemma cte_wp_at'_pspaceI:
  "\<lbrakk>cte_wp_at' P p s; ksPSpace s = ksPSpace s'\<rbrakk> \<Longrightarrow> cte_wp_at' P p s'"
  supply in_alignCheck[simp del]
  apply (clarsimp simp add: cte_wp_at'_def getObject_def)
  apply (drule equalityD2)
  apply (clarsimp simp: in_monad loadObject_cte gets_def
                        get_def bind_def return_def split_def)
  apply (case_tac b)
        apply (simp_all add: in_monad typeError_def)
   prefer 2
   apply (simp add: in_monad return_def alignError_def assert_opt_def
                    alignCheck_def magnitudeCheck_def when_def bind_def
             split: if_split_asm option.splits)
  apply (clarsimp simp: in_monad return_def alignError_def fail_def assert_opt_def
                        alignCheck_def bind_def when_def
                        objBits_cte_conv tcb_cte_cases_neqs
                 split: if_split_asm cong: image_cong
                 dest!: singleton_in_magnitude_check)
  done


locale Invariants_H_pspaceI =
  assumes valid_cap'_pspaceI:
    "\<And>cap s s'. s \<turnstile>' cap \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> s' \<turnstile>' cap"
  assumes valid_obj'_pspaceI:
    "\<And>obj s s'. valid_obj' obj s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> valid_obj' obj s'"
  assumes pspace_in_kernel_mappings'_pspaceI:
    "\<And>s s'. pspace_in_kernel_mappings' s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> pspace_in_kernel_mappings' s'"
  assumes tcb_space_clear:
    "\<And>tcb getF setF P s x y v.
     \<lbrakk> tcb_cte_cases (y - x) = Some (getF, setF);
       is_aligned x tcbBlockSizeBits; ps_clear x tcbBlockSizeBits s;
       ksPSpace s x = Some (KOTCB tcb); ksPSpace s y = Some v;
       \<lbrakk> x = y; getF = tcbCTable; setF = tcbCTable_update \<rbrakk> \<Longrightarrow> P
      \<rbrakk> \<Longrightarrow> P"

lemma pred_tcb_at'_pspaceI:
  "pred_tcb_at' proj P t s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> pred_tcb_at' proj P t s'"
  unfolding pred_tcb_at'_def by (fast intro: obj_at'_pspaceI)

lemma valid_mdb'_pspaceI:
  "valid_mdb' s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> valid_mdb' s'"
  unfolding valid_mdb'_def by simp

lemma state_refs_of'_pspaceI:
  "P (state_refs_of' s) \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> P (state_refs_of' s')"
  unfolding state_refs_of'_def ps_clear_def by (simp cong: option.case_cong)

lemma state_hyp_refs_of'_pspaceI:
  "P (state_hyp_refs_of' s) \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> P (state_hyp_refs_of' s')"
  unfolding state_hyp_refs_of'_def ps_clear_def by (simp cong: option.case_cong)

lemma (in Invariants_H_pspaceI) valid_pspace':
  "valid_pspace' s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow> valid_pspace' s'"
  by  (auto simp add: valid_pspace'_def valid_objs'_def pspace_aligned'_def
                     pspace_distinct'_def ps_clear_def no_0_obj'_def ko_wp_at'_def
                     typ_at'_def pspace_canonical'_def
           intro: valid_obj'_pspaceI valid_mdb'_pspaceI pspace_in_kernel_mappings'_pspaceI)

lemma (in Invariants_H_pspaceI) ex_cte_cap_to_pspaceI'[elim]:
  "ex_cte_cap_to' p s \<Longrightarrow> ksPSpace s = ksPSpace s' \<Longrightarrow>
     intStateIRQNode (ksInterruptState s) = intStateIRQNode (ksInterruptState s')
     \<Longrightarrow> ex_cte_cap_to' p s'"
  by (fastforce simp: ex_cte_cap_to'_def elim: cte_wp_at'_pspaceI)

lemma valid_idle'_pspace_itI[elim]:
  "\<lbrakk> valid_idle' s; ksPSpace s = ksPSpace s'; ksIdleThread s = ksIdleThread s' \<rbrakk>
      \<Longrightarrow> valid_idle' s'"
  apply (clarsimp simp: valid_idle'_def ex_nonz_cap_to'_def)
  apply (erule obj_at'_pspaceI, assumption)
  done

lemma obj_at'_weaken:
  assumes x: "obj_at' P t s"
  assumes y: "\<And>obj. P obj \<Longrightarrow> P' obj"
  shows "obj_at' P' t s"
  by (insert x, clarsimp simp: obj_at'_def y)

lemma cte_wp_at_weakenE':
  "\<lbrakk>cte_wp_at' P t s; \<And>c. P c \<Longrightarrow> P' c\<rbrakk> \<Longrightarrow> cte_wp_at' P' t s"
  by (fastforce simp: cte_wp_at'_def)

lemma obj_at'_weakenE:
  "\<lbrakk> obj_at' P p s; \<And>k. P k \<Longrightarrow> P' k \<rbrakk> \<Longrightarrow> obj_at' P' p s"
  by (clarsimp simp: obj_at'_def)

lemma pred_tcb'_weakenE:
  "\<lbrakk> pred_tcb_at' proj P t s; \<And>st. P st \<Longrightarrow> P' st \<rbrakk> \<Longrightarrow> pred_tcb_at' proj P' t s"
  apply (simp add: pred_tcb_at'_def)
  apply (erule obj_at'_weakenE)
  apply clarsimp
  done

lemma lookupAround2_char1:
  "(fst (lookupAround2 x s) = Some (y, v)) =
    (y \<le> x \<and> s y = Some v \<and> (\<forall>z. y < z \<and> z \<le> x \<longrightarrow> s z = None))"
  apply (simp    add: lookupAround2_def Let_def split_def lookupAround_def
           split del: if_split
               split: option.split)
  apply (intro conjI impI iffI)
      apply (clarsimp split: if_split_asm)
      apply (rule Max_prop)
       apply (simp add: order_less_imp_le)
      apply fastforce
     apply (clarsimp split: if_split_asm)
     apply (rule Max_prop)
      apply clarsimp
     apply fastforce
    apply (clarsimp split: if_split_asm)
    apply (subst(asm) Max_less_iff)
      apply simp
     apply fastforce
    apply (fastforce intro: order_neq_le_trans)
   apply (clarsimp cong: conj_cong)
   apply (rule conjI)
    apply fastforce
   apply (rule order_antisym)
    apply (subst Max_le_iff)
      apply simp
     apply fastforce
    apply clarsimp
    apply (rule ccontr)
    apply (fastforce simp add: linorder_not_le)
   apply (rule Max_ge)
    apply simp
   apply fastforce
  apply (intro allI impI iffI)
   apply clarsimp
   apply simp
  apply clarsimp
  apply (drule spec[where x=x])
  apply simp
  done

lemma lookupAround2_None1:
  "(fst (lookupAround2 x s) = None) = (\<forall>y \<le> x. s y = None)"
  apply (simp    add: lookupAround2_def Let_def split_def lookupAround_def
           split del: if_split
               split: option.split)
  apply safe
    apply (fastforce split: if_split_asm)
   apply (clarsimp simp: order_less_imp_le)
  apply fastforce
  done

lemma lookupAround2_None2:
  "(snd (lookupAround2 x s) = None) = (\<forall>y. x < y \<longrightarrow> s y = None)"
  apply (simp add: lookupAround2_def Let_def split_def del: maybe_def
               split: option.splits)
  apply (simp add: o_def map_option_is_None [where f=fst, unfolded map_option_case])
  apply (simp add: lookupAround_def Let_def)
  apply fastforce
  done

lemma lookupAround2_char2:
  "(snd (lookupAround2 x s) = Some y) = (x < y \<and> s y \<noteq> None \<and> (\<forall>z. x < z \<and> z < y \<longrightarrow> s z = None))"
  apply (simp add: lookupAround2_def Let_def split_def o_def
              del: maybe_def
              split: option.splits)
  apply (simp add: o_def map_option_is_None [where f=fst, unfolded map_option_case])
  apply (simp add: lookupAround_def Let_def)
  apply (rule conjI)
   apply fastforce
  apply clarsimp
  apply (rule iffI)
   apply (frule subst[where P="\<lambda>x. x \<in> y2" for y2, OF _ Min_in])
     apply simp
    apply fastforce
   apply clarsimp
   apply (subst(asm) Min_gr_iff, simp, fastforce, simp(no_asm_use), fastforce)
  apply clarsimp
  apply (rule order_antisym)
   apply (fastforce intro: Min_le)
  apply (subst Min_ge_iff)
    apply simp
   apply fastforce
  apply clarsimp
  apply (rule ccontr, simp add: linorder_not_le)
  done

lemma ps_clearI:
  "\<lbrakk> is_aligned p n; (1 :: machine_word) < 2 ^ n;
     \<And>x. \<lbrakk> x > p; x \<le> p + 2 ^ n - 1 \<rbrakk> \<Longrightarrow> ksPSpace s x = None \<rbrakk>
      \<Longrightarrow> ps_clear p n s"
  apply (subgoal_tac "p \<le> p + 1")
   apply (simp add: ps_clear_def2)
   apply (rule ccontr, erule nonemptyE, clarsimp)
   apply (drule word_leq_le_minus_one[where x="z + 1" for z])
    apply clarsimp
   apply simp
  apply (erule is_aligned_get_word_bits)
   apply (erule(1) is_aligned_no_wrap')
  apply simp
  done

lemma ps_clear_lookupAround2:
  "\<lbrakk> ps_clear p' n s; ksPSpace s p' = Some x;
     p' \<le> p; p \<le> p' + 2 ^ n - 1;
     \<lbrakk> fst (lookupAround2 p (ksPSpace s)) = Some (p', x);
       case_option True (\<lambda>x. x - p' >= 2 ^ n) (snd (lookupAround2 p (ksPSpace s)))
      \<rbrakk> \<Longrightarrow> P (lookupAround2 p (ksPSpace s)) \<rbrakk> \<Longrightarrow> P (lookupAround2 p (ksPSpace s))"
  apply (drule meta_mp)
   apply (cases "fst (lookupAround2 p (ksPSpace s))")
    apply (simp add: lookupAround2_None1)
   apply clarsimp
   apply (clarsimp simp: lookupAround2_char1)
   apply (frule spec[where x=p'])
   apply (simp add: linorder_not_less ps_clear_def mask_def add_diff_eq)
   apply (drule_tac f="\<lambda>S. a \<in> S" in arg_cong)
   apply (simp add: domI)
   apply (frule(1) order_trans, simp)
  apply (erule meta_mp)
  apply (clarsimp split: option.split)
  apply (clarsimp simp: lookupAround2_char2 ps_clear_def mask_def add_diff_eq)
  apply (drule_tac a=x2 in equals0D)
  apply (simp add: domI)
  apply (subst(asm) order_less_imp_le[OF order_le_less_trans[where y=p]],
         assumption, assumption)
  apply simp
  apply (erule impCE, simp_all)
  apply (simp add: linorder_not_le)
  apply (subst(asm) add_diff_eq[symmetric],
         subst(asm) add.commute,
         drule word_l_diffs(2),
         fastforce simp only: field_simps)
  apply (rule ccontr, simp add: linorder_not_le)
  apply (drule word_le_minus_one_leq, fastforce)
  done

lemma in_magnitude_check:
  "\<lbrakk> is_aligned x n; (1 :: machine_word) < 2 ^ n; ksPSpace s x = Some y \<rbrakk> \<Longrightarrow>
   ((v, s') \<in> fst (magnitudeCheck x (snd (lookupAround2 x (ksPSpace s))) n s))
     = (s' = s \<and> ps_clear x n s)"
  apply (rule iffI)
   apply (clarsimp simp: magnitudeCheck_def in_monad lookupAround2_None2
                         lookupAround2_char2
                  split: option.split_asm)
    apply (erule(1) ps_clearI)
    apply simp
   apply (erule(1) ps_clearI)
   apply (simp add: linorder_not_less)
   apply (drule word_leq_le_minus_one[where x="2 ^ n"])
    apply (clarsimp simp: power_overflow)
   apply (drule word_l_diffs)
    apply simp
   apply (simp add: field_simps)
  apply clarsimp
  apply (erule is_aligned_get_word_bits)
   apply (erule(1) ps_clear_lookupAround2)
     apply simp
    apply (simp add: is_aligned_no_overflow)
   apply (clarsimp simp add: magnitudeCheck_def in_monad
                      split: option.split_asm)
   apply simp
  apply (simp add: power_overflow)
  done

lemma in_magnitude_check3:
  "\<lbrakk> \<forall>z. x < z \<and> z \<le> y \<longrightarrow> ksPSpace s z = None; is_aligned x n;
     (1 :: machine_word) < 2 ^ n; ksPSpace s x = Some v; x \<le> y; y - x < 2 ^ n \<rbrakk> \<Longrightarrow>
   fst (magnitudeCheck x (snd (lookupAround2 y (ksPSpace s))) n s)
     = (if ps_clear x n s then {((), s)} else {})"
  apply (rule set_eqI, rule iffI)
   apply (clarsimp simp: magnitudeCheck_def lookupAround2_char2
                         lookupAround2_None2 in_monad
                  split: option.split_asm)
    apply (drule(1) range_convergence1)
    apply (erule(1) ps_clearI)
    apply simp
   apply (erule is_aligned_get_word_bits)
    apply (drule(1) range_convergence2)
    apply (erule(1) ps_clearI)
    apply (simp add: linorder_not_less)
    apply (drule word_leq_le_minus_one[where x="2 ^ n" for n], simp)
    apply (drule word_l_diffs, simp)
    apply (simp add: field_simps)
   apply (simp add: power_overflow)
  apply (clarsimp split: if_split_asm)
  apply (erule(1) ps_clear_lookupAround2)
    apply simp
   apply (drule word_le_minus_one_leq[where x="y - x"])
   apply (drule word_plus_mono_right[where x=x and y="y - x"])
    apply (erule is_aligned_get_word_bits)
     apply (simp add: field_simps is_aligned_no_overflow)
    apply simp
   apply (simp add: field_simps)
  apply (simp add: magnitudeCheck_def return_def
                   iffD2[OF linorder_not_less] when_def
            split: option.split_asm)
  done

lemma (in Invariants_H_pspaceI) tcb_ctes_clear:
  "\<lbrakk> tcb_cte_cases (y - x) = Some (getF, setF);
     is_aligned x tcbBlockSizeBits; ps_clear x tcbBlockSizeBits s;
     ksPSpace s x = Some (KOTCB tcb) \<rbrakk>
     \<Longrightarrow> \<not> ksPSpace s y = Some (KOCTE cte)"
  apply clarsimp
  apply (erule(4) tcb_space_clear)
  apply simp
  done


(* FIXME arch-split: naming: do we want to use the opaque naming style of Invariants_AI_2? *)
locale Invariants_H_cte_ats =
  assumes cte_wp_at_cases':
    "\<And>P p s.
      cte_wp_at' P p s =
        ((\<exists>cte. ksPSpace s p = Some (KOCTE cte) \<and> is_aligned p cte_level_bits \<and> P cte \<and>
                ps_clear p cteSizeBits s) \<or>
         (\<exists>n tcb getF setF.
            ksPSpace s (p - n) = Some (KOTCB tcb) \<and>
            is_aligned (p - n) tcbBlockSizeBits \<and>
            tcb_cte_cases n = Some (getF, setF) \<and> P (getF tcb) \<and>
            ps_clear (p - n) tcbBlockSizeBits s))"
  assumes cte_at_typ':
    "\<And>c. cte_at' c = (\<lambda>s. typ_at' CTET c s \<or> (\<exists>n. typ_at' TCBT (c - n) s \<and> n \<in> dom tcb_cte_cases))"

lemma (in Invariants_H_cte_ats) cte_wp_at_tcbI':
  assumes "ksPSpace s ptr' = Some (KOTCB tcb)"
  assumes "is_aligned ptr' tcbBlockSizeBits"
  assumes "ps_clear ptr' tcbBlockSizeBits s"
  and     "tcb_cte_cases (ptr - ptr') = Some (getF, setF)"
  and     "P (getF tcb)"
  shows "cte_wp_at' P ptr s"
  using assms
  apply (simp add: cte_wp_at_cases')
  apply (rule disjI2, rule exI[where x="ptr - ptr'"])
  apply simp
  done

lemma obj_at_ko_at':
  "obj_at' P p s \<Longrightarrow> \<exists>ko. ko_at' ko p s \<and> P ko"
  by (auto simp add: obj_at'_def)

lemma obj_at_aligned':
  fixes P :: "('a :: pspace_storable) \<Rightarrow> bool"
  assumes oat: "obj_at' P p s"
  and    oab: "\<And>(v :: 'a) (v' :: 'a). objBits v = objBits v'"
  shows "is_aligned p (objBits (obj :: 'a))"
  using oat
  apply (clarsimp simp add: obj_at'_def)
  apply (clarsimp simp add: projectKO_def fail_def return_def
                            project_inject objBits_def[symmetric]
                     split: option.splits)
  apply (erule subst[OF oab])
  done

lemma locateSlot_conv:
  "locateSlotBasic A B = return (A + 2 ^ cte_level_bits * B)"
  "locateSlotTCB = locateSlotBasic"
  "locateSlotCNode A bits B = (do
    x \<leftarrow> stateAssert (\<lambda>s. case (gsCNodes s A) of None \<Rightarrow> False | Some n \<Rightarrow> n = bits \<and> B < 2 ^ n) [];
    locateSlotBasic A B od)"
  "locateSlotCap c B = (do
    x \<leftarrow> stateAssert (\<lambda>s. ((isCNodeCap c \<or> (isZombie c \<and> capZombieType c \<noteq> ZombieTCB))
            \<and> (case gsCNodes s (capUntypedPtr c) of None \<Rightarrow> False
                | Some n \<Rightarrow> (isCNodeCap c \<and> n = capCNodeBits c
                    \<or> isZombie c \<and> n = zombieCTEBits (capZombieType c)) \<and> B < 2 ^ n))
        \<or> isThreadCap c \<or> (isZombie c \<and> capZombieType c = ZombieTCB)) [];
    locateSlotBasic (capUntypedPtr c) B od)"
  supply PPtr_def[simp] fromPPtr_def[simp]
  apply (simp_all add: locateSlotCap_def locateSlotTCB_def fun_eq_iff)
    apply (simp add: locateSlotBasic_def gen_objBits_simps cteSizeBits_cte_level_bits)
   apply (simp add: locateSlotCNode_def stateAssert_def)
  apply (cases c, simp_all add: locateSlotCNode_def isZombie_def isThreadCap_def
                                isCNodeCap_def capUntypedPtr_def stateAssert_def
                                bind_assoc exec_get locateSlotTCB_def
                         split: zombie_type.split cong: option.case_cong)
  done

lemma typ_at_tcb':
  "typ_at' TCBT = tcb_at'"
  apply (rule ext)+
  apply (simp add: obj_at'_real_def typ_at'_def)
  apply (simp add: ko_wp_at'_def)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac ko)
   apply (auto simp: projectKO_opt_tcb)[9]
  apply (case_tac ko)
  apply (auto simp: projectKO_opt_tcb)
  done

lemma typ_at_ep:
  "typ_at' EndpointT = ep_at'"
  apply (rule ext)+
  apply (simp add: obj_at'_real_def typ_at'_def)
  apply (simp add: ko_wp_at'_def)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac ko)
   apply (auto simp: projectKO_opt_ep)[9]
  apply (case_tac ko)
  apply (auto simp: projectKO_opt_ep)
  done

lemma typ_at_ntfn:
  "typ_at' NotificationT = ntfn_at'"
  apply (rule ext)+
  apply (simp add: obj_at'_real_def typ_at'_def)
  apply (simp add: ko_wp_at'_def)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac ko)
   apply (auto simp: projectKO_opt_ntfn)[8]
  apply clarsimp
  apply (case_tac ko)
  apply (auto simp: projectKO_opt_ntfn)
  done

lemma typ_at_cte:
  "typ_at' CTET = real_cte_at'"
  apply (rule ext)+
  apply (simp add: obj_at'_real_def typ_at'_def)
  apply (simp add: ko_wp_at'_def)
  apply (rule iffI)
   apply clarsimp
   apply (case_tac ko)
   apply (auto simp: projectKO_opt_cte)[8]
  apply clarsimp
  apply (case_tac ko)
  apply (auto simp: projectKO_opt_cte)
  done

lemma typ_at_lift_tcb':
  "\<lbrace>typ_at' TCBT p\<rbrace> f \<lbrace>\<lambda>_. typ_at' TCBT p\<rbrace> \<Longrightarrow> \<lbrace>tcb_at' p\<rbrace> f \<lbrace>\<lambda>_. tcb_at' p\<rbrace>"
  by (simp add: typ_at_tcb')

lemma typ_at_lift_ep':
  "\<lbrace>typ_at' EndpointT p\<rbrace> f \<lbrace>\<lambda>_. typ_at' EndpointT p\<rbrace> \<Longrightarrow> \<lbrace>ep_at' p\<rbrace> f \<lbrace>\<lambda>_. ep_at' p\<rbrace>"
  by (simp add: typ_at_ep)

lemma typ_at_lift_ntfn':
  "\<lbrace>typ_at' NotificationT p\<rbrace> f \<lbrace>\<lambda>_. typ_at' NotificationT p\<rbrace> \<Longrightarrow> \<lbrace>ntfn_at' p\<rbrace> f \<lbrace>\<lambda>_. ntfn_at' p\<rbrace>"
  by (simp add: typ_at_ntfn)

lemma typ_at_lift_cte':
  "\<lbrace>typ_at' CTET p\<rbrace> f \<lbrace>\<lambda>_. typ_at' CTET p\<rbrace> \<Longrightarrow> \<lbrace>real_cte_at' p\<rbrace> f \<lbrace>\<lambda>_. real_cte_at' p\<rbrace>"
  by (simp add: typ_at_cte)

lemma (in Invariants_H_cte_ats) typ_at_lift_cte_at':
  assumes x: "\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at' T p\<rbrace>"
  shows      "\<lbrace>cte_at' c\<rbrace> f \<lbrace>\<lambda>rv. cte_at' c\<rbrace>"
  apply (simp only: cte_at_typ')
  apply (wp hoare_vcg_disj_lift hoare_vcg_ex_lift x)
  done

(* proof is identical for all architectures *)
lemma (in Arch) koType_obj_range':
  "koTypeOf k = koTypeOf k' \<Longrightarrow> obj_range' p k = obj_range' p k'"
  apply (rule ccontr)
  apply (simp add: obj_range'_def objBitsKO_def archObjSize_def
            split: kernel_object.splits arch_kernel_object.splits)
  done

requalify_facts Arch.koType_obj_range'

lemma ko_wp_typ_at':
  "ko_wp_at' P p s \<Longrightarrow> \<exists>T. typ_at' T p s"
  by (clarsimp simp: typ_at'_def ko_wp_at'_def)

lemma typ_at_lift_valid_untyped':
  assumes P: "\<And>T p. \<lbrace>\<lambda>s. \<not>typ_at' T p s\<rbrace> f \<lbrace>\<lambda>rv s. \<not>typ_at' T p s\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_untyped' d p n idx s\<rbrace> f \<lbrace>\<lambda>rv s. valid_untyped' d p n idx s\<rbrace>"
  apply (clarsimp simp: valid_untyped'_def split del:if_split)
  apply (rule hoare_vcg_all_lift)
  apply (clarsimp simp: valid_def split del:if_split)
  apply (frule ko_wp_typ_at')
  apply clarsimp
  apply (cut_tac T=T and p=ptr' in P)
  apply (simp add: valid_def)
  apply (erule_tac x=s in allE)
  apply (erule impE)
   prefer 2
   apply (drule (1) bspec)
   apply simp
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def simp del:atLeastAtMost_iff)
  apply (elim disjE)
    apply (clarsimp simp:psubset_eq simp del:atLeastAtMost_iff)
    apply (drule_tac p=ptr' in koType_obj_range')
    apply (erule impE)
    apply simp
   apply simp
  apply (drule_tac p = ptr' in koType_obj_range')
  apply (clarsimp split:if_splits)
  done

lemma typ_at_lift_valid_irq_node':
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at' T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at' T p s)\<rbrace>"
  shows      "\<lbrace>valid_irq_node' p\<rbrace> f \<lbrace>\<lambda>_. valid_irq_node' p\<rbrace>"
  apply (simp add: valid_irq_node'_def)
  apply (wp hoare_vcg_all_lift P typ_at_lift_cte')
  done

lemma valid_bound_tcb_lift:
  "(\<And>T p. \<lbrace>typ_at' T p\<rbrace> f \<lbrace>\<lambda>_. typ_at' T p\<rbrace>) \<Longrightarrow>
  \<lbrace>valid_bound_tcb' tcb\<rbrace> f \<lbrace>\<lambda>_. valid_bound_tcb' tcb\<rbrace>"
  by (auto simp: valid_bound_tcb'_def valid_def typ_at_tcb'[symmetric] split: option.splits)

lemma mdb_next_unfold:
  "s \<turnstile> c \<leadsto> c' = (\<exists>z. s c = Some z \<and> c' = mdbNext (cteMDBNode z))"
  by (auto simp add: mdb_next_rel_def mdb_next_def)

lemma valid_dlist_prevD:
  "\<lbrakk> valid_dlist m; c \<noteq> 0; c' \<noteq> 0 \<rbrakk> \<Longrightarrow> m \<turnstile> c \<leadsto> c' = m \<turnstile> c \<leftarrow> c'"
  by (fastforce simp add: valid_dlist_def Let_def mdb_next_unfold mdb_prev_def)


lemma no_0_simps [simp]:
  assumes "no_0 m"
  shows "((m 0 = Some cte) = False) \<and> ((Some cte = m 0) = False)"
  using assms by (simp add: no_0_def)

lemma valid_dlist_def2:
  "no_0 m \<Longrightarrow> valid_dlist m = (\<forall>c c'. c \<noteq> 0 \<longrightarrow> c' \<noteq> 0 \<longrightarrow>  m \<turnstile> c \<leadsto> c' = m \<turnstile> c \<leftarrow> c')"
  apply (rule iffI)
   apply (simp add: valid_dlist_prevD)
  apply (clarsimp simp: valid_dlist_def Let_def mdb_next_unfold mdb_prev_def)
  apply (subgoal_tac "p\<noteq>0")
   prefer 2
   apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule_tac x="mdbPrev (cteMDBNode cte)" in allE)
   apply simp
   apply (erule_tac x=p in allE)
   apply clarsimp
  apply clarsimp
  apply (erule_tac x=p in allE)
  apply simp
  apply (erule_tac x="mdbNext (cteMDBNode cte)" in allE)
  apply clarsimp
  done

lemma valid_dlist_def3:
  "valid_dlist m = ((\<forall>c c'. m \<turnstile> c \<leadsto> c' \<longrightarrow> c' \<noteq> 0 \<longrightarrow> m \<turnstile> c \<leftarrow> c') \<and>
                    (\<forall>c c'. m \<turnstile> c \<leftarrow> c' \<longrightarrow> c \<noteq> 0 \<longrightarrow>  m \<turnstile> c \<leadsto> c'))"
  apply (rule iffI)
   apply (simp add: valid_dlist_def Let_def mdb_next_unfold mdb_prev_def)
   apply fastforce
  apply (clarsimp simp add: valid_dlist_def Let_def mdb_next_unfold mdb_prev_def)
  apply fastforce
  done

lemma vdlist_prevD:
  "\<lbrakk> m \<turnstile> c \<leftarrow> c'; m c = Some cte; valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow> m \<turnstile> c \<leadsto> c'"
  by (fastforce simp: valid_dlist_def3)

lemma vdlist_nextD:
  "\<lbrakk> m \<turnstile> c \<leadsto> c'; m c' = Some cte; valid_dlist m; no_0 m \<rbrakk> \<Longrightarrow> m \<turnstile> c \<leftarrow> c'"
  by (fastforce simp: valid_dlist_def3)

lemma vdlist_prevD0:
  "\<lbrakk> m \<turnstile> c \<leftarrow> c'; c \<noteq> 0; valid_dlist m \<rbrakk> \<Longrightarrow> m \<turnstile> c \<leadsto> c'"
  by (fastforce simp: valid_dlist_def3)

lemma vdlist_nextD0:
  "\<lbrakk> m \<turnstile> c \<leadsto> c'; c' \<noteq> 0; valid_dlist m \<rbrakk> \<Longrightarrow> m \<turnstile> c \<leftarrow> c'"
  by (fastforce simp: valid_dlist_def3)

lemma vdlist_prev_src_unique:
  "\<lbrakk> m \<turnstile> p \<leftarrow> x; m \<turnstile> p \<leftarrow> y; p \<noteq> 0; valid_dlist m \<rbrakk> \<Longrightarrow> x = y"
  by (drule (2) vdlist_prevD0)+ (clarsimp simp: mdb_next_unfold)

lemma vdlist_next_src_unique:
  "\<lbrakk> m \<turnstile> x \<leadsto> p; m \<turnstile> y \<leadsto> p; p \<noteq> 0; valid_dlist m \<rbrakk> \<Longrightarrow> x = y"
  by (drule (2) vdlist_nextD0)+ (clarsimp simp: mdb_prev_def)

lemma cte_at_cte_wp_atD:
  "cte_at' p s \<Longrightarrow> \<exists>cte. cte_wp_at' ((=) cte) p s"
  by (clarsimp simp add: cte_wp_at'_def)

lemma valid_pspace_no_0 [elim]:
  "valid_pspace' s \<Longrightarrow> no_0 (ctes_of s)"
  by (auto simp: valid_pspace'_def valid_mdb'_def valid_mdb_ctes_def)

lemma valid_pspace_dlist [elim]:
  "valid_pspace' s \<Longrightarrow> valid_dlist (ctes_of s)"
  by (auto simp: valid_pspace'_def valid_mdb'_def valid_mdb_ctes_def)

lemma next_rtrancl_tranclE [consumes 1, case_names eq trancl]:
  assumes major: "m \<turnstile> x \<leadsto>\<^sup>* y"
  and     r1: "x = y \<Longrightarrow> P"
  and     r2: "\<lbrakk> x \<noteq> y; m \<turnstile> x \<leadsto>\<^sup>+ y \<rbrakk> \<Longrightarrow> P"
  shows  "P"
  using major
  by (auto dest: rtranclD intro: r1 r2)

lemmas trancl_induct' [induct set] = trancl_induct [consumes 1, case_names base step]

lemma next_single_value:
  "\<lbrakk> m \<turnstile> x \<leadsto> y; m \<turnstile> x \<leadsto> z \<rbrakk> \<Longrightarrow> y = z"
  unfolding mdb_next_rel_def by simp

lemma loop_split:
  assumes loop: "m \<turnstile> c \<leadsto>\<^sup>+ c"
  and    split: "m \<turnstile> c \<leadsto>\<^sup>+ c'"
  shows  "m \<turnstile> c' \<leadsto>\<^sup>+ c"
  using split loop
proof induct
  case base
  thus ?case
    by (auto dest: next_single_value elim: tranclE2)
next
  case (step y z)
  hence "m \<turnstile> y \<leadsto>\<^sup>+ c" by simp
  hence "m \<turnstile> z \<leadsto>\<^sup>* c" using step.hyps
    by (metis next_single_value tranclD)

  thus ?case using step.prems
    by (cases rule: next_rtrancl_tranclE, simp_all)
qed

lemma no_0_lhs:
  "\<lbrakk> m \<turnstile> c \<leadsto> y; no_0 m \<rbrakk> \<Longrightarrow> c \<noteq> 0"
  unfolding no_0_def
  by (erule contrapos_pn, simp add: mdb_next_unfold)

lemma no_0_lhs_trancl:
  "\<lbrakk> m \<turnstile> c \<leadsto>\<^sup>+ y; no_0 m \<rbrakk> \<Longrightarrow> c \<noteq> 0"
  by (erule tranclE2, (rule no_0_lhs, simp_all)+)

lemma mdb_chain_0_no_loops:
  assumes asm: "mdb_chain_0 m"
  and     no0: "no_0 m"
  shows   "no_loops m"
proof -
  {
    fix c
    assume mc: "m \<turnstile> c \<leadsto>\<^sup>+ c"

    with asm have "m \<turnstile> c \<leadsto>\<^sup>+ 0"
      unfolding mdb_chain_0_def
      apply -
      apply (erule bspec, erule tranclE2)
      apply (auto intro: domI simp: mdb_next_unfold)
      done

    with mc have  "m \<turnstile> 0 \<leadsto>\<^sup>+ c" by (rule loop_split)
    hence False using no0
      by (clarsimp dest!:  no_0_lhs_trancl)
  }
  thus "no_loops m" unfolding no_loops_def by auto
qed

lemma valid_mdb_ctesE [elim]:
  "\<lbrakk>valid_mdb_ctes m;
    \<lbrakk> valid_dlist m; no_0 m; mdb_chain_0 m; valid_badges m;
      caps_contained' m; mdb_chunked m; untyped_mdb' m;
      untyped_inc' m; valid_nullcaps m; ut_revocable' m;
      class_links m; distinct_zombies m; irq_control m;
      reply_masters_rvk_fb m \<rbrakk>
          \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  unfolding valid_mdb_ctes_def by auto

lemma valid_mdb_ctesI [intro]:
  "\<lbrakk>valid_dlist m; no_0 m; mdb_chain_0 m; valid_badges m;
    caps_contained' m; mdb_chunked m; untyped_mdb' m;
    untyped_inc' m; valid_nullcaps m; ut_revocable' m;
    class_links m; distinct_zombies m; irq_control m;
    reply_masters_rvk_fb m; valid_arch_mdb_ctes m \<rbrakk>
  \<Longrightarrow> valid_mdb_ctes m"
  unfolding valid_mdb_ctes_def by auto

lemma ko_wp_at_aligned:
  "ko_wp_at' ((=) ko) p s \<Longrightarrow> is_aligned p (objBitsKO ko)"
  by (simp add: ko_wp_at'_def)

lemma ko_wp_at_norm:
  "ko_wp_at' P p s \<Longrightarrow> \<exists>ko. P ko \<and> ko_wp_at' ((=) ko) p s"
  by (auto simp add: ko_wp_at'_def)

lemma valid_mdb_machine_state [iff]:
  "valid_mdb' (ksMachineState_update f s) = valid_mdb' s"
  by (simp add: valid_mdb'_def)

lemma cte_wp_at_norm':
  "cte_wp_at' P p s \<Longrightarrow> \<exists>cte. cte_wp_at' ((=) cte) p s \<and> P cte"
  by (simp add: cte_wp_at'_def)

lemma pred_tcb_at' [elim!]:
  "pred_tcb_at' proj P t s \<Longrightarrow> tcb_at' t s"
  by (auto simp add: pred_tcb_at'_def obj_at'_def)

lemma valid_pspace_mdb' [elim!]:
  "valid_pspace' s \<Longrightarrow> valid_mdb' s"
  by (simp add: valid_pspace'_def)

lemmas hoare_use_eq_irq_node' = hoare_use_eq[where f=irq_node']

lemma ex_cte_cap_to'_pres:
  "\<lbrakk> \<And>P p. \<lbrace>cte_wp_at' P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at' P p\<rbrace>;
     \<And>P. \<lbrace>\<lambda>s. P (irq_node' s)\<rbrace> f \<lbrace>\<lambda>rv s. P (irq_node' s)\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>ex_cte_cap_wp_to' P p\<rbrace> f \<lbrace>\<lambda>rv. ex_cte_cap_wp_to' P p\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to'_def)
  apply (rule hoare_pre)
   apply (erule hoare_use_eq_irq_node')
   apply (rule hoare_vcg_ex_lift)
   apply assumption
  apply simp
  done


section "kernel_state field update identities"

context pspace_update_eq'
begin

lemma state_refs_of'_eq[iff]:
  "state_refs_of' (f s) = state_refs_of' s"
  by (rule state_refs_of'_pspaceI [OF _ pspace], rule refl)

lemma state_hyp_refs_of'_eq[iff]:
  "state_hyp_refs_of' (f s) = state_hyp_refs_of' s"
  by (rule state_hyp_refs_of'_pspaceI [OF _ pspace], rule refl)

lemma obj_at_update [iff]:
  "obj_at' P p (f s) = obj_at' P p s"
  by (fastforce intro: obj_at'_pspaceI simp: pspace)

lemma ko_wp_at_update [iff]:
  "ko_wp_at' P p (f s) = ko_wp_at' P p s"
  by (simp add: pspace ko_wp_at'_def ps_clear_def)

lemma pspace_aligned_update [iff]:
  "pspace_aligned' (f s) = pspace_aligned' s"
  by (simp add: pspace pspace_aligned'_def)

lemma pspace_distinct_update [iff]:
  "pspace_distinct' (f s) = pspace_distinct' s"
  by (simp add: pspace pspace_distinct'_def ps_clear_def)

lemma pspace_canonical_update [iff]:
  "pspace_canonical' (f s) = pspace_canonical' s"
  by (simp add: pspace pspace_canonical'_def ps_clear_def)

lemma pred_tcb_at_update [iff]:
  "pred_tcb_at' proj P p (f s) = pred_tcb_at' proj P p s"
  by (simp add: pred_tcb_at'_def)

lemma typ_at_update' [iff]:
  "typ_at' T p (f s) = typ_at' T p s"
  by (simp add: typ_at'_def)

lemma no_0_obj'_update [iff]:
  "no_0_obj' (f s) = no_0_obj' s"
  by (simp add: no_0_obj'_def pspace)

lemma pointerInUserData_update[iff]:
  "pointerInUserData p (f s) = pointerInUserData p s"
  by (simp add: pointerInUserData_def)

lemma pointerInDeviceData_update[iff]:
  "pointerInDeviceData p (f s) = pointerInDeviceData p s"
  by (simp add: pointerInDeviceData_def)

lemma pspace_domain_valid_update [iff]:
  "pspace_domain_valid (f s) = pspace_domain_valid s"
  by (simp add: pspace_domain_valid_def pspace)

end

lemma (in Arch_arch_idle_update_eq') global_refs_update' [iff]:
  "global_refs' (f s) = global_refs' s"
  by (simp add: global_refs'_def arch idle int_nd)

context arch_idle_update_eq' begin

(* exports from Arch locale version (safe for generic use) *)
interpretation Arch_arch_idle_update_eq' ..

lemmas global_refs_update'[iff] = global_refs_update'

end

context Arch_p_arch_idle_update_eq'
begin

lemma valid_global_refs_update' [iff]:
  "valid_global_refs' (f s) = valid_global_refs' s"
  by (simp add: valid_global_refs'_def pspace arch idle maxObj)

end

context p_arch_idle_update_eq'
begin

lemma valid_idle_update' [iff]:
  "valid_idle' (f s) = valid_idle' s"
  by (auto simp: pspace idle)

(* exports from Arch locale version (safe for generic use) *)
interpretation Arch_p_arch_idle_update_eq' ..

lemmas valid_global_refs_update'[iff] = valid_global_refs_update'

end

context int_update_eq'
begin

lemma irqs_masked_update [iff]:
  "irqs_masked' (f s) = irqs_masked' s"
  by (simp add: irqs_masked'_def int)

lemma irq_issued_update'[iff]:
  "irq_issued' irq (f s) = irq_issued' irq s"
  by (simp add: irq_issued'_def int)

end

context p_cur_update_eq'
begin

lemma sch_act_wf[iff]:
  "sch_act_wf ks (f s) = sch_act_wf ks s"
  by (cases ks; simp_all add: ct_in_state'_def st_tcb_at'_def tcb_in_cur_domain'_def curt curd)

end

context p_int_update_eq'
begin

lemma valid_irq_handlers_update'[iff]:
  "valid_irq_handlers' (f s) = valid_irq_handlers' s"
  by (simp add: valid_irq_handlers'_def cteCaps_of_def pspace)

end

interpretation sa_update:
  p_arch_idle_int_cur_update_eq' "ksSchedulerAction_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> sa_update: Arch_p_arch_idle_int_cur_update_eq' "ksSchedulerAction_update f" ..

interpretation ready_queue_update:
  p_arch_idle_int_cur_update_eq' "ksReadyQueues_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> ready_queue_update: Arch_p_arch_idle_int_cur_update_eq' "ksReadyQueues_update f" ..

interpretation ready_queue_bitmap1_update:
  p_arch_idle_int_cur_update_eq' "ksReadyQueuesL1Bitmap_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> ready_queue_bitmap1_update:
  Arch_p_arch_idle_int_cur_update_eq' "ksReadyQueuesL1Bitmap_update f" ..

interpretation ready_queue_bitmap2_update:
  p_arch_idle_int_cur_update_eq' "ksReadyQueuesL2Bitmap_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> ready_queue_bitmap2_update:
  Arch_p_arch_idle_int_cur_update_eq' "ksReadyQueuesL2Bitmap_update f" ..

interpretation cur_thread_update':
  p_arch_idle_int_update_eq' "ksCurThread_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> cur_thread_update':
  Arch_p_arch_idle_int_update_eq' "ksCurThread_update f" ..

interpretation machine_state_update':
  p_arch_idle_int_cur_update_eq' "ksMachineState_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> machine_state_update':
  Arch_p_arch_idle_int_cur_update_eq' "ksMachineState_update f" ..

interpretation interrupt_state_update':
  p_cur_update_eq' "ksInterruptState_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> interrupt_state_update':
  Arch_p_cur_update_eq' "ksInterruptState_update f" ..

interpretation idle_update':
  p_int_cur_update_eq' "ksIdleThread_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> idle_update':
  Arch_p_int_cur_update_eq' "ksIdleThread_update f" ..

interpretation arch_state_update':
  p_int_cur_update_eq' "ksArchState_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> arch_state_update':
  Arch_p_int_cur_update_eq' "ksArchState_update f" ..

interpretation wu_update':
  p_arch_idle_int_cur_update_eq' "ksWorkUnitsCompleted_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> wu_update':
  Arch_p_arch_idle_int_cur_update_eq' "ksWorkUnitsCompleted_update f" ..

interpretation gsCNodes_update: p_arch_idle_update_eq' "gsCNodes_update f"
  by unfold_locales simp_all

sublocale Arch \<subseteq> gsCNodes_update: Arch_p_arch_idle_update_eq' "gsCNodes_update f" ..

interpretation gsUserPages_update: p_arch_idle_update_eq' "gsUserPages_update f"
  by unfold_locales simp_all

sublocale Arch \<subseteq> gsUserPages_update: Arch_p_arch_idle_update_eq' "gsUserPages_update f" ..

interpretation ksCurDomain:
  p_arch_idle_int_update_eq' "ksCurDomain_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> ksCurDomain:
  Arch_p_arch_idle_int_update_eq' "ksCurDomain_update f" ..

interpretation ksDomScheduleIdx:
  p_arch_idle_int_cur_update_eq' "ksDomScheduleIdx_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> ksDomScheduleIdx:
  Arch_p_arch_idle_int_cur_update_eq' "ksDomScheduleIdx_update f" ..

interpretation ksDomSchedule:
  p_arch_idle_int_cur_update_eq' "ksDomSchedule_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> ksDomSchedule:
  Arch_p_arch_idle_int_cur_update_eq' "ksDomSchedule_update f" ..

interpretation ksDomainTime:
  p_arch_idle_int_cur_update_eq' "ksDomainTime_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> ksDomainTime:
  Arch_p_arch_idle_int_cur_update_eq' "ksDomainTime_update f" ..

interpretation gsUntypedZeroRanges:
  p_arch_idle_int_cur_update_eq' "gsUntypedZeroRanges_update f"
  by unfold_locales auto

sublocale Arch \<subseteq> gsUntypedZeroRanges:
  Arch_p_arch_idle_int_cur_update_eq' "gsUntypedZeroRanges_update f" ..


section "Relationship of Executable Spec to Kernel Configuration"

text \<open>
  Some values are set per kernel configuration (e.g. number of domains), but other related
  values (e.g. maximum domain) are derived from storage constraints (e.g. bytes used).
  To relate the two, we must look at the values of kernel configuration constants.
  To allow the proofs to work for all permitted values of these constants, their definitions
  should only be unfolded in this section, and the derived properties kept to a minimum.\<close>

lemma le_maxDomain_eq_less_numDomains:
  shows "x \<le> unat maxDomain \<longleftrightarrow> x < Kernel_Config.numDomains"
        "y \<le> maxDomain \<longleftrightarrow> unat y < Kernel_Config.numDomains"
  by (auto simp: Kernel_Config.numDomains_def maxDomain_def word_le_nat_alt)

lemma valid_global_refsD':
  "\<lbrakk> ctes_of s p = Some cte; valid_global_refs' s \<rbrakk> \<Longrightarrow>
  kernel_data_refs \<inter> capRange (cteCap cte) = {} \<and> global_refs' s \<subseteq> kernel_data_refs"
  by (clarsimp simp: valid_global_refs'_def valid_refs'_def ran_def) blast

lemma no_0_prev:
  "no_0 m \<Longrightarrow> \<not> m \<turnstile> p \<leftarrow> 0"
  by (simp add: mdb_prev_def)

lemma ut_revocableD':
  "\<lbrakk>m p = Some (CTE cap n); isUntypedCap cap; ut_revocable' m \<rbrakk> \<Longrightarrow> mdbRevocable n"
  unfolding ut_revocable'_def by blast

lemma nullcapsD':
  "\<lbrakk>m p = Some (CTE NullCap n); valid_nullcaps m \<rbrakk> \<Longrightarrow> n = nullMDBNode"
  unfolding valid_nullcaps_def by blast

lemma untyped_mdbD':
  "\<lbrakk>m p = Some (CTE c n); isUntypedCap c;
    m p' = Some (CTE c' n'); \<not>isUntypedCap c';
    capRange c' \<inter> untypedRange c \<noteq> {}; untyped_mdb' m \<rbrakk> \<Longrightarrow>
  p' \<in> descendants_of' p m"
  unfolding untyped_mdb'_def by blast

lemma untyped_incD':
  "\<lbrakk> m p = Some (CTE c n); isUntypedCap c;
     m p' = Some (CTE c' n'); isUntypedCap c'; untyped_inc' m \<rbrakk> \<Longrightarrow>
   (untypedRange c \<subseteq> untypedRange c' \<or> untypedRange c' \<subseteq> untypedRange c \<or> untypedRange c \<inter> untypedRange c' = {}) \<and>
   (untypedRange c \<subset> untypedRange c' \<longrightarrow> (p \<in> descendants_of' p' m \<and> untypedRange c \<inter> usableUntypedRange c' = {})) \<and>
   (untypedRange c' \<subset> untypedRange c \<longrightarrow> (p' \<in> descendants_of' p m \<and> untypedRange c' \<inter> usableUntypedRange c = {})) \<and>
   (untypedRange c = untypedRange c' \<longrightarrow> (p' \<in> descendants_of' p m \<and> usableUntypedRange c = {}
   \<or> p \<in> descendants_of' p' m \<and> usableUntypedRange c' = {} \<or> p = p'))"
  unfolding untyped_inc'_def
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (elim allE impE)
  apply simp+
  done

lemma caps_containedD':
  "\<lbrakk> m p = Some (CTE c n); m p' = Some (CTE c' n');
     \<not> isUntypedCap c'; capRange c' \<inter> untypedRange c \<noteq> {};
     caps_contained' m\<rbrakk>
  \<Longrightarrow> capRange c' \<subseteq> untypedRange c"
  unfolding caps_contained'_def by blast

lemma class_linksD:
  "\<lbrakk> m p = Some cte; m p' = Some cte'; m \<turnstile> p \<leadsto> p'; class_links m \<rbrakk> \<Longrightarrow>
  capClass (cteCap cte) = capClass (cteCap cte')"
  using class_links_def by blast

lemma mdb_chunkedD:
  "\<lbrakk> m p = Some (CTE cap n); m p' = Some (CTE cap' n');
     sameRegionAs cap cap'; p \<noteq> p'; mdb_chunked m \<rbrakk>
  \<Longrightarrow> (m \<turnstile> p \<leadsto>\<^sup>+ p' \<or> m \<turnstile> p' \<leadsto>\<^sup>+ p) \<and>
     (m \<turnstile> p \<leadsto>\<^sup>+ p' \<longrightarrow> is_chunk m cap p p') \<and>
     (m \<turnstile> p' \<leadsto>\<^sup>+ p \<longrightarrow> is_chunk m cap' p' p)"
  using mdb_chunked_def by blast

lemma irq_controlD:
  "\<lbrakk> m p = Some (CTE IRQControlCap n); m p' = Some (CTE IRQControlCap n');
    irq_control m \<rbrakk> \<Longrightarrow> p' = p"
  unfolding irq_control_def by blast

lemma irq_revocable:
  "\<lbrakk> m p = Some (CTE IRQControlCap n); irq_control m \<rbrakk> \<Longrightarrow> mdbRevocable n"
  unfolding irq_control_def by blast

lemma sch_act_wf_arch [simp]:
  "sch_act_wf sa (ksArchState_update f s) = sch_act_wf sa s"
  by (cases sa) (simp_all add: ct_in_state'_def  tcb_in_cur_domain'_def)

lemma valid_bitmaps_arch[simp]:
  "valid_bitmaps (ksArchState_update f s) = valid_bitmaps s"
  by (simp add: valid_bitmaps_def bitmapQ_defs)

lemma valid_idle_arch' [simp]:
  "valid_idle' (ksArchState_update f s) = valid_idle' s"
  by (simp add: valid_idle'_def)

lemma valid_irq_node_arch' [simp]:
  "valid_irq_node' w (ksArchState_update f s) = valid_irq_node' w s"
  by (simp add: valid_irq_node'_def)

lemma sch_act_wf_machine_state [simp]:
  "sch_act_wf sa (ksMachineState_update f s) = sch_act_wf sa s"
  by (cases sa) (simp_all add: ct_in_state'_def  tcb_in_cur_domain'_def)

lemma valid_irq_node'_machine_state [simp]:
  "valid_irq_node' x (ksMachineState_update f s) = valid_irq_node' x s"
  by (simp add: valid_irq_node'_def)

lemma valid_bitmaps_machine_state[simp]:
  "valid_bitmaps (ksMachineState_update f s) = valid_bitmaps s"
  by (simp add: valid_bitmaps_def bitmapQ_defs)

(* these should be reasonable safe for automation because of the 0 pattern *)
lemma no_0_ko_wp' [elim!]:
  "\<lbrakk> ko_wp_at' Q 0 s; no_0_obj' s \<rbrakk> \<Longrightarrow> P"
  by (simp add: ko_wp_at'_def no_0_obj'_def)

lemma no_0_obj_at' [elim!]:
  "\<lbrakk> obj_at' Q 0 s; no_0_obj' s \<rbrakk> \<Longrightarrow> P"
  by (simp add: obj_at'_def no_0_obj'_def)

lemma no_0_typ_at' [elim!]:
  "\<lbrakk> typ_at' T 0 s; no_0_obj' s \<rbrakk> \<Longrightarrow> P"
  by (clarsimp simp: typ_at'_def)

lemma no_0_ko_wp'_eq [simp]:
  "no_0_obj' s \<Longrightarrow> ko_wp_at' P 0 s = False"
  by (simp add: ko_wp_at'_def no_0_obj'_def)

lemma no_0_obj_at'_eq [simp]:
  "no_0_obj' s \<Longrightarrow> obj_at' P 0 s = False"
  by (simp add: obj_at'_def no_0_obj'_def)

lemma no_0_typ_at'_eq [simp]:
  "no_0_obj' s \<Longrightarrow> typ_at' P 0 s = False"
  by (simp add: typ_at'_def)

lemma valid_pspace_valid_objs'[elim!]:
  "valid_pspace' s \<Longrightarrow> valid_objs' s"
  by (simp add: valid_pspace'_def)

declare badgeBits_def [simp]

lemma simple_sane_strg:
  "sch_act_simple s \<longrightarrow> sch_act_sane s"
  by (simp add: sch_act_sane_def sch_act_simple_def)

lemma sch_act_wf_cases:
  "sch_act_wf action = (case action of
    ResumeCurrentThread \<Rightarrow> ct_in_state' activatable'
  | ChooseNewThread     \<Rightarrow> \<top>
  | SwitchToThread t    \<Rightarrow> \<lambda>s. st_tcb_at' runnable' t s \<and> tcb_in_cur_domain' t s)"
  by (cases action) auto

lemma (in pspace_update_eq') cteCaps_of_update[iff]: "cteCaps_of (f s) = cteCaps_of s"
  by (simp add: cteCaps_of_def pspace)

lemma vms_sch_act_update'[iff]:
  "valid_machine_state' (ksSchedulerAction_update f s) =
   valid_machine_state' s"
  by (simp add: valid_machine_state'_def )

lemma obj_at'_and:
  "obj_at' (P and P') t s = (obj_at' P t s \<and> obj_at' P' t s)"
  by (rule iffI, (clarsimp simp: obj_at'_def)+)

lemma obj_at'_activatable_st_tcb_at':
  "obj_at' (activatable' \<circ> tcbState) t = st_tcb_at' activatable' t"
  by (rule ext, clarsimp simp: st_tcb_at'_def)

lemma st_tcb_at'_runnable_is_activatable:
  "st_tcb_at' runnable' t s \<Longrightarrow> st_tcb_at' activatable' t s"
  by (simp add: st_tcb_at'_def)
     (fastforce elim: obj_at'_weakenE)

lemma tcb_at'_has_tcbPriority:
 "tcb_at' t s \<Longrightarrow> \<exists>p. obj_at' (\<lambda>tcb. tcbPriority tcb = p) t s"
 by (clarsimp simp add: obj_at'_def)

lemma pred_tcb_at'_Not:
  "pred_tcb_at' f (Not o P) t s = (tcb_at' t s \<and> \<not> pred_tcb_at' f P t s)"
  by (auto simp: pred_tcb_at'_def obj_at'_def)

lemma obj_at'_conj_distrib:
  "obj_at' (\<lambda>ko. P ko \<and> Q ko) p s \<Longrightarrow> obj_at' P p s \<and> obj_at' Q p s"
  by (auto simp: obj_at'_def)

lemma obj_at'_conj:
  "obj_at' (\<lambda>ko. P ko \<and> Q ko) p s = (obj_at' P p s \<and> obj_at' Q p s)"
  using obj_at'_conj_distrib obj_at_conj' by blast

lemma not_obj_at'_strengthen:
  "obj_at' (Not \<circ> P) p s \<Longrightarrow> \<not> obj_at' P p s"
  by (clarsimp simp: obj_at'_def)

lemma not_pred_tcb_at'_strengthen:
  "pred_tcb_at' f (Not \<circ> P) p s \<Longrightarrow> \<not> pred_tcb_at' f P p s"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def)

lemma obj_at'_ko_at'_prop:
  "ko_at' ko t s \<Longrightarrow> obj_at' P t s = P ko"
  by (drule obj_at_ko_at', clarsimp simp: obj_at'_def)

lemma valid_refs'_cteCaps:
  "valid_refs' S (ctes_of s) = (\<forall>c \<in> ran (cteCaps_of s). S \<inter> capRange c = {})"
  by (fastforce simp: valid_refs'_def cteCaps_of_def elim!: ranE)

lemma valid_cap_sizes_cteCaps:
  "valid_cap_sizes' n (ctes_of s) = (\<forall>c \<in> ran (cteCaps_of s). 2 ^ capBits c \<le> n)"
  apply (simp add: valid_cap_sizes'_def cteCaps_of_def)
  apply (fastforce elim!: ranE)
  done

lemma cte_at_valid_cap_sizes_0:
  "valid_cap_sizes' n ctes \<Longrightarrow> ctes p = Some cte \<Longrightarrow> 0 < n"
  apply (clarsimp simp: valid_cap_sizes'_def)
  apply (drule bspec, erule ranI)
  apply (rule Suc_le_lessD, erule order_trans[rotated])
  apply simp
  done

lemma invs_valid_stateI' [elim!]:
  "invs' s \<Longrightarrow> valid_state' s"
  by (simp add: invs'_def)

lemma tcb_at_invs' [elim!]:
  "invs' s \<Longrightarrow> tcb_at' (ksCurThread s) s"
  by (simp add: invs'_def cur_tcb'_def)

lemma invs_valid_objs' [elim!]:
  "invs' s \<Longrightarrow> valid_objs' s"
  by (simp add: invs'_def valid_state'_def valid_pspace'_def)

lemma invs_pspace_aligned' [elim!]:
  "invs' s \<Longrightarrow> pspace_aligned' s"
  by (simp add: invs'_def valid_state'_def valid_pspace'_def)

lemma invs_pspace_distinct' [elim!]:
  "invs' s \<Longrightarrow> pspace_distinct' s"
  by (simp add: invs'_def valid_state'_def valid_pspace'_def)

lemma invs_valid_pspace' [elim!]:
  "invs' s \<Longrightarrow> valid_pspace' s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_arch_state' [elim!]:
  "invs' s \<Longrightarrow> valid_arch_state' s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_cur' [elim!]:
  "invs' s \<Longrightarrow> cur_tcb' s"
  by (simp add: invs'_def)

lemma invs_mdb' [elim!]:
  "invs' s \<Longrightarrow> valid_mdb' s"
  by (simp add: invs'_def valid_state'_def valid_pspace'_def)

lemma valid_mdb_no_loops [elim!]:
  "valid_mdb_ctes m \<Longrightarrow> no_loops m"
  by (auto intro: mdb_chain_0_no_loops)

lemma invs_no_loops [elim!]:
  "invs' s \<Longrightarrow> no_loops (ctes_of s)"
  apply (rule valid_mdb_no_loops)
  apply (simp add: invs'_def valid_state'_def valid_pspace'_def valid_mdb'_def)
  done

lemma invs_iflive'[elim!]:
  "invs' s \<Longrightarrow> if_live_then_nonz_cap' s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_unsafe_then_cap' [elim!]:
  "invs' s \<Longrightarrow> if_unsafe_then_cap' s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_sym' [elim!]:
  "invs' s \<Longrightarrow> sym_refs (state_refs_of' s)"
  by (simp add: invs'_def valid_state'_def)

lemma invs_sym_hyp' [elim!]:
  "invs' s \<Longrightarrow> sym_refs (state_hyp_refs_of' s)"
  by (simp add: invs'_def valid_state'_def)

lemma invs_sch_act_wf' [elim!]:
  "invs' s \<Longrightarrow> sch_act_wf (ksSchedulerAction s) s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_valid_bitmaps[elim!]:
  "invs' s \<Longrightarrow> valid_bitmaps s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_sym_heap_sched_pointers[elim!]:
  "invs' s \<Longrightarrow> sym_heap_sched_pointers s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_valid_sched_pointers[elim!]:
  "invs' s \<Longrightarrow> valid_sched_pointers s"
  by (simp add: invs'_def valid_state'_def)

lemma invs_valid_idle'[elim!]:
  "invs' s \<Longrightarrow> valid_idle' s"
  by (fastforce simp: invs'_def valid_state'_def)

lemma invs_valid_global'[elim!]:
  "invs' s \<Longrightarrow> valid_global_refs' s"
  by (fastforce simp: invs'_def valid_state'_def)

lemma invs_pspace_canonical'[elim!]:
  "invs' s \<Longrightarrow> pspace_canonical' s"
  by (fastforce dest!: invs_valid_pspace' simp: valid_pspace'_def)

lemma valid_pspace_canonical'[elim!]:
  "valid_pspace' s \<Longrightarrow> pspace_canonical' s"
  by (rule valid_pspaceE')

lemma invs'_invs_no_cicd:
  "invs' s \<Longrightarrow> all_invs_but_ct_idle_or_in_cur_domain' s"
  by (simp add: invs'_to_invs_no_cicd'_def)

lemma einvs_valid_etcbs: "einvs s \<longrightarrow> valid_etcbs s"
  by (clarsimp simp: valid_sched_def)

lemma invs'_bitmapQ_no_L1_orphans:
  "invs' s \<Longrightarrow> bitmapQ_no_L1_orphans s"
  by (simp add: invs'_def valid_state'_def valid_bitmaps_def)

lemma invs_ksCurDomain_maxDomain' [elim!]:
  "invs' s \<Longrightarrow> ksCurDomain s \<le> maxDomain"
  by (simp add: invs'_def valid_state'_def)

lemma simple_st_tcb_at_state_refs_ofD':
  "st_tcb_at' simple' t s \<Longrightarrow> bound_tcb_at' (\<lambda>x. tcb_bound_refs' x = state_refs_of' s t) t s"
  by (fastforce simp: pred_tcb_at'_def obj_at'_def state_refs_of'_def
                      projectKO_eq project_inject)

lemma cur_tcb_arch' [iff]:
  "cur_tcb' (ksArchState_update f s) = cur_tcb' s"
  by (simp add: cur_tcb'_def)

lemma cur_tcb'_machine_state [simp]:
  "cur_tcb' (ksMachineState_update f s) = cur_tcb' s"
  by (simp add: cur_tcb'_def)

lemma invs_no_0_obj'[elim!]:
  "invs' s \<Longrightarrow> no_0_obj' s"
  by (simp add: invs'_def valid_state'_def valid_pspace'_def)

lemma pred_tcb'_neq_contra:
  "\<lbrakk> pred_tcb_at' proj P p s; pred_tcb_at' proj Q p s; \<And>st. P st \<noteq> Q st \<rbrakk> \<Longrightarrow> False"
  by (clarsimp simp: pred_tcb_at'_def obj_at'_def)

lemma not_pred_tcb':
  "(\<not>pred_tcb_at' proj P t s) = (\<not>tcb_at' t s \<or> pred_tcb_at' proj (\<lambda>a. \<not>P a) t s)"
  by (auto simp: pred_tcb_at'_def obj_at'_def)

lemma invs'_ksDomSchedule:
  "invs' s \<Longrightarrow> KernelStateData_H.ksDomSchedule s = KernelStateData_H.ksDomSchedule (newKernelState undefined)"
unfolding invs'_def valid_state'_def by clarsimp

lemma invs'_ksDomScheduleIdx:
  "invs' s \<Longrightarrow> KernelStateData_H.ksDomScheduleIdx s < length (KernelStateData_H.ksDomSchedule (newKernelState undefined))"
unfolding invs'_def valid_state'_def by clarsimp

lemma valid_bitmap_valid_bitmapQ_exceptE:
  "\<lbrakk> valid_bitmapQ_except d p s; bitmapQ d p s \<longleftrightarrow> \<not> tcbQueueEmpty (ksReadyQueues s (d,p));
     bitmapQ_no_L2_orphans s \<rbrakk>
   \<Longrightarrow> valid_bitmapQ s"
  unfolding valid_bitmapQ_def valid_bitmapQ_except_def
  by force

lemma valid_bitmap_valid_bitmapQ_exceptI[intro]:
  "valid_bitmapQ s \<Longrightarrow> valid_bitmapQ_except d p s"
  unfolding valid_bitmapQ_except_def valid_bitmapQ_def
  by simp

lemma rule_out_intv:
  "\<lbrakk> ksPSpace s a = Some obj; ksPSpace s b = Some obj'; pspace_distinct' s; a \<noteq> b \<rbrakk>
   \<Longrightarrow> b \<notin> mask_range a (objBitsKO obj)"
  apply (drule(1) pspace_distinctD')
  apply (subst (asm) ps_clear_def)
  apply (drule_tac x = b in orthD2)
   apply fastforce
  apply (drule neq_out_intv)
   apply (simp add: mask_def add_diff_eq)
  apply (simp add: mask_def add_diff_eq)
  done

lemma distinct_obj_range'_not_subset:
  "\<lbrakk> ksPSpace s a = Some obj; ksPSpace s b = Some obj'; pspace_distinct' s;
     pspace_aligned' s; a \<noteq> b \<rbrakk>
   \<Longrightarrow> \<not> obj_range' b obj' \<subseteq> obj_range' a obj"
  unfolding obj_range'_def
  apply (frule_tac x=a in pspace_alignedD')
   apply assumption
  apply (frule_tac x=b in pspace_alignedD')
   apply assumption
  apply (frule (3) rule_out_intv)
  using is_aligned_no_overflow_mask
  by fastforce

lemma obj_range'_disjoint:
  "\<lbrakk> ksPSpace s a = Some obj; ksPSpace s b = Some obj'; pspace_distinct' s;
     pspace_aligned' s; a \<noteq> b \<rbrakk>
   \<Longrightarrow> obj_range' a obj \<inter> obj_range' b obj' = {}"
  apply (frule_tac x=a in pspace_alignedD')
   apply assumption
  apply (frule_tac x=b in pspace_alignedD')
   apply assumption
  apply (frule_tac p=a and p'=b in aligned_mask_range_cases)
   apply assumption
  apply (fastforce dest: distinct_obj_range'_not_subset
                   simp: obj_range'_def)
  done

(* The normalise_obj_at' tactic was designed to simplify situations similar to:
  ko_at' ko p s \<Longrightarrow>
  obj_at' (complicated_P (obj_at' (complicated_Q (obj_at' ...)) p s)) p s

  It seems to also offer assistance in cases where there is lots of st_tcb_at', ko_at', obj_at'
  confusion. If your goal looks like that kind of mess, try it out. It can help to not unfold
  obj_at'_def which speeds up proofs.
 *)
context begin

private definition
  "ko_at'_defn v \<equiv> ko_at' v"

private lemma ko_at_defn_rewr:
  "ko_at'_defn ko p s \<Longrightarrow> (obj_at' P p s = P ko)"
  unfolding ko_at'_defn_def
  by (auto simp: obj_at'_def)

private lemma ko_at_defn_uniqueD:
  "ko_at'_defn ko p s \<Longrightarrow> ko_at'_defn ko' p s \<Longrightarrow> ko' = ko"
  unfolding ko_at'_defn_def
  by (auto simp: obj_at'_def)

private lemma ko_at_defn_pred_tcb_at':
  "ko_at'_defn ko p s \<Longrightarrow> (pred_tcb_at' proj P p s = P (proj (tcb_to_itcb' ko)))"
  by (auto simp: pred_tcb_at'_def ko_at_defn_rewr)

private lemma ko_at_defn_ko_wp_at':
  "ko_at'_defn ko p s \<Longrightarrow> (ko_wp_at' P p s = P (injectKO ko))"
  by (clarsimp simp: ko_at'_defn_def obj_at'_real_def
                     ko_wp_at'_def project_inject)

method normalise_obj_at' =
  (clarsimp?, elim obj_at_ko_at'[folded ko_at'_defn_def, elim_format],
   clarsimp simp: ko_at_defn_rewr ko_at_defn_pred_tcb_at' ko_at_defn_ko_wp_at',
   ((drule(1) ko_at_defn_uniqueD)+)?,
   clarsimp simp: ko_at'_defn_def)

end

end
