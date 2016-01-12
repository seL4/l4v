(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Invariants_AI
imports LevityCatch_AI
begin

-- ---------------------------------------------------------------------------
section "Things to Move Up"

(* FIXME: move to spec level *)
(* global data and code of the kernel, not covered by any cap *)
axiomatization
  kernel_data_refs :: "word32 set"

-- ---------------------------------------------------------------------------
section "Invariant Definitions for Abstract Spec"

definition
  "is_ep ko \<equiv> case ko of Endpoint p \<Rightarrow> True | _ \<Rightarrow> False"
definition
  "is_ntfn ko \<equiv> case ko of Notification p \<Rightarrow> True | _ \<Rightarrow> False"
definition
  "is_tcb ko \<equiv> case ko of TCB t \<Rightarrow> True | _ \<Rightarrow> False"
definition
  "is_cap_table bits ko \<equiv>
   case ko of CNode sz cs \<Rightarrow> bits = sz \<and> well_formed_cnode_n bits cs
            | _ \<Rightarrow> False"

definition
  obj_at :: "(Structures_A.kernel_object \<Rightarrow> bool) \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "obj_at P ref s \<equiv> \<exists>ko. kheap s ref = Some ko \<and> P ko"

abbreviation
  "ep_at \<equiv> obj_at is_ep"
abbreviation
  "ntfn_at \<equiv> obj_at is_ntfn"
abbreviation
  "tcb_at \<equiv> obj_at is_tcb"
abbreviation
  "cap_table_at bits \<equiv> obj_at (is_cap_table bits)"
abbreviation
  "real_cte_at cref \<equiv> cap_table_at (length (snd cref)) (fst cref)"

abbreviation
  "ko_at k \<equiv> obj_at (op = k)"

(*
 * sseefried: 'itcb' is projection of the "mostly preserved" fields of 'tcb'. Many functions
 * in the spec will leave these fields of a TCB unchanged. The 'crunch' tool is easily able
 * to ascertain this from the types of the fields.
 *
 * The 'itcb' record is closely associated with the 'pred_tcb_at' definition.
 * 'pred_tcb_at' is used to assert an arbitrary predicate over the fields in 'itcb' for a TCB
 * Before the introduction of this data structure 'st_tcb_at' was defined directly. It is
 * now an abbreviation of a partial application of the 'pred_tcb_at' function, specifically
 * a partial application to the projection function 'itcb_state'.
 *
 * The advantage of this approach is that we an assert 'pred_tcb_at proj P t' is preserved
 * across calls to many functions. We get "for free" that 'st_tcb_at P t' is also preserved.
 * In the future we may introduce other abbreviations that assert preservation over other
 * fields in the TCB record.
 *)
record itcb =
  itcb_state         :: thread_state
  itcb_fault_handler :: cap_ref
  itcb_ipc_buffer    :: vspace_ref
  itcb_fault         :: "fault option"
  itcb_bound_notification     :: "obj_ref option"


definition "tcb_to_itcb tcb \<equiv> \<lparr> itcb_state         = tcb_state tcb,
                                itcb_fault_handler = tcb_fault_handler tcb,
                                itcb_ipc_buffer    = tcb_ipc_buffer tcb,
                                itcb_fault         = tcb_fault tcb,
                                itcb_bound_notification     = tcb_bound_notification tcb \<rparr>"

(* sseefried: The simplification rules below are used to help produce
 * lemmas that talk about fields of the 'tcb' data structure rather than
 * the 'itcb' data structure when the lemma refers to a predicate of the
 * form 'pred_tcb_at proj P t'.
 *
 * e.g. You might have a lemma that has an assumption
 *   \<And>tcb. itcb_state (tcb_to_itcb (f tcb)) = itcb_state (tcb_to_itcb tcb)
 *
 * This simplifies to:
 *   \<And>tcb. tcb_state (f tcb) = tcb_state tcb
 *)

(* Need one of these simp rules for each field in 'itcb' *)
lemma [simp]: "itcb_state (tcb_to_itcb tcb) = tcb_state tcb"
  by (auto simp: tcb_to_itcb_def)

(* Need one of these simp rules for each field in 'itcb' *)
lemma [simp]: "itcb_fault_handler (tcb_to_itcb tcb) = tcb_fault_handler tcb"
  by (auto simp: tcb_to_itcb_def)

(* Need one of these simp rules for each field in 'itcb' *)
lemma [simp]: "itcb_ipc_buffer (tcb_to_itcb tcb) = tcb_ipc_buffer tcb"
  by (auto simp: tcb_to_itcb_def)

(* Need one of these simp rules for each field in 'itcb' *)
lemma [simp]: "itcb_fault (tcb_to_itcb tcb) = tcb_fault tcb"
  by (auto simp: tcb_to_itcb_def)

(* Need one of these simp rules for each field in 'itcb' *)
lemma [simp]: "itcb_bound_notification (tcb_to_itcb tcb) = tcb_bound_notification tcb"
  by (auto simp: tcb_to_itcb_def)

definition
  pred_tcb_at :: "(itcb \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> word32 \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "pred_tcb_at proj test \<equiv> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (proj (tcb_to_itcb tcb)))"

abbreviation "st_tcb_at \<equiv> pred_tcb_at itcb_state"
abbreviation "bound_tcb_at \<equiv> pred_tcb_at itcb_bound_notification"

(* sseefried: 'st_tcb_at_def' only exists to make existing proofs go through. Use 'pred_tcb_at_def' from now on. *)
lemma st_tcb_at_def: "st_tcb_at test \<equiv> obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> test (tcb_state tcb))"
  by (simp add: pred_tcb_at_def)

text {* An alternative formulation that allows abstraction over type: *}

datatype aa_type =
    AASIDPool
  | APageTable
  | APageDirectory
  | AIntData vmpage_size

datatype a_type =
    ATCB
  | AEndpoint
  | ANTFN
  | ACapTable nat
  | AGarbage
  | AArch aa_type

definition
  a_type :: "Structures_A.kernel_object \<Rightarrow> a_type"
where
 "a_type ob \<equiv> case ob of
           CNode sz cspace          \<Rightarrow> if well_formed_cnode_n sz cspace
                                       then ACapTable sz else AGarbage
         | TCB tcb                  \<Rightarrow> ATCB
         | Endpoint endpoint        \<Rightarrow> AEndpoint
         | Notification notification   \<Rightarrow> ANTFN
         | ArchObj ao               \<Rightarrow> AArch (case ao of
           PageTable pt             \<Rightarrow> APageTable
         | PageDirectory pd         \<Rightarrow> APageDirectory
         | DataPage sz              \<Rightarrow> AIntData sz
         | ARM_Structs_A.ASIDPool f \<Rightarrow> AASIDPool)"

abbreviation
  "typ_at T \<equiv> obj_at (\<lambda>ob. a_type ob = T)"

(* this time with typ_at. might lead to confusion, but this is how
   the rest should have been defined.. *)
abbreviation
  "asid_pool_at \<equiv> typ_at (AArch AASIDPool)"
abbreviation
  "page_table_at \<equiv> typ_at (AArch APageTable)"
abbreviation
  "page_directory_at \<equiv> typ_at (AArch APageDirectory)"

definition
  "pde_at p \<equiv> page_directory_at (p && ~~ mask pd_bits)
                  and K (is_aligned p 2)"
definition
  "pte_at p \<equiv> page_table_at (p && ~~ mask pt_bits)
                  and K (is_aligned p 2)"

text {* cte with property at *}


definition
  cte_wp_at :: "(cap \<Rightarrow> bool) \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "cte_wp_at P p s \<equiv> \<exists>cap. fst (get_cap p s) = {(cap,s)} \<and> P cap"

abbreviation
  cte_at :: "cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "cte_at \<equiv> cte_wp_at \<top>"


subsection "Valid caps and objects"

primrec
  untyped_range :: "cap \<Rightarrow> word32 set"
where
  "untyped_range (cap.UntypedCap p n f)                 = {p..p + (1 << n) - 1}"
| "untyped_range (cap.NullCap)                          = {}"
| "untyped_range (cap.EndpointCap r badge rights)       = {}"
| "untyped_range (cap.NotificationCap r badge rights)  = {}"
| "untyped_range (cap.CNodeCap r bits guard)            = {}"
| "untyped_range (cap.ThreadCap r)                      = {}"
| "untyped_range (cap.DomainCap)                        = {}"
| "untyped_range (cap.ReplyCap r master)                = {}"
| "untyped_range (cap.IRQControlCap)                    = {}"
| "untyped_range (cap.IRQHandlerCap irq)                = {}"
| "untyped_range (cap.Zombie r b n)                     = {}"
| "untyped_range (cap.ArchObjectCap cap)                = {}"

primrec
  usable_untyped_range :: "cap \<Rightarrow> word32 set"
where
 "usable_untyped_range (cap.UntypedCap p n f) =
  (if f < 2^n  then {p+of_nat f .. p + 2 ^ n - 1} else {})"

definition
  "obj_range p obj \<equiv> {p .. p + 2^obj_bits obj - 1}"

definition
  "pspace_no_overlap ptr bits \<equiv>
           \<lambda>s. \<forall>x ko. kheap s x = Some ko \<longrightarrow>
                {x .. x + (2 ^ obj_bits ko - 1)} \<inter> {ptr .. (ptr &&~~ mask bits)  + (2 ^  bits - 1)} = {}"

definition
  "valid_untyped c \<equiv> \<lambda>s.
  \<forall>p obj.
     kheap s p = Some obj \<longrightarrow>
     obj_range p obj \<inter> untyped_range c \<noteq> {} \<longrightarrow>
     ( obj_range p obj \<subseteq> untyped_range c \<and> usable_untyped_range c \<inter> obj_range p obj = {} )"

primrec
  cap_bits :: "cap \<Rightarrow> nat"
where
  "cap_bits cap.NullCap = 0"
| "cap_bits (cap.UntypedCap r b f) = b"
| "cap_bits (cap.EndpointCap r b R) = obj_bits (Endpoint undefined)"
| "cap_bits (cap.NotificationCap r b R) = obj_bits (Notification undefined)"
| "cap_bits (cap.CNodeCap r b m) = cte_level_bits + b"
| "cap_bits (cap.ThreadCap r) = obj_bits (TCB undefined)"
| "cap_bits (DomainCap) = 0"
| "cap_bits (cap.ReplyCap r m) = obj_bits (TCB undefined)"
| "cap_bits (cap.Zombie r zs n) =
    (case zs of None \<Rightarrow> obj_bits (TCB undefined)
            | Some n \<Rightarrow> cte_level_bits + n)"
| "cap_bits (cap.IRQControlCap) = 0"
| "cap_bits (cap.IRQHandlerCap irq) = 0"
| "cap_bits (cap.ArchObjectCap x) = arch_obj_size x"

definition
  "cap_aligned c \<equiv>
   is_aligned (obj_ref_of c) (cap_bits c) \<and> cap_bits c < word_bits"

definition
  "vmsz_aligned ref sz \<equiv> is_aligned ref (pageBitsForSize sz)"

text {*
  Below, we define several predicates for capabilities on the abstract specification.
  Please note that we distinguish between well-formedness predicates,
  which merely refine the basic type and are independent of the kernel state,
  and the validity of the capability references,
  which necessarily depends on the current kernel state.

  Eventually, we will combine all predicates into @{text valid_cap}.
*}

definition
  "wellformed_mapdata sz \<equiv>
   \<lambda>(asid, vref). 0 < asid \<and> asid \<le> 2^asid_bits - 1
                \<and> vmsz_aligned vref sz \<and> vref < kernel_base"

datatype capclass =
  PhysicalClass | ReplyClass "obj_ref" | IRQClass | ASIDMasterClass | NullClass | DomainClass

definition
  wellformed_acap :: "arch_cap \<Rightarrow> bool"
where
  "wellformed_acap ac \<equiv>
   case ac of
     ARM_Structs_A.ASIDPoolCap r as
       \<Rightarrow> is_aligned as asid_low_bits \<and> as \<le> 2^asid_bits - 1
   | ARM_Structs_A.PageCap r rghts sz mapdata \<Rightarrow> rghts \<in> valid_vm_rights \<and>
     case_option True (wellformed_mapdata sz) mapdata
   | ARM_Structs_A.PageTableCap r (Some mapdata) \<Rightarrow>
     wellformed_mapdata ARMSection mapdata
   | ARM_Structs_A.PageDirectoryCap r (Some asid) \<Rightarrow>
     0 < asid \<and> asid \<le> 2^asid_bits - 1
   | _ \<Rightarrow> True"

definition
  wellformed_cap :: "cap \<Rightarrow> bool"
where
  "wellformed_cap c \<equiv>
  case c of
    Structures_A.UntypedCap p sz idx \<Rightarrow> sz \<ge> 4
  | Structures_A.NotificationCap r badge rights \<Rightarrow> AllowGrant \<notin> rights
  | Structures_A.CNodeCap r bits guard \<Rightarrow> bits \<noteq> 0 \<and> length guard \<le> 32
  | Structures_A.IRQHandlerCap irq \<Rightarrow> irq \<le> maxIRQ
  | Structures_A.Zombie r b n \<Rightarrow> (case b of None \<Rightarrow> n \<le> 5
                                          | Some b \<Rightarrow> n \<le> 2 ^ b \<and> b \<noteq> 0)
  | Structures_A.ArchObjectCap ac \<Rightarrow> wellformed_acap ac
  | _ \<Rightarrow> True"

definition
  valid_cap_ref :: "cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_cap_ref c s \<equiv> case c of
    Structures_A.NullCap \<Rightarrow> True
  | Structures_A.UntypedCap p b idx \<Rightarrow> valid_untyped c s \<and> idx \<le> 2^ b \<and> p \<noteq> 0
  | Structures_A.EndpointCap r badge rights \<Rightarrow> ep_at r s
  | Structures_A.NotificationCap r badge rights \<Rightarrow> ntfn_at r s
  | Structures_A.CNodeCap r bits guard \<Rightarrow> cap_table_at bits r s
  | Structures_A.ThreadCap r \<Rightarrow> tcb_at r s
  | Structures_A.DomainCap \<Rightarrow> True
  | Structures_A.ReplyCap r m \<Rightarrow> tcb_at r s
  | Structures_A.IRQControlCap \<Rightarrow> True
  | Structures_A.IRQHandlerCap irq \<Rightarrow> True
  | Structures_A.Zombie r b n \<Rightarrow>
      (case b of None \<Rightarrow> tcb_at r s | Some b \<Rightarrow> cap_table_at b r s)
  | Structures_A.ArchObjectCap ac \<Rightarrow> (case ac of
    ARM_Structs_A.ASIDPoolCap r as \<Rightarrow> typ_at (AArch AASIDPool) r s
  | ARM_Structs_A.ASIDControlCap \<Rightarrow> True
  | ARM_Structs_A.PageCap r rghts sz mapdata \<Rightarrow> typ_at (AArch (AIntData sz)) r s
  | ARM_Structs_A.PageTableCap r mapdata \<Rightarrow> typ_at (AArch APageTable) r s
  | ARM_Structs_A.PageDirectoryCap r mapdata\<Rightarrow>typ_at(AArch APageDirectory) r s)"


definition
  valid_cap :: "cap \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_cap c s \<equiv> cap_aligned c \<and> (case c of
    Structures_A.NullCap \<Rightarrow> True
  | Structures_A.UntypedCap p b f \<Rightarrow> valid_untyped c s \<and> 4 \<le> b \<and> f \<le> 2 ^ b \<and> p \<noteq> 0
  | Structures_A.EndpointCap r badge rights \<Rightarrow> ep_at r s
  | Structures_A.NotificationCap r badge rights \<Rightarrow>
         ntfn_at r s \<and> AllowGrant \<notin> rights
  | Structures_A.CNodeCap r bits guard \<Rightarrow>
         cap_table_at bits r s \<and> bits \<noteq> 0 \<and> length guard \<le> 32
  | Structures_A.ThreadCap r \<Rightarrow> tcb_at r s
  | Structures_A.DomainCap \<Rightarrow> True
  | Structures_A.ReplyCap r m \<Rightarrow> tcb_at r s
  | Structures_A.IRQControlCap \<Rightarrow> True
  | Structures_A.IRQHandlerCap irq \<Rightarrow> irq \<le> maxIRQ
  | Structures_A.Zombie r b n \<Rightarrow>
         (case b of None \<Rightarrow> tcb_at r s \<and> n \<le> 5
                  | Some b \<Rightarrow> cap_table_at b r s \<and> n \<le> 2 ^ b \<and> b \<noteq> 0)
  | Structures_A.ArchObjectCap ac \<Rightarrow> (case ac of
    ARM_Structs_A.ASIDPoolCap r as \<Rightarrow>
         typ_at (AArch AASIDPool) r s \<and> is_aligned as asid_low_bits
           \<and> as \<le> 2^asid_bits - 1
  | ARM_Structs_A.ASIDControlCap \<Rightarrow> True
  | ARM_Structs_A.PageCap r rghts sz mapdata \<Rightarrow>
    typ_at (AArch (AIntData sz)) r s \<and> rghts \<in> valid_vm_rights \<and>
    (case mapdata of None \<Rightarrow> True | Some (asid, ref) \<Rightarrow> 0 < asid \<and> asid \<le> 2^asid_bits - 1
                                             \<and> vmsz_aligned ref sz \<and> ref < kernel_base)
  | ARM_Structs_A.PageTableCap r mapdata \<Rightarrow>
    typ_at (AArch APageTable) r s \<and>
    (case mapdata of None \<Rightarrow> True
       | Some (asid, vref) \<Rightarrow> 0 < asid \<and> asid \<le> 2 ^ asid_bits - 1
                                \<and> vref < kernel_base
                                \<and> is_aligned vref (pageBitsForSize ARMSection))
  | ARM_Structs_A.PageDirectoryCap r mapdata \<Rightarrow>
    typ_at (AArch APageDirectory) r s \<and>
    case_option True (\<lambda>asid. 0 < asid \<and> asid \<le> 2^asid_bits - 1) mapdata))"

abbreviation
  valid_cap_syn :: "'z::state_ext state \<Rightarrow> cap \<Rightarrow> bool" ("_ \<turnstile> _" [60, 60] 61)
where
  "s \<turnstile> c \<equiv> valid_cap c s"

primrec
  acap_class :: "arch_cap \<Rightarrow> capclass"
where
  "acap_class (arch_cap.ASIDPoolCap x y)      = PhysicalClass"
| "acap_class (arch_cap.ASIDControlCap)       = ASIDMasterClass"
| "acap_class (arch_cap.PageCap x y sz z)     = PhysicalClass"
| "acap_class (arch_cap.PageTableCap x y)     = PhysicalClass"
| "acap_class (arch_cap.PageDirectoryCap x y) = PhysicalClass"

primrec
  cap_class :: "cap \<Rightarrow> capclass"
where
  "cap_class (cap.NullCap)                          = NullClass"
| "cap_class (cap.UntypedCap p n f)                 = PhysicalClass"
| "cap_class (cap.EndpointCap ref badge r)          = PhysicalClass"
| "cap_class (cap.NotificationCap ref badge r)     = PhysicalClass"
| "cap_class (cap.CNodeCap ref n bits)              = PhysicalClass"
| "cap_class (cap.ThreadCap ref)                    = PhysicalClass"
| "cap_class (cap.DomainCap)                        = DomainClass"
| "cap_class (cap.Zombie r b n)                     = PhysicalClass"
| "cap_class (cap.IRQControlCap)                    = IRQClass"
| "cap_class (cap.IRQHandlerCap irq)                = IRQClass"
| "cap_class (cap.ReplyCap tcb m)                   = ReplyClass tcb"
| "cap_class (cap.ArchObjectCap cap)                = acap_class cap"

definition
  valid_cs_size :: "nat \<Rightarrow> cnode_contents \<Rightarrow> bool" where
  "valid_cs_size sz cs \<equiv>
  sz < word_bits - cte_level_bits \<and> well_formed_cnode_n sz cs"

definition
  valid_cs :: "nat \<Rightarrow> cnode_contents \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "valid_cs sz cs s \<equiv> (\<forall>cap \<in> ran cs. s \<turnstile> cap) \<and> valid_cs_size sz cs"

definition
  valid_tcb_state :: "Structures_A.thread_state \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_tcb_state ts s \<equiv> case ts of
    Structures_A.BlockedOnReceive ref d \<Rightarrow> ep_at ref s
  | Structures_A.BlockedOnSend ref sp \<Rightarrow> ep_at ref s
  | Structures_A.BlockedOnNotification ref \<Rightarrow> ntfn_at ref s
  | _ \<Rightarrow> True"

abbreviation
  "inactive st \<equiv> st = Structures_A.Inactive"

abbreviation
  "halted st \<equiv> case st of
                     Structures_A.Inactive \<Rightarrow> True
                   | Structures_A.IdleThreadState \<Rightarrow> True
                   | _ \<Rightarrow> False"

definition
  tcb_cap_cases ::
  "cap_ref \<rightharpoonup> ((Structures_A.tcb \<Rightarrow> cap) \<times>
               ((cap \<Rightarrow> cap) \<Rightarrow> Structures_A.tcb \<Rightarrow> Structures_A.tcb) \<times>
               (obj_ref \<Rightarrow> Structures_A.thread_state \<Rightarrow> cap \<Rightarrow> bool))"
where
  "tcb_cap_cases \<equiv>
   [tcb_cnode_index 0 \<mapsto> (tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>)),
    tcb_cnode_index 1 \<mapsto> (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. \<top>)),
    tcb_cnode_index 2 \<mapsto> (tcb_reply, tcb_reply_update,
                          (\<lambda>t st c. (is_master_reply_cap c \<and> obj_ref_of c = t)
                                  \<or> (halted st \<and> (c = cap.NullCap)))),
    tcb_cnode_index 3 \<mapsto> (tcb_caller, tcb_caller_update,
                          (\<lambda>_ st. case st of
                                    Structures_A.BlockedOnReceive e d \<Rightarrow>
                                      (op = cap.NullCap)
                                  | _ \<Rightarrow> is_reply_cap or (op = cap.NullCap))),
    tcb_cnode_index 4 \<mapsto> (tcb_ipcframe, tcb_ipcframe_update,
                          (\<lambda>_ _. is_arch_cap or (op = cap.NullCap)))]"

definition
  valid_ipc_buffer_cap :: "cap \<Rightarrow> word32 \<Rightarrow> bool"
where
  "valid_ipc_buffer_cap c bufptr \<equiv>
         case c of
              cap.ArchObjectCap (arch_cap.PageCap ref rghts sz mapdata) \<Rightarrow>
                   is_aligned bufptr msg_align_bits

            | _ \<Rightarrow> True"

definition
  valid_fault :: "ExceptionTypes_A.fault \<Rightarrow> bool"
where
  "valid_fault f \<equiv>
   \<forall>mw b n g. f = (ExceptionTypes_A.CapFault mw b
                     (ExceptionTypes_A.GuardMismatch n g)) \<longrightarrow> length g\<le>32"

definition
  valid_bound_ntfn :: "32 word option \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_bound_ntfn ntfn_opt s \<equiv> case ntfn_opt of
                                 None \<Rightarrow> True
                               | Some a \<Rightarrow> ntfn_at a s"

definition
  valid_bound_tcb :: "32 word option \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_bound_tcb tcb_opt s \<equiv> case tcb_opt of
                                 None \<Rightarrow> True
                               | Some t \<Rightarrow> tcb_at t s"

abbreviation (input)
  "bound a \<equiv> a \<noteq> None"


definition
  valid_ntfn :: "Structures_A.notification \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ntfn ntfn s \<equiv> (case ntfn_obj ntfn of 
    Structures_A.IdleNtfn \<Rightarrow>  True
  | Structures_A.WaitingNtfn ts \<Rightarrow>
      (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at t s) 
       \<and> distinct ts
       \<and> (case ntfn_bound_tcb ntfn of Some tcb \<Rightarrow> ts = [tcb] | _ \<Rightarrow> True))
  | Structures_A.ActiveNtfn b \<Rightarrow> True)
 \<and> valid_bound_tcb (ntfn_bound_tcb ntfn) s"

definition
  valid_tcb :: "obj_ref \<Rightarrow> Structures_A.tcb \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_tcb p t s \<equiv>
     (\<forall>(getF, setF, restr) \<in> ran tcb_cap_cases.
       s \<turnstile> getF t \<and> restr p (tcb_state t) (getF t))
     \<and> valid_ipc_buffer_cap (tcb_ipcframe t) (tcb_ipc_buffer t)
     \<and> valid_tcb_state (tcb_state t) s
     \<and> (case tcb_fault t of Some f \<Rightarrow> valid_fault f | _ \<Rightarrow> True)
     \<and> length (tcb_fault_handler t) = word_bits
     \<and> valid_bound_ntfn (tcb_bound_notification t) s"

definition
  tcb_cap_valid :: "cap \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "tcb_cap_valid cap ptr s \<equiv> tcb_at (fst ptr) s \<longrightarrow>
     st_tcb_at (\<lambda>st. case tcb_cap_cases (snd ptr) of
                          Some (getF, setF, restr) \<Rightarrow> restr (fst ptr) st cap
                        | None \<Rightarrow> True)
               (fst ptr) s
      \<and> (snd ptr = tcb_cnode_index 4 \<longrightarrow>
           (\<forall>tcb. ko_at (TCB tcb) (fst ptr) s
                   \<longrightarrow> valid_ipc_buffer_cap cap (tcb_ipc_buffer tcb)))"

definition
  valid_ep :: "Structures_A.endpoint \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ep ep s \<equiv> case ep of
    Structures_A.IdleEP \<Rightarrow> True
  | Structures_A.SendEP ts \<Rightarrow>
      (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at t s) \<and> distinct ts)
  | Structures_A.RecvEP ts \<Rightarrow>
      (ts \<noteq> [] \<and> (\<forall>t \<in> set ts. tcb_at t s) \<and> distinct ts)"



definition
  kernel_mapping_slots :: "12 word set" where
 "kernel_mapping_slots \<equiv> {x. x \<ge> ucast (kernel_base >> 20)}"

definition
  equal_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "equal_kernel_mappings \<equiv> \<lambda>s.
    \<forall>x y pd pd'. ko_at (ArchObj (PageDirectory pd)) x s
         \<and> ko_at (ArchObj (PageDirectory pd')) y s
       \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pd w = pd' w)"

primrec
  valid_pte :: "ARM_Structs_A.pte \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pte (ARM_Structs_A.InvalidPTE) = \<top>"
| "valid_pte (ARM_Structs_A.LargePagePTE ptr x y) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        typ_at (AArch (AIntData ARMLargePage)) (Platform.ptrFromPAddr ptr) s)"
| "valid_pte (ARM_Structs_A.SmallPagePTE ptr x y) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        typ_at (AArch (AIntData ARMSmallPage)) (Platform.ptrFromPAddr ptr) s)"

primrec
  valid_pde :: "ARM_Structs_A.pde \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_pde (ARM_Structs_A.InvalidPDE) = \<top>"
| "valid_pde (ARM_Structs_A.SectionPDE ptr x y z) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        typ_at (AArch (AIntData ARMSection)) (Platform.ptrFromPAddr ptr) s)"
| "valid_pde (ARM_Structs_A.SuperSectionPDE ptr x z) =
   (\<lambda>s. is_aligned ptr pageBits \<and>
        typ_at (AArch (AIntData ARMSuperSection))
               (Platform.ptrFromPAddr ptr) s)"
| "valid_pde (ARM_Structs_A.PageTablePDE ptr x z) =
   (typ_at (AArch APageTable) (Platform.ptrFromPAddr ptr))"

primrec
  valid_arch_obj :: "arch_kernel_obj \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_obj (ARM_Structs_A.ASIDPool pool) =
   (\<lambda>s. \<forall>x \<in> ran pool. typ_at (AArch APageDirectory) x s)"
| "valid_arch_obj (ARM_Structs_A.PageDirectory pd) =
   (\<lambda>s. \<forall>x \<in> -kernel_mapping_slots. valid_pde (pd x) s)"
| "valid_arch_obj (ARM_Structs_A.PageTable pt) = (\<lambda>s. \<forall>x. valid_pte (pt x) s)"
| "valid_arch_obj (DataPage sz) = \<top>"

definition
  wellformed_pte :: "ARM_Structs_A.pte \<Rightarrow> bool"
where
  "wellformed_pte pte \<equiv> case pte of
     ARM_Structs_A.pte.LargePagePTE p attr r \<Rightarrow>
       ParityEnabled \<notin> attr \<and> r \<in> valid_vm_rights
   | ARM_Structs_A.pte.SmallPagePTE p attr r \<Rightarrow>
       ParityEnabled \<notin> attr \<and> r \<in> valid_vm_rights
   | _ \<Rightarrow> True"

definition
  wellformed_pde :: "ARM_Structs_A.pde \<Rightarrow> bool"
where
  "wellformed_pde pde \<equiv> case pde of
     ARM_Structs_A.pde.PageTablePDE p attr mw \<Rightarrow> attr \<subseteq> {ParityEnabled}
   | ARM_Structs_A.pde.SectionPDE p attr mw r \<Rightarrow> r \<in> valid_vm_rights
   | ARM_Structs_A.pde.SuperSectionPDE p attr r \<Rightarrow> r \<in> valid_vm_rights
   | _ \<Rightarrow> True"

definition
  wellformed_arch_obj :: "arch_kernel_obj \<Rightarrow> bool"
where
  "wellformed_arch_obj ao \<equiv> case ao of
     PageTable pt \<Rightarrow> (\<forall>pte\<in>range pt. wellformed_pte pte)
   | PageDirectory pd \<Rightarrow> (\<forall>pde\<in>range pd. wellformed_pde pde)
   | _ \<Rightarrow> True"

definition
  valid_obj :: "obj_ref \<Rightarrow> Structures_A.kernel_object \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_obj ptr ko s \<equiv> case ko of
    Endpoint p \<Rightarrow> valid_ep p s
  | Notification p \<Rightarrow> valid_ntfn p s
  | TCB t \<Rightarrow> valid_tcb ptr t s
  | CNode sz cs \<Rightarrow> valid_cs sz cs s
  | ArchObj ao \<Rightarrow> wellformed_arch_obj ao"

definition
  valid_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_objs s \<equiv> \<forall>ptr \<in> dom $ kheap s. \<exists>obj. kheap s ptr = Some obj \<and> valid_obj ptr obj s"

definition
  pde_ref :: "ARM_Structs_A.pde \<Rightarrow> obj_ref option"
where
  "pde_ref pde \<equiv> case pde of
    ARM_Structs_A.PageTablePDE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

datatype vs_ref = VSRef word32 "aa_type option"

definition
  vs_ref_atype :: "vs_ref \<Rightarrow> aa_type option" where
 "vs_ref_atype vsref \<equiv> case vsref of VSRef x atype \<Rightarrow> atype"

definition
  vs_refs :: "Structures_A.kernel_object \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs \<equiv> \<lambda>ko. case ko of
    ArchObj (ARM_Structs_A.ASIDPool pool) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | ArchObj (ARM_Structs_A.PageDirectory pd) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) `
      graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None else pde_ref (pd x))
  | _ \<Rightarrow> {}"

type_synonym vs_chain = "vs_ref list \<times> obj_ref"
type_synonym 'a rel = "('a \<times> 'a) set"

definition
  vs_lookup1 :: "'z::state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup1 s \<equiv> {((rs,p),(rs',p')). \<exists>ko r. ko_at ko p s
                                      \<and> rs' = (r # rs)
                                      \<and> (r, p') \<in> vs_refs ko}"

abbreviation (input)
  vs_lookup_trans :: "'z::state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup_trans s \<equiv> (vs_lookup1 s)^*"

abbreviation
  vs_lookup1_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  ("_ \<rhd>1 _" [80,80] 81) where
  "ref \<rhd>1 ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup1 s"

abbreviation
  vs_lookup_trans_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  ("_ \<rhd>* _" [80,80] 81) where
  "ref \<rhd>* ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup_trans s"

definition
  vs_asid_refs :: "(word8 \<rightharpoonup> obj_ref) \<Rightarrow> vs_chain set"
where
  "vs_asid_refs t \<equiv> (\<lambda>(r,p). ([VSRef (ucast r) None], p)) ` graph_of t"

definition
  vs_lookup :: "'z::state_ext state \<Rightarrow> vs_chain set"
where
  "vs_lookup \<equiv> \<lambda>s. vs_lookup_trans s `` vs_asid_refs (arm_asid_table (arch_state s))"

abbreviation
  vs_lookup_abbr :: "vs_ref list \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
  ("_ \<rhd> _" [80,80] 81) where
  "rs \<rhd> p \<equiv> \<lambda>s. (rs,p) \<in> vs_lookup s"

abbreviation
  is_reachable_abbr :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" ("\<exists>\<rhd> _" [80] 81) where
  "\<exists>\<rhd> p \<equiv> \<lambda>s. \<exists>ref. (ref \<rhd> p) s"

definition
  valid_arch_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_objs \<equiv> \<lambda>s. \<forall>p rs ao. (rs \<rhd> p) s \<longrightarrow> ko_at (ArchObj ao) p s \<longrightarrow> valid_arch_obj ao s"

definition
  pde_ref_pages :: "ARM_Structs_A.pde \<Rightarrow> obj_ref option"
where
  "pde_ref_pages pde \<equiv> case pde of
    ARM_Structs_A.PageTablePDE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | ARM_Structs_A.SectionPDE ptr x y z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | ARM_Structs_A.SuperSectionPDE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  pte_ref_pages :: "ARM_Structs_A.pte \<Rightarrow> obj_ref option"
where
  "pte_ref_pages pte \<equiv> case pte of
    ARM_Structs_A.SmallPagePTE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | ARM_Structs_A.LargePagePTE ptr x z \<Rightarrow> Some (Platform.ptrFromPAddr ptr)
  | _ \<Rightarrow> None"

definition
  vs_refs_pages :: "Structures_A.kernel_object \<Rightarrow> (vs_ref \<times> obj_ref) set" where
  "vs_refs_pages \<equiv> \<lambda>ko. case ko of
    ArchObj (ARM_Structs_A.ASIDPool pool) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some AASIDPool), p)) ` graph_of pool
  | ArchObj (ARM_Structs_A.PageDirectory pd) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageDirectory), p)) `
      graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None else pde_ref_pages (pd x))
  | ArchObj (ARM_Structs_A.PageTable pt) \<Rightarrow>
      (\<lambda>(r,p). (VSRef (ucast r) (Some APageTable), p)) `
      graph_of (pte_ref_pages o pt)
  | _ \<Rightarrow> {}"

definition
  vs_lookup_pages1 :: "'z :: state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup_pages1 s \<equiv> {((rs,p),(rs',p')). \<exists>ko r. ko_at ko p s
                                          \<and> rs' = (r # rs)
                                          \<and> (r, p') \<in> vs_refs_pages ko}"

abbreviation (input)
  vs_lookup_pages_trans :: "'z :: state_ext state \<Rightarrow> vs_chain rel" where
  "vs_lookup_pages_trans s \<equiv> (vs_lookup_pages1 s)^*"

abbreviation
  vs_lookup_pages1_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"
  ("_ \<unrhd>1 _" [80,80] 81) where
  "ref \<unrhd>1 ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup_pages1 s"

abbreviation
  vs_lookup_pages_trans_abbr :: "vs_chain \<Rightarrow> vs_chain \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"
  ("_ \<unrhd>* _" [80,80] 81) where
  "ref \<unrhd>* ref' \<equiv> \<lambda>s. (ref,ref') \<in> vs_lookup_pages_trans s"

definition
  vs_lookup_pages :: "'z ::state_ext state \<Rightarrow> vs_chain set"
where
  "vs_lookup_pages \<equiv> \<lambda>s. vs_lookup_pages_trans s `` vs_asid_refs (arm_asid_table (arch_state s))"

abbreviation
  vs_lookup_pages_abbr :: "vs_ref list \<Rightarrow> obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool"
  ("_ \<unrhd> _" [80,80] 81) where
  "rs \<unrhd> p \<equiv> \<lambda>s. (rs,p) \<in> vs_lookup_pages s"

abbreviation
  is_reachable_pages_abbr :: "obj_ref \<Rightarrow> 'z :: state_ext state \<Rightarrow> bool" ("\<exists>\<unrhd> _" [80] 81) where
  "\<exists>\<unrhd> p \<equiv> \<lambda>s. \<exists>ref. (ref \<unrhd> p) s"

definition
  pde_mapping_bits :: "nat"
where
 "pde_mapping_bits \<equiv> pageBitsForSize ARMSection"

definition
  pte_mapping_bits :: "nat"
where
 "pte_mapping_bits \<equiv> pageBitsForSize ARMSmallPage"

definition
  valid_pte_kernel_mappings :: "ARM_Structs_A.pte \<Rightarrow> vspace_ref
                                   \<Rightarrow> arm_vspace_region_uses \<Rightarrow> bool"
where
 "valid_pte_kernel_mappings pte vref uses \<equiv> case pte of
    ARM_Structs_A.InvalidPTE \<Rightarrow>
        \<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}.
                    uses x \<noteq> ArmVSpaceKernelWindow
  | ARM_Structs_A.SmallPagePTE ptr atts rghts \<Rightarrow>
        Platform.ptrFromPAddr ptr = vref
        \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}. uses x = use)
             \<and> (use = ArmVSpaceKernelWindow
                    \<or> use = ArmVSpaceDeviceWindow))
        \<and> rghts = {}
  | ARM_Structs_A.LargePagePTE ptr atts rghts \<Rightarrow>
        Platform.ptrFromPAddr ptr = (vref && ~~ mask (pageBitsForSize ARMLargePage))
        \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pte_mapping_bits - 1}. uses x = use)
             \<and> (use = ArmVSpaceKernelWindow
                    \<or> use = ArmVSpaceDeviceWindow))
        \<and> rghts = {}"

definition
  valid_pt_kernel_mappings :: "vspace_ref \<Rightarrow> arm_vspace_region_uses \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
 "valid_pt_kernel_mappings vref uses obj \<equiv> case obj of
    ArchObj (PageTable pt) \<Rightarrow>
        \<forall>x. valid_pte_kernel_mappings
             (pt x) (vref + (ucast x << pte_mapping_bits)) uses
  | _ \<Rightarrow> False"

definition
  valid_pde_kernel_mappings :: "ARM_Structs_A.pde \<Rightarrow> vspace_ref \<Rightarrow> arm_vspace_region_uses \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_pde_kernel_mappings pde vref uses \<equiv> case pde of
    ARM_Structs_A.InvalidPDE \<Rightarrow>
        (\<lambda>s. \<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}.
                    uses x \<noteq> ArmVSpaceKernelWindow)
  | ARM_Structs_A.PageTablePDE ptr _ _ \<Rightarrow>
        obj_at (valid_pt_kernel_mappings vref uses)
                    (Platform.ptrFromPAddr ptr)
  | ARM_Structs_A.SectionPDE ptr atts _ rghts \<Rightarrow>
        (\<lambda>s. Platform.ptrFromPAddr ptr = vref
             \<and> (\<exists>use. (\<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}. uses x = use)
                   \<and> (use = ArmVSpaceKernelWindow
                            \<or> use = ArmVSpaceDeviceWindow))
             \<and> rghts = {})
  | ARM_Structs_A.SuperSectionPDE ptr atts rghts \<Rightarrow>
        (\<lambda>s. Platform.ptrFromPAddr ptr = (vref && ~~ mask (pageBitsForSize ARMSuperSection))
             \<and> (\<forall>x \<in> {vref .. vref + 2 ^ pde_mapping_bits - 1}.
                   uses x = ArmVSpaceKernelWindow)
             \<and> rghts = {})"

definition
  valid_pd_kernel_mappings :: "arm_vspace_region_uses \<Rightarrow> 'z::state_ext state
                                    \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
 "valid_pd_kernel_mappings uses \<equiv> \<lambda>s obj.
  case obj of
    ArchObj (PageDirectory pd) \<Rightarrow>
      (\<forall>x. valid_pde_kernel_mappings
             (pd x) (ucast x << pde_mapping_bits) uses s)
  | _ \<Rightarrow> False"

definition
  valid_global_pd_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
 "valid_global_pd_mappings \<equiv> \<lambda>s.
  obj_at (valid_pd_kernel_mappings (arm_kernel_vspace (arch_state s)) s)
    (arm_global_pd (arch_state s)) s"

definition
  valid_ao_at :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_ao_at p \<equiv> \<lambda>s. \<exists>ao. ko_at (ArchObj ao) p s \<and> valid_arch_obj ao s"

definition
  "valid_pde_mappings pde \<equiv> case pde of
    ARM_Structs_A.SectionPDE ptr _ _ _ \<Rightarrow> is_aligned ptr pageBits
  | ARM_Structs_A.SuperSectionPDE ptr _ _ \<Rightarrow> is_aligned ptr pageBits
  | _ \<Rightarrow> True"

definition
  "empty_table S ko \<equiv>
   case ko of
     ArchObj (ARM_Structs_A.PageDirectory pd) \<Rightarrow>
       \<forall>x. (\<forall>r. pde_ref (pd x) = Some r \<longrightarrow> r \<in> S) \<and>
            valid_pde_mappings (pd x) \<and>
            (x \<notin> kernel_mapping_slots \<longrightarrow> pd x = ARM_Structs_A.InvalidPDE)
   | ArchObj (ARM_Structs_A.PageTable pt) \<Rightarrow>
         pt = (\<lambda>x. ARM_Structs_A.InvalidPTE)
   | _ \<Rightarrow> False"

definition
  "valid_kernel_mappings_if_pd S ko \<equiv> case ko of
    ArchObj (ARM_Structs_A.PageDirectory pd) \<Rightarrow>
        \<forall>x r. pde_ref (pd x) = Some r
                  \<longrightarrow> ((r \<in> S) = (x \<in> kernel_mapping_slots))
  | _ \<Rightarrow> True"

definition
  "aligned_pte pte \<equiv>
     case pte of
       ARM_Structs_A.LargePagePTE p _ _ \<Rightarrow> vmsz_aligned p ARMLargePage
     | ARM_Structs_A.SmallPagePTE p _ _ \<Rightarrow> vmsz_aligned p ARMSmallPage
     | _ \<Rightarrow> True"

lemmas aligned_pte_simps[simp] =
       aligned_pte_def[split_simps ARM_Structs_A.pte.split]

definition
  valid_global_objs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_global_objs \<equiv>
  \<lambda>s. valid_ao_at (arm_global_pd (arch_state s)) s \<and>
           obj_at (empty_table (set (arm_global_pts (arch_state s))))
                  (arm_global_pd (arch_state s)) s \<and>
      (\<forall>p\<in>set (arm_global_pts (arch_state s)).
          \<exists>pt. ko_at (ArchObj (PageTable pt)) p s \<and> (\<forall>x. aligned_pte (pt x)))"

definition
  valid_asid_table :: "(word8 \<rightharpoonup> obj_ref) \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_asid_table table \<equiv> \<lambda>s. (\<forall>p \<in> ran table. asid_pool_at p s) \<and>
                                inj_on table (dom table)"

definition
  valid_global_pts :: "'z :: state_ext state \<Rightarrow> bool"
where
  "valid_global_pts \<equiv> \<lambda>s.
   \<forall>p \<in> set (arm_global_pts (arch_state s)). typ_at (AArch APageTable) p s"
(* this property now follows from valid_global_objs:
   "valid_global_objs s \<Longrightarrow> valid_global_pts s" *)

definition
  valid_arch_state :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_arch_state \<equiv> \<lambda>s.
  typ_at (AArch (AIntData ARMSmallPage)) (arm_globals_frame (arch_state s)) s \<and>
  valid_asid_table (arm_asid_table (arch_state s)) s \<and>
  page_directory_at (arm_global_pd (arch_state s)) s \<and>
  valid_global_pts s \<and>
  is_inv (arm_hwasid_table (arch_state s))
             (option_map fst o arm_asid_map (arch_state s))"

definition
  pd_at_asid :: "asid \<Rightarrow> obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "pd_at_asid asid pd \<equiv> \<lambda>s.
         ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> pd) s"

definition
  valid_asid_map :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_asid_map \<equiv>
   \<lambda>s. dom (arm_asid_map (arch_state s)) \<subseteq> {0 .. mask asid_bits} \<and>
       (\<forall>(asid, hwasid, pd) \<in> graph_of (arm_asid_map (arch_state s)).
            pd_at_asid asid pd s \<and> asid \<noteq> 0)"

datatype reftype
  = TCBWaitingSend | TCBWaitingRecv | TCBBlockedSend | TCBBlockedRecv
     | TCBSignal | TCBBound | EPSend | EPRecv | NTFNSignal | NTFNBound

primrec
 symreftype :: "reftype \<Rightarrow> reftype"
where
  "symreftype TCBWaitingSend = TCBWaitingRecv"
| "symreftype TCBWaitingRecv = TCBWaitingSend"
| "symreftype TCBBlockedSend = EPSend"
| "symreftype TCBBlockedRecv = EPRecv"
| "symreftype TCBSignal       = NTFNSignal"
| "symreftype TCBBound       = NTFNBound"
| "symreftype EPSend         = TCBBlockedSend"
| "symreftype EPRecv         = TCBBlockedRecv"
| "symreftype NTFNSignal       = TCBSignal"
| "symreftype NTFNBound       = TCBBound"

definition
  tcb_st_refs_of :: "Structures_A.thread_state  \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "tcb_st_refs_of z \<equiv> case z of (Structures_A.Running)               => {}
  | (Structures_A.Inactive)              => {}
  | (Structures_A.Restart)               => {}
  | (Structures_A.BlockedOnReply)        => {}
  | (Structures_A.IdleThreadState)       => {}
  | (Structures_A.BlockedOnReceive x b)  => {(x, TCBBlockedRecv)}
  | (Structures_A.BlockedOnSend x payl)  => {(x, TCBBlockedSend)}
  | (Structures_A.BlockedOnNotification x) => {(x, TCBSignal)}"

definition
  ep_q_refs_of   :: "Structures_A.endpoint      \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "ep_q_refs_of x \<equiv> case x of  
    Structures_A.IdleEP    => {}
  | (Structures_A.RecvEP q) => set q \<times> {EPRecv}
  | (Structures_A.SendEP q) => set q \<times> {EPSend}"

definition
  ntfn_q_refs_of  :: "ntfn                   \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "ntfn_q_refs_of x \<equiv> case x of
     Structures_A.IdleNtfn         => {}
  | (Structures_A.WaitingNtfn q)   => set q \<times> {NTFNSignal}
  | (Structures_A.ActiveNtfn b)  => {}"

(* FIXME-NTFN: two new functions: ntfn_bound_refs and tcb_bound_refs, include below by union *)

definition 
  ntfn_bound_refs :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set"
where 
  "ntfn_bound_refs t \<equiv> case t of
     Some tcb \<Rightarrow> {(tcb, NTFNBound)}
   | None \<Rightarrow> {}"

definition
  tcb_bound_refs :: "obj_ref option \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "tcb_bound_refs a \<equiv> case a of
     Some ntfn \<Rightarrow> {(ntfn, TCBBound)}
   | None \<Rightarrow> {}"

definition
  refs_of :: "Structures_A.kernel_object \<Rightarrow> (obj_ref \<times> reftype) set"
where
  "refs_of x \<equiv> case x of
     CNode sz fun      => {}
   | TCB tcb           => tcb_st_refs_of (tcb_state tcb) \<union> tcb_bound_refs (tcb_bound_notification tcb)
   | Endpoint ep       => ep_q_refs_of ep
   | Notification ntfn => ntfn_q_refs_of (ntfn_obj ntfn) \<union> ntfn_bound_refs (ntfn_bound_tcb ntfn)
   | ArchObj ao        => {}"

definition
  state_refs_of :: "'z::state_ext state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> reftype) set"
where
 "state_refs_of s \<equiv> \<lambda>x. case (kheap s x) of Some ko \<Rightarrow> refs_of ko | None \<Rightarrow> {}"

definition
  sym_refs :: "(obj_ref \<Rightarrow> (obj_ref \<times> reftype) set) \<Rightarrow> bool"
where
 "sym_refs st \<equiv> \<forall>x. \<forall>(y, tp) \<in> st x. (x, symreftype tp) \<in> st y"

definition
  pspace_aligned :: "'z::state_ext state \<Rightarrow> bool"
where
  "pspace_aligned s \<equiv>
     \<forall>x \<in> dom (kheap s). is_aligned x (obj_bits (the (kheap s x)))"

text "objects don't overlap"
definition
  pspace_distinct :: "'z::state_ext state \<Rightarrow> bool"
where
  "pspace_distinct \<equiv>
   \<lambda>s. \<forall>x y ko ko'. kheap s x = Some ko \<and> kheap s y = Some ko' \<and> x \<noteq> y \<longrightarrow>
         {x .. x + (2 ^ obj_bits ko - 1)} \<inter>
         {y .. y + (2 ^ obj_bits ko' - 1)} = {}"

text "objects live in the kernel window"
definition
  pspace_in_kernel_window :: "'z::state_ext state \<Rightarrow> bool"
where
 "pspace_in_kernel_window \<equiv> \<lambda>s.
    \<forall>x ko. kheap s x = Some ko \<longrightarrow>
       (\<forall>y \<in> {x .. x + (2 ^ obj_bits ko) - 1}.
             arm_kernel_vspace (arch_state s) y = ArmVSpaceKernelWindow)"

primrec
  live :: "Structures_A.kernel_object \<Rightarrow> bool"
where
  "live (CNode sz fun)      = False"
| "live (TCB tcb)           = (bound (tcb_bound_notification tcb) \<or> (tcb_state tcb \<noteq> Structures_A.Inactive \<and>
                               tcb_state tcb \<noteq> Structures_A.IdleThreadState))"
| "live (Endpoint ep)       = (ep \<noteq> Structures_A.IdleEP)"
| "live (Notification ntfn) = (bound (ntfn_bound_tcb ntfn) \<or> (\<exists>ts. ntfn_obj ntfn = Structures_A.WaitingNtfn ts))"
| "live (ArchObj ao)        = False"

fun
  zobj_refs :: "cap \<Rightarrow> obj_ref set"
where
  "zobj_refs (cap.Zombie r b n) = {}"
| "zobj_refs x                  = obj_refs x"

definition
  ex_nonz_cap_to :: "obj_ref \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "ex_nonz_cap_to ref \<equiv> (\<lambda>s. \<exists>cref. cte_wp_at (\<lambda>c. ref \<in> zobj_refs c) cref s)"

text {* All live objects have caps. The contrapositive
        of this is significant in establishing invariants
        over retype. The exception are objects that are
        not in the scope of any untyped capability, as
        these can never be retyped. *}
definition
  if_live_then_nonz_cap :: "'z::state_ext state \<Rightarrow> bool"
where
 "if_live_then_nonz_cap s \<equiv>
    \<forall>ptr. obj_at live ptr s \<longrightarrow> ex_nonz_cap_to ptr s"

definition
  caps_of_state :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cap option"
where
 "caps_of_state s \<equiv> (\<lambda>p. if (\<exists>cap. fst (get_cap p s) = {(cap, s)})
                         then Some (THE cap. fst (get_cap p s) = {(cap, s)})
                         else None)"

primrec
  cte_refs :: "cap \<Rightarrow> (irq \<Rightarrow> obj_ref) \<Rightarrow> cslot_ptr set"
where
  "cte_refs (cap.UntypedCap p n fr) f                = {}"
| "cte_refs (cap.NullCap) f                          = {}"
| "cte_refs (cap.EndpointCap r badge rights) f       = {}"
| "cte_refs (cap.NotificationCap r badge rights) f  = {}"
| "cte_refs (cap.CNodeCap r bits guard) f            =
     {r} \<times> {xs. length xs = bits}"
| "cte_refs (cap.ThreadCap r) f                      =
     {r} \<times> (dom tcb_cap_cases)"
| "cte_refs (cap.DomainCap) f                        = {}"
| "cte_refs (cap.Zombie r b n) f                     =
     {r} \<times> {xs. length xs = (zombie_cte_bits b) \<and>
                unat (of_bl xs :: word32) < n}"
| "cte_refs (cap.IRQControlCap) f                    = {}"
| "cte_refs (cap.IRQHandlerCap irq) f                = {(f irq, [])}"
| "cte_refs (cap.ReplyCap tcb master) f              = {}"
| "cte_refs (cap.ArchObjectCap cap) f                = {}"

definition
  ex_cte_cap_wp_to :: "(cap \<Rightarrow> bool) \<Rightarrow> cslot_ptr \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "ex_cte_cap_wp_to P ptr \<equiv> \<lambda>s. \<exists>cref.
        cte_wp_at (\<lambda>c. P c \<and> ptr \<in> cte_refs c (interrupt_irq_node s)) cref s"

abbreviation
 "ex_cte_cap_to \<equiv> ex_cte_cap_wp_to \<top>"

(* All non-Null caps live either in capability tables to which there
   are appropriate existing capabilities. *)

definition
  appropriate_cte_cap :: "cap \<Rightarrow> cap \<Rightarrow> bool"
where
 "appropriate_cte_cap cap cte_cap \<equiv>
  case cap of
    cap.NullCap \<Rightarrow> True
  | cap.NotificationCap _ _ _ \<Rightarrow> True
  | _ \<Rightarrow> cap_irqs cte_cap = {}"

definition
  if_unsafe_then_cap :: "'z::state_ext state \<Rightarrow> bool"
where
 "if_unsafe_then_cap s \<equiv> \<forall>cref cap. caps_of_state s cref = Some cap
                         \<longrightarrow> cap \<noteq> cap.NullCap
                        \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) cref s"

text {* All zombies are final. *}
definition
  zombies_final :: "'z::state_ext state \<Rightarrow> bool"
where
 "zombies_final \<equiv>
  \<lambda>s. \<forall>p. cte_wp_at is_zombie p s \<longrightarrow> cte_wp_at (\<lambda>cap. is_final_cap' cap s) p s"

definition
  valid_pspace :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_pspace \<equiv> valid_objs and pspace_aligned and
                  pspace_distinct and if_live_then_nonz_cap
                  and zombies_final
                  and (\<lambda>s. sym_refs (state_refs_of s))"

definition
  null_filter :: "('a \<Rightarrow> cap option) \<Rightarrow> ('a \<Rightarrow> cap option)"
where
  "null_filter f \<equiv> (\<lambda>x. if f x = Some cap.NullCap then None else f x)"

definition
  untyped_mdb :: "cdt \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
 "untyped_mdb m cs \<equiv>
  \<forall>ptr ptr' cap cap'.
      cs ptr = Some cap \<longrightarrow> is_untyped_cap cap \<longrightarrow>
      cs ptr' = Some cap' \<longrightarrow> obj_refs cap' \<inter> untyped_range cap \<noteq> {} \<longrightarrow>
      ptr' \<in> descendants_of ptr m"

text "inclusion properties on untyped caps"
definition
  untyped_inc :: "cdt \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
  "untyped_inc m cs \<equiv>
  \<forall>p p' c c'.
     cs p = Some c \<longrightarrow> is_untyped_cap c \<longrightarrow>
     cs p' = Some c' \<longrightarrow> is_untyped_cap c' \<longrightarrow>
     (untyped_range c \<subseteq> untyped_range c' \<or>
      untyped_range c' \<subseteq> untyped_range c \<or>
      untyped_range c \<inter> untyped_range c' = {}) \<and>
     (untyped_range c \<subset> untyped_range c' \<longrightarrow> (p \<in> descendants_of p' m \<and> untyped_range c \<inter> usable_untyped_range c' = {})) \<and>
     (untyped_range c' \<subset> untyped_range c \<longrightarrow> (p' \<in> descendants_of p m \<and> untyped_range c' \<inter> usable_untyped_range c = {})) \<and>
     (untyped_range c = untyped_range c' \<longrightarrow>
       (p' \<in> descendants_of p m \<and> usable_untyped_range c = {} \<or> p \<in> descendants_of p' m \<and> usable_untyped_range c' = {} \<or> p = p'))"

definition
  "cap_range c \<equiv> untyped_range c \<union> obj_refs c"

definition
  descendants_inc :: "cdt \<Rightarrow> (cslot_ptr \<rightharpoonup> cap) \<Rightarrow> bool"
where
  "descendants_inc m cs \<equiv>
  \<forall>p p'. p \<in> descendants_of p' m \<longrightarrow> (cap_class (the (cs p)) = cap_class (the (cs p')) \<and> cap_range (the (cs p)) \<subseteq> cap_range (the (cs p')))"

abbreviation
  "awaiting_reply ts \<equiv> ts = Structures_A.BlockedOnReply"

definition
  "valid_ioc s \<equiv>
   \<forall>p. is_original_cap s p \<longrightarrow> cte_wp_at (\<lambda>x. x \<noteq> cap.NullCap)  p s"

definition
  "has_reply_cap t s \<equiv> \<exists>p. cte_wp_at (op = (cap.ReplyCap t False)) p s"

definition
  "mdb_cte_at ct_at m \<equiv> \<forall>p c. m c = Some p \<longrightarrow> ct_at p \<and> ct_at c"

definition
  "no_mloop m \<equiv> \<forall>p. \<not> m \<Turnstile> p \<rightarrow> p"

definition
  "ut_revocable r cs \<equiv> \<forall>p cap. cs p = Some cap \<longrightarrow> is_untyped_cap cap \<longrightarrow> r p"

definition
  "irq_revocable r cs \<equiv> \<forall>p. cs p = Some cap.IRQControlCap \<longrightarrow> r p"

definition
  "reply_master_revocable r cs \<equiv> \<forall>p cap. cs p = Some cap \<longrightarrow>
                                          is_master_reply_cap cap \<longrightarrow> r p"

definition
  "reply_caps_mdb m cs \<equiv> \<forall>ptr t.
     cs ptr = Some (cap.ReplyCap t False) \<longrightarrow>
     (\<exists>ptr'. m ptr = Some ptr' \<and> cs ptr' = Some (cap.ReplyCap t True))"

definition
  "reply_masters_mdb m cs \<equiv> \<forall>ptr t.
     cs ptr = Some (cap.ReplyCap t True) \<longrightarrow> m ptr = None \<and>
     (\<forall>ptr'\<in>descendants_of ptr m. cs ptr' = Some (cap.ReplyCap t False))"

definition
  "reply_mdb m cs \<equiv> reply_caps_mdb m cs \<and> reply_masters_mdb m cs"

definition
  "valid_mdb \<equiv> \<lambda>s. mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s) \<and>
                   untyped_mdb (cdt s) (caps_of_state s) \<and> descendants_inc (cdt s) (caps_of_state s) \<and>
                   no_mloop (cdt s) \<and> untyped_inc (cdt s) (caps_of_state s) \<and>
                   ut_revocable (is_original_cap s) (caps_of_state s) \<and>
                   irq_revocable (is_original_cap s) (caps_of_state s) \<and>
                   reply_master_revocable (is_original_cap s) (caps_of_state s) \<and>
                   reply_mdb (cdt s) (caps_of_state s)"

abbreviation "idle_tcb_at \<equiv> pred_tcb_at (\<lambda>t. (itcb_state t, itcb_bound_notification t))"

definition
  "valid_idle \<equiv> \<lambda>s. idle_tcb_at (\<lambda>p. (idle (fst p)) \<and> (snd p = None)) (idle_thread s) s 
                   \<and> idle_thread s = idle_thread_ptr"

definition
  "only_idle \<equiv> \<lambda>s. \<forall>t. st_tcb_at idle t s \<longrightarrow> t = idle_thread s"

definition
  "valid_reply_masters \<equiv> \<lambda>s. \<forall>p t. cte_wp_at (op = (cap.ReplyCap t True)) p s \<longrightarrow>
                                     p = (t, tcb_cnode_index 2)"

definition
  "unique_reply_caps cs \<equiv>
   \<forall>ptr ptr' cap cap'.
       cs ptr = Some cap \<longrightarrow> is_reply_cap cap \<longrightarrow>
       cs ptr' = Some cap' \<longrightarrow> cap = cap' \<longrightarrow> ptr = ptr'"

definition
  "valid_reply_caps \<equiv> \<lambda>s.
       (\<forall>t. has_reply_cap t s \<longrightarrow> st_tcb_at awaiting_reply t s) \<and>
       unique_reply_caps (caps_of_state s)"

definition
  valid_refs :: "obj_ref set \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "valid_refs R \<equiv> \<lambda>s. \<forall>cref. \<not>cte_wp_at (\<lambda>c. R \<inter> cap_range c \<noteq> {}) cref s"

definition
  global_refs :: "'z::state_ext state \<Rightarrow> obj_ref set"
where
  "global_refs \<equiv> \<lambda>s.
  {idle_thread s, arm_globals_frame (arch_state s), arm_global_pd (arch_state s)} \<union>
   range (interrupt_irq_node s) \<union>
   set (arm_global_pts (arch_state s))"

definition
  valid_global_refs :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_global_refs \<equiv> \<lambda>s. valid_refs (global_refs s) s"

definition
  valid_irq_node :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_irq_node \<equiv> \<lambda>s. inj (interrupt_irq_node s)
      \<and> (\<forall>irq. cap_table_at 0 (interrupt_irq_node s irq) s)"

definition
  irq_issued :: "irq \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
  "irq_issued irq \<equiv> \<lambda>s. interrupt_states s irq = irq_state.IRQSignal"

definition
  valid_irq_handlers :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_irq_handlers \<equiv> \<lambda>s. \<forall>cap \<in> ran (caps_of_state s). \<forall>irq \<in> cap_irqs cap. irq_issued irq s"

definition valid_irq_masks :: "(word8 \<Rightarrow> irq_state) \<Rightarrow> (word8 \<Rightarrow> bool) \<Rightarrow> bool" where
  "valid_irq_masks table masked \<equiv> \<forall>irq. table irq = IRQInactive \<longrightarrow> masked irq"
definition valid_irq_states :: "'z::state_ext state \<Rightarrow> bool" where
  "valid_irq_states \<equiv> \<lambda>s.
    valid_irq_masks (interrupt_states s) (irq_masks (machine_state s))"

text "caps point at objects in the kernel window"
definition
  cap_refs_in_kernel_window :: "'z::state_ext state \<Rightarrow> bool"
where
 "cap_refs_in_kernel_window \<equiv> \<lambda>s. valid_refs
         {x. arm_kernel_vspace (arch_state s) x \<noteq> ArmVSpaceKernelWindow} s"

definition
  vs_cap_ref :: "cap \<Rightarrow> vs_ref list option"
where
  "vs_cap_ref cap \<equiv> case cap of
   Structures_A.ArchObjectCap (ARM_Structs_A.ASIDPoolCap _ asid) \<Rightarrow>
     Some [VSRef (ucast (asid_high_bits_of asid)) None]
 | Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap _ (Some asid)) \<Rightarrow>
     Some [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Structures_A.ArchObjectCap (ARM_Structs_A.PageTableCap _ (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Structures_A.ArchObjectCap (ARM_Structs_A.PageCap word rights ARMSmallPage (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 8) (Some APageTable),
           VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Structures_A.ArchObjectCap (ARM_Structs_A.PageCap word rights ARMLargePage (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef ((vptr >> 12) && mask 8) (Some APageTable),
           VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Structures_A.ArchObjectCap (ARM_Structs_A.PageCap word rights ARMSection (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | Structures_A.ArchObjectCap (ARM_Structs_A.PageCap word rights ARMSuperSection (Some (asid, vptr))) \<Rightarrow>
     Some [VSRef (vptr >> 20) (Some APageDirectory),
           VSRef (asid && mask asid_low_bits) (Some AASIDPool),
           VSRef (ucast (asid_high_bits_of asid)) None]
 | _ \<Rightarrow> None"

definition
  "is_pg_cap cap \<equiv> \<exists>p R sz m. cap =
   cap.ArchObjectCap (arch_cap.PageCap p R sz m)"

definition
  "is_pd_cap c \<equiv>
   \<exists>p asid. c = cap.ArchObjectCap (arch_cap.PageDirectoryCap p asid)"

definition
  "is_pt_cap c \<equiv> \<exists>p asid. c = cap.ArchObjectCap (arch_cap.PageTableCap p asid)"

definition
  "cap_asid cap \<equiv> case cap of
    Structures_A.ArchObjectCap (ARM_Structs_A.PageCap _ _ _ (Some (asid, _))) \<Rightarrow> Some asid
  | Structures_A.ArchObjectCap (ARM_Structs_A.PageTableCap _ (Some (asid, _))) \<Rightarrow> Some asid
  | Structures_A.ArchObjectCap (ARM_Structs_A.PageDirectoryCap _ (Some asid)) \<Rightarrow> Some asid
  | _ \<Rightarrow> None"

  (* needed for retype: if reachable, then cap, if cap then protected by untyped cap.
     strengthened for preservation in cap delete: ref in cap must unmap the right objects *)
definition
  "valid_vs_lookup \<equiv> \<lambda>s. \<forall>p ref. (ref \<unrhd> p) s \<longrightarrow>
  ref \<noteq> [VSRef 0 (Some AASIDPool), VSRef 0 None] \<and>
  (\<exists>p' cap. caps_of_state s p' = Some cap \<and>
            p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"

  (* needed for map: installing new object should add only one mapping *)
definition
  "valid_table_caps \<equiv> \<lambda>s.
  \<forall>r p cap. caps_of_state s p = Some cap \<longrightarrow>
            (is_pd_cap cap \<or> is_pt_cap cap) \<longrightarrow>
            cap_asid cap = None \<longrightarrow>
            r \<in> obj_refs cap \<longrightarrow>
            obj_at (empty_table (set (arm_global_pts (arch_state s)))) r s"

  (* needed to preserve valid_table_caps in map *)
definition
  "unique_table_caps \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
  cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
  cap_asid cap = None \<longrightarrow>
  obj_refs cap' = obj_refs cap \<longrightarrow>
  (is_pd_cap cap \<longrightarrow> is_pd_cap cap' \<longrightarrow> p' = p) \<and>
  (is_pt_cap cap \<longrightarrow> is_pt_cap cap' \<longrightarrow> p' = p)"

definition
  table_cap_ref :: "cap \<Rightarrow> vs_ref list option"
where
  "table_cap_ref cap \<equiv> case cap of
     Structures_A.ArchObjectCap (ARM_Structs_A.ASIDPoolCap _ asid) \<Rightarrow>
       Some [VSRef (ucast (asid_high_bits_of asid)) None]
   | Structures_A.ArchObjectCap
       (ARM_Structs_A.PageDirectoryCap _ (Some asid)) \<Rightarrow>
       Some [VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None]
   | Structures_A.ArchObjectCap
       (ARM_Structs_A.PageTableCap _ (Some (asid, vptr))) \<Rightarrow>
       Some [VSRef (vptr >> 20) (Some APageDirectory),
             VSRef (asid && mask asid_low_bits) (Some AASIDPool),
             VSRef (ucast (asid_high_bits_of asid)) None]
   | _ \<Rightarrow> None"

  (* needed to avoid a single page insertion
     resulting in multiple valid lookups *)
definition
  "unique_table_refs \<equiv> \<lambda>cs. \<forall>p p' cap cap'.
  cs p = Some cap \<longrightarrow> cs p' = Some cap' \<longrightarrow>
  obj_refs cap' = obj_refs cap \<longrightarrow>
  table_cap_ref cap' = table_cap_ref cap"

definition
  valid_kernel_mappings :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_kernel_mappings \<equiv>
     \<lambda>s. \<forall>ko \<in> ran (kheap s).
          valid_kernel_mappings_if_pd
             (set (arm_global_pts (arch_state s))) ko"

definition
  "valid_arch_caps \<equiv> valid_vs_lookup and valid_table_caps and
                     (\<lambda>s. unique_table_caps (caps_of_state s)
                        \<and> unique_table_refs (caps_of_state s))"

definition
  "valid_machine_state \<equiv>
   \<lambda>s. \<forall>p. in_user_frame p (s::'z::state_ext state) \<or> underlying_memory (machine_state s) p = 0"

definition
  valid_state :: "'z::state_ext state \<Rightarrow> bool"
where
  "valid_state \<equiv> valid_pspace
                  and valid_mdb
                  and valid_ioc
                  and valid_idle
                  and only_idle
                  and if_unsafe_then_cap
                  and valid_reply_caps
                  and valid_reply_masters
                  and valid_global_refs
                  and valid_arch_state
                  and valid_irq_node
                  and valid_irq_handlers
                  and valid_irq_states
                  and valid_machine_state
                  and valid_arch_objs
                  and valid_arch_caps
                  and valid_global_objs
                  and valid_kernel_mappings
                  and equal_kernel_mappings
                  and valid_asid_map
                  and valid_global_pd_mappings
                  and pspace_in_kernel_window
                  and cap_refs_in_kernel_window"

definition
 "ct_in_state test \<equiv> \<lambda>s. st_tcb_at test (cur_thread s) s"

definition
  "cur_tcb s \<equiv> tcb_at (cur_thread s) s"

definition
  invs :: "'z::state_ext state \<Rightarrow> bool" where
  "invs \<equiv> valid_state and cur_tcb"


subsection "Derived concepts"

definition
  untyped_children_in_mdb :: "'z::state_ext state \<Rightarrow> bool"
where
 "untyped_children_in_mdb s \<equiv>
    \<forall>ptr ptr' cap. (cte_wp_at (op = cap) ptr s \<and> is_untyped_cap cap
                     \<and> cte_wp_at (\<lambda>cap'. obj_refs cap' \<inter> untyped_range cap \<noteq> {}) ptr' s)
                     \<longrightarrow> ptr' \<in> descendants_of ptr (cdt s)"

definition
  "caps_contained s \<equiv> \<forall>c p c' p'.
  cte_wp_at (op = c) p s \<longrightarrow>
  cte_wp_at (op = c') p' s \<longrightarrow>
  obj_ref_of c' \<in> untyped_range c \<longrightarrow>
  (is_cnode_cap c' \<or> is_thread_cap c') \<longrightarrow>
  obj_ref_of c' + obj_size c' - 1 \<in> untyped_range c"

definition
  obj_irq_refs :: "cap \<Rightarrow> (word32 + irq) set"
where
 "obj_irq_refs cap \<equiv> (Inl ` obj_refs cap) \<union> (Inr ` cap_irqs cap)"

definition
  "obj_bits_type T \<equiv> case T of
    ACapTable n \<Rightarrow> 4 + n
  | AGarbage \<Rightarrow> 4
  | ATCB \<Rightarrow> obj_bits (TCB undefined)
  | AEndpoint \<Rightarrow> obj_bits (Endpoint undefined)
  | ANTFN \<Rightarrow> obj_bits (Notification undefined)
  | AArch T' \<Rightarrow> (case T' of
    AASIDPool \<Rightarrow> obj_bits (ArchObj (ARM_Structs_A.ASIDPool undefined))
  | AIntData sz \<Rightarrow> obj_bits (ArchObj (DataPage sz))
  | APageDirectory \<Rightarrow> obj_bits (ArchObj (ARM_Structs_A.PageDirectory undefined))
  | APageTable \<Rightarrow> obj_bits (ArchObj (ARM_Structs_A.PageTable undefined)))"

definition
  "typ_range p T \<equiv> {p .. p + 2^obj_bits_type T - 1}"

abbreviation
  CapTableObject :: Structures_A.apiobject_type where
  "CapTableObject == Structures_A.CapTableObject"

abbreviation
  Untyped :: Structures_A.apiobject_type where
  "Untyped == Structures_A.Untyped"

abbreviation
  "active st \<equiv> st = Structures_A.Running \<or> st = Structures_A.Restart"

abbreviation
  "simple st \<equiv> st = Structures_A.Inactive \<or>
                 st = Structures_A.Running \<or>
                 st = Structures_A.Restart \<or>
                 idle st \<or> awaiting_reply st"
abbreviation
  "ct_active \<equiv> ct_in_state active"

abbreviation
  "ct_running  \<equiv> ct_in_state  (\<lambda>st. st = Structures_A.Running)"

abbreviation
  "ct_idle \<equiv> ct_in_state idle"

abbreviation(input)
 "all_invs_but_sym_refs
    \<equiv> valid_objs and pspace_aligned and pspace_distinct and valid_ioc
       and if_live_then_nonz_cap and zombies_final
       and valid_mdb and valid_idle and only_idle and if_unsafe_then_cap
       and valid_reply_caps and valid_reply_masters and valid_global_refs
       and valid_arch_state and valid_machine_state and valid_irq_states
       and valid_irq_node and valid_irq_handlers and valid_arch_objs
       and valid_arch_caps and valid_global_objs and valid_kernel_mappings
       and equal_kernel_mappings and valid_asid_map
       and valid_global_pd_mappings
       and pspace_in_kernel_window and cap_refs_in_kernel_window
       and cur_tcb"


-- ---------------------------------------------------------------------------
section "Lemmas"

lemma valid_bound_ntfn_None[simp]:
  "valid_bound_ntfn None = \<top>"
  by (auto simp: valid_bound_ntfn_def)

lemma valid_bound_ntfn_Some[simp]:
  "valid_bound_ntfn (Some x) = ntfn_at x"
  by (auto simp: valid_bound_ntfn_def)

lemma valid_bound_tcb_None[simp]:
  "valid_bound_tcb None = \<top>"
  by (auto simp: valid_bound_tcb_def)

lemma valid_bound_tcb_Some[simp]:
  "valid_bound_tcb (Some x) = tcb_at x"
  by (auto simp: valid_bound_tcb_def)

lemmas wellformed_acap_simps =
  wellformed_mapdata_def wellformed_acap_def[split_simps arch_cap.split]

lemmas wellformed_cap_simps =
  wellformed_acap_simps wellformed_cap_def[split_simps cap.split]

lemmas valid_cap_ref_simps' =
  valid_cap_ref_def[split_simps cap.split arch_cap.split]

(*Pure wizardry*)
lemma valid_cap_ref_simps :
  "valid_cap_ref NullCap (s::'z_1::state_ext state) = True \<and>
valid_cap_ref (UntypedCap (x::word32) (xa::nat) (xb::nat)) (sa::'z_1::state_ext state) =
(valid_untyped (UntypedCap x xa xb) sa \<and> xb \<le> (2::nat) ^ xa \<and> x \<noteq> (0::word32)) \<and>
valid_cap_ref (EndpointCap (xc::word32) (xd::word32) (xe::rights set))
 (sb::'z_1::state_ext state) =
ep_at xc sb \<and>
valid_cap_ref (NotificationCap (xf::word32) (xg::word32) (xh::rights set))
 (sc::'z_1::state_ext state) =
ntfn_at xf sc \<and>
valid_cap_ref (ReplyCap (xi::word32) (xj::bool)) (sd::'z_1::state_ext state) =
tcb_at xi sd \<and>
valid_cap_ref (CNodeCap (xk::word32) (xl::nat) (xm::bool list))
 (se::'z_1::state_ext state) =
cap_table_at xl xk se \<and>
valid_cap_ref (ThreadCap (xn::word32)) (sf::'z_1::state_ext state) = tcb_at xn sf \<and>
valid_cap_ref DomainCap (sp::'z_1::state_ext state) = True \<and>
valid_cap_ref IRQControlCap (sg::'z_1::state_ext state) = True \<and>
valid_cap_ref (IRQHandlerCap (xo::word8)) (sh::'z_1::state_ext state) = True \<and>
valid_cap_ref (Zombie (xp::word32) (xq::nat option) (xr::nat))
 (si::'z_1::state_ext state) =
(case xq of None \<Rightarrow> tcb_at xp si | Some (b::nat) \<Rightarrow> cap_table_at b xp si) \<and>
valid_cap_ref (ArchObjectCap (ASIDPoolCap (xs::word32) (xt::word32)))
 (sj::'z_1::state_ext state) =
asid_pool_at xs sj \<and>
valid_cap_ref (ArchObjectCap ASIDControlCap) (sk::'z_1::state_ext state) = True \<and>
valid_cap_ref
 (ArchObjectCap
   (PageCap (xu::word32) (xv::rights set) (xw::vmpage_size)
     (xx::(word32 \<times> word32) option)))
 (sl::'z_1::state_ext state) =
typ_at (AArch (AIntData xw)) xu sl \<and>
valid_cap_ref
 (ArchObjectCap (PageTableCap (xy::word32) (xz::(word32 \<times> word32) option)))
 (sm::'z_1::state_ext state) =
page_table_at xy sm \<and>
valid_cap_ref (ArchObjectCap (PageDirectoryCap (ya::word32) (yb::word32 option)))
 (sn::'z_1::state_ext state) =
page_directory_at ya sn"
  by (rule valid_cap_ref_simps')

lemmas valid_cap_simps' = valid_cap_def[split_simps cap.split arch_cap.split]

lemma valid_cap_simps :
  "(s::'z_1::state_ext state) \<turnstile> NullCap = (cap_aligned NullCap \<and> True) \<and>
(sa::'z_1::state_ext state) \<turnstile> UntypedCap (x::word32) (xa::nat) (xb::nat) =
(cap_aligned (UntypedCap x xa xb) \<and>
 valid_untyped (UntypedCap x xa xb) sa \<and>
 (4::nat) \<le> xa \<and> xb \<le> (2::nat) ^ xa \<and> x \<noteq> (0::word32)) \<and>
(sb::'z_1::state_ext state) \<turnstile> EndpointCap (xc::word32) (xd::word32) (xe::rights set) =
(cap_aligned (EndpointCap xc xd xe) \<and> ep_at xc sb) \<and>
(sc::'z_1::state_ext state) \<turnstile> NotificationCap (xf::word32) (xg::word32)
                        (xh::rights set) =
(cap_aligned (NotificationCap xf xg xh) \<and> ntfn_at xf sc \<and> AllowGrant \<notin> xh) \<and>
(sd::'z_1::state_ext state) \<turnstile> ReplyCap (xi::word32) (xj::bool) =
(cap_aligned (ReplyCap xi xj) \<and> tcb_at xi sd) \<and>
(se::'z_1::state_ext state) \<turnstile> CNodeCap (xk::word32) (xl::nat) (xm::bool list) =
(cap_aligned (CNodeCap xk xl xm) \<and>
 cap_table_at xl xk se \<and> xl \<noteq> (0::nat) \<and> length xm \<le> (32::nat)) \<and>
(sf::'z_1::state_ext state) \<turnstile> ThreadCap (xn::word32) =
(cap_aligned (ThreadCap xn) \<and> tcb_at xn sf) \<and>
(sp::'z_1::state_ext state) \<turnstile> DomainCap = (cap_aligned DomainCap \<and> True) \<and>
(sg::'z_1::state_ext state) \<turnstile> IRQControlCap = (cap_aligned IRQControlCap \<and> True) \<and>
(sh::'z_1::state_ext state) \<turnstile> IRQHandlerCap (xo::word8) =
(cap_aligned (IRQHandlerCap xo) \<and> xo \<le> maxIRQ) \<and>
(si::'z_1::state_ext state) \<turnstile> Zombie (xp::word32) (xq::nat option) (xr::nat) =
(cap_aligned (Zombie xp xq xr) \<and>
 (case xq of None \<Rightarrow> tcb_at xp si \<and> xr \<le> (5::nat)
  | Some (b::nat) \<Rightarrow> cap_table_at b xp si \<and> xr \<le> (2::nat) ^ b \<and> b \<noteq> (0::nat))) \<and>
(sj::'z_1::state_ext state) \<turnstile> ArchObjectCap (ASIDPoolCap (xs::word32) (xt::word32)) =
(cap_aligned (ArchObjectCap (ASIDPoolCap xs xt)) \<and>
 asid_pool_at xs sj \<and>
 is_aligned xt asid_low_bits \<and> xt \<le> (2::word32) ^ asid_bits - (1::word32)) \<and>
(sk::'z_1::state_ext state) \<turnstile> ArchObjectCap ASIDControlCap =
(cap_aligned (ArchObjectCap ASIDControlCap) \<and> True) \<and>
(sl::'z_1::state_ext state) \<turnstile> ArchObjectCap
                        (PageCap (xu::word32) (xv::rights set) (xw::vmpage_size)
                          (xx::(word32 \<times> word32) option)) =
(cap_aligned (ArchObjectCap (PageCap xu xv xw xx)) \<and>
 typ_at (AArch (AIntData xw)) xu sl \<and>
 xv \<in> valid_vm_rights \<and>
 (case xx of None \<Rightarrow> True
  | Some (asid, ref::word32) \<Rightarrow>
      (0::word32) < asid \<and>
      asid \<le> (2::word32) ^ asid_bits - (1::word32) \<and>
      vmsz_aligned ref xw \<and> ref < kernel_base)) \<and>
(sm::'z_1::state_ext state) \<turnstile> ArchObjectCap
                        (PageTableCap (xy::word32)
                          (xz::(word32 \<times> word32) option)) =
(cap_aligned (ArchObjectCap (PageTableCap xy xz)) \<and>
 page_table_at xy sm \<and>
 (case xz of None \<Rightarrow> True
  | Some (asid, vref::word32) \<Rightarrow>
      (0::word32) < asid \<and>
      asid \<le> (2::word32) ^ asid_bits - (1::word32) \<and>
      vref < kernel_base \<and> is_aligned vref (pageBitsForSize ARMSection))) \<and>
(sn::'z_1::state_ext state) \<turnstile> ArchObjectCap
                        (PageDirectoryCap (ya::word32) (yb::word32 option)) =
(cap_aligned (ArchObjectCap (PageDirectoryCap ya yb)) \<and>
 page_directory_at ya sn \<and>
 (case yb of None \<Rightarrow> True
  | Some (asid::word32) \<Rightarrow>
      (0::word32) < asid \<and> asid \<le> (2::word32) ^ asid_bits - (1::word32)))"
 by (rule valid_cap_simps')



lemma is_ep:
  "is_ep ko = (\<exists>ep. ko = Endpoint ep)"
  unfolding is_ep_def by (cases ko) auto

lemma is_ntfn:
  "is_ntfn ko = (\<exists>ep. ko = Notification ep)"
  unfolding is_ntfn_def by (cases ko) auto

lemma is_tcb:
  "is_tcb ko = (\<exists>tcb. ko = TCB tcb)"
  unfolding is_tcb_def by (cases ko) auto

lemma is_cap_table:
  "is_cap_table bits ko =
  (\<exists>cs. ko = CNode bits cs \<and> well_formed_cnode_n bits cs)"
  unfolding is_cap_table_def by (cases ko) auto

lemmas is_obj_defs = is_ep is_ntfn is_tcb is_cap_table

-- "sanity check"
lemma obj_at_get_object:
  "obj_at P ref s \<Longrightarrow> fst (get_object ref s) \<noteq> {}"
  by (auto simp: obj_at_def get_object_def gets_def get_def
                 return_def assert_def bind_def)

lemma ko_at_tcb_at:
  "ko_at (TCB t) p s \<Longrightarrow> tcb_at p s"
  by (simp add: obj_at_def is_tcb)

lemma tcb_at_def:
  "tcb_at t s = (\<exists>tcb. get_tcb t s = Some tcb)"
  by (simp add: obj_at_def get_tcb_def is_tcb_def
           split: option.splits Structures_A.kernel_object.splits)

lemma pred_tcb_def2:
  "pred_tcb_at proj test addr s = (\<exists>tcb. (get_tcb addr s) = Some tcb \<and> test (proj (tcb_to_itcb tcb)))"
  by (simp add: obj_at_def pred_tcb_at_def get_tcb_def
            split: option.splits Structures_A.kernel_object.splits)

(* sseefried: 'st_tcb_def2' only exists to make existing proofs go through. Can use 'pred_tcb_at_def2' instead *)
lemmas st_tcb_def2 = pred_tcb_def2[where proj=itcb_state,simplified]

lemma obj_at_eq_helper:
  "\<lbrakk> \<And>obj. P obj = P' obj \<rbrakk> \<Longrightarrow> obj_at P = obj_at P'"
  apply (rule ext)+
  apply (simp add: obj_at_def)
  done

lemmas a_type_simps =
  a_type_def[split_simps Structures_A.kernel_object.split arch_kernel_obj.split]

lemma tcb_at_typ:
  "tcb_at = typ_at ATCB"
  apply (rule obj_at_eq_helper)
  apply (simp add: is_tcb_def a_type_def
            split: Structures_A.kernel_object.splits)
  done

lemma ntfn_at_typ:
  "ntfn_at = typ_at ANTFN"
  apply (rule obj_at_eq_helper)
  apply (simp add: is_ntfn_def a_type_def
            split: Structures_A.kernel_object.splits)
  done

lemma ep_at_typ:
  "ep_at = typ_at AEndpoint"
  apply (rule obj_at_eq_helper)
  apply (simp add: is_ep_def a_type_def
            split: Structures_A.kernel_object.splits)
  done

lemma length_set_helper:
  "({x :: 'a list. length x = l} = {x. length x = l'}) = (l = l')"
  apply (rule iffI, simp_all)
  apply (cases "replicate l undefined \<in> {x :: 'a list. length x = l}")
   apply simp
  apply (subst(asm) mem_simps)
  apply simp
  done

lemma cap_table_at_typ:
  "cap_table_at n = typ_at (ACapTable n)"
  apply (rule obj_at_eq_helper)
  apply (case_tac obj, simp_all add: is_cap_table_def a_type_def
                                     well_formed_cnode_n_def)
  apply (auto simp: length_set_helper)
  done

lemma cte_at_def:
  "cte_at p s \<equiv> \<exists>cap. fst (get_cap p s) = {(cap,s)}"
  by (simp add: cte_wp_at_def)

lemma vmsz_aligned_ARMSection:
  "vmsz_aligned vref ARMSection = is_aligned vref (pageBitsForSize ARMSection)"
  by (simp add: vmsz_aligned_def pageBitsForSize_def)

lemma valid_cap_def2:
  "s \<turnstile> c \<equiv> cap_aligned c \<and> wellformed_cap c \<and> valid_cap_ref c s"
  apply (rule eq_reflection)
  apply (cases c)
          apply (simp_all add: valid_cap_simps wellformed_cap_simps
                               valid_cap_ref_simps
                        split: option.splits)
    apply (fastforce+)[4]
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
    apply (auto simp add: valid_cap_simps wellformed_acap_simps
                          valid_cap_ref_simps vmsz_aligned_ARMSection
                split: option.splits)
done

lemma tcb_cnode_index_distinct[simp]:
  "(tcb_cnode_index n = tcb_cnode_index m)
       = ((of_nat n :: 3 word) = (of_nat m :: 3 word))"
  by (simp add: tcb_cnode_index_def)


lemma tcb_cap_cases_simps[simp]:
  "tcb_cap_cases (tcb_cnode_index 0) =
   Some (tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>))"
  "tcb_cap_cases (tcb_cnode_index (Suc 0)) =
   Some (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. \<top>))"
  "tcb_cap_cases (tcb_cnode_index 2) =
   Some (tcb_reply, tcb_reply_update,
         (\<lambda>t st c. (is_master_reply_cap c \<and> obj_ref_of c = t) \<or>
                   (halted st \<and> (c = cap.NullCap))))"
  "tcb_cap_cases (tcb_cnode_index 3) =
   Some (tcb_caller, tcb_caller_update,
         (\<lambda>_ st. case st of
                   Structures_A.BlockedOnReceive e d \<Rightarrow> (op = cap.NullCap)
                 | _ \<Rightarrow> is_reply_cap or (op = cap.NullCap)))"
  "tcb_cap_cases (tcb_cnode_index 4) =
   Some (tcb_ipcframe, tcb_ipcframe_update,
         (\<lambda>_ _. is_arch_cap or (op = cap.NullCap)))"
  by (simp add: tcb_cap_cases_def)+

lemma ran_tcb_cap_cases:
  "ran (tcb_cap_cases) =
    {(tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>)),
     (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. \<top>)),
     (tcb_reply, tcb_reply_update, (\<lambda>t st c.
                                       (is_master_reply_cap c \<and> obj_ref_of c = t)
                                     \<or> (halted st \<and> (c = cap.NullCap)))),
     (tcb_caller, tcb_caller_update, (\<lambda>_ st. case st of
                                       Structures_A.BlockedOnReceive e d \<Rightarrow>
                                         (op = cap.NullCap)
                                     | _ \<Rightarrow> is_reply_cap or (op = cap.NullCap))),
     (tcb_ipcframe, tcb_ipcframe_update, (\<lambda>_ _. is_arch_cap or (op = cap.NullCap)))}"
  by (simp add: tcb_cap_cases_def ran_map_upd
                insert_commute)

lemma tcb_cnode_map_tcb_cap_cases:
  "tcb_cnode_map tcb = (\<lambda>bl. map_option (\<lambda>x. fst x tcb) (tcb_cap_cases bl))"
  by (rule ext) (simp add: tcb_cnode_map_def tcb_cap_cases_def)

lemma ran_tcb_cnode_map:
  "ran (tcb_cnode_map t) =
   {tcb_vtable t, tcb_ctable t, tcb_caller t, tcb_reply t, tcb_ipcframe t}"
  by (fastforce simp: tcb_cnode_map_def)

lemma st_tcb_idle_cap_valid_Null [simp]:
  "st_tcb_at (idle or inactive) (fst sl) s \<longrightarrow>
   tcb_cap_valid cap.NullCap sl s"
  by (fastforce simp: tcb_cap_valid_def tcb_cap_cases_def
                     pred_tcb_at_def obj_at_def
                     valid_ipc_buffer_cap_def)

lemmas
  wellformed_pte_simps[simp] =
  wellformed_pte_def[split_simps ARM_Structs_A.pte.split]

lemmas
  wellformed_pde_simps[simp] =
  wellformed_pde_def[split_simps ARM_Structs_A.pde.split]

lemmas
  wellformed_arch_obj_simps[simp] =
  wellformed_arch_obj_def[split_simps arch_kernel_obj.split]
 
lemma valid_objsI [intro]:
  "(\<And>obj x. kheap s x = Some obj \<Longrightarrow> valid_obj x obj s) \<Longrightarrow> valid_objs s"
  unfolding valid_objs_def by auto

lemma valid_objsE [elim]:
  "\<lbrakk> valid_objs s; kheap s x = Some obj; valid_obj x obj s \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding valid_objs_def by (auto simp: dom_def)

lemmas vs_ref_atype_simps[simp] = vs_ref_atype_def[split_simps vs_ref.split]

lemma vs_lookup1_obj_at:
  "((rs,p) \<rhd>1 (r # rs,p')) s = obj_at (\<lambda>ko. (r, p') \<in> vs_refs ko) p s"
  by (fastforce simp: vs_lookup1_def obj_at_def)

lemma vs_lookup1I:
  "\<lbrakk> ko_at ko p s; (r, p') \<in> vs_refs ko;
          rs' = r # rs \<rbrakk> \<Longrightarrow> ((rs,p) \<rhd>1 (rs',p')) s"
  by (fastforce simp add: vs_lookup1_def)

lemma vs_lookup1D:
  "(x \<rhd>1 y) s \<Longrightarrow> \<exists>rs r p p' ko. x = (rs,p) \<and> y = (r # rs,p')
                          \<and> ko_at ko p s \<and> (r,p') \<in> vs_refs ko"
  by (cases x, cases y) (fastforce simp: vs_lookup1_def)

lemma vs_lookup_pages1D:
  "(x \<unrhd>1 y) s \<Longrightarrow> \<exists>rs r p p' ko. x = (rs,p) \<and> y = (r # rs,p')
                          \<and> ko_at ko p s \<and> (r,p') \<in> vs_refs_pages ko"
  by (cases x, cases y) (fastforce simp: vs_lookup_pages1_def)

lemma obj_at_ko_at:
  "obj_at P p s \<Longrightarrow> \<exists>ko. ko_at ko p s \<and> P ko"
  by (auto simp add: obj_at_def)

lemma vs_lookup1_stateI:
  assumes 1: "(r \<rhd>1 r') s"
  assumes ko: "\<And>ko. ko_at ko (snd r) s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') (snd r) s'"
  shows "(r \<rhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup1_def)

lemma vs_lookup_trans_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  shows "vs_lookup_trans s \<subseteq> vs_lookup_trans s'"
proof -
  have "vs_lookup1 s \<subseteq> vs_lookup1 s'"
    by (fastforce dest: ko elim: vs_lookup1_stateI)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup s \<subseteq> vs_lookup s'"
  unfolding vs_lookup_def
  apply (rule Image_mono)
   apply (rule vs_lookup_trans_sub)
   apply (erule ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done

lemma vs_lookup_pages1_stateI:
  assumes 1: "(r \<unrhd>1 r') s"
  assumes ko: "\<And>ko. ko_at ko (snd r) s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') (snd r) s'"
  shows "(r \<unrhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup_pages1_def)

lemma vs_lookup_pages_trans_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow>
                      obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  shows "vs_lookup_pages_trans s \<subseteq> vs_lookup_pages_trans s'"
proof -
  have "vs_lookup_pages1 s \<subseteq> vs_lookup_pages1 s'"
    by (fastforce simp add: ko elim: vs_lookup_pages1_stateI)
  thus ?thesis by (rule rtrancl_mono)
qed

lemma vs_lookup_pages_sub:
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow>
                      obj_at (\<lambda>ko'. vs_refs_pages ko \<subseteq> vs_refs_pages ko') p s'"
  assumes table:
    "graph_of (arm_asid_table (arch_state s)) \<subseteq>
     graph_of (arm_asid_table (arch_state s'))"
  shows "vs_lookup_pages s \<subseteq> vs_lookup_pages s'"
  unfolding vs_lookup_pages_def
  apply (rule Image_mono)
   apply (rule vs_lookup_pages_trans_sub)
   apply (erule ko)
  apply (unfold vs_asid_refs_def)
  apply (rule image_mono)
  apply (rule table)
  done

lemma vs_lookup_pagesI:
  "\<lbrakk> ref' \<in> vs_asid_refs (arm_asid_table (arch_state s));
     (ref',(ref,p)) \<in> (vs_lookup_pages1 s)^*  \<rbrakk> \<Longrightarrow>
  (ref \<unrhd> p) s"
  by (simp add: vs_lookup_pages_def) blast

lemma vs_lookup_stateI:
  assumes 1: "(ref \<rhd> p) s"
  assumes ko: "\<And>ko p. ko_at ko p s \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s'"
  assumes table: "graph_of (arm_asid_table (arch_state s)) \<subseteq> graph_of (arm_asid_table (arch_state s'))"
  shows "(ref \<rhd> p) s'"
  using 1 vs_lookup_sub [OF ko table] by blast

lemma valid_arch_objsD:
  "\<lbrakk> (ref \<rhd> p) s; ko_at (ArchObj ao) p s; valid_arch_objs s \<rbrakk> \<Longrightarrow> valid_arch_obj ao s"
  by (fastforce simp add: valid_arch_objs_def)

(* should work for unmap and non-arch ops *)
lemma valid_arch_objs_stateI:
  assumes 1: "valid_arch_objs s"
  assumes ko: "\<And>ko p. ko_at ko p s' \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s"
  assumes arch: "graph_of (arm_asid_table (arch_state s')) \<subseteq> graph_of (arm_asid_table (arch_state s))"
  assumes vao: "\<And>p ref ao'.
                \<lbrakk> (ref \<rhd> p) s; (ref \<rhd> p) s'; \<forall>ao. ko_at (ArchObj ao) p s \<longrightarrow> valid_arch_obj ao s;
                  ko_at (ArchObj ao') p s' \<rbrakk> \<Longrightarrow> valid_arch_obj ao' s'"
  shows "valid_arch_objs s'"
  using 1 unfolding valid_arch_objs_def
  apply clarsimp
  apply (frule vs_lookup_stateI)
    apply (erule ko)
   apply (rule arch)
  apply (erule allE, erule impE, fastforce)
  apply (erule (3) vao)
  done

lemma asid_pool_at_ko:
  "asid_pool_at p s \<Longrightarrow> \<exists>pool. ko_at (ArchObj (ARM_Structs_A.ASIDPool pool)) p s"
  apply (clarsimp simp: obj_at_def a_type_def)
  apply (case_tac ko, simp_all split: split_if_asm)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, auto)
  done

lemma typ_at_pg:
  "typ_at (AArch (AIntData sz)) buf s = ko_at (ArchObj (DataPage sz)) buf s"
  unfolding obj_at_def
  by (auto simp: a_type_def split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm split_if_asm)

lemma symreftype_inverse[simp]:
  "symreftype (symreftype t) = t"
  by (cases t, simp+)

lemma tcb_st_refs_of_simps[simp]:
 "tcb_st_refs_of (Structures_A.Running)               = {}"
 "tcb_st_refs_of (Structures_A.Inactive)              = {}"
 "tcb_st_refs_of (Structures_A.Restart)               = {}"
 "tcb_st_refs_of (Structures_A.BlockedOnReply)        = {}"
 "tcb_st_refs_of (Structures_A.IdleThreadState)       = {}"
 "\<And>x. tcb_st_refs_of (Structures_A.BlockedOnReceive x b)  = {(x, TCBBlockedRecv)}"
 "\<And>x. tcb_st_refs_of (Structures_A.BlockedOnSend x payl)  = {(x, TCBBlockedSend)}"
 "\<And>x. tcb_st_refs_of (Structures_A.BlockedOnNotification x) = {(x, TCBSignal)}"
  by (auto simp: tcb_st_refs_of_def)

lemma ep_q_refs_of_simps[simp]:
 "ep_q_refs_of  Structures_A.IdleEP    = {}"
 "\<And>q. ep_q_refs_of (Structures_A.RecvEP q) = set q \<times> {EPRecv}"
 "\<And>q. ep_q_refs_of (Structures_A.SendEP q) = set q \<times> {EPSend}"
  by (auto simp: ep_q_refs_of_def)

lemma ntfn_q_refs_of_simps[simp]:
 "ntfn_q_refs_of Structures_A.IdleNtfn        = {}"
 "ntfn_q_refs_of (Structures_A.WaitingNtfn q)   = set q \<times> {NTFNSignal}"
 "ntfn_q_refs_of (Structures_A.ActiveNtfn b)  = {}"
  by (auto simp: ntfn_q_refs_of_def)

lemma ntfn_bound_refs_simps[simp]:
  "ntfn_bound_refs (Some t) = {(t, NTFNBound)}"
  "ntfn_bound_refs None = {}"
  by (auto simp: ntfn_bound_refs_def)

lemma tcb_bound_refs_simps[simp]:
  "tcb_bound_refs (Some a) = {(a, TCBBound)}"
  "tcb_bound_refs None = {}"
  by (auto simp: tcb_bound_refs_def)

lemma tcb_bound_refs_def2:
  "tcb_bound_refs a = set_option a \<times> {TCBBound}"
by (simp add: tcb_bound_refs_def split: option.splits)

lemma refs_of_simps[simp]:
 "refs_of (CNode sz cs)       = {}"
 "refs_of (TCB tcb)           = tcb_st_refs_of (tcb_state tcb) \<union> tcb_bound_refs (tcb_bound_notification tcb)"
 "refs_of (Endpoint ep)       = ep_q_refs_of ep"
 "refs_of (Notification ntfn) = ntfn_q_refs_of (ntfn_obj ntfn) \<union> ntfn_bound_refs (ntfn_bound_tcb ntfn)"
 "refs_of (ArchObj ao)        = {}"
  by (auto simp: refs_of_def)


lemma refs_of_rev:
 "(x, TCBBlockedRecv) \<in> refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (\<exists>b.  tcb_state tcb = Structures_A.BlockedOnReceive x b))"
 "(x, TCBBlockedSend) \<in> refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (\<exists>pl. tcb_state tcb = Structures_A.BlockedOnSend    x pl))"
 "(x, TCBSignal) \<in> refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_state tcb = Structures_A.BlockedOnNotification x))"
 "(x, EPRecv) \<in> refs_of ko =
    (\<exists>ep. ko = Endpoint ep \<and> (\<exists>q. ep = Structures_A.RecvEP q \<and> x \<in> set q))"
 "(x, EPSend) \<in> refs_of ko =
    (\<exists>ep. ko = Endpoint ep \<and> (\<exists>q. ep = Structures_A.SendEP q \<and> x \<in> set q))"
 "(x, NTFNSignal) \<in> refs_of ko =
    (\<exists>ntfn. ko = Notification ntfn \<and> (\<exists>q. ntfn_obj ntfn = Structures_A.WaitingNtfn q \<and> x \<in> set q))"
 "(x, TCBBound) \<in>  refs_of ko =
    (\<exists>tcb. ko = TCB tcb \<and> (tcb_bound_notification tcb = Some x))"
 "(x, NTFNBound) \<in> refs_of ko =
    (\<exists>ntfn. ko = Notification ntfn \<and> (ntfn_bound_tcb ntfn = Some x))"
  by (auto simp:  refs_of_def
                     tcb_st_refs_of_def
                     ep_q_refs_of_def
                     ntfn_q_refs_of_def
                     ntfn_bound_refs_def
                     tcb_bound_refs_def
              split: Structures_A.kernel_object.splits
                     Structures_A.thread_state.splits
                     Structures_A.endpoint.splits
                     Structures_A.ntfn.splits
                     option.split)

lemma st_tcb_at_refs_of_rev:
  "obj_at (\<lambda>ko. (x, TCBBlockedRecv) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts. \<exists>b.  ts = Structures_A.BlockedOnReceive x b ) t s"
  "obj_at (\<lambda>ko. (x, TCBBlockedSend) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts. \<exists>pl. ts = Structures_A.BlockedOnSend x pl   ) t s"
  "obj_at (\<lambda>ko. (x, TCBSignal) \<in> refs_of ko) t s
     = st_tcb_at (\<lambda>ts.      ts = Structures_A.BlockedOnNotification x) t s"
  by (simp add: refs_of_rev pred_tcb_at_def)+

lemma state_refs_of_elemD:
  "\<lbrakk> ref \<in> state_refs_of s x \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. ref \<in> refs_of obj) x s"
  by (clarsimp simp add: state_refs_of_def obj_at_def
                  split: option.splits)

lemma state_refs_of_eqD:
  "\<lbrakk> state_refs_of s x = S; S \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>obj. refs_of obj = S) x s"
  by (clarsimp simp add: state_refs_of_def obj_at_def
                  split: option.splits)

lemma sym_refsD:
  "\<lbrakk> (y, tp) \<in> st x; sym_refs st \<rbrakk> \<Longrightarrow> (x, symreftype tp) \<in> st y"
  apply (simp add: sym_refs_def)
  apply (drule spec, drule(1) bspec)
  apply simp
  done

lemma sym_refsE:
  "\<lbrakk> sym_refs st; (y, symreftype tp) \<in> st x \<rbrakk> \<Longrightarrow> (x, tp) \<in> st y"
  by (drule(1) sym_refsD, simp)

lemma obj_at_state_refs_ofD:
  "obj_at P p s \<Longrightarrow> \<exists>ko. P ko \<and> state_refs_of s p = refs_of ko"
  apply (clarsimp simp: obj_at_def state_refs_of_def)
  apply fastforce
  done

lemma ko_at_state_refs_ofD:
  "ko_at ko p s \<Longrightarrow> state_refs_of s p = refs_of ko"
  by (clarsimp dest!: obj_at_state_refs_ofD)

definition
  "tcb_ntfn_is_bound ntfn ko = (case ko of TCB tcb \<Rightarrow> tcb_bound_notification tcb = ntfn | _ \<Rightarrow> False)"

lemma st_tcb_at_state_refs_ofD:
  "st_tcb_at P t s \<Longrightarrow> \<exists>ts ntfnptr. P ts \<and> obj_at (tcb_ntfn_is_bound ntfnptr) t s
          \<and> state_refs_of s t = (tcb_st_refs_of ts \<union> tcb_bound_refs ntfnptr)"
  by (auto simp: pred_tcb_at_def obj_at_def tcb_ntfn_is_bound_def
                 state_refs_of_def)

lemma bound_tcb_at_state_refs_ofD:
  "bound_tcb_at P t s \<Longrightarrow> \<exists>ts ntfnptr. P ntfnptr \<and> obj_at (tcb_ntfn_is_bound ntfnptr) t s
          \<and> state_refs_of s t = (tcb_st_refs_of ts \<union> tcb_bound_refs ntfnptr)"
  by (auto simp: pred_tcb_at_def obj_at_def tcb_ntfn_is_bound_def
                 state_refs_of_def)

lemma sym_refs_obj_atD:
  "\<lbrakk> obj_at P p s; sym_refs (state_refs_of s) \<rbrakk> \<Longrightarrow>
     \<exists>ko. P ko \<and> state_refs_of s p = refs_of ko \<and>
        (\<forall>(x, tp)\<in>refs_of ko. obj_at (\<lambda>ko. (p, symreftype tp) \<in> refs_of ko) x s)"
  apply (drule obj_at_state_refs_ofD)
  apply (erule exEI, clarsimp)
  apply (drule sym, simp)
  apply (drule(1) sym_refsD)
  apply (erule state_refs_of_elemD)
  done

lemma sym_refs_ko_atD:
  "\<lbrakk> ko_at ko p s; sym_refs (state_refs_of s) \<rbrakk> \<Longrightarrow>
     state_refs_of s p = refs_of ko \<and>
     (\<forall>(x, tp)\<in>refs_of ko.  obj_at (\<lambda>ko. (p, symreftype tp) \<in> refs_of ko) x s)"
  by (drule(1) sym_refs_obj_atD, simp)

lemma sym_refs_st_tcb_atD:
  "\<lbrakk> st_tcb_at P t s; sym_refs (state_refs_of s) \<rbrakk> \<Longrightarrow>
     \<exists>ts ntfn. P ts \<and> obj_at (tcb_ntfn_is_bound ntfn) t s 
        \<and> state_refs_of s t = tcb_st_refs_of ts \<union> tcb_bound_refs ntfn
        \<and> (\<forall>(x, tp)\<in>tcb_st_refs_of ts \<union> tcb_bound_refs ntfn. obj_at (\<lambda>ko. (t, symreftype tp) \<in> refs_of ko) x s)"
  apply (drule st_tcb_at_state_refs_ofD)
  apply (erule exE)+
  apply (rule_tac x=ts in exI)
  apply (rule_tac x=ntfnptr in exI)
  apply clarsimp
  apply (frule obj_at_state_refs_ofD)
  apply (drule (1)sym_refs_obj_atD)
  apply auto
  done 

lemma sym_refs_simp:
  "\<lbrakk> sym_refs S \<rbrakk> \<Longrightarrow> ((y, symreftype tp) \<in> S x) = ((x, tp) \<in> S y)"
  apply safe
   apply (erule(1) sym_refsE)
  apply (erule(1) sym_refsD)
  done

lemma delta_sym_refs:
  assumes x: "sym_refs rfs'"
      and y: "\<And>x y tp. \<lbrakk> (y, tp) \<in> rfs x; (y, tp) \<notin> rfs' x \<rbrakk> \<Longrightarrow> (x, symreftype tp) \<in> rfs y"
      and z: "\<And>x y tp. \<lbrakk> (y, tp) \<in> rfs' x; (y, tp) \<notin> rfs x \<rbrakk> \<Longrightarrow> (x, symreftype tp) \<notin> rfs y"
  shows      "sym_refs rfs"
  unfolding sym_refs_def
  apply clarsimp
  apply (case_tac "(a, b) \<in> rfs' x")
   apply (drule sym_refsD [OF _ x])
   apply (rule ccontr)
   apply (frule(1) z)
   apply simp
  apply (erule(1) y)
  done

lemma pspace_alignedE [elim]:
  "\<lbrakk> pspace_aligned s;
   x \<in> dom (kheap s); is_aligned x (obj_bits (the (kheap s x))) \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding pspace_aligned_def by auto

lemma ex_nonz_cap_toE:
  "\<lbrakk> ex_nonz_cap_to p s; \<And>cref. cte_wp_at (\<lambda>c. p \<in> zobj_refs c) cref s \<Longrightarrow> Q \<rbrakk>
    \<Longrightarrow> Q"
  by (fastforce simp: ex_nonz_cap_to_def)

lemma refs_of_live:
  "refs_of ko \<noteq> {} \<Longrightarrow> live ko"
  apply (cases ko, simp_all)
    apply (rename_tac tcb_ext)
     apply (case_tac "tcb_state tcb_ext", simp_all)
    apply (fastforce simp: tcb_bound_refs_def)+
  apply (rename_tac notification)
  apply (case_tac "ntfn_obj notification", simp_all)
   apply (fastforce simp: ntfn_bound_refs_def)+
  done

lemma refs_of_live_obj:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> P ko; refs_of ko = {} \<rbrakk> \<Longrightarrow> False \<rbrakk> \<Longrightarrow> obj_at live p s"
  by (fastforce simp: obj_at_def intro!: refs_of_live)

lemma if_live_then_nonz_capD:
  assumes x: "if_live_then_nonz_cap s" "obj_at P p s"
  assumes y: "\<And>obj. \<lbrakk> P obj; kheap s p = Some obj \<rbrakk> \<Longrightarrow> live obj"
  shows "ex_nonz_cap_to p s" using x
  apply (clarsimp simp: if_live_then_nonz_cap_def)
  apply (erule allE[where x=p])
  apply (fastforce simp: obj_at_def dest!: y)
  done

lemma if_live_then_nonz_capD2:
  "\<lbrakk> if_live_then_nonz_cap s; kheap s p = Some obj;
     live obj \<rbrakk> \<Longrightarrow> ex_nonz_cap_to p s"
  apply (subgoal_tac "ko_at obj p s")
   apply (erule(1) if_live_then_nonz_capD)
   apply simp
  apply (simp add: obj_at_def)
  done

lemma caps_of_state_cte_wp_at:
 "caps_of_state s = (\<lambda>p. if (\<exists>cap. cte_wp_at (op = cap) p s)
                         then Some (THE cap. cte_wp_at (op = cap) p s)
                         else None)"
  by (clarsimp simp: cte_wp_at_def caps_of_state_def intro!: ext)

lemma cte_wp_at_caps_of_state:
 "cte_wp_at P p s = (\<exists>cap. caps_of_state s p = Some cap \<and> P cap)"
  by (clarsimp simp add: cte_wp_at_def caps_of_state_def)

lemmas ex_cte_cap_to_def =
  ex_cte_cap_wp_to_def[where P="\<top>", simplified simp_thms]

lemma ex_cte_cap_wp_to_weakenE:
  "\<lbrakk> ex_cte_cap_wp_to P p s;
      \<And>cte_cap. \<lbrakk> P cte_cap; p \<in> cte_refs cte_cap (interrupt_irq_node s) \<rbrakk> \<Longrightarrow> Q cte_cap \<rbrakk>
       \<Longrightarrow> ex_cte_cap_wp_to Q p s"
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (elim exEI)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma if_unsafe_then_capD:
  "\<lbrakk> cte_wp_at P p s; if_unsafe_then_cap s; \<And>cap. P cap \<Longrightarrow> cap \<noteq> cap.NullCap \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to (\<lambda>cap. \<exists>cap'. P cap' \<and> appropriate_cte_cap cap' cap) p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (unfold if_unsafe_then_cap_def)
  apply (elim allE, drule(1) mp)
  apply (auto elim!: ex_cte_cap_wp_to_weakenE)
  done

lemma zombies_finalD:
  "\<lbrakk> cte_wp_at P p s; zombies_final s; \<And>cap. P cap \<Longrightarrow> is_zombie cap \<rbrakk>
     \<Longrightarrow> cte_wp_at (\<lambda>cap. is_final_cap' cap s) p s"
  unfolding zombies_final_def
  apply (drule spec, erule mp)
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma physical_valid_cap_not_empty_range:
  "\<lbrakk>valid_cap cap s; cap_class cap = PhysicalClass\<rbrakk> \<Longrightarrow> cap_range cap \<noteq> {}"
  apply (case_tac cap)
   apply (simp_all add:cap_range_def valid_cap_simps cap_aligned_def is_aligned_no_overflow)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap,simp_all)
  done

lemma valid_ioc_def2:
  "valid_ioc s \<equiv>
   \<forall>p. is_original_cap s p \<longrightarrow> null_filter (caps_of_state s) p \<noteq> None"
  apply (rule eq_reflection)
  apply (clarsimp simp add: valid_ioc_def)
  apply (intro iff_allI weak_imp_cong refl)
  apply (clarsimp simp: null_filter_def cte_wp_at_caps_of_state)
  apply fastforce
  done

lemma valid_reply_capsD:
  "\<lbrakk> has_reply_cap t s; valid_reply_caps s \<rbrakk>
    \<Longrightarrow> st_tcb_at awaiting_reply t s"
  unfolding valid_reply_caps_def
  by simp

lemma reply_master_caps_of_stateD:
  "\<And>sl. \<lbrakk> valid_reply_masters s; caps_of_state s sl = Some (cap.ReplyCap t True)\<rbrakk>
   \<Longrightarrow> sl = (t, tcb_cnode_index 2)"
  by (simp add: valid_reply_masters_def cte_wp_at_caps_of_state
           del: split_paired_All)

lemma has_reply_cap_cte_wpD:
  "\<And>t sl. cte_wp_at (op = (cap.ReplyCap t False)) sl s \<Longrightarrow> has_reply_cap t s"
  by (fastforce simp: has_reply_cap_def)

lemma reply_cap_doesnt_exist_strg:
  "(valid_reply_caps s \<and> st_tcb_at (Not \<circ> awaiting_reply) t s)
      \<longrightarrow> \<not> has_reply_cap t s"
  by (clarsimp dest!: valid_reply_capsD
                simp: st_tcb_def2)

lemma mdb_cte_atD:
  "\<lbrakk> m c = Some p; mdb_cte_at ct_at m \<rbrakk>
     \<Longrightarrow> ct_at p \<and> ct_at c"
  by (simp add: mdb_cte_at_def)

lemma zobj_refs_to_obj_refs:
  "(x \<in> zobj_refs cap) = (x \<in> obj_refs cap \<and> \<not> is_zombie cap)"
  by (cases cap, simp_all add: is_zombie_def)

lemma idle_no_refs:
  "valid_idle s \<Longrightarrow> state_refs_of s (idle_thread s) = {}"
  apply (clarsimp simp: valid_idle_def)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def tcb_ntfn_is_bound_def state_refs_of_def)
  done

lemma idle_not_queued:
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s);
   state_refs_of s ptr = queue \<times> {rt}\<rbrakk> \<Longrightarrow>
   idle_thread s \<notin> queue"
  by (frule idle_no_refs, fastforce simp: valid_idle_def sym_refs_def)

lemma idle_not_queued':
  "\<lbrakk>valid_idle s; sym_refs (state_refs_of s);
   state_refs_of s ptr = insert t queue \<times> {rt}\<rbrakk> \<Longrightarrow>
   idle_thread s \<notin> queue"
  by (frule idle_no_refs, fastforce simp: valid_idle_def sym_refs_def)

lemma mdb_cte_atI:
  "\<lbrakk> \<And>c p. m c = Some p \<Longrightarrow> ct_at p \<and> ct_at c \<rbrakk>
     \<Longrightarrow> mdb_cte_at ct_at m"
  by (simp add: mdb_cte_at_def)

lemma only_idleD:
  "\<lbrakk> st_tcb_at idle t s; only_idle s \<rbrakk> \<Longrightarrow> t = idle_thread s"
  by (simp add: only_idle_def)

lemma only_idleI:
  "(\<And>t. st_tcb_at idle t s \<Longrightarrow> t = idle_thread s) \<Longrightarrow> only_idle s"
  by (simp add: only_idle_def)

lemmas cap_asid_simps [simp] =
  cap_asid_def [split_simps cap.split arch_cap.split option.split prod.split]

text {*
  A pointer is inside a user frame if its top bits point to any object
  of type @{text IntData}.
*}
lemma in_user_frame_def:
  "in_user_frame p \<equiv> \<lambda>s.
   \<exists>sz. typ_at (AArch (AIntData sz)) (p && ~~ mask (pageBitsForSize sz)) s"
  apply (rule eq_reflection, rule ext)
  apply (simp add: in_user_frame_def obj_at_def)
  apply (rule_tac f=Ex in arg_cong)
  apply (rule ext, rule iffI)
   apply (simp add: a_type_simps)
  apply clarsimp
  apply (case_tac ko, simp_all add: a_type_simps split: split_if_asm)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all add: a_type_simps)
  done

lemma obj_at_weakenE:
  "\<lbrakk> obj_at P r s; \<And>ko. P ko \<Longrightarrow> P' ko \<rbrakk> \<Longrightarrow> obj_at P' r s"
  by (clarsimp simp: obj_at_def)

lemma idle_global[intro!]:
  "idle_thread s \<in> global_refs s"
  by (simp add: global_refs_def)

lemma valid_refs_def2:
  "valid_refs R = (\<lambda>s. \<forall>c \<in> ran (caps_of_state s). R \<inter> cap_range c = {})"
  apply (simp add: valid_refs_def cte_wp_at_caps_of_state ran_def)
  apply (rule ext, fastforce)
  done

lemma idle_no_ex_cap:
  "\<lbrakk>valid_global_refs s; valid_objs s\<rbrakk> \<Longrightarrow>
   \<not> ex_nonz_cap_to (idle_thread s) s"
  apply (simp add: ex_nonz_cap_to_def valid_global_refs_def valid_refs_def2 cte_wp_at_caps_of_state
              del: split_paired_Ex split_paired_All)
  apply (intro allI notI impI)
  apply (drule bspec, blast intro: ranI)
  apply (clarsimp simp: cap_range_def zobj_refs_to_obj_refs)
  apply (blast intro: idle_global)
  done

lemma caps_of_state_cteD:
  "caps_of_state s p = Some cap \<Longrightarrow> cte_wp_at (op = cap) p s"
  by (simp add: cte_wp_at_caps_of_state)

lemma untyped_mdb_alt:
  "untyped_mdb (cdt s) (caps_of_state s) = untyped_children_in_mdb s"
  apply (simp add: untyped_children_in_mdb_def untyped_mdb_def cte_wp_at_caps_of_state)
  apply fastforce
  done

lemma untyped_children_in_mdbE:
  assumes x: "untyped_children_in_mdb s" "cte_wp_at (op = cap) ptr s"
             "is_untyped_cap cap" "cte_wp_at P ptr' s"
  assumes y: "\<And>cap'. \<lbrakk> cte_wp_at (op = cap') ptr' s; P cap' \<rbrakk> \<Longrightarrow>
                 obj_refs cap' \<inter> untyped_range cap \<noteq> {}"
  assumes z: "ptr' \<in> descendants_of ptr (cdt s) \<Longrightarrow> Q"
  shows Q using x
  apply (clarsimp simp: untyped_children_in_mdb_def
                  simp del: split_paired_All split_paired_Ex)
  apply (erule allE[where x=ptr], erule allE[where x=ptr'], erule impE)
   apply (rule exI, (erule conjI)+)
   apply (clarsimp simp: cte_wp_at_def y)
  apply (erule z)
  done

lemma obj_at_pspaceI:
  "\<lbrakk> obj_at P ref s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> obj_at P ref s'"
  by (simp add: obj_at_def)

lemma cte_wp_at_cases:
  "cte_wp_at P t s = ((\<exists>sz fun cap. kheap s (fst t) = Some (CNode sz fun) \<and>
                                    well_formed_cnode_n sz fun \<and>
                                    fun (snd t) = Some cap \<and> P cap) \<or>
                      (\<exists>tcb get set restr. kheap s (fst t) = Some (TCB tcb) \<and>
                             tcb_cap_cases (snd t) = Some (get, set, restr) \<and>
                             P (get tcb)))"
  apply (cases t)
  apply (cases "kheap s (fst t)")
   apply (simp add: cte_wp_at_def get_cap_def
                    get_object_def gets_def get_def return_def assert_def
                    fail_def bind_def)
  apply (simp add: cte_wp_at_def get_cap_def tcb_cnode_map_def bind_def
                   get_object_def assert_opt_def return_def gets_def get_def
                   assert_def fail_def dom_def
              split: split_if_asm Structures_A.kernel_object.splits
                     option.splits)
  apply (simp add: tcb_cap_cases_def)
  done

lemma cte_wp_at_cases2:
  "cte_wp_at P t s =
   ((\<exists>sz fun cap. kheap s (fst t) = Some (CNode sz fun) \<and>
                  well_formed_cnode_n sz fun \<and> fun (snd t) = Some cap \<and> P cap) \<or>
    (\<exists>tcb cap. kheap s (fst t) = Some (TCB tcb) \<and>
               (tcb_cnode_map tcb (snd t) = Some cap \<and> P cap)))"
  by (auto simp add: cte_wp_at_cases tcb_cap_cases_def tcb_cnode_map_def)

lemma cte_wp_at_pspaceI:
  "\<lbrakk> cte_wp_at P slot s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> cte_wp_at P slot s'"
  by (simp add: cte_wp_at_cases)

lemma valid_cap_pspaceI:
  "\<lbrakk> s \<turnstile> cap; kheap s = kheap s' \<rbrakk> \<Longrightarrow> s' \<turnstile> cap"
  unfolding valid_cap_def
  by (cases cap)
     (auto intro: obj_at_pspaceI cte_wp_at_pspaceI
           simp: obj_range_def valid_untyped_def pred_tcb_at_def
          split: arch_cap.split option.split sum.split)

lemma valid_arch_obj_pspaceI:
  "\<lbrakk> valid_arch_obj obj s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_arch_obj obj s'"
  apply (cases obj, simp_all)
    apply (simp add: obj_at_def)
   apply (erule allEI)
   apply (rename_tac "fun" x)
   apply (case_tac "fun x", simp_all add: obj_at_def)
  apply (erule ballEI)
  apply (rename_tac "fun" x)
  apply (case_tac "fun x", simp_all add: obj_at_def)
  done

(* FIXME-NTFN: ugly proof *)
lemma valid_obj_pspaceI:
  "\<lbrakk> valid_obj ptr obj s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_obj ptr obj s'"
  unfolding valid_obj_def
  apply (cases obj)
      apply (auto simp add: valid_ntfn_def valid_cs_def valid_tcb_def valid_ep_def 
                           valid_tcb_state_def pred_tcb_at_def valid_bound_ntfn_def valid_bound_tcb_def
                 intro: obj_at_pspaceI valid_cap_pspaceI valid_arch_obj_pspaceI
                 split: Structures_A.ntfn.splits Structures_A.endpoint.splits
                        Structures_A.thread_state.splits option.split
          | auto split: kernel_object.split)+
  done

lemma valid_objs_pspaceI:
  "\<lbrakk> valid_objs s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_objs s'"
  unfolding valid_objs_def
  by (auto intro: valid_obj_pspaceI dest!: bspec [OF _ domI])

lemma state_refs_of_pspaceI:
  "\<lbrakk> P (state_refs_of s); kheap s = kheap s' \<rbrakk> \<Longrightarrow> P (state_refs_of s')"
  unfolding state_refs_of_def
  by simp

lemma distinct_pspaceI:
  "pspace_distinct s \<Longrightarrow> kheap s = kheap s' \<Longrightarrow> pspace_distinct s'"
  by (simp add: pspace_distinct_def)

lemma iflive_pspaceI:
  "if_live_then_nonz_cap s \<Longrightarrow> kheap s = kheap s' \<Longrightarrow> if_live_then_nonz_cap s'"
  unfolding if_live_then_nonz_cap_def ex_nonz_cap_to_def
  by (fastforce simp: obj_at_def intro: cte_wp_at_pspaceI)

lemma cte_wp_at_pspace:
  "kheap s = kheap s' \<Longrightarrow> cte_wp_at P p s = cte_wp_at P p s'"
  by (fastforce elim!: cte_wp_at_pspaceI)

lemma caps_of_state_pspace:
  assumes x: "kheap s = kheap s'"
  shows      "caps_of_state s = caps_of_state s'"
  by (simp add: caps_of_state_cte_wp_at cte_wp_at_pspace [OF x] cong: if_cong)

lemma ifunsafe_pspaceI:
  "if_unsafe_then_cap s \<Longrightarrow> kheap s = kheap s' \<Longrightarrow> interrupt_irq_node s = interrupt_irq_node s'
       \<Longrightarrow> if_unsafe_then_cap s'"
  unfolding if_unsafe_then_cap_def ex_cte_cap_wp_to_def
  apply (frule caps_of_state_pspace)
  by (auto simp: cte_wp_at_cases)

lemma valid_idle_pspaceI:
  "valid_idle s \<Longrightarrow> \<lbrakk>kheap s = kheap s'; idle_thread s = idle_thread s'\<rbrakk> \<Longrightarrow> valid_idle s'"
  unfolding valid_idle_def pred_tcb_at_def
  by (fastforce elim!: obj_at_pspaceI cte_wp_at_pspaceI)

lemma obj_irq_refs_Int:
  "(obj_irq_refs cap \<inter> obj_irq_refs cap' = {})
     = (obj_refs cap \<inter> obj_refs cap' = {}
            \<and> cap_irqs cap \<inter> cap_irqs cap' = {})"
  by (simp add: obj_irq_refs_def Int_Un_distrib Int_Un_distrib2
                image_Int[symmetric] Int_image_empty)

lemma is_final_cap'_def2:
  "is_final_cap' cap =
    (\<lambda>s. \<exists>cref. \<forall>cref'. cte_wp_at (\<lambda>c. obj_irq_refs cap \<inter> obj_irq_refs c \<noteq> {}) cref' s
                  = (cref' = cref))"
  unfolding obj_irq_refs_Int
  apply (rule ext)
  apply (auto simp: is_final_cap'_def cte_wp_at_def
                    set_eq_iff)
  done

lemma zombies_final_pspaceI:
  assumes x: "zombies_final s"
      and y: "kheap s = kheap s'"
  shows      "zombies_final s'"
  using x unfolding zombies_final_def is_final_cap'_def2
  by (simp only: cte_wp_at_pspace [OF y])

lemma pspace_pspace_update:
  "kheap (kheap_update (\<lambda>a. ps) s) = ps" by simp

lemma valid_pspace_eqI:
  "\<lbrakk> valid_pspace s; kheap s = kheap s' \<rbrakk> \<Longrightarrow> valid_pspace s'"
  unfolding valid_pspace_def
  by (auto simp: pspace_aligned_def
           intro: valid_objs_pspaceI state_refs_of_pspaceI
                  distinct_pspaceI iflive_pspaceI
                  ifunsafe_pspaceI zombies_final_pspaceI)

lemma cte_wp_caps_of_lift:
  assumes c: "\<And>p P. cte_wp_at P p s = cte_wp_at P p s'"
  shows "caps_of_state s = caps_of_state s'"
  apply (rule ext)
  apply (case_tac "caps_of_state s' x")
   apply (rule classical)
   apply (clarsimp dest!: caps_of_state_cteD simp add: c)
   apply (simp add: cte_wp_at_caps_of_state)
  apply clarsimp
  apply (clarsimp dest!: caps_of_state_cteD simp add: c [symmetric])
  apply (simp add: cte_wp_at_caps_of_state)
  done

lemma valid_mdb_eqI:
  assumes "valid_mdb s"
  assumes c: "\<And>p P. cte_wp_at P p s = cte_wp_at P p s'"
  assumes "cdt s = cdt s'"
  assumes "is_original_cap s = is_original_cap s'"
  shows "valid_mdb s'" using assms
  apply (simp add: valid_mdb_def)
   apply (rule conjI)
   apply (force simp add: valid_mdb_def swp_def mdb_cte_at_def)
  apply (clarsimp simp add: cte_wp_caps_of_lift [OF c])
  done

declare word_neq_0_conv[simp del]

lemma set_object_at_obj:
  "\<lbrace> \<lambda>s. obj_at P p s \<and> (p = r \<longrightarrow> P obj) \<rbrace> set_object r obj \<lbrace> \<lambda>rv. obj_at P p \<rbrace>"
  by (clarsimp simp: valid_def in_monad obj_at_def set_object_def)

lemma set_object_at_obj1:
  "P obj \<Longrightarrow> \<lbrace> obj_at P p \<rbrace> set_object r obj \<lbrace> \<lambda>rv. obj_at P p \<rbrace>"
  by (clarsimp simp: valid_def in_monad obj_at_def set_object_def)

lemma set_object_at_obj2:
  "(\<And>ko. Q ko \<Longrightarrow> \<not>P ko) \<Longrightarrow>
  \<lbrace> obj_at P p and obj_at Q r \<rbrace> set_object r obj \<lbrace> \<lambda>rv. obj_at P p \<rbrace>"
  by (clarsimp simp: valid_def in_monad obj_at_def set_object_def)

lemma test:
  "\<lbrace> ep_at p and tcb_at r \<rbrace> set_object r obj \<lbrace> \<lambda>rv. ep_at p \<rbrace>"
  apply (rule set_object_at_obj2)
  apply (clarsimp simp: is_obj_defs)
  done

text {* Lemmas about well-formed states *}

lemma valid_pspaceI [intro]:
  "\<lbrakk> valid_objs s; pspace_aligned s; sym_refs (state_refs_of s);
     pspace_distinct s; if_live_then_nonz_cap s; zombies_final s \<rbrakk>
     \<Longrightarrow> valid_pspace s"
  unfolding valid_pspace_def by simp

lemma valid_pspaceE [elim?]:
  assumes vp: "valid_pspace s"
  and     rl: "\<lbrakk> valid_objs s; pspace_aligned s; sym_refs (state_refs_of s);
                 pspace_distinct s; if_live_then_nonz_cap s;
                 zombies_final s \<rbrakk> \<Longrightarrow> R"
  shows    R
  using vp
  unfolding valid_pspace_def by (auto intro: rl)

lemma valid_objs_valid_cs [dest?]:
  assumes vp: "valid_objs s"
  and    ran: "CNode sz ct \<in> ran (kheap s)"
  shows  "valid_cs sz ct s"
  using vp ran unfolding valid_objs_def
  by (auto simp: valid_obj_def ran_def dom_def)

lemma valid_pspace_valid_cs [dest?]:
  assumes vp: "valid_pspace s"
  and    ran: "CNode sz ct \<in> ran (kheap s)"
  shows  "valid_cs sz ct s"
  using vp
  by (rule valid_pspaceE)
     (simp add: valid_objs_valid_cs ran)

lemma valid_pspace_aligned:
  assumes vp: "valid_pspace s"
  and    lup: "kheap s addr = Some ko"
  shows  "is_aligned addr (obj_bits ko)"
  using vp
  apply (rule valid_pspaceE)
  apply (unfold pspace_aligned_def)
  apply (drule bspec [OF _ domI])
   apply (rule lup)
  apply (simp add: lup)
  done

lemma valid_pspace_valid_cs_size [intro?]:
  assumes ran: "CNode sz cs \<in> ran (kheap s)"
  and      vp: "valid_pspace s"
  shows  "valid_cs_size sz cs"
  using valid_pspace_valid_cs [OF vp ran]
  unfolding valid_cs_def ..

lemma valid_objs_valid_cs_size [intro?]:
  assumes ran: "CNode sz cs \<in> ran (kheap s)"
  and      vp: "valid_objs s"
  shows  "valid_cs_size sz cs"
  using valid_objs_valid_cs [OF vp ran]
  unfolding valid_cs_def ..

lemma valid_cs_size_objsI [intro?]:
  "\<lbrakk> valid_objs s; kheap s r = Some (CNode sz ps) \<rbrakk>
  \<Longrightarrow> valid_cs_size sz ps"
  by (drule ranI, erule valid_objs_valid_cs_size)

lemma valid_cs_sizeI [intro?]:
  "\<lbrakk> valid_pspace s; kheap s r = Some (CNode sz ps) \<rbrakk>
  \<Longrightarrow> valid_cs_size sz ps"
  by (drule ranI, erule valid_pspace_valid_cs_size)

lemma wf_cs_insert:
  "\<lbrakk> well_formed_cnode_n sz cs; cs ref \<noteq> None \<rbrakk> \<Longrightarrow> well_formed_cnode_n sz (cs (ref \<mapsto> val))"
  apply (clarsimp simp: well_formed_cnode_n_def)
  apply (subst insert_absorb, simp_all)
  apply (drule domI, fastforce)
  done

lemma obj_bits_CNode:
  "\<lbrakk> valid_cs_size sz ps; ps cref = Some cap \<rbrakk> \<Longrightarrow>
  obj_bits (CNode sz ps) = 4 + length cref"
  unfolding valid_cs_size_def
  by (auto simp: well_formed_cnode_n_def cte_level_bits_def)

lemma obj_bits_CNode':
  "\<lbrakk> valid_cs_size sz ps; cref \<in> dom ps \<rbrakk> \<Longrightarrow>
  obj_bits (CNode sz ps) = 4 + length cref"
  by (drule domD, erule exE, rule obj_bits_CNode)

lemma valid_cs_sizeE [elim]:
  assumes "valid_cs_size sz cs"
  and     "\<lbrakk> sz < word_bits - cte_level_bits; dom cs = {x. length x = sz};
            obj_bits (CNode sz cs) = cte_level_bits + sz\<rbrakk>
           \<Longrightarrow> R"
  shows "R"
  using assms
  by (auto simp: valid_cs_size_def well_formed_cnode_n_def)

lemmas  pageBitsForSize_simps[simp] =
        pageBitsForSize_def[split_simps vmpage_size.split]

lemma arch_kobj_size_bounded:
  "arch_kobj_size obj < word_bits"
  apply (cases obj, simp_all add: word_bits_conv pageBits_def)
  apply (rename_tac vmpage_size)
  apply (case_tac vmpage_size, simp_all)
  done

lemma valid_arch_sizes:
  "obj_bits (ArchObj obj) < word_bits"
  by (simp add: arch_kobj_size_bounded)

lemma valid_obj_sizes:
  assumes vp: "valid_objs s"
  and     ko: "ko \<in> ran (kheap s)"
  shows   "obj_bits ko < word_bits"
proof (cases ko)
  case CNode
  thus ?thesis using vp ko
    by (auto dest!: valid_objs_valid_cs_size)
next
  case (ArchObj ako)
  show ?thesis using ArchObj by (simp only: valid_arch_sizes)
qed (auto elim: valid_pspaceE
          simp: valid_arch_sizes[unfolded word_bits_conv] word_bits_conv)

lemma valid_pspace_obj_sizes:
  assumes vp: "valid_pspace s"
  and     ko: "ko \<in> ran (kheap s)"
  shows   "obj_bits ko < word_bits" using assms
  by - (rule valid_obj_sizes, auto simp: valid_pspace_def)

lemma valid_objs_replicate:
  assumes aligned: "pspace_aligned s"
  assumes valid: "valid_objs s"
  and     dom:   "x \<in> dom (kheap s)"
  shows   "to_bl x = (take (word_bits - (obj_bits (the (kheap s x)))) (to_bl x)) @
                     replicate (obj_bits (the (kheap s x))) False"
proof -
  let ?a = "obj_bits (the (kheap s x))"

  from aligned have "is_aligned x ?a" using dom
    unfolding pspace_aligned_def ..

  thus ?thesis
    proof (rule is_aligned_replicate[where 'a=32, folded word_bits_def])
  show "obj_bits (the (kheap s x)) \<le> word_bits"
    by (rule order_less_imp_le, rule valid_obj_sizes [OF _ dom_ran]) fact+
  qed
qed

lemma valid_pspace_replicate:
  assumes "valid_pspace s"
  and     "x \<in> dom (kheap s)"
  shows   "to_bl x = (take (word_bits - (obj_bits (the (kheap s x)))) (to_bl x)) @
                     replicate (obj_bits (the (kheap s x))) False"
  using assms
  by - (rule valid_objs_replicate, auto simp: valid_pspace_def)

lemma valid_objs_captable_dom_length:
  assumes "valid_objs s"
  assumes "CNode sz ct \<in> ran (kheap s)"
  assumes ct: "ct y \<noteq> None"
  shows "length y < word_bits - cte_level_bits"
proof -
  have "valid_cs_size sz ct" by (rule valid_objs_valid_cs_size) fact+
  thus ?thesis using ct
    by (auto simp: valid_cs_size_def well_formed_cnode_n_def)
qed

lemma valid_pspace_captable_dom_length:
  assumes "valid_pspace s"
  and     "CNode sz ct \<in> ran (kheap s)"
  and     "ct y \<noteq> None"
  shows "length y < word_bits - cte_level_bits"
  using assms
  by - (rule valid_objs_captable_dom_length, auto simp: valid_pspace_def)

lemma valid_objs_replicate':
  assumes valid: "valid_objs s"
  and   aligned: "pspace_aligned s"
  and     dom:   "x \<in> dom (kheap s)"
  and      l1:   "l1 = word_bits - (obj_bits (the (kheap s x)))"
  and      l2:   "l2 = (obj_bits (the (kheap s x)))"
  and      yv:   "y = (to_bl x)"
  shows   "to_bl x = (take l1 y) @ replicate l2 False"
  by ((subst l1 l2 yv)+, rule valid_objs_replicate) fact+

lemma valid_pspace_replicate':
  assumes valid: "valid_pspace s"
  and     dom:   "x \<in> dom (kheap s)"
  and      l1:   "l1 = word_bits - (obj_bits (the (kheap s x)))"
  and      l2:   "l2 = (obj_bits (the (kheap s x)))"
  and      yv:   "y = (to_bl x)"
  shows   "to_bl x = (take l1 y) @ replicate l2 False"
  by ((subst l1 l2 yv)+, rule valid_pspace_replicate) fact+

lemma pspace_replicate_dom:
  assumes "valid_pspace s"
  and pv: "kheap s (of_bl x) = Some (CNode sz ct)"
  shows   "replicate (obj_bits (CNode sz ct) - cte_level_bits) False \<in> dom ct"
proof -
  have "valid_cs_size sz ct"
    by (rule valid_cs_sizeI) fact+

  thus ?thesis
    by (rule valid_cs_sizeE) simp
qed

lemma obj_at_valid_objsE:
  "\<lbrakk> obj_at P p s; valid_objs s;
    \<And>ko. \<lbrakk> kheap s p = Some ko; P ko; valid_obj p ko s \<rbrakk> \<Longrightarrow> Q
  \<rbrakk> \<Longrightarrow> Q"
  by (auto simp: valid_objs_def obj_at_def dom_def)

lemma valid_CNodeCapE:
  assumes p: "s \<turnstile> cap.CNodeCap ptr cbits guard" "valid_objs s" "pspace_aligned s"
  assumes R: "\<And>cs. \<lbrakk> 0 < cbits; kheap s ptr = Some (CNode cbits cs);
               \<forall>cap\<in>ran cs. s \<turnstile> cap; dom cs = {x. length x = cbits};
               is_aligned ptr (4 + cbits); cbits < word_bits - cte_level_bits
              \<rbrakk> \<Longrightarrow> P"
  shows "P"
  using p
  apply (clarsimp simp: pspace_aligned_def valid_cap_def)
  apply (erule (1) obj_at_valid_objsE)
  apply (drule bspec, blast)
  apply (clarsimp simp add: is_cap_table)
  apply (clarsimp simp: valid_obj_def valid_cs_def well_formed_cnode_n_def)
  apply (erule valid_cs_sizeE)
  apply (clarsimp simp: cap_aligned_def)
  apply (drule (3) R)
    apply (auto simp: cte_level_bits_def)
  done

lemma cap_table_at_cte_at:
  "\<lbrakk> cap_table_at cbits ptr s; length offset = cbits \<rbrakk>
  \<Longrightarrow> cte_at (ptr, offset) s"
  apply (clarsimp simp: obj_at_def cte_wp_at_cases is_cap_table
                        well_formed_cnode_n_def length_set_helper)
  apply (rule domD, simp)
  done

declare map_nth_0 [simp del]

lemma valid_cs_sizeE2:
  assumes v: "valid_cs_size sz cs"
  assumes c: "cref \<in> dom cs"
  assumes R: "\<lbrakk>length cref \<le> word_bits - cte_level_bits;
               dom cs = {x. length x = length cref};
               obj_bits (CNode sz cs) = cte_level_bits + length cref\<rbrakk> \<Longrightarrow> R"
  shows "R"
proof -
  from v have sz:
    "sz < word_bits - cte_level_bits"
    "dom cs = {x. length x = sz}"
    "obj_bits (CNode sz cs) = cte_level_bits + sz"
    by auto
  with c
  have "sz = length cref" by auto
  with sz
  show ?thesis
    by - (rule R, auto)
qed

lemma pred_tcb_weakenE:
  "\<lbrakk> pred_tcb_at proj P t s; \<And>tcb . P (proj tcb) \<Longrightarrow> P' (proj tcb) \<rbrakk> \<Longrightarrow> pred_tcb_at proj P' t s"
  by (auto simp: pred_tcb_at_def elim: obj_at_weakenE)

(* sseefried:
     This lemma exists only to make existing proofs go through more easily.
     Replacing 'st_tcb_at_weakenE' with 'pred_tcb_at_weakenE' in a proof
     should yield the same result.
*)
lemma st_tcb_weakenE:
  "\<lbrakk> st_tcb_at P t s; \<And>st . P st \<Longrightarrow> P' st \<rbrakk> \<Longrightarrow> st_tcb_at P' t s"
  by (auto simp: pred_tcb_weakenE)

lemma tcb_at_st_tcb_at:
  "tcb_at = st_tcb_at (\<lambda>_. True)"
  apply (rule ext)+
  apply (simp add: tcb_at_def pred_tcb_at_def obj_at_def is_tcb_def)
  apply (rule arg_cong [where f=Ex], rule ext)
  apply (case_tac ko, simp_all)
  done

lemma pred_tcb_at_tcb_at:
  "pred_tcb_at proj P t s \<Longrightarrow> tcb_at t s"
  by (auto simp: tcb_at_def pred_tcb_at_def obj_at_def is_tcb)

lemmas st_tcb_at_tcb_at = pred_tcb_at_tcb_at[where proj=itcb_state, simplified]

lemma cte_wp_at_weakenE:
  "\<lbrakk> cte_wp_at P t s; \<And>c. P c \<Longrightarrow> P' c \<rbrakk> \<Longrightarrow> cte_wp_at P' t s"
  by (simp add: cte_wp_at_def) blast

lemma le_minus_minus:
  "\<lbrakk> a \<le> b - c; (c :: ('a :: len) word) \<le> b \<rbrakk> \<Longrightarrow> c \<le> b - a"
  by (simp add: word_le_nat_alt unat_sub)

lemma tcb_at_cte_at:
  "\<lbrakk> tcb_at t s; ref \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> cte_at (t, ref) s"
  by (clarsimp simp: obj_at_def cte_wp_at_cases is_tcb)

lemma cte_at_cases:
  "cte_at t s = ((\<exists>sz fun. kheap s (fst t) = Some (CNode sz fun) \<and>
                        well_formed_cnode_n sz fun \<and>
                        (snd t) \<in> dom fun) \<or>
                (\<exists>tcb. kheap s (fst t) = Some (TCB tcb) \<and>
                         (snd t \<in> dom tcb_cap_cases)))"
  by (auto simp add: cte_wp_at_cases dom_def)

lemma cte_atE [consumes 1, case_names CNode TCB, elim?]:
  assumes cat: "cte_at t s"
  and     rct: "\<And>sz fun. \<lbrakk>kheap s (fst t) = Some (CNode sz fun); snd t \<in> dom fun\<rbrakk> \<Longrightarrow> R"
  and    rtcb: "\<And>tcb. \<lbrakk>kheap s (fst t) = Some (TCB tcb); snd t \<in> dom tcb_cap_cases \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using cat by (auto simp: cte_at_cases intro: rct rtcb)

lemma cte_wp_atE:
  "\<lbrakk>cte_wp_at P t s;
  \<And>sz fun cte. \<lbrakk>kheap s (fst t) = Some (CNode sz fun); well_formed_cnode_n sz fun;
                fun (snd t) = Some cte; P cte\<rbrakk> \<Longrightarrow> R;
  \<And>tcb getF setF restr. \<lbrakk>kheap s (fst t) = Some (TCB tcb);
                          tcb_cap_cases (snd t) = Some (getF, setF, restr); P (getF tcb) \<rbrakk> \<Longrightarrow> R \<rbrakk>
  \<Longrightarrow> R"
  by (fastforce simp: cte_wp_at_cases dom_def)

lemma cte_wp_at_cteI:
  "\<lbrakk>kheap s (fst t) = Some (CNode sz fun); well_formed_cnode_n sz fun; fun (snd t) = Some cte; P cte\<rbrakk>
  \<Longrightarrow> cte_wp_at P t s"
  by (auto simp: cte_wp_at_cases dom_def well_formed_cnode_n_def length_set_helper)

lemma cte_wp_at_tcbI:
  "\<lbrakk>kheap s (fst t) = Some (TCB tcb); tcb_cap_cases (snd t) = Some (getF, setF); P (getF tcb) \<rbrakk>
  \<Longrightarrow> cte_wp_at P t s"
  by (auto simp: cte_wp_at_cases dom_def)

lemma ko_at_obj_congD:
  "\<lbrakk> ko_at k1 p s; ko_at k2 p s \<rbrakk> \<Longrightarrow> k1 = k2"
  unfolding obj_at_def
  by simp

text {* using typ_at triples to prove other triples *}

lemma cte_at_typ:
  "cte_at p = (\<lambda>s. typ_at (ACapTable (length (snd p))) (fst p) s
                \<or> (typ_at ATCB (fst p) s \<and> snd p \<in> dom tcb_cap_cases))"
  apply (rule ext)
  apply (simp add: cte_at_cases obj_at_def)
  apply (rule arg_cong2[where f="op \<or>"])
   apply (safe, simp_all add: a_type_def DomainI)
    apply (clarsimp simp add: a_type_def well_formed_cnode_n_def length_set_helper)
    apply (drule_tac m="fun" in domI)
    apply simp
   apply (case_tac ko, simp_all)
   apply (simp add: well_formed_cnode_n_def length_set_helper split: split_if_asm)
  apply (case_tac ko, simp_all split: split_if_asm)
  done

lemma valid_cte_at_typ:
  assumes P: "\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows      "\<lbrace>cte_at c\<rbrace> f \<lbrace>\<lambda>rv. cte_at c\<rbrace>"
  unfolding cte_at_typ
  apply (rule hoare_vcg_disj_lift [OF P])
  apply (rule hoare_vcg_conj_lift [OF P])
  apply (rule hoare_vcg_prop)
  done

lemma length_helper:
  "\<exists>y. length y = n"
  apply (rule_tac x="replicate n x" in exI)
  apply simp
  done

lemma pspace_typ_at:
  "kheap s p = Some obj \<Longrightarrow> \<exists>T. typ_at T p s"
  by (clarsimp simp: obj_at_def)

lemma obj_bits_T:
  "obj_bits v = obj_bits_type (a_type v)"
  apply (cases v, simp_all add: obj_bits_type_def a_type_def)
   apply (clarsimp simp: obj_bits.simps well_formed_cnode_n_def
                         length_set_helper length_helper cte_level_bits_def)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all add: obj_bits.simps)
  done

lemma obj_range_T:
  "obj_range p v = typ_range p (a_type v)"
  by (simp add: obj_range_def typ_range_def obj_bits_T)

lemma valid_untyped_T:
  "valid_untyped c =
  (\<lambda>s. \<forall>T p. \<not>typ_at T p s \<or> typ_range p T \<inter> untyped_range c = {} \<or>
         (typ_range p T \<subseteq> untyped_range c \<and> typ_range p T \<inter> usable_untyped_range c = {}))"
  apply (simp add: valid_untyped_def obj_range_T obj_at_def)
  apply (rule ext)
  apply (rule iffI)
    apply clarsimp
    apply (elim allE)
    apply (erule(1) impE)+
      apply fastforce
  apply clarsimp
    apply (elim allE disjE)
    apply (erule(1) impE)
    apply fastforce+
  done

lemma valid_untyped_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows "\<lbrace>valid_untyped (cap.UntypedCap r n fr)\<rbrace> f
         \<lbrace>\<lambda>rv. valid_untyped (cap.UntypedCap r n fr)\<rbrace>"
  unfolding valid_untyped_T
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_vcg_disj_lift [OF P])
  apply (rule hoare_vcg_prop)
  done

lemma cap_aligned_Null [simp]:
  "cap_aligned (cap.NullCap)"
  by (simp add: cap_aligned_def word_bits_def is_aligned_def)

lemma valid_cap_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_cap c s\<rbrace> f \<lbrace>\<lambda>rv s. valid_cap c s\<rbrace>"
  apply (simp add: valid_cap_def)
  apply (rule hoare_vcg_conj_lift)
   apply (simp add: valid_def)
  apply (case_tac c,
         simp_all add: valid_cap_def hoare_post_taut P P[where P=id, simplified]
                       ep_at_typ tcb_at_typ ntfn_at_typ
                       cap_table_at_typ hoare_vcg_prop
                       hoare_pre_cont)
      apply (rule hoare_vcg_conj_lift [OF valid_untyped_typ[OF P]])
      apply (simp add: valid_def)
     apply (rule hoare_vcg_conj_lift [OF P hoare_vcg_prop])+
   apply (rename_tac option nat)
   apply (case_tac option, simp_all add: tcb_at_typ cap_table_at_typ)[1]
    apply (rule hoare_vcg_conj_lift [OF P])
    apply (rule hoare_vcg_prop)
   apply (rule hoare_vcg_conj_lift [OF P])
   apply (rule hoare_vcg_prop)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap,
         simp_all add: P P[where P=id, simplified]
                       hoare_vcg_prop)
  apply (auto intro: hoare_vcg_conj_lift [OF P] hoare_vcg_prop)
  done

lemma valid_tcb_state_typ:
  assumes P: "\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_tcb_state st s\<rbrace> f \<lbrace>\<lambda>rv s. valid_tcb_state st s\<rbrace>"
  by (case_tac st,
      simp_all add: valid_tcb_state_def hoare_post_taut
                    ep_at_typ P tcb_at_typ ntfn_at_typ)

lemma ntfn_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>ntfn_at c\<rbrace> f \<lbrace>\<lambda>rv. ntfn_at c\<rbrace>"
  by (simp add: ntfn_at_typ)

lemma valid_tcb_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_tcb p tcb s\<rbrace> f \<lbrace>\<lambda>rv s. valid_tcb p tcb s\<rbrace>"
  apply (simp add: valid_tcb_def valid_bound_ntfn_def split_def)
  apply (wp valid_tcb_state_typ valid_cap_typ P hoare_vcg_const_Ball_lift
            valid_case_option_post_wp ntfn_at_typ_at)
  done

lemma valid_cs_typ:
  assumes P: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_cs sz cs s\<rbrace> f \<lbrace>\<lambda>rv s. valid_cs sz cs s\<rbrace>"
  apply (simp add: valid_cs_def)
  apply (rule hoare_vcg_conj_lift [OF _ hoare_vcg_prop])
  apply (rule hoare_vcg_const_Ball_lift)
  apply (rule valid_cap_typ [OF P])
  done

lemma valid_ep_typ:
  assumes P: "\<And>p. \<lbrace>typ_at ATCB p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ATCB p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_ep ep s\<rbrace> f \<lbrace>\<lambda>rv s. valid_ep ep s\<rbrace>"
  apply (case_tac ep,
         simp_all add: valid_ep_def hoare_post_taut tcb_at_typ)
   apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])
   apply (rule hoare_vcg_conj_lift [OF _ hoare_vcg_prop])
   apply (rule hoare_vcg_const_Ball_lift [OF P])
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])
  apply (rule hoare_vcg_conj_lift [OF _ hoare_vcg_prop])
  apply (rule hoare_vcg_const_Ball_lift [OF P])
  done

lemma valid_ntfn_typ:
  assumes P: "\<And>p. \<lbrace>typ_at ATCB p\<rbrace> f \<lbrace>\<lambda>rv. typ_at ATCB p\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_ntfn ntfn s\<rbrace> f \<lbrace>\<lambda>rv s. valid_ntfn ntfn s\<rbrace>"
  apply (case_tac "ntfn_obj ntfn",
         simp_all add: valid_ntfn_def valid_bound_tcb_def hoare_post_taut tcb_at_typ)
    defer 2
    apply ((case_tac "ntfn_bound_tcb ntfn", simp_all add: hoare_post_taut tcb_at_typ P)+)[2]
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])+
  apply (rule hoare_vcg_conj_lift)
   apply (rule hoare_vcg_const_Ball_lift [OF P])
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop])
  apply (case_tac "ntfn_bound_tcb ntfn", simp_all add: hoare_post_taut tcb_at_typ P)
  apply (rule hoare_vcg_conj_lift [OF hoare_vcg_prop], simp add: P)
  done

lemma valid_arch_obj_typ:
  assumes P: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_arch_obj ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_arch_obj ob s\<rbrace>"
  apply (cases ob, simp_all)
    apply (rule hoare_vcg_const_Ball_lift [OF P])
   apply (rule hoare_vcg_all_lift)
   apply (rename_tac "fun" x)
   apply (case_tac "fun x", simp_all add: hoare_vcg_prop P)
  apply (rule hoare_vcg_ball_lift)
  apply (rename_tac "fun" x)
  apply (case_tac "fun x", simp_all add: hoare_vcg_prop P)
  apply (rule P)
  done

lemma valid_obj_typ:
  assumes P: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. valid_obj p ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_obj p ob s\<rbrace>"
  apply (case_tac ob, simp_all add: valid_obj_def P P [where P=id, simplified]
         valid_cs_typ valid_tcb_typ valid_ep_typ valid_ntfn_typ valid_arch_obj_typ)
  apply wp
  done

lemma valid_irq_node_typ:
  assumes P: "\<And>p. \<lbrace>\<lambda>s. typ_at (ACapTable 0) p s\<rbrace> f \<lbrace>\<lambda>rv s. typ_at (ACapTable 0) p s\<rbrace>"
  assumes Q: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  shows      "\<lbrace>valid_irq_node\<rbrace> f \<lbrace>\<lambda>rv. valid_irq_node\<rbrace>"
  apply (simp add: valid_irq_node_def cap_table_at_typ)
  apply (wp Q hoare_use_eq [OF Q P] hoare_vcg_all_lift)
  done

lemma wf_cs_upd:
  "\<lbrakk> cs x = Some y \<rbrakk> \<Longrightarrow>
     well_formed_cnode_n n (cs (x \<mapsto> z)) = well_formed_cnode_n n cs"
  apply (clarsimp simp: well_formed_cnode_n_def)
  apply (subst insert_absorb)
   apply (erule domI)
  apply (rule refl)
  done

lemma pageBits_clb_less_word_bits [simp]:
  "pageBits - cte_level_bits < word_bits"
  by (rule less_imp_diff_less, simp)

lemma obj_atE:
  "\<lbrakk> obj_at P p s; \<And>ko. \<lbrakk> kheap s p = Some ko; P ko \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: obj_at_def)

lemma ko_at_weakenE:
  "\<lbrakk> ko_at k ptr s; P k \<rbrakk> \<Longrightarrow> obj_at P ptr s"
  by (erule obj_at_weakenE, simp)

lemma cte_wp_at_valid_objs_valid_cap:
  "\<lbrakk> cte_wp_at P p s; valid_objs s \<rbrakk> \<Longrightarrow> \<exists>cap. P cap \<and> valid_cap cap s"
  apply (clarsimp simp: cte_wp_at_cases valid_objs_def)
  apply (erule disjE)
   apply clarsimp
   apply (drule bspec, erule domI)
   apply (clarsimp simp: valid_obj_def valid_cs_def)
   apply (drule bspec, erule ranI)
   apply fastforce
  apply clarsimp
  apply (drule bspec, erule domI)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (fastforce simp: ran_def)
  done

lemma is_cap_simps':
  "is_cnode_cap cap = (\<exists>r bits g. cap = cap.CNodeCap r bits g)"
  "is_thread_cap cap = (\<exists>r. cap = cap.ThreadCap r)"
  "is_domain_cap cap = (cap = cap.DomainCap)"
  "is_untyped_cap cap = (\<exists>r bits f. cap = cap.UntypedCap r bits f)"
  "is_ep_cap cap = (\<exists>r b R. cap = cap.EndpointCap r b R)"
  "is_ntfn_cap cap = (\<exists>r b R. cap = cap.NotificationCap r b R)"
  "is_zombie cap = (\<exists>r b n. cap = cap.Zombie r b n)"
  "is_arch_cap cap = (\<exists>a. cap = cap.ArchObjectCap a)"
  "is_reply_cap cap = (\<exists>x. cap = cap.ReplyCap x False)"
  "is_master_reply_cap cap = (\<exists>x. cap = cap.ReplyCap x True)"
  by (cases cap, auto simp: is_zombie_def is_arch_cap_def
                            is_reply_cap_def is_master_reply_cap_def)+

lemmas is_cap_simps =
  is_cap_simps' is_pd_cap_def is_pg_cap_def is_pt_cap_def

lemma wf_unique:
  "well_formed_cnode_n bits f \<Longrightarrow>
  (THE n. well_formed_cnode_n n f) = bits"
  by (clarsimp simp: well_formed_cnode_n_def length_set_helper)

lemma wf_obj_bits:
  "well_formed_cnode_n bits f \<Longrightarrow>
  obj_bits (CNode bits f) = 4 + bits"
  by (auto simp: cte_level_bits_def)

lemma wf_cs_n_unique:
  "\<lbrakk> well_formed_cnode_n n f; well_formed_cnode_n n' f \<rbrakk>
  \<Longrightarrow> n = n'"
  by (clarsimp simp: well_formed_cnode_n_def length_set_helper)

lemma typ_at_range:
  "\<lbrakk> typ_at T p s; pspace_aligned s; valid_objs s \<rbrakk> \<Longrightarrow>
  typ_range p T \<noteq> {}"
  apply (erule (1) obj_at_valid_objsE)
  apply (clarsimp simp: pspace_aligned_def)
  apply (drule bspec)
   apply blast
  apply clarsimp
  apply (case_tac ko)
       apply (clarsimp simp: a_type_def split: split_if_asm)
        apply (clarsimp simp: typ_range_def obj_bits_type_def interval_empty cte_level_bits_def)
        apply (erule notE)
        apply (erule is_aligned_no_overflow)
       apply (clarsimp simp: valid_obj_def valid_cs_def valid_cs_size_def)
      apply (auto simp: a_type_def typ_range_def interval_empty obj_bits_type_def word_bits_def
                        arch_kobj_size_bounded[simplified word_bits_conv]
                  dest!: is_aligned_no_overflow
               | simp split: arch_kernel_obj.splits)+
  done

lemma typ_at_eq_kheap_obj:
  "typ_at ATCB p s \<longleftrightarrow> (\<exists>tcb. kheap s p = Some (TCB tcb))"
  "typ_at AEndpoint p s \<longleftrightarrow> (\<exists>ep. kheap s p = Some (Endpoint ep))"
  "typ_at ANTFN p s \<longleftrightarrow> (\<exists>ntfn. kheap s p = Some (Notification ntfn))"
  "typ_at (ACapTable n) p s \<longleftrightarrow>
   (\<exists>cs. kheap s p = Some (CNode n cs) \<and> well_formed_cnode_n n cs)"
  "typ_at AGarbage p s \<longleftrightarrow>
   (\<exists>n cs. kheap s p = Some (CNode n cs) \<and> \<not> well_formed_cnode_n n cs)"
  "typ_at (AArch AASIDPool) p s \<longleftrightarrow>
   (\<exists>f. kheap s p = Some (ArchObj (ARM_Structs_A.ASIDPool f)))"
  "typ_at (AArch APageTable) p s \<longleftrightarrow>
   (\<exists>pt. kheap s p = Some (ArchObj (PageTable pt)))"
  "typ_at (AArch APageDirectory) p s \<longleftrightarrow>
   (\<exists>pd. kheap s p = Some (ArchObj (PageDirectory pd)))"
  "typ_at (AArch (AIntData sz)) p s \<longleftrightarrow>
   (kheap s p = Some (ArchObj (DataPage sz)))"
apply (auto simp add: obj_at_def a_type_def)
apply (case_tac ko, simp_all add: wf_unique
                    split: split_if_asm arch_kernel_obj.splits, fastforce?)+
done

lemma a_type_ACapTableE:
  "\<lbrakk>a_type ko = ACapTable n;
    (!!cs. \<lbrakk>ko = CNode n cs; well_formed_cnode_n n cs\<rbrakk> \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)
lemma a_type_AGarbageE:
  "\<lbrakk>a_type ko = AGarbage;
    (!!n cs. \<lbrakk>ko = CNode n cs; \<not> well_formed_cnode_n n cs\<rbrakk> \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  apply (case_tac ko, simp_all add: a_type_simps split: split_if_asm)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all add: a_type_simps)
  done
lemma a_type_ATCBE:
  "\<lbrakk>a_type ko = ATCB; (!!tcb. ko = TCB tcb \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)
lemma a_type_AEndpointE:
  "\<lbrakk>a_type ko = AEndpoint; (!!ep. ko = Endpoint ep \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)
lemma a_type_ANTFNE:
  "\<lbrakk>a_type ko = ANTFN; (!!ntfn. ko = Notification ntfn \<Longrightarrow> R)\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)
lemma a_type_AASIDPoolE:
  "\<lbrakk>a_type ko = AArch AASIDPool;
    (!!ap. ko = ArchObj (arch_kernel_obj.ASIDPool ap) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)
lemma a_type_APageDirectoryE:
  "\<lbrakk>a_type ko = AArch APageDirectory;
    (!!pd. ko = ArchObj (PageDirectory pd) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)
lemma a_type_APageTableE:
  "\<lbrakk>a_type ko = AArch APageTable; (!!pt. ko = ArchObj (PageTable pt) \<Longrightarrow> R)\<rbrakk>
   \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)
lemma a_type_AIntDataE:
  "\<lbrakk>a_type ko = AArch (AIntData sz); ko = ArchObj (DataPage sz) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (case_tac ko, simp_all add: a_type_simps split: split_if_asm,
      rename_tac arch_kernel_obj,
      case_tac arch_kernel_obj, simp_all add: a_type_simps)

lemmas a_type_elims[elim!] =
   a_type_ACapTableE a_type_AGarbageE a_type_ATCBE
   a_type_AEndpointE a_type_ANTFNE
   a_type_AASIDPoolE a_type_APageDirectoryE a_type_APageTableE a_type_AIntDataE

lemma valid_objs_caps_contained:
  "\<lbrakk> valid_objs s; pspace_aligned s \<rbrakk> \<Longrightarrow> caps_contained s"
  unfolding caps_contained_def
  apply (intro allI impI)
  apply (drule (1) cte_wp_at_valid_objs_valid_cap)
  apply (drule (1) cte_wp_at_valid_objs_valid_cap)
  apply clarsimp
  apply (case_tac c, simp_all)
  apply (erule disjE)
   apply (clarsimp simp: valid_cap_def is_cap_simps)
   apply (clarsimp simp: valid_untyped_T)
   apply (simp add: cap_table_at_typ)
   apply (erule allE, erule allE, erule (1) impE)
   apply (drule (2) typ_at_range)
   apply (clarsimp simp: typ_range_def obj_bits_type_def interval_empty cte_level_bits_def)
   apply fastforce
  apply (clarsimp simp: valid_cap_def is_cap_simps)
  apply (clarsimp simp: valid_untyped_T)
  apply (simp add: tcb_at_typ)
  apply (erule allE, erule allE, erule (1) impE)
  apply (drule (2) typ_at_range)
  apply (clarsimp simp: typ_range_def obj_bits_type_def interval_empty)
  apply fastforce
  done

declare word_neq_0_conv [simp del]
lemma P_null_filter_caps_of_cte_wp_at:
  "\<not> P cap.NullCap \<Longrightarrow>
   (null_filter (caps_of_state s) x \<noteq> None \<and> P (the (null_filter (caps_of_state s) x)))
     = (cte_wp_at P x s)"
  by (simp add: cte_wp_at_caps_of_state null_filter_def, fastforce)

lemma cte_wp_at_cte_at:
  "cte_wp_at P p s \<Longrightarrow> cte_at p s"
  by (erule cte_wp_at_weakenE, rule TrueI)

lemma real_cte_at_cte:
  "real_cte_at cref s \<Longrightarrow> cte_at cref s"
  by (cases cref, clarsimp simp: cap_table_at_cte_at)

lemma real_cte_tcb_valid:
  "real_cte_at ptr s \<longrightarrow> tcb_cap_valid cap ptr s"
  by (clarsimp simp: tcb_cap_valid_def obj_at_def is_cap_table is_tcb)

lemma swp_cte_at_caps_of:
  "swp (cte_wp_at P) s = (\<lambda>p. \<exists>c. caps_of_state s p = Some c \<and> P c)"
  apply (rule ext)
  apply (simp add: cte_wp_at_caps_of_state swp_def)
  done

lemma valid_mdb_def2:
  "valid_mdb = (\<lambda>s. mdb_cte_at (\<lambda>p. \<exists>c. caps_of_state s p = Some c \<and> cap.NullCap \<noteq> c) (cdt s) \<and>
                    untyped_mdb (cdt s) (caps_of_state s) \<and> descendants_inc (cdt s) (caps_of_state s) \<and>
                    no_mloop (cdt s) \<and> untyped_inc (cdt s) (caps_of_state s) \<and>
                    ut_revocable (is_original_cap s) (caps_of_state s) \<and>
                    irq_revocable (is_original_cap s) (caps_of_state s) \<and>
                    reply_master_revocable (is_original_cap s) (caps_of_state s) \<and>
                    reply_mdb (cdt s) (caps_of_state s))"
  by (auto simp add: valid_mdb_def swp_cte_at_caps_of)

lemma cte_wp_valid_cap:
  "\<lbrakk> cte_wp_at (op = c) p s; valid_objs s \<rbrakk> \<Longrightarrow> s \<turnstile> c"
  apply (simp add: cte_wp_at_cases)
  apply (erule disjE)
   apply clarsimp
   apply (simp add: valid_objs_def dom_def)
   apply (erule allE, erule impE, fastforce)
   apply (fastforce simp: ran_def valid_obj_def valid_cs_def)
  apply clarsimp
  apply (simp add: valid_objs_def dom_def)
  apply (erule allE, erule impE, fastforce)
  apply (fastforce simp: ran_def valid_obj_def valid_tcb_def)
  done

lemma cte_wp_tcb_cap_valid:
  "\<lbrakk> cte_wp_at (op = c) p s; valid_objs s \<rbrakk> \<Longrightarrow> tcb_cap_valid c p s"
  apply (clarsimp simp: tcb_cap_valid_def obj_at_def
                        pred_tcb_at_def cte_wp_at_cases)
  apply (erule disjE, (clarsimp simp: is_tcb)+)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (drule bspec, erule ranI, simp)
  apply clarsimp
  done

lemma caps_of_state_cte_at:
  "caps_of_state s p = Some c \<Longrightarrow> cte_at p s"
  by (simp add: cte_wp_at_caps_of_state)

lemma cte_wp_cte_at:
  "cte_wp_at P p s \<Longrightarrow> cte_at p s"
  by (auto simp add: cte_wp_at_cases)

locale pspace_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes pspace: "kheap (f s) = kheap s"
begin

lemma valid_space_update [iff]:
  "valid_pspace (f s) = valid_pspace s"
  by (fastforce intro: valid_pspace_eqI simp: pspace)

lemma obj_at_update [iff]:
  "obj_at P p (f s) = obj_at P p s"
  by (fastforce intro: obj_at_pspaceI simp: pspace)

lemma in_user_frame_update[iff]:
  "in_user_frame p (f s) = in_user_frame p s"
  by (simp add: in_user_frame_def)

lemma cte_wp_at_update [iff]:
  "cte_wp_at P p (f s) = cte_wp_at P p s"
  by (fastforce intro: cte_wp_at_pspaceI simp: pspace)

lemma iflive_update [iff]:
  "if_live_then_nonz_cap (f s) = if_live_then_nonz_cap s"
  by (simp add: if_live_then_nonz_cap_def ex_nonz_cap_to_def)

lemma valid_objs_update [iff]:
  "valid_objs (f s) = valid_objs s"
  by (fastforce intro: valid_objs_pspaceI simp: pspace)

lemma pspace_aligned_update [iff]:
  "pspace_aligned (f s) = pspace_aligned s"
  by (simp add: pspace_aligned_def pspace)

lemma pspace_distinct_update [iff]:
  "pspace_distinct (f s) = pspace_distinct s"
  by (simp add: pspace_distinct_def pspace)

lemma pred_tcb_at_update [iff]:
  "pred_tcb_at proj P p (f s) = pred_tcb_at proj P p s"
  by (simp add: pred_tcb_at_def)

lemma valid_cap_update [iff]:
  "(f s) \<turnstile> c = s \<turnstile> c"
  by (auto intro: valid_cap_pspaceI simp: pspace)

lemma get_cap_update [iff]:
  "(fst (get_cap p (f s)) = {(cap, f s)}) = (fst (get_cap p s) = {(cap, s)})"
  apply (simp add: get_cap_def get_object_def bind_assoc
                   exec_gets split_def assert_def pspace)
  apply (clarsimp simp: fail_def)
  apply (case_tac y, simp_all add: assert_opt_def split: option.splits)
      apply (simp_all add: return_def fail_def assert_def bind_def)
  done

lemma caps_of_state_update [iff]:
  "caps_of_state (f s) = caps_of_state s"
  by (rule ext) (auto simp: caps_of_state_def)

lemma valid_refs_update [iff]:
  "valid_refs R (f s) = valid_refs R s"
  by (simp add: valid_refs_def)

lemma valid_asid_table_update [iff]:
  "valid_asid_table t (f s) = valid_asid_table t s"
  by (simp add: valid_asid_table_def)

lemma valid_global_pts_update [iff]:
  "arm_global_pts (arch_state (f s)) = arm_global_pts (arch_state s) \<Longrightarrow>
   valid_global_pts (f s) = valid_global_pts s"
  by (simp add: valid_global_pts_def)

lemma has_reply_cap_update [iff]:
  "has_reply_cap t (f s) = has_reply_cap t s"
  by (simp add: has_reply_cap_def)

lemma valid_reply_caps_update [iff]:
  "valid_reply_caps (f s) = valid_reply_caps s"
  by (simp add: valid_reply_caps_def)

lemma valid_reply_masters_update [iff]:
  "valid_reply_masters (f s) = valid_reply_masters s"
  by (simp add: valid_reply_masters_def)

lemma valid_pte_update [iff]:
  "valid_pte pte (f s) = valid_pte pte s"
  by (cases pte) auto

lemma valid_pde_update [iff]:
  "valid_pde pde (f s) = valid_pde pde s"
  by (cases pde) auto

lemma valid_arch_obj_update [iff]:
  "valid_arch_obj ao (f s) = valid_arch_obj ao s"
  by (cases ao) auto

lemma valid_ao_at_update [iff]:
  "valid_ao_at p (f s) = valid_ao_at p s"
  by (simp add: valid_ao_at_def)

lemma equal_kernel_mappings_update [iff]:
  "equal_kernel_mappings (f s) = equal_kernel_mappings s"
  by (simp add: equal_kernel_mappings_def)

lemma valid_pt_kernel_mappings [iff]:
  "valid_pde_kernel_mappings pde vref uses (f s)
      = valid_pde_kernel_mappings pde vref uses s"
  by (cases pde, simp_all add: valid_pde_kernel_mappings_def)

lemma valid_pd_kernel_mappings [iff]:
  "valid_pd_kernel_mappings uses (f s)
      = valid_pd_kernel_mappings uses s"
  by (rule ext, simp add: valid_pd_kernel_mappings_def)

end

locale arch_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes arch: "arch_state (f s) = arch_state s"

locale arch_idle_update_eq = arch_update_eq +
  assumes idle: "idle_thread (f s) = idle_thread s"
  assumes irq: "interrupt_irq_node (f s) = interrupt_irq_node s"
begin

lemma global_refs_update [iff]:
  "global_refs (f s) = global_refs s"
  by (simp add: global_refs_def arch idle irq)

end

locale p_arch_update_eq = pspace_update_eq + arch_update_eq
begin

lemma vs_lookup1_update [iff]:
  "vs_lookup1 (f s) = vs_lookup1 s"
  by (simp add: vs_lookup1_def)

lemma vs_lookup_trans_update [iff]:
  "vs_lookup_trans (f s) = vs_lookup_trans s"
  by simp

lemma vs_lookup_update [iff]:
  "vs_lookup (f s) = vs_lookup s"
  by (simp add: vs_lookup_def arch)

lemma vs_lookup_pages1_update [iff]:
  "vs_lookup_pages1 (f s) = vs_lookup_pages1 s"
  by (simp add: vs_lookup_pages1_def)

lemma vs_lookup_pages_trans_update [iff]:
  "vs_lookup_pages_trans (f s) = vs_lookup_pages_trans s"
  by simp

lemma vs_lookup_pages_update [iff]:
  "vs_lookup_pages (f s) = vs_lookup_pages s"
  by (simp add: vs_lookup_pages_def arch)

lemma valid_arch_objs_update [iff]:
  "valid_arch_objs (f s) = valid_arch_objs s"
  by (simp add: valid_arch_objs_def)

lemma valid_vs_lookup_update [iff]:
  "valid_vs_lookup (f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def arch)

lemma valid_table_caps_update [iff]:
  "valid_table_caps (f s) = valid_table_caps s"
  by (simp add: valid_table_caps_def arch)

lemma valid_arch_cap_update [iff]:
  "valid_arch_caps (f s) = valid_arch_caps s"
  by (simp add: valid_arch_caps_def)

lemma valid_global_objs_update [iff]:
  "valid_global_objs (f s) = valid_global_objs s"
  by (simp add: valid_global_objs_def arch)

lemma valid_global_pd_mappings_update [iff]:
  "valid_global_pd_mappings (f s) = valid_global_pd_mappings s"
  by (simp add: valid_global_pd_mappings_def
                arch)

lemma pspace_in_kernel_window_update [iff]:
  "pspace_in_kernel_window (f s) = pspace_in_kernel_window s"
  by (simp add: pspace_in_kernel_window_def arch pspace)

lemma cap_refs_in_kernel_window_update [iff]:
  "cap_refs_in_kernel_window (f s) = cap_refs_in_kernel_window s"
  by (simp add: cap_refs_in_kernel_window_def arch pspace)

end


locale p_arch_idle_update_eq = p_arch_update_eq + arch_idle_update_eq
begin

lemma ifunsafe_update [iff]:
  "if_unsafe_then_cap (f s) = if_unsafe_then_cap s"
  by (simp add: if_unsafe_then_cap_def ex_cte_cap_wp_to_def irq)

lemma valid_global_refs_update [iff]:
  "valid_global_refs (f s) = valid_global_refs s"
  by (simp add: valid_global_refs_def arch idle)

lemma valid_asid_map_update [iff]:
  "valid_asid_map (f s) = valid_asid_map s"
  by (simp add: valid_asid_map_def pd_at_asid_def arch)

lemma valid_arch_state_update [iff]:
  "valid_arch_state (f s) = valid_arch_state s"
  by (simp add: valid_arch_state_def arch)

lemma valid_idle_update [iff]:
  "valid_idle (f s) = valid_idle s"
  by (auto intro: valid_idle_pspaceI simp: pspace idle)

lemma valid_kernel_mappings_update [iff]:
  "valid_kernel_mappings (f s) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def
                pspace arch)

lemma only_idle_update [iff]:
  "only_idle (f s) = only_idle s"
  by (simp add: only_idle_def idle)

lemma valid_irq_node_update[iff]:
  "valid_irq_node (f s) = valid_irq_node s"
  by (simp add: valid_irq_node_def irq)

end

locale irq_states_update_eq =
  fixes f :: "'z::state_ext state \<Rightarrow> 'c::state_ext state"
  assumes int: "interrupt_states (f s) = interrupt_states s"
begin

lemma irq_issued_update [iff]:
  "irq_issued irq (f s) = irq_issued irq s"
  by (simp add: irq_issued_def int)

end

locale pspace_int_update_eq = pspace_update_eq + irq_states_update_eq
begin

lemma valid_irq_handlers_update [iff]:
  "valid_irq_handlers (f s) = valid_irq_handlers s"
  by (simp add: valid_irq_handlers_def)

end

locale p_arch_idle_update_int_eq = p_arch_idle_update_eq + pspace_int_update_eq

interpretation revokable_update:
  p_arch_idle_update_int_eq "is_original_cap_update f"
  by unfold_locales auto

interpretation machine_state_update:
  p_arch_idle_update_int_eq "machine_state_update f"
  by unfold_locales auto

interpretation cdt_update:
  p_arch_idle_update_int_eq "cdt_update f"
  by unfold_locales auto

interpretation cur_thread_update:
  p_arch_idle_update_int_eq "cur_thread_update f"
  by unfold_locales auto

interpretation more_update:
  p_arch_idle_update_int_eq "trans_state f"
  by unfold_locales auto

interpretation interrupt_update:
  p_arch_idle_update_eq "interrupt_states_update f"
  by unfold_locales auto

interpretation irq_node_update:
  pspace_int_update_eq "interrupt_irq_node_update f"
  by unfold_locales auto

interpretation arch_update:
  pspace_int_update_eq "arch_state_update f"
  by unfold_locales auto

interpretation more_update':
  pspace_int_update_eq "trans_state f"
  by unfold_locales auto

interpretation irq_node_update_arch:
  p_arch_update_eq "interrupt_irq_node_update f"
  by unfold_locales auto

interpretation more_update_arch:
  p_arch_update_eq "trans_state f"
  by unfold_locales auto


lemma obj_ref_in_untyped_range:
  "\<lbrakk> is_untyped_cap c; cap_aligned c \<rbrakk> \<Longrightarrow> obj_ref_of c \<in> untyped_range c"
  apply (clarsimp simp: is_cap_simps cap_aligned_def)
  apply (erule is_aligned_no_overflow)
  done

lemma untyped_range_non_empty:
  "\<lbrakk> is_untyped_cap c; cap_aligned c \<rbrakk> \<Longrightarrow> untyped_range c \<noteq> {}"
  by (blast dest: obj_ref_in_untyped_range)

lemma valid_mdb_cur [iff]:
  "valid_mdb (cur_thread_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_mdb_more_update [iff]:
  "valid_mdb (trans_state f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_mdb_machine [iff]:
  "valid_mdb (machine_state_update f s) = valid_mdb s"
  by (auto elim: valid_mdb_eqI)

lemma valid_refs_cte:
  assumes "\<And>P p. cte_wp_at P p s = cte_wp_at P p s'"
  shows "valid_refs R s = valid_refs R s'"
  by (simp add: valid_refs_def assms)

lemma valid_refs_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_refs R s\<rbrace> f \<lbrace>\<lambda>_ s. valid_refs R s\<rbrace>"
  apply (simp add: valid_refs_def2)
  apply (rule ctes)
  done

lemma valid_global_refs_cte:
  assumes "\<And>P p. cte_wp_at P p s = cte_wp_at P p s'"
  assumes "idle_thread s = idle_thread s'"
  assumes "interrupt_irq_node s = interrupt_irq_node s'"
  assumes "arm_globals_frame (arch_state s) = arm_globals_frame (arch_state s')"
  assumes "arm_global_pd (arch_state s) = arm_global_pd (arch_state s')"
  assumes "set (arm_global_pts (arch_state s)) = set (arm_global_pts (arch_state s'))"
  assumes "ran (arm_asid_table (arch_state s)) = ran (arm_asid_table (arch_state s'))"
  shows "valid_global_refs s = valid_global_refs s'"
  by (simp add: valid_global_refs_def assms valid_refs_def global_refs_def)

lemma valid_global_refs_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes idle: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  assumes irq: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  shows "\<lbrace>valid_global_refs\<rbrace> f \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  unfolding valid_global_refs_def valid_refs_def2 global_refs_def
  apply (rule hoare_lift_Pf [where f="caps_of_state"])
   apply (rule hoare_lift_Pf [where f="idle_thread"])
    apply (rule hoare_lift_Pf [where f="interrupt_irq_node"])
     apply (rule arch)
    apply (rule irq)
   apply (rule idle)
  apply (rule ctes)
  done

lemma valid_arch_state_lift:
  assumes typs: "\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>_. typ_at T p\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  shows "\<lbrace>valid_arch_state\<rbrace> f \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  apply (simp add: valid_arch_state_def valid_asid_table_def
                   valid_global_pts_def)
  apply (rule hoare_lift_Pf[where f="\<lambda>s. arch_state s"])
   apply (wp arch typs hoare_vcg_conj_lift hoare_vcg_const_Ball_lift )
  done

lemma has_reply_cap_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (has_reply_cap t s)\<rbrace> f \<lbrace>\<lambda>_ s. P (has_reply_cap t s)\<rbrace>"
  unfolding has_reply_cap_def
  by (simp add: cte_wp_at_caps_of_state, rule ctes)

lemma valid_reply_caps_st_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  assumes tcbs: "\<And>P t. \<lbrace>st_tcb_at P t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  shows "\<lbrace>valid_reply_caps\<rbrace> f \<lbrace>\<lambda>_. valid_reply_caps\<rbrace>"
  unfolding valid_reply_caps_def
  apply (rule hoare_vcg_conj_lift)
   apply (rule hoare_vcg_all_lift)
   apply (subst disj_not1 [THEN sym])+
   apply (rule hoare_vcg_disj_lift)
    apply (rule has_reply_cap_cte_lift)
    apply (rule ctes)
   apply (rule tcbs)
  apply (rule ctes)
  done

lemma valid_reply_masters_cte:
  assumes "\<And>P p. cte_wp_at P p s = cte_wp_at P p s'"
  shows "valid_reply_masters s = valid_reply_masters s'"
  by (simp add: valid_reply_masters_def assms tcb_at_typ)

lemma valid_reply_masters_cte_lift:
  assumes ctes: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>valid_reply_masters\<rbrace> f \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  unfolding valid_reply_masters_def
  apply (rule hoare_vcg_all_lift)+
  apply (subst disj_not1 [THEN sym])+
  apply (rule hoare_vcg_disj_lift)
   apply (simp add: cte_wp_at_caps_of_state)
   apply (rule ctes)
  apply wp
  done

lemma pred_tcb_at_disj:
  "(pred_tcb_at proj P t s \<or> pred_tcb_at proj Q t s) = pred_tcb_at proj (\<lambda>a. P a \<or> Q a) t s"
  by (fastforce simp add: pred_tcb_at_def obj_at_def)

lemma dom_empty_cnode: "dom (empty_cnode us) = {x. length x = us}"
  unfolding empty_cnode_def
  by (simp add: dom_def)

declare is_aligned_0' [simp]

lemma obj_at_default_cap_valid:
  "\<lbrakk>obj_at (\<lambda>ko. ko = default_object ty us) x s;
   ty = CapTableObject \<Longrightarrow> 0 < us;
   ty \<noteq> Untyped; ty \<noteq> ArchObject ASIDPoolObj;
   cap_aligned (default_cap ty x us)\<rbrakk>
  \<Longrightarrow> s \<turnstile> default_cap ty x us"
  unfolding valid_cap_def
  by (clarsimp elim!: obj_at_weakenE
      simp: default_object_def dom_empty_cnode well_formed_cnode_n_def
            is_tcb is_ep is_ntfn is_cap_table
            arch_default_cap_def default_arch_object_def
            a_type_def valid_vm_rights_def
     split: Structures_A.apiobject_type.splits
            ARM_Structs_A.aobject_type.split_asm
            option.splits)

lemma obj_ref_default [simp]:
  "obj_ref_of (default_cap ty x us) = x"
  by (cases ty,
      auto simp: arch_default_cap_def
          split: ARM_Structs_A.aobject_type.split)

lemma valid_pspace_aligned2 [elim!]:
  "valid_pspace s \<Longrightarrow> pspace_aligned s"
  by (simp add: valid_pspace_def)

lemma valid_pspace_distinct [elim!]:
  "valid_pspace s \<Longrightarrow> pspace_distinct s"
  by (simp add: valid_pspace_def)

lemma ctable_vtable_neq [simp]:
  "get_tcb_ctable_ptr ptr \<noteq> get_tcb_vtable_ptr ptr"
  unfolding get_tcb_ctable_ptr_def get_tcb_vtable_ptr_def
  by simp

lemma ep_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>ep_at c\<rbrace> f \<lbrace>\<lambda>rv. ep_at c\<rbrace>"
  by (simp add: ep_at_typ)

lemma tcb_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>tcb_at c\<rbrace> f \<lbrace>\<lambda>rv. tcb_at c\<rbrace>"
  by (simp add: tcb_at_typ)

lemma cap_table_at_typ_at:
  "(\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>) \<Longrightarrow> \<lbrace>cap_table_at n c\<rbrace> f \<lbrace>\<lambda>rv. cap_table_at n c\<rbrace>"
  by (simp add: cap_table_at_typ)

lemma valid_pde_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pde pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pde pde s\<rbrace>"
  by (cases pde) (simp | wp x)+

lemma valid_pte_lift:
  assumes x: "\<And>T p. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_pte pte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pte pte s\<rbrace>"
  by (cases pte) (simp | wp x)+

lemma pde_at_typ:
  assumes x: "\<And>p T. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows      "\<lbrace>pde_at p\<rbrace> f \<lbrace>\<lambda>rv. pde_at p\<rbrace>"
  by (simp add: pde_at_def | wp x)+

lemma pte_at_typ:
  assumes x: "\<And>p T. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows      "\<lbrace>pte_at p\<rbrace> f \<lbrace>\<lambda>rv. pte_at p\<rbrace>"
  by (simp add: pte_at_def | wp x)+

lemmas abs_typ_at_lifts  =
  ep_at_typ_at ntfn_at_typ_at tcb_at_typ_at
  cap_table_at_typ_at
  valid_tcb_state_typ valid_cte_at_typ valid_ntfn_typ
  valid_ep_typ valid_cs_typ valid_arch_obj_typ valid_untyped_typ
  valid_tcb_typ valid_obj_typ valid_cap_typ
  valid_pde_lift valid_pte_lift
  pde_at_typ pte_at_typ

lemma valid_idle_lift:
  assumes "\<And>P t. \<lbrace>idle_tcb_at P t\<rbrace> f \<lbrace>\<lambda>_. idle_tcb_at P t\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>valid_idle\<rbrace> f \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: valid_idle_def)
  apply (rule hoare_lift_Pf [where f="idle_thread"])
   apply (rule hoare_vcg_conj_lift)
    apply (rule assms)+
  done


lemma pspace_alignedD [intro?]:
  "\<lbrakk> kheap s p = Some ko; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned p (obj_bits ko)"
  unfolding pspace_aligned_def by (drule bspec, blast, simp)

lemma page_directory_pde_atI:
  "\<lbrakk> page_directory_at p s; x < 2 ^ pageBits;
         pspace_aligned s \<rbrakk> \<Longrightarrow> pde_at (p + (x << 2)) s"
  apply (clarsimp simp: obj_at_def pde_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def
                  split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.splits split_if_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self
                   word_bits_conv)
  apply (subgoal_tac "p = (p + (x << 2) && ~~ mask pd_bits)")
   apply simp
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: pd_bits_def pageBits_def)
  apply simp
  apply (subst upper_bits_unset_is_l2p[unfolded word_bits_conv])
   apply (simp add: pd_bits_def pageBits_def)
  apply (rule shiftl_less_t2n)
   apply (simp add: pd_bits_def pageBits_def)
  apply (simp add: pd_bits_def pageBits_def)
  done

lemma page_table_pte_atI:
  "\<lbrakk> page_table_at p s; x < 2^(pt_bits - 2); pspace_aligned s \<rbrakk> \<Longrightarrow> pte_at (p + (x << 2)) s"
  apply (clarsimp simp: obj_at_def pte_at_def)
  apply (drule (1) pspace_alignedD[rotated])
  apply (clarsimp simp: a_type_def
                  split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.splits split_if_asm)
  apply (simp add: aligned_add_aligned is_aligned_shiftl_self
                   word_bits_conv)
  apply (subgoal_tac "p = (p + (x << 2) && ~~ mask pt_bits)")
   apply simp
  apply (rule sym, rule add_mask_lower_bits)
   apply (simp add: pt_bits_def pageBits_def)
  apply simp
  apply (subst upper_bits_unset_is_l2p[unfolded word_bits_conv])
   apply (simp add: pt_bits_def pageBits_def)
  apply (rule shiftl_less_t2n)
   apply (simp add: pt_bits_def pageBits_def)
  apply (simp add: pt_bits_def pageBits_def)
  done

lemmas caps_of_state_valid_cap = cte_wp_valid_cap [OF caps_of_state_cteD]

lemma obj_ref_is_tcb:
  "\<lbrakk> r \<in> obj_refs cap; tcb_at r s; s \<turnstile> cap \<rbrakk> \<Longrightarrow>
  is_thread_cap cap \<or> is_zombie cap"
  by (clarsimp simp: valid_cap_def is_cap_simps obj_at_def is_obj_defs a_type_def
               split: cap.splits arch_cap.splits)

lemma obj_ref_is_cap_table:
  "\<lbrakk> r \<in> obj_refs cap; cap_table_at n r s; s \<turnstile> cap \<rbrakk> \<Longrightarrow>
  is_cnode_cap cap \<or> is_zombie cap"
  by (clarsimp simp: valid_cap_def is_cap_simps obj_at_def is_obj_defs a_type_def
               split: cap.splits arch_cap.splits split_if_asm)

lemma ut_revocableD:
  "\<lbrakk> cs p = Some cap; is_untyped_cap cap; ut_revocable r cs \<rbrakk> \<Longrightarrow> r p"
  by (auto simp: ut_revocable_def)

lemma untyped_range_is_untyped_cap [elim!]:
  "untyped_range cap \<noteq> {} \<Longrightarrow> is_untyped_cap cap"
  by (cases cap) auto

lemma not_is_untyped_no_range [elim!]:
  "\<not>is_untyped_cap cap \<Longrightarrow> untyped_range cap = {}"
  by (cases cap) auto

lemma untyped_mdbD:
  "\<lbrakk> cs ptr = Some cap; is_untyped_cap cap; cs ptr' = Some cap';
     obj_refs cap' \<inter> untyped_range cap \<noteq> {}; untyped_mdb m cs \<rbrakk>
  \<Longrightarrow> ptr' \<in> descendants_of ptr m"
  unfolding untyped_mdb_def by blast

lemma untyped_incD:
  "\<lbrakk> cs p = Some c; is_untyped_cap c; cs p' = Some c'; is_untyped_cap c'; untyped_inc m cs \<rbrakk> \<Longrightarrow>
  (untyped_range c \<subseteq> untyped_range c' \<or> untyped_range c' \<subseteq> untyped_range c \<or> untyped_range c \<inter> untyped_range c' = {}) \<and>
  (untyped_range c \<subset> untyped_range c' \<longrightarrow> (p \<in> descendants_of p' m \<and> untyped_range c \<inter> usable_untyped_range c' = {})) \<and>
  (untyped_range c' \<subset> untyped_range c \<longrightarrow> (p' \<in> descendants_of p m \<and> untyped_range c' \<inter> usable_untyped_range c = {})) \<and>
  (untyped_range c = untyped_range c' \<longrightarrow> (p' \<in> descendants_of p m \<and> usable_untyped_range c = {}
  \<or> p \<in> descendants_of p' m \<and> usable_untyped_range c' = {} \<or> p = p'))"
  unfolding untyped_inc_def
  apply (drule_tac x = p in spec)
  apply (drule_tac x = p' in spec)
  apply (elim allE impE)
    apply simp+
  done

lemma cte_wp_at_norm:
  "cte_wp_at P p s \<Longrightarrow> \<exists>c. cte_wp_at (op = c) p s \<and> P c"
  by (auto simp add: cte_wp_at_cases)

lemma valid_mdb_arch_state [simp]:
  "valid_mdb (arch_state_update f s) = valid_mdb s"
  by (simp add: valid_mdb_def swp_def)

lemma valid_idle_arch_state [simp]:
  "valid_idle (arch_state_update f s) = valid_idle s"
  by (simp add: valid_idle_def)

lemma if_unsafe_then_cap_arch_state [simp]:
  "if_unsafe_then_cap (arch_state_update f s) = if_unsafe_then_cap s"
  by (simp add: if_unsafe_then_cap_def ex_cte_cap_wp_to_def)

lemma swp_cte_at_arch_update [iff]:
  "swp cte_at (s\<lparr>arch_state := a\<rparr>) = swp cte_at s"
  by (simp add: cte_wp_at_cases swp_def)

lemma swp_caps_of_state_arch_update [iff]:
  "caps_of_state (s\<lparr>arch_state := a\<rparr>) = caps_of_state s"
  apply (rule cte_wp_caps_of_lift)
  apply (simp add: cte_wp_at_cases)
  done

lemma vs_lookup1_ko_at_dest:
  "\<lbrakk> ((ref, p) \<rhd>1 (ref', p')) s; ko_at (ArchObj ao) p s; valid_arch_obj ao s \<rbrakk> \<Longrightarrow>
  \<exists>ao'. ko_at (ArchObj ao') p' s \<and> (\<exists>tp. vs_ref_atype (hd ref') = Some tp
                                            \<and> a_type (ArchObj ao) = AArch tp)"
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def split_def)
  apply (cases ao, simp_all add: graph_of_def)
   apply clarsimp
   apply (drule bspec, fastforce simp: ran_def)
   apply (clarsimp simp add: a_type_def obj_at_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm split_if_asm)
  apply (clarsimp split: split_if_asm)
  apply (simp add: pde_ref_def a_type_def
            split: ARM_Structs_A.pde.splits)
  apply (erule_tac x=a in ballE)
   apply (clarsimp simp add: obj_at_def)
  apply simp
  done

lemma vs_lookup1_is_arch:
  "(a \<rhd>1 b) s \<Longrightarrow> \<exists>ao'. ko_at (ArchObj ao') (snd a) s"
  apply (clarsimp simp: vs_lookup1_def)
  apply (case_tac ko, auto simp: vs_refs_def)
  done

lemma vs_lookup_trancl_step:
  "\<lbrakk> r \<in> vs_lookup s; (r, r') \<in> (vs_lookup1 s)^+ \<rbrakk> \<Longrightarrow> r' \<in> vs_lookup s"
  apply (clarsimp simp add: vs_lookup_def)
  apply (drule (1) rtrancl_trancl_trancl)
  apply (drule trancl_into_rtrancl)+
  apply blast
  done

lemma vs_lookup_pages_trancl_step:
  "\<lbrakk> r \<in> vs_lookup_pages s; (r, r') \<in> (vs_lookup_pages1 s)^+ \<rbrakk> \<Longrightarrow> r' \<in> vs_lookup_pages s"
  apply (clarsimp simp add: vs_lookup_pages_def)
  apply (drule (1) rtrancl_trancl_trancl)
  apply (drule trancl_into_rtrancl)+
  apply blast
  done

lemma vs_lookup_step:
  "\<lbrakk> (ref \<rhd> p) s; ((ref, p) \<rhd>1 (ref', p')) s \<rbrakk> \<Longrightarrow> (ref' \<rhd> p') s"
  unfolding vs_lookup_def
  apply clarsimp
  apply (drule rtrancl_trans)
   apply (erule r_into_rtrancl)
  apply blast
  done

lemma vs_lookup_pages_step:
  "\<lbrakk> (ref \<unrhd> p) s; ((ref, p) \<unrhd>1 (ref', p')) s \<rbrakk> \<Longrightarrow> (ref' \<unrhd> p') s"
  unfolding vs_lookup_pages_def
  apply clarsimp
  apply (drule rtrancl_trans)
   apply (erule r_into_rtrancl)
  apply blast
  done

lemma vs_asid_refsI:
  "table asid = Some p \<Longrightarrow>
  ([VSRef (ucast asid) None],p) \<in> vs_asid_refs table"
  by (fastforce simp: vs_asid_refs_def graph_of_def)

(* Non-recursive introduction rules for vs_lookup and vs_lookup_pages
   NOTE: exhaustive if assuming valid_objs and valid_asid_table *)
lemma vs_lookup_atI:
  "arm_asid_table (arch_state s) a = Some p \<Longrightarrow> ([VSRef (ucast a) None] \<rhd> p) s"
  unfolding vs_lookup_def by (drule vs_asid_refsI) fastforce

lemma vs_lookup_apI:
  "\<And>a p\<^sub>1 ap b.
     \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<rhd> p) s"
  apply (simp add: vs_lookup_def Image_def vs_asid_refs_def graph_of_def)
  apply (intro exI conjI, assumption)
  apply (rule rtrancl_into_rtrancl)
   apply (rule rtrancl_refl)
  apply (fastforce simp: vs_lookup1_def obj_at_def
                        vs_refs_def graph_of_def image_def)
  done

lemma vs_lookup_pdI:
  "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c.
     \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
      kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
      ap b = Some p\<^sub>2;
      kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
      c \<notin> kernel_mapping_slots;
      pd c = ARM_Structs_A.pde.PageTablePDE p f w\<rbrakk>
     \<Longrightarrow> ([VSRef (ucast c) (Some APageDirectory),
           VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None]
          \<rhd> Platform.ptrFromPAddr p) s"
  apply (simp add: vs_lookup_def Image_def vs_asid_refs_def graph_of_def)
  apply (intro exI conjI, assumption)
  apply (rule rtrancl_into_rtrancl)
   apply (rule rtrancl_into_rtrancl)
    apply (rule rtrancl_refl)
  apply (fastforce simp: vs_lookup1_def obj_at_def
                        vs_refs_def graph_of_def image_def)
  apply (simp add: vs_lookup1_def obj_at_def vs_refs_def graph_of_def image_def)
  apply (rule_tac x=c in exI)
  apply (simp add: pde_ref_def ptrFormPAddr_addFromPPtr)
  done

(* FIXME: move *)
lemma bexEI: "\<lbrakk>\<exists>x\<in>S. Q x; \<And>x. \<lbrakk>x \<in> S; Q x\<rbrakk> \<Longrightarrow> P x\<rbrakk> \<Longrightarrow> \<exists>x\<in>S. P x" by blast

lemma vs_lookup_pages_vs_lookupI: "(ref \<rhd> p) s \<Longrightarrow> (ref \<unrhd> p) s"
    apply (clarsimp simp: vs_lookup_pages_def vs_lookup_def Image_def
                    elim!: bexEI)
    apply (erule rtrancl.induct, simp_all)
    apply (rename_tac a b c)
    apply (subgoal_tac "(b \<unrhd>1 c) s", erule (1) rtrancl_into_rtrancl)
    apply (thin_tac "x : rtrancl r" for x r)+
    apply (simp add: vs_lookup1_def vs_lookup_pages1_def split_def)
    apply (erule exEI)
    apply clarsimp
    apply (case_tac x, simp_all add: vs_refs_def vs_refs_pages_def
                              split: arch_kernel_obj.splits)
    apply (clarsimp simp: split_def graph_of_def image_def  split: split_if_asm)
    apply (intro exI conjI impI, assumption)
     apply (simp add: pde_ref_def pde_ref_pages_def
               split: ARM_Structs_A.pde.splits)
    apply (rule refl)
    done

lemmas
  vs_lookup_pages_atI = vs_lookup_atI[THEN vs_lookup_pages_vs_lookupI] and
  vs_lookup_pages_apI = vs_lookup_apI[THEN vs_lookup_pages_vs_lookupI]

lemma vs_lookup_pages_pdI:
  "\<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
    c \<notin> kernel_mapping_slots; pde_ref_pages (pd c) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast c) (Some APageDirectory),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s"
  apply (frule (2) vs_lookup_pages_apI)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def
                     vs_refs_pages_def graph_of_def image_def
              split: split_if_asm)

lemma vs_lookup_pages_ptI:
  "\<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
    kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
    ap b = Some p\<^sub>2;
    kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
    c \<notin> kernel_mapping_slots; pd c = ARM_Structs_A.PageTablePDE addr x y;
    kheap s (Platform.ptrFromPAddr addr) = Some (ArchObj (PageTable pt));
    pte_ref_pages (pt d) = Some p\<rbrakk>
   \<Longrightarrow> ([VSRef (ucast d) (Some APageTable),
         VSRef (ucast c) (Some APageDirectory),
         VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] \<unrhd> p) s"
  apply (frule (5) vs_lookup_pdI[THEN vs_lookup_pages_vs_lookupI])
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def
                     vs_refs_pages_def graph_of_def image_def
              split: split_if_asm)

lemma stronger_arch_objsD_lemma:
  "\<lbrakk>valid_arch_objs s; r \<in> vs_lookup s; (r,r') \<in> (vs_lookup1 s)\<^sup>+ \<rbrakk>
  \<Longrightarrow> \<exists>ao. ko_at (ArchObj ao) (snd r') s \<and>
          valid_arch_obj ao s"
  apply (erule trancl_induct)
   apply (frule vs_lookup1_is_arch)
   apply (cases r)
   apply clarsimp
   apply (frule (2) valid_arch_objsD)
   apply (drule (1) vs_lookup_step)
   apply (drule (2) vs_lookup1_ko_at_dest)
   apply clarsimp
   apply (drule (2) valid_arch_objsD)
   apply fastforce
  apply clarsimp
  apply (frule (2) vs_lookup1_ko_at_dest)
  apply (drule (1) vs_lookup_trancl_step)
  apply (drule (1) vs_lookup_step)
  apply clarsimp
  apply (drule (2) valid_arch_objsD)
  apply fastforce
  done

lemma stronger_arch_objsD:
  "\<lbrakk> (ref \<rhd> p) s;
     valid_arch_objs s;
     valid_asid_table (arm_asid_table (arch_state s)) s \<rbrakk> \<Longrightarrow>
  \<exists>ao. ko_at (ArchObj ao) p s \<and>
       valid_arch_obj ao s"
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def graph_of_def)
  apply (clarsimp simp: valid_asid_table_def)
  apply (drule bspec, fastforce simp: ran_def)
  apply (drule rtranclD)
  apply (erule disjE)
   prefer 2
   apply clarsimp
   apply (drule stronger_arch_objsD_lemma)
     apply (erule vs_lookup_atI)
    apply assumption
   apply clarsimp
  apply clarsimp
  apply (simp add: valid_arch_objs_def)
  apply (erule_tac x=p in allE)
  apply (erule impE)
   apply (rule exI)
   apply (erule vs_lookup_atI)
  apply (clarsimp simp: obj_at_def)
  done

(* FIXME: move *)
declare ranI [intro]

(* An alternative definition for valid_arch_objs.

   The predicates valid_asid_table and valid_arch_objs are very compact
   but sometimes hard to use.
   The lemma below basically unrolls vs_lookup.
   Though less elegant, this formulation better separates the relevant cases. *)
lemma valid_arch_objs_alt:
  "(\<forall>p\<in>ran (arm_asid_table (arch_state s)). asid_pool_at p s) \<and>
   valid_arch_objs s \<longleftrightarrow>
   (\<forall>a p. arm_asid_table (arch_state s) a = Some p \<longrightarrow>
          typ_at (AArch AASIDPool) p s) \<and>
   (\<forall>a p\<^sub>1 ap b p.
          arm_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap)) \<longrightarrow>
          ap b = Some p \<longrightarrow> page_directory_at p s) \<and>
   (\<forall>a p\<^sub>1 ap b p\<^sub>2 pd c.
          arm_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd)) \<longrightarrow>
          c \<notin> kernel_mapping_slots \<longrightarrow> valid_pde (pd c) s) \<and>
   (\<forall>a p\<^sub>1 ap b p\<^sub>2 pd c addr f w pt.
          arm_asid_table (arch_state s) a = Some p\<^sub>1 \<longrightarrow>
          kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap)) \<longrightarrow>
          ap b = Some p\<^sub>2 \<longrightarrow>
          kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd)) \<longrightarrow>
          c \<notin> kernel_mapping_slots \<longrightarrow>
          pd c = ARM_Structs_A.pde.PageTablePDE addr f w \<longrightarrow>
          kheap s (Platform.ptrFromPAddr addr) =
            Some (ArchObj (PageTable pt)) \<longrightarrow>
          (\<forall>d. valid_pte (pt d) s))"
  apply (intro iffI conjI)
       apply fastforce
      apply (clarsimp simp: obj_at_def)
      apply (thin_tac "Ball S P" for S P)
      apply (frule vs_lookup_atI)
      apply (drule valid_arch_objsD)
        apply (simp add: obj_at_def)
       apply assumption
      apply (clarsimp simp: obj_at_def ranI)
     apply (clarsimp simp: obj_at_def)
     apply (thin_tac "Ball S P" for S P)
     apply (frule (2) vs_lookup_apI)
     apply (drule valid_arch_objsD)
       apply (simp add: obj_at_def)
      apply assumption
     apply fastforce
    apply (clarsimp simp: obj_at_def)
    apply (thin_tac "Ball S P" for S P)
    apply (frule (5) vs_lookup_pdI)
    apply (drule valid_arch_objsD)
      apply (simp add: obj_at_def)
     apply assumption
    apply fastforce
   apply (clarsimp simp: ran_def)
  apply (clarsimp simp: valid_arch_objs_def vs_lookup_def)
  apply (erule converse_rtranclE)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: obj_at_def ran_def)
  apply (erule converse_rtranclE)
   apply (drule vs_lookup1D)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply fastforce
  apply (erule converse_rtranclE)
   apply (clarsimp dest!: vs_lookup1D)
   apply (clarsimp simp: vs_asid_refs_def graph_of_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: obj_at_def)
   apply (clarsimp simp: vs_refs_def graph_of_def image_def)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (drule spec, drule spec, erule impE, assumption)
   apply (clarsimp simp: graph_of_def  split: split_if_asm)
   apply (drule_tac x=ab in spec)
   apply (clarsimp simp: pde_ref_def obj_at_def
                  split: ARM_Structs_A.pde.splits)
  apply (clarsimp dest!: vs_lookup1D)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp simp: vs_refs_def graph_of_def image_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: graph_of_def  split: split_if_asm)
  apply (drule_tac x=ab in spec)
  apply (clarsimp simp: pde_ref_def obj_at_def
                 split: ARM_Structs_A.pde.splits)
  done

lemma vs_lookupE:
  "\<lbrakk> (ref \<rhd> p) s;
    \<And>ref' p'. \<lbrakk> (ref',p') \<in> vs_asid_refs (arm_asid_table (arch_state s));
                ((ref',p') \<rhd>* (ref,p)) s \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
  by (auto simp: vs_lookup_def)

(* Non-recursive elim rules for vs_lookup and vs_lookup_pages
   NOTE: effectively rely on valid_objs and valid_asid_table *)
lemma vs_lookupE_alt:
  assumes vl: "(ref \<rhd> p) s"
  assumes va: "valid_arch_objs s"
  assumes vt: "(\<forall>p\<in>ran (arm_asid_table (arch_state s)). asid_pool_at p s)"
  assumes 0: "\<And>a. arm_asid_table (arch_state s) a = Some p \<Longrightarrow>
                   typ_at (AArch AASIDPool) p s \<Longrightarrow>
                   R [VSRef (ucast a) None] p"
  assumes 1: "\<And>a p\<^sub>1 ap b.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p; page_directory_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 2: "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
        c \<notin> kernel_mapping_slots; pde_ref (pd c) = Some p; page_table_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast c) (Some APageDirectory),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  shows "R ref p"
proof -
  note vao = valid_arch_objs_alt[THEN iffD1, OF conjI[OF vt va]]
  note vat = vao[THEN conjunct1, rule_format]
  note vap = vao[THEN conjunct2, THEN conjunct1, rule_format]
  note vpd = vao[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]

  from vl
  show ?thesis
    apply (clarsimp simp: vs_lookup_def)
    apply (clarsimp simp: Image_def vs_asid_refs_def graph_of_def)
    apply (frule vat)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (1) 0)
    apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def
                   dest!: vs_lookup1D)
    apply (frule (2) vap)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (3) 1)
    apply (clarsimp simp: vs_refs_def graph_of_def obj_at_def
                   dest!: vs_lookup1D  split: split_if_asm)
    apply (frule (4) vpd)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (5) 2)
     apply (simp add: valid_pde_def pde_ref_def split: ARM_Structs_A.pde.splits)
    by (clarsimp simp: obj_at_def pde_ref_def vs_refs_def
                split: ARM_Structs_A.pde.splits
                dest!: vs_lookup1D)
qed

lemma vs_lookup_pagesE_alt:
  assumes vl: "(ref \<unrhd> p) s"
  assumes va: "valid_arch_objs s"
  assumes vt: "(\<forall>p\<in>ran (arm_asid_table (arch_state s)). asid_pool_at p s)"
  assumes 0: "\<And>a. arm_asid_table (arch_state s) a = Some p \<Longrightarrow>
                   typ_at (AArch AASIDPool) p s \<Longrightarrow>
                   R [VSRef (ucast a) None] p"
  assumes 1: "\<And>a p\<^sub>1 ap b.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p; page_directory_at p s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 2: "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
        c \<notin> kernel_mapping_slots;
        pde_ref_pages (pd c) = Some p; valid_pde (pd c) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast c) (Some APageDirectory),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  assumes 3: "\<And>a p\<^sub>1 ap b p\<^sub>2 pd c addr x y pt d.
       \<lbrakk>arm_asid_table (arch_state s) a = Some p\<^sub>1;
        kheap s p\<^sub>1 = Some (ArchObj (arch_kernel_obj.ASIDPool ap));
        ap b = Some p\<^sub>2;
        kheap s p\<^sub>2 = Some (ArchObj (PageDirectory pd));
        c \<notin> kernel_mapping_slots; pd c = ARM_Structs_A.PageTablePDE addr x y;
        kheap s (Platform.ptrFromPAddr addr) = Some (ArchObj (PageTable pt));
        pte_ref_pages (pt d) = Some p; valid_pte (pt d) s\<rbrakk>
       \<Longrightarrow> R [VSRef (ucast d) (Some APageTable),
              VSRef (ucast c) (Some APageDirectory),
              VSRef (ucast b) (Some AASIDPool), VSRef (ucast a) None] p"
  shows "R ref p"
proof -
  note vao = valid_arch_objs_alt[THEN iffD1, OF conjI[OF vt va]]
  note vat = vao[THEN conjunct1, rule_format]
  note vap = vao[THEN conjunct2, THEN conjunct1, rule_format]
  note vpd = vao[THEN conjunct2, THEN conjunct2, THEN conjunct1, rule_format]
  note vpt = vao[THEN conjunct2, THEN conjunct2, THEN conjunct2, rule_format]

  from vl
  show ?thesis
    apply (clarsimp simp: vs_lookup_pages_def)
    apply (clarsimp simp: Image_def vs_asid_refs_def graph_of_def)
    apply (frule vat)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (1) 0)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                   dest!: vs_lookup_pages1D)
    apply (frule (2) vap)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (3) 1)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                   dest!: vs_lookup_pages1D  split: split_if_asm)
    apply (frule (4) vpd)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (6) 2)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                          pde_ref_pages_def
                   dest!: vs_lookup_pages1D
                   split: split_if_asm ARM_Structs_A.pde.splits)
    apply (frule_tac d=ac in vpt, assumption+)
    apply (erule converse_rtranclE)
     apply clarsimp
     apply (erule (8) 3)
    apply (clarsimp simp: vs_refs_pages_def graph_of_def obj_at_def
                          pte_ref_pages_def
                   dest!: vs_lookup_pages1D
                   split: ARM_Structs_A.pte.splits)
    done
qed

lemma valid_asid_tableD:
  "\<lbrakk> T x = Some p; valid_asid_table T s \<rbrakk> \<Longrightarrow> asid_pool_at p s"
  by (auto simp: valid_asid_table_def ran_def)

declare graph_of_empty[simp]

lemma pde_graph_ofI:
  "\<lbrakk>pd x = pde; x \<notin> kernel_mapping_slots; pde_ref pde = Some v\<rbrakk>
   \<Longrightarrow> (x, v) \<in> graph_of (\<lambda>x. if x \<in> kernel_mapping_slots then None
                              else pde_ref (pd x))"
  by (rule graph_ofI, simp)

lemma vs_refs_pdI:
  "\<lbrakk>pd (ucast r) = ARM_Structs_A.PageTablePDE x a b;
    ucast r \<notin> kernel_mapping_slots; \<forall>n \<ge> 12. n < 32 \<longrightarrow> \<not> r !! n\<rbrakk>
   \<Longrightarrow> (VSRef r (Some APageDirectory), Platform.ptrFromPAddr x)
       \<in> vs_refs (ArchObj (PageDirectory pd))"
  apply (simp add: vs_refs_def)
  apply (rule image_eqI[rotated])
   apply (rule pde_graph_ofI)
     apply (simp add: pde_ref_def)+
  apply (simp add: ucast_ucast_mask)
  apply (rule word_eqI)
  apply (simp add: word_size)
  apply (rule ccontr, auto)
  done

lemma a_type_pdD:
  "a_type ko = AArch APageDirectory \<Longrightarrow> \<exists>pd. ko = ArchObj (ARM_Structs_A.PageDirectory pd)"
  by (clarsimp simp: a_type_def
               split: Structures_A.kernel_object.splits
                      arch_kernel_obj.splits split_if_asm)

lemma empty_table_is_valid:
  "\<lbrakk>empty_table (set (arm_global_pts (arch_state s))) (ArchObj ao);
    valid_arch_state s\<rbrakk>
   \<Longrightarrow> valid_arch_obj ao s"
  by (cases ao, simp_all add: empty_table_def)

lemma empty_table_pde_refD:
  "\<lbrakk> pde_ref (pd x) = Some r; empty_table S (ArchObj (PageDirectory pd)) \<rbrakk> \<Longrightarrow>
  r \<in> S"
  by (simp add: empty_table_def)

lemma valid_global_ptsD:
  "\<lbrakk>r \<in> set (arm_global_pts (arch_state s)); valid_global_objs s\<rbrakk>
   \<Longrightarrow> \<exists>pt. ko_at (ArchObj (PageTable pt)) r s \<and> (\<forall>x. aligned_pte (pt x))"
  by (clarsimp simp: valid_global_objs_def)

lemma valid_table_caps_pdD:
  "\<lbrakk> caps_of_state s p = Some (cap.ArchObjectCap (arch_cap.PageDirectoryCap pd None));
     valid_table_caps s \<rbrakk> \<Longrightarrow>
    obj_at (empty_table (set (arm_global_pts (arch_state s)))) pd s"
  apply (clarsimp simp: valid_table_caps_def simp del: split_paired_All)
  apply (erule allE)+
  apply (erule (1) impE)
  apply (fastforce simp add: is_pd_cap_def cap_asid_def)
  done

lemma valid_vs_lookupD:
  "\<lbrakk> (ref \<unrhd> p) s; valid_vs_lookup s \<rbrakk> \<Longrightarrow>
  (\<exists>slot cap. caps_of_state s slot = Some cap \<and> p \<in> obj_refs cap \<and> vs_cap_ref cap = Some ref)"
  by (simp add: valid_vs_lookup_def)

lemma vs_lookup_induct:
  assumes r: "(ref \<rhd> p) s"
  assumes a: "\<And>asid p. \<lbrakk> arm_asid_table (arch_state s) asid = Some p \<rbrakk> \<Longrightarrow> P [VSRef (ucast asid) None] p s"
  assumes s: "\<And>ref p ref' p'. \<lbrakk> (ref \<rhd> p) s; ((ref,p) \<rhd>1 (ref',p')) s; P ref p s \<rbrakk> \<Longrightarrow> P ref' p' s"
  shows "P ref p s"
  using r
  apply (clarsimp simp: vs_lookup_def)
  apply (drule rtranclD)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (frule a)
  apply (erule disjE, simp)
  apply clarsimp
  apply (drule vs_lookup_atI)
  apply (erule trancl_induct2)
   apply (erule (2) s)
  apply (drule (1) vs_lookup_trancl_step)
  apply (erule (2) s)
  done

lemma vs_lookup_pages_induct:
  assumes r: "(ref \<unrhd> p) s"
  assumes a: "\<And>asid p. \<lbrakk> arm_asid_table (arch_state s) asid = Some p \<rbrakk> \<Longrightarrow> P [VSRef (ucast asid) None] p s"
  assumes s: "\<And>ref p ref' p'. \<lbrakk> (ref \<unrhd> p) s; ((ref,p) \<unrhd>1 (ref',p')) s; P ref p s \<rbrakk> \<Longrightarrow> P ref' p' s"
  shows "P ref p s"
  using r
  apply (clarsimp simp: vs_lookup_pages_def)
  apply (drule rtranclD)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (frule a)
  apply (erule disjE, simp)
  apply clarsimp
  apply (drule vs_lookup_pages_atI)
  apply (erule trancl_induct2)
   apply (erule (2) s)
  apply (drule (1) vs_lookup_pages_trancl_step)
  apply (erule (2) s)
  done

lemma vs_ref_order:
  "\<lbrakk> (r \<rhd> p) s; valid_arch_objs s; valid_arch_state s \<rbrakk>
       \<Longrightarrow> \<exists>tp. r \<noteq> [] \<and> typ_at (AArch tp) p s \<and>
            rev (Some tp # map vs_ref_atype r)
               \<le> [None, Some AASIDPool, Some APageDirectory, Some APageTable]"
  apply (erule vs_lookup_induct)
   apply (clarsimp simp: valid_arch_state_def valid_asid_table_def
                         ranI)
  apply (clarsimp dest!: vs_lookup1D elim!: obj_atE)
  apply (clarsimp simp: vs_refs_def a_type_def[where ob="ArchObj ao" for ao]
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm
                 dest!: graph_ofD)
   apply (drule valid_arch_objsD, simp add: obj_at_def, assumption)
   apply (case_tac rs, simp_all)[1]
   apply (case_tac list, simp_all add: ranI)[1]
   apply (case_tac lista, simp_all)[1]
   apply (frule prefix_length_le, clarsimp)
  apply (drule valid_arch_objsD, simp add: obj_at_def, assumption)
  apply (clarsimp simp: pde_ref_def
                 split: ARM_Structs_A.pde.split_asm split_if_asm)
  apply (drule_tac x=a in bspec, simp)
  apply (case_tac rs, simp_all)[1]
  apply (case_tac list, simp_all)[1]
  apply (case_tac lista, simp_all)[1]
  apply (frule prefix_length_le, clarsimp)
  done

lemma addrFromPPtr_ptrFromPAddr_id[simp]:
  "Platform.addrFromPPtr (Platform.ptrFromPAddr x) = x"
by (simp add: Platform.addrFromPPtr_def Platform.ptrFromPAddr_def)

lemma valid_pte_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pte pte s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pte pte s\<rbrace>"
  by (cases pte) (simp | wp x)+

lemma valid_pde_lift2:
  assumes x: "\<And>T p. \<lbrace>Q and typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q s \<and> valid_pde pde s\<rbrace> f \<lbrace>\<lambda>rv s. valid_pde pde s\<rbrace>"
  by (cases pde) (simp | wp x)+

lemma valid_arch_obj_typ2:
  assumes P: "\<And>P p T. \<lbrace>\<lambda>s. Q s \<and> P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Q s \<and> valid_arch_obj ob s\<rbrace> f \<lbrace>\<lambda>rv s. valid_arch_obj ob s\<rbrace>"
  apply (cases ob, simp_all)
    apply (wp hoare_vcg_const_Ball_lift [OF P], simp)
   apply (rule hoare_pre, wp hoare_vcg_all_lift valid_pte_lift2 P)
    apply clarsimp
    apply assumption
   apply clarsimp
  apply (wp hoare_vcg_ball_lift valid_pde_lift2 P)
    apply clarsimp
    apply assumption
   apply clarsimp
  apply wp
  done

lemma is_master_reply_cap_NullCap:
  "is_master_reply_cap cap.NullCap = False"
  by (simp add: is_cap_simps)

lemma unique_reply_capsD:
  "\<lbrakk> unique_reply_caps cs; reply_masters_mdb m cs;
     cs master = Some (cap.ReplyCap t True);
     sl\<in>descendants_of master m; sl'\<in>descendants_of master m \<rbrakk>
   \<Longrightarrow> sl = sl'"
  by (simp add: unique_reply_caps_def reply_masters_mdb_def is_cap_simps
           del: split_paired_All)

lemma valid_arch_objsI [intro?]:
  "(\<And>p ao. \<lbrakk> (\<exists>\<rhd> p) s; ko_at (ArchObj ao) p s \<rbrakk> \<Longrightarrow> valid_arch_obj ao s) \<Longrightarrow> valid_arch_objs s"
  by (simp add: valid_arch_objs_def)

(* FIXME: duplicated with caps_of_state_valid_cap *)
lemmas caps_of_state_valid =  caps_of_state_valid_cap

lemma vs_lookup1_stateI2:
  assumes 1: "(r \<rhd>1 r') s"
  assumes ko: "\<And>ko. \<lbrakk> ko_at ko (snd r) s; vs_refs ko \<noteq> {} \<rbrakk> \<Longrightarrow> obj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') (snd r) s'"
  shows "(r \<rhd>1 r') s'" using 1 ko
  by (fastforce simp: obj_at_def vs_lookup1_def)

lemma valid_reply_mastersD:
  "\<lbrakk> cte_wp_at (op = (cap.ReplyCap t True)) p s; valid_reply_masters s \<rbrakk>
   \<Longrightarrow> p = (t, tcb_cnode_index 2)"
  by (simp add: valid_reply_masters_def del: split_paired_All)

lemma valid_cap_aligned:
  "s \<turnstile> cap \<Longrightarrow> cap_aligned cap"
  by (simp add: valid_cap_def)

lemma valid_pspace_vo [elim!]:
  "valid_pspace s \<Longrightarrow> valid_objs s"
  by (simp add: valid_pspace_def)

lemma pred_tcb_at_conj_strg:
  "pred_tcb_at proj P t s \<and> pred_tcb_at proj Q t s \<longrightarrow> pred_tcb_at proj (\<lambda>a. P a \<and> Q a) t s"
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma real_cte_at_typ_valid:
  "\<lbrace>typ_at (ACapTable (length (snd p))) (fst p)\<rbrace>
     f
   \<lbrace>\<lambda>rv. typ_at (ACapTable (length (snd p))) (fst p)\<rbrace>
   \<Longrightarrow> \<lbrace>real_cte_at p\<rbrace> f \<lbrace>\<lambda>rv. real_cte_at p\<rbrace>"
  by (simp add: cap_table_at_typ)

lemma dmo_aligned:
  "\<lbrace>pspace_aligned\<rbrace> do_machine_op f \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: pspace_aligned_def)
  done

lemma cte_wp_at_eqD2:
  "\<lbrakk>cte_wp_at (op = c) p s; cte_wp_at P p s \<rbrakk> \<Longrightarrow> P c"
  by (auto elim!: cte_wp_atE split: split_if_asm)

lemma not_pred_tcb:
  "(\<not>pred_tcb_at proj P t s) = (\<not>tcb_at t s \<or> pred_tcb_at proj (\<lambda>a. \<not>P a) t s)"
  apply (simp add: pred_tcb_at_def obj_at_def is_tcb_def)
  apply (auto split: Structures_A.kernel_object.splits)
  done

lemma vs_lookupI:
  "\<lbrakk> ref' \<in> vs_asid_refs (arm_asid_table (arch_state s));
     (ref',(ref,p)) \<in> (vs_lookup1 s)^*  \<rbrakk> \<Longrightarrow>
  (ref \<rhd> p) s"
  by (simp add: vs_lookup_def) blast

lemma vs_lookup1_trans_is_append':
  "(a, b) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> \<exists>zs. fst b = zs @ fst a"
  by (erule rtrancl_induct) (auto dest!: vs_lookup1D)

lemma vs_lookup1_trans_is_append:
  "((xs, a), (ys, b)) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> \<exists>zs. ys = zs @ xs"
  by (drule vs_lookup1_trans_is_append') auto

lemma vs_lookup_trans_ptr_eq':
  "(a, b) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> fst a = fst b \<longrightarrow> snd b = snd a"
  apply (erule rtrancl_induct)
   apply simp
  apply clarsimp
  apply (cases a)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (frule vs_lookup1_trans_is_append)
  apply simp
  done

lemma vs_lookup_trans_ptr_eq:
  "((r,p), (r,p')) \<in> (vs_lookup1 s)\<^sup>* \<Longrightarrow> p = p'"
  by (drule vs_lookup_trans_ptr_eq') simp

lemma vs_lookup_atD:
  "([VSRef (ucast asid) None] \<rhd> p) s \<Longrightarrow> arm_asid_table (arch_state s) asid = Some p"
  apply (simp add: vs_lookup_def)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule rtranclD)
  apply (erule disjE)
   apply (clarsimp simp: up_ucast_inj_eq)
  apply clarsimp
  apply (drule tranclD2)
  apply (clarsimp simp: up_ucast_inj_eq)
  apply (drule vs_lookup1D)
  apply (clarsimp simp: vs_refs_def)
  apply (clarsimp split: split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  done

lemma vs_lookup_atE:
  "([VSRef (ucast asid) None] \<rhd> p) s \<Longrightarrow> (arm_asid_table (arch_state s) asid = Some p \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast dest: vs_lookup_atD)

lemma vs_lookup_2ConsD:
  "((v # v' # vs) \<rhd> p) s \<Longrightarrow> \<exists>p'. ((v'#vs) \<rhd> p') s \<and> ((v' # vs,p') \<rhd>1 (v # v' # vs, p)) s"
  apply (clarsimp simp: vs_lookup_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_asid_refs_def)
  apply (fastforce simp: vs_lookup1_def)
  done

lemma only_idle_arch [iff]:
  "only_idle (arch_state_update f s) = only_idle s"
  by (simp add: only_idle_def)

(* TODO: move to Wellform before the instantiation. should be instantiated retroactively, but isn't. *)
(* FIXME: would be nice to be in the iff-set. *)
lemma (in pspace_update_eq) state_refs_update:
  "state_refs_of (f s) = state_refs_of s"
  by (simp add: state_refs_of_def pspace cong: option.case_cong)

declare more_update.state_refs_update[iff]

lemma zombies_final_arch_update [iff]:
  "zombies_final (arch_state_update f s) = zombies_final s"
  by (simp add: zombies_final_def is_final_cap'_def)

lemma zombies_final_more_update [iff]:
  "zombies_final (trans_state f s) = zombies_final s"
  by (simp add: zombies_final_def is_final_cap'_def)

lemma state_refs_arch_update [iff]:
  "state_refs_of (arch_state_update f s) = state_refs_of s"
  by (simp add: state_refs_of_def)

lemma valid_global_refs_asid_table_udapte [iff]:
  "valid_global_refs (s\<lparr>arch_state := arm_asid_table_update f (arch_state s)\<rparr>) =
  valid_global_refs s"
  by (simp add: valid_global_refs_def global_refs_def)

lemma pspace_in_kernel_window_arch_update[simp]:
  "arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
     \<Longrightarrow> pspace_in_kernel_window (arch_state_update f s) = pspace_in_kernel_window s"
  by (simp add: pspace_in_kernel_window_def)

lemma valid_global_refs_more_update[iff]:
  "valid_global_refs (trans_state f s) = valid_global_refs s"
  by (simp add: valid_global_refs_def global_refs_def)

lemma valid_irq_states_more_update[iff]:
  "valid_irq_states (trans_state f s) = valid_irq_states s"
  by (simp add: valid_irq_states_def)

lemma valid_ioc_arch_state_update[iff]:
  "valid_ioc (arch_state_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

lemma valid_ioc_more_update[iff]:
  "valid_ioc (trans_state f s) = valid_ioc s"
  by (simp add: valid_ioc_def)
lemma valid_ioc_interrupt_states_update[iff]:
  "valid_ioc (interrupt_states_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)
lemma valid_ioc_machine_state_update[iff]:
  "valid_ioc (machine_state_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)
lemma valid_ioc_cur_thread_update[iff]:
  "valid_ioc (cur_thread_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

lemma vms_ioc_update[iff]:
  "valid_machine_state (is_original_cap_update f s::'z::state_ext state) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

lemma valid_machine_state_more_update[iff]:
  "valid_machine_state (trans_state f s) = valid_machine_state s"
  by (simp add: valid_machine_state_def)

lemma only_idle_lift_weak:
  assumes "\<And>Q P t. \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace> f \<lbrace>\<lambda>_ s. Q (st_tcb_at P t s)\<rbrace>"
  assumes "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>only_idle\<rbrace> f \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: only_idle_def)
  apply (rule hoare_vcg_all_lift)
  apply (rule hoare_lift_Pf [where f="idle_thread"])
   apply (rule assms)+
  done

lemma only_idle_lift:
  assumes T: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  assumes s: "\<And>P t. \<lbrace>st_tcb_at P t\<rbrace> f \<lbrace>\<lambda>_. st_tcb_at P t\<rbrace>"
  assumes i: "\<And>P. \<lbrace>\<lambda>s. P (idle_thread s)\<rbrace> f \<lbrace>\<lambda>_ s. P (idle_thread s)\<rbrace>"
  shows "\<lbrace>only_idle\<rbrace> f \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: only_idle_def)
  apply (rule hoare_vcg_all_lift)
  apply (subst imp_conv_disj not_pred_tcb)+ 
  apply (rule hoare_vcg_disj_lift)+
    apply (simp add: tcb_at_typ)
    apply (rule T)
   apply (rule s)
  apply (rule hoare_lift_Pf [where f="idle_thread"])
   apply (rule assms)+
  done

lemmas vs_cap_ref_simps =
       vs_cap_ref_def [split_simps cap.split arch_cap.split vmpage_size.split]
lemmas table_cap_ref_simps =
       table_cap_ref_def [split_simps cap.split arch_cap.split]

lemma table_cap_ref_vs_cap_ref_eq:
  "table_cap_ref cap = Some ref \<Longrightarrow> table_cap_ref cap' = Some ref \<Longrightarrow>
   vs_cap_ref cap = vs_cap_ref cap'"
  by (auto simp: table_cap_ref_def vs_cap_ref_simps
          split: cap.splits arch_cap.splits option.splits)

lemma vs_cap_ref_eq_imp_table_cap_ref_eq:
  "is_pg_cap cap = is_pg_cap cap' \<Longrightarrow> vs_cap_ref cap = vs_cap_ref cap'
   \<Longrightarrow> table_cap_ref cap = table_cap_ref cap'"
  by (auto simp: is_cap_simps vs_cap_ref_def table_cap_ref_simps
          split: cap.splits arch_cap.splits vmpage_size.splits option.splits)

lemma valid_arch_objs_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
      and y: "\<And>ao p. \<lbrace>\<lambda>s. \<not> ko_at (ArchObj ao) p s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> ko_at (ArchObj ao) p s\<rbrace>"
  shows      "\<lbrace>valid_arch_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_arch_objs\<rbrace>"
  apply (simp add: valid_arch_objs_def)
  apply (wp hoare_vcg_all_lift hoare_convert_imp [OF x]
            hoare_convert_imp [OF y] valid_arch_obj_typ z)
  done

lemma valid_validate_vm_rights[simp]:
  "validate_vm_rights rs \<in> valid_vm_rights"
and validate_vm_rights_subseteq[simp]:
  "validate_vm_rights rs \<subseteq> rs"
and validate_vm_rights_simps[simp]:
  "validate_vm_rights vm_read_write = vm_read_write"
  "validate_vm_rights vm_read_only = vm_read_only"
  "validate_vm_rights vm_kernel_only = vm_kernel_only"
  by (simp_all add: validate_vm_rights_def valid_vm_rights_def
                    vm_read_write_def vm_read_only_def vm_kernel_only_def)

lemma validate_vm_rights_inter: (* NOTE: unused *)
  "validate_vm_rights (validate_vm_rights fun \<inter> msk) =
   validate_vm_rights (fun \<inter> msk)"
  by (simp add: validate_vm_rights_def vm_read_write_def vm_read_only_def
              vm_kernel_only_def)

lemma validate_vm_rights_def':
  "validate_vm_rights rs =
   (THE rs'. rs' \<subseteq> rs \<and> rs' : valid_vm_rights \<and>
     (\<forall>rs''. rs'' \<subseteq> rs \<longrightarrow> rs'' : valid_vm_rights \<longrightarrow> rs'' \<subseteq> rs'))"
  apply (rule the_equality[symmetric])
   apply  (auto simp add: validate_vm_rights_def valid_vm_rights_def
                       vm_read_write_def vm_read_only_def vm_kernel_only_def)[1]
  apply (simp add: validate_vm_rights_def valid_vm_rights_def
                 vm_read_write_def vm_read_only_def vm_kernel_only_def)
  apply safe
            apply simp+
       apply (drule_tac x="{AllowRead, AllowWrite}" in spec, simp+)
    apply (drule_tac x="{AllowRead, AllowWrite}" in spec, simp+)
   apply (drule_tac x="{AllowRead, AllowWrite}" in spec, simp+)
  apply (drule_tac x="{AllowRead}" in spec, simp)
  done

lemma validate_vm_rights_eq[simp]:
  "rs : valid_vm_rights \<Longrightarrow> validate_vm_rights rs = rs"
  by (auto simp add: validate_vm_rights_def valid_vm_rights_def
                     vm_read_write_def vm_read_only_def vm_kernel_only_def)

lemma cap_rights_update_id [intro!, simp]:
  "wellformed_cap c \<Longrightarrow> cap_rights_update (cap_rights c) c = c"
  unfolding cap_rights_update_def
           acap_rights_update_def
  by (cases c) (auto simp: wellformed_cap_simps split: arch_cap.splits)

lemma cap_mask_UNIV [simp]:
  "wellformed_cap c \<Longrightarrow> mask_cap UNIV c = c"
by (simp add: mask_cap_def)

lemma wf_empty_bits:
  "well_formed_cnode_n bits (empty_cnode bits)"
  by (simp add: well_formed_cnode_n_def empty_cnode_def dom_def)

lemma well_formed_cnode_valid_cs_size:
  "valid_cs_size bits s \<Longrightarrow> well_formed_cnode_n bits s"
  by (clarsimp simp: valid_cs_size_def)

lemma empty_cnode_bits:
  "obj_bits (CNode n (empty_cnode n)) = 4 + n"
  by (simp add: wf_empty_bits cte_level_bits_def)

lemma irq_revocableD:
  "\<lbrakk> cs p = Some cap.IRQControlCap; irq_revocable (is_original_cap s) cs \<rbrakk> \<Longrightarrow> is_original_cap s p"
  by (fastforce simp add: irq_revocable_def simp del: split_paired_All)

lemma invs_valid_stateI [elim!]:
  "invs s \<Longrightarrow> valid_state s"
  by (simp add: invs_def)

lemma tcb_at_invs [elim!]:
  "invs s \<Longrightarrow> tcb_at (cur_thread s) s"
  by (simp add: invs_def cur_tcb_def)

lemma invs_valid_objs [elim!]:
  "invs s \<Longrightarrow> valid_objs s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_psp_aligned [elim!]:
  "invs s \<Longrightarrow> pspace_aligned s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_mdb [elim!]:
  "invs s \<Longrightarrow> valid_mdb s"
  by (simp add: invs_def valid_state_def)

lemma invs_mdb_cte [elim!]:
  "invs s \<Longrightarrow> mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)"
  by (simp add: invs_def valid_state_def valid_mdb_def)

lemma invs_valid_pspace [elim!]:
  "invs s \<Longrightarrow> valid_pspace s"
  by (simp add: invs_def valid_state_def)

lemma invs_arch_state [elim!]:
  "invs s \<Longrightarrow> valid_arch_state s"
  by (simp add: invs_def valid_state_def)

lemma invs_cur [elim!]:
  "invs s \<Longrightarrow> cur_tcb s"
  by (simp add: invs_def)

lemma invs_distinct [elim!]:
  "invs s \<Longrightarrow> pspace_distinct s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_iflive [elim!]:
  "invs s \<Longrightarrow> if_live_then_nonz_cap s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_sym_refs [elim!]:
  "invs s \<Longrightarrow> sym_refs (state_refs_of s)"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma invs_valid_reply_caps [elim!]:
  "invs s \<Longrightarrow> valid_reply_caps s"
  by (simp add: invs_def valid_state_def)

lemma invs_valid_reply_masters [elim!]:
  "invs s \<Longrightarrow> valid_reply_masters s"
  by (simp add: invs_def valid_state_def)

lemma invs_vobjs_strgs:
  "invs s \<longrightarrow> valid_objs s"
  by auto

lemma invs_valid_global_refs [elim!]:
  "invs s \<Longrightarrow> valid_global_refs s"
  by (simp add: invs_def valid_state_def)

lemma invs_zombies [elim!]:
  "invs s \<Longrightarrow> zombies_final s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma objs_valid_tcb_ctable:
  "\<lbrakk>valid_objs s; get_tcb t s = Some tcb\<rbrakk> \<Longrightarrow> s \<turnstile> tcb_ctable tcb"
  apply (clarsimp simp: get_tcb_def split: option.splits Structures_A.kernel_object.splits)
  apply (erule cte_wp_valid_cap[rotated])
  apply (rule cte_wp_at_tcbI[where t="(a, b)" for a b, where b3="tcb_cnode_index 0"])
    apply fastforce+
  done

lemma invs_valid_tcb_ctable:
  "\<lbrakk>invs s; get_tcb t s = Some tcb\<rbrakk> \<Longrightarrow> s \<turnstile> tcb_ctable tcb"
  apply (drule invs_valid_stateI)
  apply (clarsimp simp: valid_state_def valid_pspace_def objs_valid_tcb_ctable)
  done

lemma invs_arch_objs [elim!]:
  "invs s \<Longrightarrow> valid_arch_objs s"
  by (simp add: invs_def valid_state_def)

lemma invs_valid_idle[elim!]:
  "invs s \<Longrightarrow> valid_idle s"
  by (fastforce simp: invs_def valid_state_def)


lemma simple_st_tcb_at_state_refs_ofD:
  "st_tcb_at simple t s \<Longrightarrow> bound_tcb_at (\<lambda>x. tcb_bound_refs x = state_refs_of s t) t s"
  by (fastforce simp: pred_tcb_at_def obj_at_def state_refs_of_def)


lemma active_st_tcb_at_state_refs_ofD:
  "st_tcb_at active t s \<Longrightarrow> bound_tcb_at (\<lambda>x. tcb_bound_refs x = state_refs_of s t) t s"
  by (fastforce simp: pred_tcb_at_def obj_at_def state_refs_of_def)

lemma cur_tcb_revokable [iff]:
  "cur_tcb (is_original_cap_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma cur_tcb_arch [iff]:
  "cur_tcb (arch_state_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

lemma invs_pd_caps:
  "invs s \<Longrightarrow> valid_table_caps s"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_valid_vs_lookup[elim!]:
  "invs s \<Longrightarrow> valid_vs_lookup s "
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_valid_global_objs[elim!]:
  "invs s \<Longrightarrow> valid_global_objs s "
  by (clarsimp simp: invs_def valid_state_def)

lemma get_irq_slot_real_cte:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>real_cte_at\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_irq_node_def)
  done

lemma all_invs_but_sym_refs_check:
  "(all_invs_but_sym_refs and sym_refs \<circ> state_refs_of) = invs"
  by (simp add: invs_def valid_state_def valid_pspace_def
                o_def pred_conj_def conj_comms)

lemma invs_unique_table_caps[elim!]:
  "invs s \<Longrightarrow> unique_table_caps (caps_of_state s)"
  by (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)

lemma invs_unique_refs[elim!]:
  "invs s \<Longrightarrow> unique_table_refs (caps_of_state s)"
  by (simp add: invs_def valid_state_def valid_arch_caps_def)

lemma invs_valid_asid_map[elim!]:
  "invs s \<Longrightarrow> valid_asid_map s"
  by (simp add: invs_def valid_state_def)

lemma invs_equal_kernel_mappings[elim!]:
  "invs s \<Longrightarrow> equal_kernel_mappings s"
  by (simp add:invs_def valid_state_def)

lemma invs_valid_irq_node[elim!]:
  "invs s \<Longrightarrow> valid_irq_node s"
  by (simp add: invs_def valid_state_def)

lemma invs_ifunsafe[elim!]:
  "invs s \<Longrightarrow> if_unsafe_then_cap s"
  by (simp add: invs_def valid_state_def valid_pspace_def)

lemma cte_wp_at_cap_aligned:
  "\<lbrakk>cte_wp_at P p s; invs s\<rbrakk> \<Longrightarrow> \<exists>c. P c \<and> cap_aligned c"
  apply (drule (1) cte_wp_at_valid_objs_valid_cap [OF _ invs_valid_objs])
  apply (fastforce simp: valid_cap_def)
  done

lemma cte_wp_at_cap_aligned':
  "\<lbrakk>cte_wp_at (op = cap) p s; invs s\<rbrakk> \<Longrightarrow> cap_aligned cap"
  apply (drule (1) cte_wp_at_valid_objs_valid_cap [OF _ invs_valid_objs])
  apply (fastforce simp: valid_cap_def)
  done

locale invs_locale =
  fixes ex_inv :: "'z::state_ext state \<Rightarrow> bool"
  assumes dmo_ex_inv[wp]: "\<And>f. \<lbrace>invs and ex_inv\<rbrace> do_machine_op f \<lbrace>\<lambda>rv::unit. ex_inv\<rbrace>"
  assumes cap_insert_ex_inv[wp]: "\<And>cap src dest.
  \<lbrace>ex_inv and invs and K (src \<noteq> dest)\<rbrace>
      cap_insert cap src dest
  \<lbrace>\<lambda>_.ex_inv\<rbrace>"
  assumes cap_delete_one_ex_inv[wp]: "\<And>cap.
   \<lbrace>ex_inv and invs\<rbrace> cap_delete_one cap \<lbrace>\<lambda>_.ex_inv\<rbrace>"

  assumes set_endpoint_ex_inv[wp]: "\<And>a b.\<lbrace>ex_inv\<rbrace> set_endpoint a b \<lbrace>\<lambda>_.ex_inv\<rbrace>"
  assumes sts_ex_inv[wp]: "\<And>a b. \<lbrace>ex_inv\<rbrace> set_thread_state a b \<lbrace>\<lambda>_.ex_inv\<rbrace>"

  assumes setup_caller_cap_ex_inv[wp]: "\<And>send receive. \<lbrace>ex_inv and valid_mdb\<rbrace> setup_caller_cap send receive \<lbrace>\<lambda>_.ex_inv\<rbrace>"
  assumes do_ipc_transfer_ex_inv[wp]: "\<And>a b c d e f. \<lbrace>ex_inv and valid_objs and valid_mdb\<rbrace> do_ipc_transfer a b c d e f \<lbrace>\<lambda>_.ex_inv\<rbrace>"

  assumes thread_set_ex_inv[wp]: "\<And>a b. \<lbrace>ex_inv\<rbrace> thread_set a b \<lbrace>\<lambda>_.ex_inv\<rbrace>"


lemma invs_locale_trivial:
  "invs_locale \<top>"
  apply unfold_locales
  apply wp
done

lemma in_dxo_pspaceD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> kheap s' = kheap s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_cdtD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> cdt s' = cdt s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_revokableD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> is_original_cap s' = is_original_cap s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_cur_threadD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> cur_thread s' = cur_thread s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_idle_threadD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> idle_thread s' = idle_thread s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_machine_stateD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> machine_state s' = machine_state s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_irq_nodeD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> interrupt_irq_node s' = interrupt_irq_node s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_interruptD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> interrupt_states s' = interrupt_states s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma in_dxo_archD:
  "((), s') \<in> fst (do_extended_op f s) \<Longrightarrow> arch_state s' = arch_state s"
  by (clarsimp simp: do_extended_op_def select_f_def in_monad)

lemma sym_refs_bound_tcb_atD:
  "\<lbrakk>bound_tcb_at P t s; sym_refs (state_refs_of s)\<rbrakk>
    \<Longrightarrow> \<exists>ts ntfnptr.
        P ntfnptr \<and>
        obj_at (tcb_ntfn_is_bound ntfnptr) t s \<and>
        state_refs_of s t = tcb_st_refs_of ts \<union> tcb_bound_refs ntfnptr \<and>
        (\<forall>(x, tp)\<in>tcb_st_refs_of ts \<union> tcb_bound_refs ntfnptr.
            obj_at (\<lambda>ko. (t, symreftype tp) \<in> refs_of ko) x s)"
  apply (drule bound_tcb_at_state_refs_ofD)
  apply (erule exE)+
  apply (rule_tac x=ts in exI)
  apply (rule_tac x=ntfnptr in exI)
  apply clarsimp
  apply (frule obj_at_state_refs_ofD)
  apply (drule (1)sym_refs_obj_atD)
  apply auto
  done

end
