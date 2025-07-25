(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
The main architecture independent data types and type definitions in
the abstract model.
*)

chapter "Basic Data Structures"

theory Structures_A
imports
  ExecSpec.Structs_B
  Arch_Structs_A
  "ExecSpec.MachineExports"
begin

arch_requalify_types (A)
  aobject_type
  arch_cap
  arch_kernel_obj
  arch_state
  arch_tcb
  aa_type

arch_requalify_consts (A)
  acap_rights
  acap_rights_update
  arch_kobj_size
  arch_obj_size
  aobj_ref
  arch_is_frame_type
  badge_bits
  default_arch_tcb
  arch_tcb_context_get
  arch_tcb_context_set
  arch_tcb_set_registers
  arch_tcb_get_registers
  cte_level_bits
  tcb_bits
  endpoint_bits
  ntfn_bits
  aa_type
  untyped_min_bits
  untyped_max_bits
  msg_label_bits

text \<open>
  User mode can request these objects to be created by retype:
\<close>
datatype apiobject_type =
    Untyped
  | TCBObject
  | EndpointObject
  | NotificationObject
  | CapTableObject
  | ArchObject aobject_type

definition
  is_frame_type :: "apiobject_type \<Rightarrow> bool"
where
  "is_frame_type obj \<equiv> case obj of
        ArchObject aobj \<Rightarrow> arch_is_frame_type aobj
      | _ \<Rightarrow> False"


text \<open>These allow more informative type signatures for IPC operations.\<close>
type_synonym badge = data
type_synonym msg_label = data
type_synonym message = data


text \<open>This type models refences to capability slots. The first element
  of the tuple points to the object the capability is contained in. The second
  element is the index of the slot inside a slot-containing object. The default
  slot-containing object is a cnode, thus the name @{text cnode_index}.
\<close>
type_synonym cnode_index = "bool list"
type_synonym cslot_ptr = "obj_ref \<times> cnode_index"


text \<open>Capabilities. Capabilities represent explicit authority to perform some
action and are required for all system calls. Capabilities to Endpoint,
Notification, Thread and CNode objects allow manipulation of standard kernel
objects. Untyped capabilities allow the creation and removal of kernel objects
from a memory region. Reply capabilities allow sending a one-off message to
a thread waiting for a reply. IRQHandler and IRQControl caps allow a user to
configure the way interrupts on one or all IRQs are handled. Capabilities to
architecture-specific facilities are provided through the @{text arch_cap} type.
Null capabilities are the contents of empty capability slots; they confer no
authority and can be freely replaced. Zombie capabilities are stored when
the deletion of CNode and Thread objects is partially completed; they confer no
authority but cannot be replaced until the deletion is finished.
\<close>

datatype cap
         = NullCap
         | UntypedCap bool obj_ref nat nat
           \<comment> \<open>device flag, pointer, size in bits (i.e. @{text "size = 2^bits"}) and freeIndex (i.e. @{text "freeRef = obj_ref + (freeIndex * 2^4)"})\<close>
         | EndpointCap obj_ref badge cap_rights
         | NotificationCap obj_ref badge cap_rights
         | ReplyCap obj_ref bool cap_rights
         | CNodeCap obj_ref nat "bool list"
           \<comment> \<open>CNode ptr, number of bits translated, guard\<close>
         | ThreadCap obj_ref
         | DomainCap
         | IRQControlCap
         | IRQHandlerCap irq
         | Zombie obj_ref "nat option" nat
           \<comment> \<open>@{text "cnode ptr * nat + tcb or cspace ptr"}\<close>
         | ArchObjectCap (the_arch_cap: arch_cap)

lemmas cap_cases =
  cap.induct[where cap=cap and P="\<lambda>cap'. cap' = cap \<longrightarrow> P cap'" for cap P, simplified, rule_format]

lemmas cap_cases_asm =
cap.induct[where cap=cap and P="\<lambda>cap'. cap = cap' \<longrightarrow> P cap' \<longrightarrow> R" for P R cap,
  simplified, rule_format, rotated -1]

text \<open>The CNode object is an array of capability slots. The domain of the
function will always be the set of boolean lists of some specific length.
Empty slots contain a Null capability.
\<close>
type_synonym cnode_contents = "cnode_index \<Rightarrow> cap option"

text \<open>Various access functions for the cap type are defined for
convenience.\<close>
definition
  the_cnode_cap :: "cap \<Rightarrow> obj_ref \<times> nat \<times> bool list" where
  "the_cnode_cap cap \<equiv>
  case cap of
    CNodeCap oref bits guard \<Rightarrow> (oref, bits, guard)"

primrec (nonexhaustive)
  cap_ep_badge :: "cap \<Rightarrow> badge"
where
  "cap_ep_badge (EndpointCap _ badge _) = badge"
| "cap_ep_badge (NotificationCap _ badge _) = badge"

primrec (nonexhaustive)
  cap_ep_ptr :: "cap \<Rightarrow> badge"
where
  "cap_ep_ptr (EndpointCap obj_ref _ _) = obj_ref"
| "cap_ep_ptr (NotificationCap obj_ref _ _) = obj_ref"

definition
  bits_of :: "cap \<Rightarrow> nat" where
  "bits_of cap \<equiv> case cap of
    UntypedCap _ _ bits _ \<Rightarrow> bits
  | CNodeCap _ radix_bits _ \<Rightarrow> radix_bits"

definition
  free_index_of :: "cap \<Rightarrow> nat" where
  "free_index_of cap \<equiv> case cap of
    UntypedCap _ _ _ free_index \<Rightarrow> free_index"

definition
  is_reply_cap :: "cap \<Rightarrow> bool" where
  "is_reply_cap cap \<equiv> case cap of ReplyCap _ m _ \<Rightarrow> \<not> m | _ \<Rightarrow> False"
definition
  is_master_reply_cap :: "cap \<Rightarrow> bool" where
  "is_master_reply_cap cap \<equiv> case cap of ReplyCap _ m _ \<Rightarrow> m | _ \<Rightarrow> False"
definition
  is_zombie :: "cap \<Rightarrow> bool" where
  "is_zombie cap \<equiv> case cap of Zombie _ _ _ \<Rightarrow> True | _ \<Rightarrow> False"
definition
  is_arch_cap :: "cap \<Rightarrow> bool" where
  "is_arch_cap cap \<equiv> case cap of ArchObjectCap _ \<Rightarrow> True | _ \<Rightarrow> False"

context
notes [[function_internals =true]]
begin

fun is_cnode_cap :: "cap \<Rightarrow> bool"
where
  "is_cnode_cap (CNodeCap _ _ _) = True"
| "is_cnode_cap _                = False"

fun is_thread_cap :: "cap \<Rightarrow> bool"
where
  "is_thread_cap (ThreadCap _) = True"
| "is_thread_cap _             = False"

fun is_domain_cap :: "cap \<Rightarrow> bool"
where
  "is_domain_cap DomainCap = True"
| "is_domain_cap _ = False"

fun is_untyped_cap :: "cap \<Rightarrow> bool"
where
  "is_untyped_cap (UntypedCap _ _ _ _) = True"
| "is_untyped_cap _                  = False"

fun is_ep_cap :: "cap \<Rightarrow> bool"
where
  "is_ep_cap (EndpointCap _ _ _) = True"
| "is_ep_cap _                   = False"

fun is_ntfn_cap :: "cap \<Rightarrow> bool"
where
  "is_ntfn_cap (NotificationCap _ _ _) = True"
| "is_ntfn_cap _                        = False"

primrec (nonexhaustive)
  cap_rights :: "cap \<Rightarrow> cap_rights"
where
  "cap_rights (EndpointCap _ _ cr) = cr"
| "cap_rights (NotificationCap _ _ cr) = cr"
| "cap_rights (ReplyCap _ _ cr) = cr"
| "cap_rights (ArchObjectCap acap) = acap_rights acap"
end

text \<open>Various update functions for cap data common to various kinds of
cap are defined here.\<close>
definition
  cap_rights_update :: "cap_rights \<Rightarrow> cap \<Rightarrow> cap" where
  "cap_rights_update cr' cap \<equiv>
   case cap of
     EndpointCap oref badge cr \<Rightarrow> EndpointCap oref badge cr'
   | NotificationCap oref badge cr
     \<Rightarrow> NotificationCap oref badge (cr' - {AllowGrant, AllowGrantReply})
   | ReplyCap t m cr \<Rightarrow> ReplyCap t m (cr' - {AllowRead, AllowGrantReply} \<union> {AllowWrite})
   | ArchObjectCap acap \<Rightarrow> ArchObjectCap (acap_rights_update cr' acap)
   | _ \<Rightarrow> cap"

definition
  badge_update :: "badge \<Rightarrow> cap \<Rightarrow> cap" where
  "badge_update data cap \<equiv>
   case cap of
     EndpointCap oref badge cr \<Rightarrow> EndpointCap oref (data && mask badge_bits) cr
   | NotificationCap oref badge cr \<Rightarrow> NotificationCap oref (data && mask badge_bits) cr
   | _ \<Rightarrow> cap"


definition
  mask_cap :: "cap_rights \<Rightarrow> cap \<Rightarrow> cap" where
  "mask_cap rights cap \<equiv> cap_rights_update (cap_rights cap \<inter> rights) cap"

section \<open>Message Info\<close>

text \<open>The message info is the first thing interpreted on a user system call
and determines the structure of the message the user thread is sending either to
another user or to a system service. It is also passed to user threads receiving
a message to indicate the structure of the message they have received. The
@{text mi_length} parameter is the number of data words in the body of the
message. The @{text mi_extra_caps} parameter is the number of caps to be passed
together with the message. The @{text mi_caps_unwrapped} parameter is a bitmask
allowing threads receiving a message to determine how extra capabilities were
transferred. The @{text mi_label} parameter is transferred directly from sender
to receiver as part of the message.
\<close>

datatype message_info =
  MI (mi_length: length_type)
     (mi_extra_caps: length_type)
     (mi_caps_unwrapped: data)
     (mi_label: msg_label)

text \<open>Message infos are encoded to or decoded from a data word.\<close>
primrec
  message_info_to_data :: "message_info \<Rightarrow> data"
where
  "message_info_to_data (MI len exc unw mlabel) =
   (let
        extra = exc << 7;
        unwrapped = unw << 9;
        label = mlabel << 12
    in
       label || extra || unwrapped || len)"

definition
  data_to_message_info :: "data \<Rightarrow> message_info"
where
  "data_to_message_info w \<equiv>
   MI (let v = w && mask 7 in if v > 120 then 120 else v)
      ((w >> 7) && mask 2)
      ((w >> 9) && mask 3)
      ((w >> 12) && mask msg_label_bits)"

section \<open>Kernel Objects\<close>

text \<open>Endpoints are synchronous points of communication for threads. At any
time an endpoint may contain a queue of threads waiting to send, a queue of
threads waiting to receive or be idle. Whenever threads would be waiting to
send and receive simultaneously messages are transferred immediately.
\<close>

datatype endpoint
           = IdleEP
           | SendEP "obj_ref list"
           | RecvEP "obj_ref list"

text \<open>Notifications are sets of binary semaphores (stored in the
\emph{badge word}). Unlike endpoints, threads may choose to block waiting to
receive, but not to send.\<close>

datatype ntfn
           = IdleNtfn
           | WaitingNtfn "obj_ref list"
           | ActiveNtfn badge

record notification =
  ntfn_obj :: ntfn
  ntfn_bound_tcb :: "obj_ref option"


definition
  default_ep :: endpoint where
  "default_ep \<equiv> IdleEP"

definition
  default_ntfn :: ntfn where
  "default_ntfn \<equiv> IdleNtfn"

definition
  default_notification :: notification where
  "default_notification \<equiv> \<lparr>
     ntfn_obj = default_ntfn,
     ntfn_bound_tcb = None \<rparr>"


text \<open>Thread Control Blocks are the in-kernel representation of a thread.

Threads which can execute are either in the Running state for normal execution,
in the Restart state if their last operation has not completed yet or in the
IdleThreadState for the unique system idle thread. Threads can also be blocked
waiting for any of the different kinds of system messages. The Inactive state
indicates that the TCB is not currently used by a running thread.

TCBs also contain some special-purpose capability slots. The CTable slot is a
capability to a CNode through which the thread accesses capabilities with which
to perform system calls. The VTable slot is a capability to a virtual address
space (an architecture-specific capability type) in which the thread runs. If
the thread has issued a Reply cap to another thread and is awaiting a reply,
that cap will have a "master" Reply cap as its parent in the Reply slot. The
Caller slot is used to initially store any Reply cap issued to this thread. The
IPCFrame slot stores a capability to a memory frame (an architecture-specific
capability type) through which messages will be sent and received.

If the thread has encountered a fault and is waiting to send it to its
supervisor the fault is stored in @{text tcb_fault}. The user register file is
stored in @{text tcb_context}, the pointer to the cap in the IPCFrame slot in
@{text tcb_ipc_buffer} and the identity of the Endpoint cap through which faults
are to be sent in @{text tcb_fault_handler}.
\<close>

record sender_payload =
 sender_badge           :: badge
 sender_can_grant       :: bool
 sender_can_grant_reply :: bool
 sender_is_call         :: bool

record receiver_payload =
 receiver_can_grant :: bool

datatype thread_state
  = Running
  | Inactive
  | Restart
  | BlockedOnReceive obj_ref receiver_payload
  | BlockedOnSend obj_ref sender_payload
  | BlockedOnReply
  | BlockedOnNotification obj_ref
  | IdleThreadState

type_synonym priority = word8

type_synonym domain = word8

type_synonym tcb_flags = "tcb_flag set"

text \<open>
  The set of TCB flags may be larger than the set of configured flags (e.g. FpuDisabled is only
  used when FPU is configured), hence we only convert flags in `tcbFlagMask`. \<close>
definition word_to_tcb_flags :: "machine_word \<Rightarrow> tcb_flags" where
  "word_to_tcb_flags w \<equiv> {flag. w && tcbFlagToWord flag && tcbFlagMask \<noteq> 0}"

definition tcb_flags_to_word :: "tcb_flags \<Rightarrow> machine_word" where
  "tcb_flags_to_word flags \<equiv> THE w. word_to_tcb_flags w = flags \<and> w && ~~ tcbFlagMask = 0"

record tcb =
 tcb_ctable        :: cap
 tcb_vtable        :: cap
 tcb_reply         :: cap
 tcb_caller        :: cap
 tcb_ipcframe      :: cap
 tcb_state         :: thread_state
 tcb_fault_handler :: cap_ref
 tcb_ipc_buffer    :: vspace_ref
 tcb_fault         :: "fault option"
 tcb_bound_notification :: "obj_ref option"
 tcb_mcpriority    :: priority
 tcb_priority      :: priority
 tcb_time_slice    :: nat
 tcb_domain        :: domain
 tcb_flags         :: tcb_flags
 tcb_arch          :: arch_tcb (* arch_tcb must have a field for user context *)


text \<open>Determines whether a thread in a given state may be scheduled.\<close>
primrec
  runnable :: "Structures_A.thread_state \<Rightarrow> bool"
where
  "runnable (Running)               = True"
| "runnable (Inactive)              = False"
| "runnable (Restart)               = True"
| "runnable (BlockedOnReceive x y)  = False"
| "runnable (BlockedOnSend x y)     = False"
| "runnable (BlockedOnNotification x) = False"
| "runnable (IdleThreadState)       = False"
| "runnable (BlockedOnReply)        = False"


definition default_domain :: "domain" where
  "default_domain \<equiv> minBound"

definition default_priority :: "priority" where
  "default_priority \<equiv> minBound"

definition default_tcb :: "domain \<Rightarrow> tcb" where
  "default_tcb d \<equiv> \<lparr>
      tcb_ctable   = NullCap,
      tcb_vtable   = NullCap,
      tcb_reply    = NullCap,
      tcb_caller   = NullCap,
      tcb_ipcframe = NullCap,
      tcb_state    = Inactive,
      tcb_fault_handler = to_bl (0::machine_word),
      tcb_ipc_buffer = 0,
      tcb_fault      = None,
      tcb_bound_notification  = None,
      tcb_mcpriority = minBound,
      tcb_priority   = default_priority,
      tcb_time_slice = timeSlice,
      tcb_domain     = d,
      tcb_flags      = {},
      tcb_arch       = default_arch_tcb\<rparr>"

text \<open>
All kernel objects are CNodes, TCBs, Endpoints, Notifications or architecture
specific.
\<close>
datatype kernel_object
         = CNode nat cnode_contents \<comment> \<open>size in bits, and contents\<close>
         | TCB tcb
         | Endpoint endpoint
         | Notification notification
         | ArchObj (the_arch_obj: arch_kernel_obj)

lemmas kernel_object_cases =
  kernel_object.induct[where kernel_object=x and P="\<lambda>x'. x = x' \<longrightarrow> P x'" for x P, simplified, rule_format]

lemmas kernel_object_cases_asm =
kernel_object.induct[where kernel_object=x and P="\<lambda>x'. x = x' \<longrightarrow> P x' \<longrightarrow> R" for P R x,
  simplified, rule_format, rotated -1]

definition aobj_of :: "kernel_object \<Rightarrow> arch_kernel_obj option"
  where
  "aobj_of ko \<equiv> case ko of ArchObj aobj \<Rightarrow> Some aobj | _ \<Rightarrow> None"

text \<open>Checks whether a cnode's contents are well-formed.\<close>

definition
  well_formed_cnode_n :: "nat \<Rightarrow> cnode_contents \<Rightarrow> bool" where
 "well_formed_cnode_n n \<equiv> \<lambda>cs. dom cs = {x. length x = n}"

primrec
  obj_bits :: "kernel_object \<Rightarrow> nat"
where
  "obj_bits (CNode sz cs) = cte_level_bits + sz"
| "obj_bits (TCB t) = tcb_bits"
| "obj_bits (Endpoint ep) = endpoint_bits"
| "obj_bits (Notification ntfn) = ntfn_bits"
| "obj_bits (ArchObj ao) = arch_kobj_size ao"

primrec (nonexhaustive)
  obj_size :: "cap \<Rightarrow> machine_word"
where
  "obj_size NullCap = 0"
| "obj_size (UntypedCap dev r bits f) = 1 << bits"
| "obj_size (EndpointCap r b R) = 1 << obj_bits (Endpoint undefined)"
| "obj_size (NotificationCap r b R) = 1 << obj_bits (Notification undefined)"
| "obj_size (CNodeCap r bits g) = 1 << (cte_level_bits + bits)"
| "obj_size (ThreadCap r) = 1 << obj_bits (TCB undefined)"
| "obj_size (Zombie r zb n) = (case zb of None \<Rightarrow> 1 << obj_bits (TCB undefined)
                                        | Some n \<Rightarrow> 1 << (cte_level_bits + n))"
| "obj_size (ArchObjectCap a) = 1 << arch_obj_size a"


text \<open>Object types:\<close>

datatype a_type =
    ATCB
  | AEndpoint
  | ANTFN
  | ACapTable nat
  | AGarbage nat \<comment> \<open>number of bytes of garbage\<close>
  | AArch aa_type

definition
  a_type :: "kernel_object \<Rightarrow> a_type"
where
 "a_type ob \<equiv> case ob of
           CNode sz cspace           \<Rightarrow> if well_formed_cnode_n sz cspace
                                        then ACapTable sz else AGarbage (cte_level_bits + sz)
         | TCB tcb                   \<Rightarrow> ATCB
         | Endpoint endpoint         \<Rightarrow> AEndpoint
         | Notification notification \<Rightarrow> ANTFN
         | ArchObj ao                \<Rightarrow> AArch (aa_type ao)"


section \<open>Kernel State\<close>

text \<open>The kernel's heap is a partial function containing kernel objects.\<close>
type_synonym kheap = "obj_ref \<Rightarrow> kernel_object option"

text \<open>
Capabilities are created either by cloning an existing capability or by creating
a subordinate capability from it. This results in a capability derivation tree
or CDT. The kernel provides a Revoke operation which deletes all capabilities
derived from one particular capability. To support this, the kernel stores the
CDT explicitly. It is here stored as a tree, a partial mapping from
capability slots to parent capability slots.
\<close>
type_synonym cdt = "cslot_ptr \<Rightarrow> cslot_ptr option"

datatype irq_state =
   IRQInactive
 | IRQSignal
 | IRQTimer
 | IRQReserved

text \<open>The current scheduler action, which is part of the scheduling state.\<close>
datatype scheduler_action =
    resume_cur_thread
  | switch_thread (sch_act_target : obj_ref)
  | choose_new_thread

type_synonym ready_queue = "obj_ref list"

text \<open>The kernel state includes a heap, a capability derivation tree
(CDT), a bitmap used to determine if a capability is the original
capability to that object, a pointer to the current thread, a pointer
to the system idle thread, the state of the underlying machine,
per-irq pointers to cnodes (each containing one notification through which
interrupts are delivered), an array recording which
interrupts are used for which purpose, and the state of the
architecture-specific kernel module.

Note: for each irq, @{text "interrupt_irq_node irq"} points to a cnode which
can contain the notification cap through which interrupts are delivered. In
C, this all lives in a single array. In the abstract spec though, to prove
security, we can't have a single object accessible by everyone. Hence the need
to separate irq handlers.
\<close>
record abstract_state =
  kheap              :: kheap
  cdt                :: cdt
  is_original_cap    :: "cslot_ptr \<Rightarrow> bool"
  cur_thread         :: obj_ref
  idle_thread        :: obj_ref
  scheduler_action   :: scheduler_action
  domain_list        :: "(domain \<times> machine_word) list"
  domain_index       :: nat
  cur_domain         :: domain
  domain_time        :: "machine_word"
  ready_queues       :: "domain \<Rightarrow> priority \<Rightarrow> ready_queue"
  machine_state      :: machine_state
  interrupt_irq_node :: "irq \<Rightarrow> obj_ref"
  interrupt_states   :: "irq \<Rightarrow> irq_state"
  arch_state         :: arch_state

text \<open>The following record extends the abstract kernel state with extra
state of type @{typ "'a"}. The specification operates over states of
this extended type. By choosing an appropriate concrete type for @{typ "'a"}
we may obtain different \emph{instantiations} of the kernel specifications
at differing levels of abstraction. See \autoref{c:ext-spec} for further
information.
\<close>
record 'a state = abstract_state + exst :: 'a

section \<open>Helper functions\<close>

text \<open>This wrapper lifts monadic operations on the underlying machine state to
monadic operations on the kernel state.\<close>
definition
  do_machine_op :: "(machine_state, 'a) nondet_monad \<Rightarrow> ('z state, 'a) nondet_monad"
where
 "do_machine_op mop \<equiv> do
    ms \<leftarrow> gets machine_state;
    (r, ms') \<leftarrow> select_f (mop ms);
    modify (\<lambda>state. state \<lparr> machine_state := ms' \<rparr>);
    return r
  od"

text \<open>This function generates the cnode indices used when addressing the
capability slots within a TCB.
\<close>
definition
  tcb_cnode_index :: "nat \<Rightarrow> cnode_index" where
  "tcb_cnode_index n \<equiv> to_bl (of_nat n :: 3 word)"

text \<open>Zombie capabilities store the bit size of the CNode cap they were
created from or None if they were created from a TCB cap. This function
decodes the bit-length of cnode indices into the relevant kernel objects.
\<close>
definition
  zombie_cte_bits :: "nat option \<Rightarrow> nat" where
 "zombie_cte_bits N \<equiv> case N of Some n \<Rightarrow> n | None \<Rightarrow> 3"

lemma zombie_cte_bits_simps[simp]:
 "zombie_cte_bits (Some n) = n"
 "zombie_cte_bits None     = 3"
  by (simp add: zombie_cte_bits_def)+

text \<open>The first capability slot of the relevant kernel object.\<close>
primrec (nonexhaustive)
  first_cslot_of :: "cap \<Rightarrow> cslot_ptr"
where
  "first_cslot_of (ThreadCap oref) = (oref, tcb_cnode_index 0)"
| "first_cslot_of (CNodeCap oref bits g) = (oref, replicate bits False)"
| "first_cslot_of (Zombie oref bits n) = (oref, replicate (zombie_cte_bits bits) False)"

text \<open>The set of all objects referenced by a capability.\<close>
primrec
  obj_refs :: "cap \<Rightarrow> obj_ref set"
where
  "obj_refs NullCap = {}"
| "obj_refs (ReplyCap r m cr) = {}"
| "obj_refs IRQControlCap = {}"
| "obj_refs (IRQHandlerCap irq) = {}"
| "obj_refs (UntypedCap dev r s f) = {}"
| "obj_refs (CNodeCap r bits guard) = {r}"
| "obj_refs (EndpointCap r b cr) = {r}"
| "obj_refs (NotificationCap r b cr) = {r}"
| "obj_refs (ThreadCap r) = {r}"
| "obj_refs DomainCap = {}"
| "obj_refs (Zombie ptr b n) = {ptr}"
| "obj_refs (ArchObjectCap x) = set_option (aobj_ref x)"

text \<open>
  The partial definition below is sometimes easier to work with.
  It also provides cases for UntypedCap and ReplyCap which are not
  true object references in the sense of the other caps.
\<close>
primrec (nonexhaustive)
  obj_ref_of :: "cap \<Rightarrow> obj_ref"
where
  "obj_ref_of (UntypedCap dev r s f) = r"
| "obj_ref_of (ReplyCap r m cr) = r"
| "obj_ref_of (CNodeCap r bits guard) = r"
| "obj_ref_of (EndpointCap r b cr) = r"
| "obj_ref_of (NotificationCap r b cr) = r"
| "obj_ref_of (ThreadCap r) = r"
| "obj_ref_of (Zombie ptr b n) = ptr"
| "obj_ref_of (ArchObjectCap x) = the (aobj_ref x)"

primrec (nonexhaustive)
  cap_bits_untyped :: "cap \<Rightarrow> nat"
where
  "cap_bits_untyped (UntypedCap dev r s f) = s"

definition tcb_cnode_map :: "tcb \<Rightarrow> cnode_index \<Rightarrow> cap option"
  where
  "tcb_cnode_map tcb \<equiv>
   [tcb_cnode_index 0 \<mapsto> tcb_ctable tcb,
    tcb_cnode_index 1 \<mapsto> tcb_vtable tcb,
    tcb_cnode_index 2 \<mapsto> tcb_reply tcb,
    tcb_cnode_index 3 \<mapsto> tcb_caller tcb,
    tcb_cnode_index 4 \<mapsto> tcb_ipcframe tcb]"

definition cap_of :: "kernel_object \<Rightarrow> cnode_index \<Rightarrow> cap option"
  where
  "cap_of kobj \<equiv> case kobj of CNode _ cs \<Rightarrow> cs | TCB tcb \<Rightarrow> tcb_cnode_map tcb | _ \<Rightarrow> Map.empty"

text \<open>The set of all caps contained in a kernel object.\<close>

definition
  caps_of :: "kernel_object \<Rightarrow> cap set" where
  "caps_of kobj \<equiv> ran (cap_of kobj)"

section "Cap transfers"

record captransfer =
  ct_receive_root :: cap_ref
  ct_receive_index :: cap_ref
  ct_receive_depth :: data

text \<open>A thread's IPC buffer capability must be to a page that is capable of
containing the IPC buffer without the end of the buffer spilling into another
page.\<close>
definition cap_transfer_data_size :: nat
  where
  "cap_transfer_data_size \<equiv> 3"

definition msg_max_length :: nat
  where
  "msg_max_length \<equiv> 120"

definition msg_max_extra_caps :: nat
  where
  "msg_max_extra_caps \<equiv> 3"

definition max_ipc_length :: nat
  where
  "max_ipc_length \<equiv> cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2"

definition msg_align_bits :: nat
  where
  "msg_align_bits \<equiv> word_size_bits + (LEAST n. max_ipc_length \<le> 2 ^ n)"

lemma msg_align_bits':
  "msg_align_bits = word_size_bits + 7"
proof -
  have "(LEAST n. (cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2) \<le> 2 ^ n) = 7"
  proof (rule Least_equality)
    show "(cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2)  \<le> 2 ^ 7"
      by (simp add: cap_transfer_data_size_def msg_max_length_def msg_max_extra_caps_def)
  next
    fix y
    assume "(cap_transfer_data_size + msg_max_length + msg_max_extra_caps + 2) \<le> 2 ^ y"
    hence "(2 :: nat) ^ 7 \<le> 2 ^ y"
      by (simp add: cap_transfer_data_size_def msg_max_length_def msg_max_extra_caps_def)
    thus "7 \<le> y"
      by (rule power_le_imp_le_exp [rotated], simp)
  qed
  thus ?thesis unfolding msg_align_bits_def max_ipc_length_def by simp
qed

end
