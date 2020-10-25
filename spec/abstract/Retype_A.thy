(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
Retyping and untyped invocation
*)

chapter "Retyping and Untyped Invocations"

theory Retype_A
imports
  CSpaceAcc_A
  "./$L4V_ARCH/ArchVSpaceAcc_A"
  Invocations_A
  "./$L4V_ARCH/ArchRetype_A"
begin

context begin interpretation Arch .

requalify_consts
  arch_default_cap
  default_arch_object
  init_arch_objects

end


section "Creating Caps"

text \<open>The original capability created when an object of a given type is
created with a particular address and size.\<close>
primrec
  default_cap :: "apiobject_type  \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> cap"
where
  "default_cap CapTableObject oref s _ = CNodeCap oref s []"
| "default_cap Untyped oref s dev = UntypedCap dev oref s 0"
| "default_cap TCBObject oref s _ = ThreadCap oref"
| "default_cap EndpointObject oref s _ = EndpointCap oref 0 UNIV"
| "default_cap NotificationObject oref s _ = NotificationCap oref 0 {AllowRead, AllowWrite}"
| "default_cap SchedContextObject oref s _ = SchedContextCap oref (s - min_sched_context_bits)"
| "default_cap ReplyObject oref _ _ = ReplyCap oref {AllowGrant, AllowWrite}"
| "default_cap (ArchObject aobj) oref s dev = ArchObjectCap (arch_default_cap aobj oref s dev)"

text \<open>Create and install a new capability to a newly created object.\<close>
definition
  create_cap ::
  "apiobject_type \<Rightarrow> nat \<Rightarrow> cslot_ptr \<Rightarrow> bool \<Rightarrow> cslot_ptr \<times> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "create_cap type bits untyped is_device \<equiv> \<lambda>(dest,oref). do
    dest_p \<leftarrow> gets (\<lambda>s. cdt s dest);
    cdt \<leftarrow> gets cdt;
    set_cdt (cdt (dest \<mapsto> untyped));
    do_extended_op (create_cap_ext untyped dest dest_p);
    set_original dest True;
    set_cap (default_cap type oref bits is_device) dest
   od"

section "Creating Objects"

text \<open>Properties of an empty CNode object.\<close>
definition
  empty_cnode :: "nat \<Rightarrow> cnode_contents" where
  "empty_cnode bits \<equiv> \<lambda>x. if length x = bits then Some NullCap else None"


text \<open>The initial state objects of various types are in when created.\<close>
definition
  default_object :: "apiobject_type \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> domain \<Rightarrow> kernel_object" where
  "default_object api dev n d \<equiv> case api of
           Untyped \<Rightarrow> undefined
         | CapTableObject \<Rightarrow> CNode n (empty_cnode n)
         | TCBObject \<Rightarrow> TCB (default_tcb d)
         | EndpointObject \<Rightarrow> Endpoint default_ep
         | NotificationObject \<Rightarrow> Notification default_notification
         | SchedContextObject \<Rightarrow> SchedContext default_sched_context (n - min_sched_context_bits)
         | ReplyObject \<Rightarrow> Reply default_reply
         | ArchObject aobj \<Rightarrow> ArchObj (default_arch_object aobj dev n)"

text \<open>The size in bits of the objects that will be created when a given type
and size is requested.\<close>
definition
  obj_bits_api :: "apiobject_type \<Rightarrow> nat \<Rightarrow> nat" where
  "obj_bits_api type obj_size_bits \<equiv> case type of
           Untyped \<Rightarrow> obj_size_bits
         | CapTableObject \<Rightarrow> obj_size_bits + slot_bits
         | TCBObject \<Rightarrow> obj_bits (TCB (default_tcb default_domain))
         | EndpointObject \<Rightarrow> obj_bits (Endpoint undefined)
         | NotificationObject \<Rightarrow> obj_bits (Notification undefined)
         | SchedContextObject \<Rightarrow> obj_size_bits
         | ReplyObject \<Rightarrow> obj_bits (Reply default_reply)
         | ArchObject aobj \<Rightarrow> obj_bits $ ArchObj $ default_arch_object aobj False obj_size_bits"

section "Main Retype Implementation"

text \<open>
Create @{text "numObjects"} objects, starting from
@{text obj_ref}, return of list pointers to them. For some types, each
returned pointer points to a group of objects.
\<close>

definition
  retype_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> apiobject_type \<Rightarrow> bool \<Rightarrow> (obj_ref list,'z::state_ext) s_monad"
where
  "retype_region ptr numObjects o_bits type dev \<equiv> do
    obj_size \<leftarrow> return $ 2 ^ obj_bits_api type o_bits;
    ptrs \<leftarrow> return $ map (\<lambda>p. ptr_add ptr (p * obj_size)) [0..< numObjects];
    when (type \<noteq> Untyped) (do
      kh \<leftarrow> gets kheap;
      cd \<leftarrow> gets cur_domain;
      kh' \<leftarrow> return $ foldr (\<lambda>p kh. kh(p \<mapsto> default_object type dev o_bits cd)) ptrs kh;
      modify $ kheap_update (K kh')
    od);
    return $ ptrs
  od"

section "Invoking Untyped Capabilities"

text \<open>Remove objects from a region of the heap.\<close>
definition
  detype :: "(obj_ref set) \<Rightarrow> 'z::state_ext state \<Rightarrow> 'z::state_ext state" where
 "detype S s \<equiv> s \<lparr> kheap := (\<lambda>x. if x \<in> S then None else kheap s x)\<rparr>"

text \<open>Delete objects within a specified region.\<close>
definition
  delete_objects :: "machine_word \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "delete_objects ptr bits = do
     do_machine_op (freeMemory ptr bits);
     modify (detype {ptr..ptr + 2 ^ bits - 1})
  od"

(* FIXME: we need a sensible place for these configurable constants. *)
definition
  reset_chunk_bits :: nat where
  "reset_chunk_bits = 8"

definition
  get_free_ref :: "obj_ref \<Rightarrow> nat \<Rightarrow> obj_ref" where
  "get_free_ref base free_index \<equiv> base +  (of_nat free_index)"

definition
  get_free_index :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> nat" where
  "get_free_index base free \<equiv> unat $ (free - base)"

primrec(nonexhaustive) is_device_untyped_cap
where
  "is_device_untyped_cap (UntypedCap isdev _ _ _) = isdev"

text \<open>The definitions of reset\_untyped\_cap and invoke\_untyped are moved to InvocationFuns\_A.thy;
for MCS, the function preemption\_point is defined in InvocationFuns\_A.thy which imports Ipc\_R.
This is because of the dependency on update\_time\_stamp and check\_budget. Some invocation functions
that call preemption\_point, namely, invoke\_untyped, invoke\_cnode, and invoke\_tcb, are also
defined in InvocationFuns\_A.thy\<close>


end
