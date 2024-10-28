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
  ArchVSpaceAcc_A
  Invocations_A
  ArchRetype_A
begin

arch_requalify_consts (A)
  arch_default_cap
  default_arch_object
  init_arch_objects

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
| "default_cap NotificationObject oref s _ =
     NotificationCap oref 0 {AllowRead, AllowWrite}"
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

abbreviation (input) "extended_state_update \<equiv> trans_state"

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

definition
  get_free_ref :: "obj_ref \<Rightarrow> nat \<Rightarrow> obj_ref" where
  "get_free_ref base free_index \<equiv> base +  (of_nat free_index)"

definition
  get_free_index :: "obj_ref \<Rightarrow> obj_ref \<Rightarrow> nat" where
  "get_free_index base free \<equiv> unat $ (free - base)"

primrec(nonexhaustive) is_device_untyped_cap
where
  "is_device_untyped_cap (UntypedCap isdev _ _ _) = isdev"

text \<open>Untyped capabilities note a currently free region. Sometimes this
region is reset during a Retype operation. This progressively clears the
underlying memory and also the object level representation, moving the free
region pointer back to the start of the newly cleared region each time.\<close>
definition
  reset_untyped_cap :: "cslot_ptr \<Rightarrow> (unit,'z::state_ext) p_monad"
where
  "reset_untyped_cap src_slot = doE
  cap \<leftarrow> liftE $ get_cap src_slot;
  sz \<leftarrow> returnOk $ bits_of cap;
  base \<leftarrow> returnOk $ obj_ref_of cap;
  if free_index_of cap = 0
    then returnOk ()
  else doE
    liftE $ delete_objects base sz;
  dev \<leftarrow> returnOk $ is_device_untyped_cap cap;

  if dev \<or> sz < resetChunkBits
      then liftE $ do
        unless dev $ do_machine_op $ clearMemory base (2 ^ sz);
        set_cap (UntypedCap dev base sz 0) src_slot
      od
    else mapME_x (\<lambda>i. doE
          liftE $ do_machine_op $ clearMemory (base + (of_nat i << resetChunkBits))
              (2 ^ resetChunkBits);
          liftE $ set_cap (UntypedCap dev base sz
              (i * 2 ^ resetChunkBits)) src_slot;
          preemption_point
        odE) (rev [i \<leftarrow> [0 ..< 2 ^ (sz - resetChunkBits)].
            i * 2 ^ resetChunkBits < free_index_of cap])
    odE
  odE"

text \<open>Untyped capabilities confer authority to the Retype method. This
clears existing objects from a region, creates new objects of the requested type,
initialises them and installs new capabilities to them.\<close>
definition
  invoke_untyped :: "untyped_invocation \<Rightarrow> (unit,'z::state_ext) p_monad"
where
"invoke_untyped ui \<equiv> case ui
    of Retype src_slot reset base retype_base new_type obj_sz slots is_device \<Rightarrow>
doE
  whenE reset $ reset_untyped_cap src_slot;
  liftE $ do

  cap \<leftarrow> get_cap src_slot;

  \<comment> \<open>Update the untyped cap to track the amount of space used.\<close>
  total_object_size \<leftarrow> return $ (of_nat (length slots) << (obj_bits_api new_type obj_sz));
  free_ref \<leftarrow> return $ retype_base + total_object_size;
  set_cap (UntypedCap is_device base (bits_of cap) (unat (free_ref - base))) src_slot;

  \<comment> \<open>Create new objects.\<close>
  orefs \<leftarrow> retype_region retype_base (length slots) obj_sz new_type is_device;
  init_arch_objects new_type is_device retype_base (length slots) obj_sz orefs;
  sequence_x (map (create_cap new_type obj_sz src_slot is_device) (zip slots orefs))
od odE"

end
