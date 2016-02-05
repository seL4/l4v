(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
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

unqualify_consts (in Arch)
  "arch_default_cap :: aobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> arch_cap"
  "default_arch_object :: aobject_type \<Rightarrow> nat \<Rightarrow> arch_kernel_obj"
  "init_arch_objects :: apiobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> obj_ref list \<Rightarrow> (unit,'z::state_ext) s_monad"


section "Creating Caps"

text {* The original capability created when an object of a given type is
created with a particular address and size. *}
primrec
  default_cap :: "apiobject_type  \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> cap"
where
  "default_cap CapTableObject oref s = CNodeCap oref s []"
| "default_cap Untyped oref s = UntypedCap oref s 0"
| "default_cap TCBObject oref s = ThreadCap oref"
| "default_cap EndpointObject oref s = EndpointCap oref 0 UNIV"
| "default_cap NotificationObject oref s =
     NotificationCap oref 0 {AllowRead, AllowWrite}"
| "default_cap (ArchObject aobj) oref s = ArchObjectCap (arch_default_cap aobj oref s)"

text {* Create and install a new capability to a newly created object. *}
definition
  create_cap ::
  "apiobject_type \<Rightarrow> nat \<Rightarrow> cslot_ptr \<Rightarrow> cslot_ptr \<times> obj_ref \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "create_cap type bits untyped \<equiv> \<lambda>(dest,oref). do
    dest_p \<leftarrow> gets (\<lambda>s. cdt s dest);
    cdt \<leftarrow> gets cdt;
    set_cdt (cdt (dest \<mapsto> untyped));
    do_extended_op (create_cap_ext untyped dest dest_p);
    set_original dest True;
    set_cap (default_cap type oref bits) dest
   od"

section "Creating Objects"

text {* Properties of an empty CNode object. *}
definition
  empty_cnode :: "nat \<Rightarrow> cnode_contents" where
  "empty_cnode bits \<equiv> \<lambda>x. if length x = bits then Some NullCap else None"

text {* The initial state objects of various types are in when created. *}
definition
  default_object :: "apiobject_type \<Rightarrow> nat \<Rightarrow> kernel_object" where
  "default_object api n \<equiv> case api of
           Untyped \<Rightarrow> undefined
         | CapTableObject \<Rightarrow> CNode n (empty_cnode n)
         | TCBObject \<Rightarrow> TCB default_tcb
         | EndpointObject \<Rightarrow> Endpoint default_ep
         | NotificationObject \<Rightarrow> Notification default_notification
         | ArchObject aobj \<Rightarrow> ArchObj (default_arch_object aobj n)"

text {* The size in bits of the objects that will be created when a given type
and size is requested. *}
definition
  obj_bits_api :: "apiobject_type \<Rightarrow> nat \<Rightarrow> nat" where
  "obj_bits_api type obj_size_bits \<equiv> case type of
           Untyped \<Rightarrow> obj_size_bits
         | CapTableObject \<Rightarrow> obj_size_bits + slot_bits
         | TCBObject \<Rightarrow> obj_bits (TCB default_tcb)
         | EndpointObject \<Rightarrow> obj_bits (Endpoint undefined)
         | NotificationObject \<Rightarrow> obj_bits (Notification undefined)
         | ArchObject aobj \<Rightarrow> obj_bits $ ArchObj $ default_arch_object aobj obj_size_bits"

section "Main Retype Implementation"

text {*
Create @{text "numObjects"} objects, starting from
@{text obj_ref}, return of list pointers to them. For some types, each
returned pointer points to a group of objects.
*}
 
definition
  retype_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> apiobject_type \<Rightarrow> (obj_ref list,'z::state_ext) s_monad"
where
  "retype_region ptr numObjects o_bits type \<equiv> do
    obj_size \<leftarrow> return $ 2 ^ obj_bits_api type o_bits;
    ptrs \<leftarrow> return $ map (\<lambda>p. ptr_add ptr (p * obj_size)) [0..< numObjects];
    when (type \<noteq> Untyped) (do
      kh \<leftarrow> gets kheap;
      kh' \<leftarrow> return $ foldr (\<lambda>p kh. kh(p \<mapsto> default_object type o_bits)) ptrs kh;
      do_extended_op (retype_region_ext ptrs type);
      modify $ kheap_update (K kh')
    od);
    return $ ptrs
  od"

section "Invoking Untyped Capabilities"

text {* Remove objects from a region of the heap. *}
definition
  detype :: "(obj_ref set) \<Rightarrow> 'z::state_ext state \<Rightarrow> 'z::state_ext state" where
 "detype S s \<equiv> s \<lparr> kheap := (\<lambda>x. if x \<in> S then None else kheap s x), exst := detype_ext S (exst s)\<rparr>"

text {* Delete objects within a specified region. *}
definition
  delete_objects :: "machine_word \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "delete_objects ptr bits = do
     do_machine_op (freeMemory ptr bits);
     modify (detype {ptr..ptr + 2 ^ bits - 1})
  od"



text {* Untyped capabilities confer authority to the Retype method. This
clears existing objects from a region, creates new objects of the requested type,
initialises them and installs new capabilities to them. *}
fun
  invoke_untyped :: "untyped_invocation \<Rightarrow> (unit,'z::state_ext) s_monad"
where
"invoke_untyped (Retype src_slot base free_region_base new_type obj_sz slots) =
do
  cap \<leftarrow> get_cap src_slot;

  (* If we are creating the first object, detype the entire region. *)
  when (base = free_region_base)
    $ delete_objects base (bits_of cap);

  (* Update the untyped cap to track the amount of space used. *)
  total_object_size \<leftarrow> return $ (of_nat (length slots) << (obj_bits_api new_type obj_sz));
  free_ref \<leftarrow> return $ free_region_base + total_object_size;
  set_cap (UntypedCap base (bits_of cap) (unat (free_ref - base))) src_slot;

  (* Create new objects. *)
  orefs \<leftarrow> retype_region free_region_base (length slots) obj_sz new_type;
  init_arch_objects new_type free_region_base (length slots) obj_sz orefs;
  sequence_x (map (create_cap new_type obj_sz src_slot) (zip slots orefs))
od"

end
