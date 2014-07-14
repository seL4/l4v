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

header "Retyping and Untyped Invocations"

theory Retype_A
imports
  CSpaceAcc_A
  ArchVSpaceAcc_A
  Invocations_A
begin

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
| "default_cap AsyncEndpointObject oref s =
     AsyncEndpointCap oref 0 {AllowRead, AllowWrite}"
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
         | AsyncEndpointObject \<Rightarrow> AsyncEndpoint default_async_ep
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
         | AsyncEndpointObject \<Rightarrow> obj_bits (AsyncEndpoint undefined)
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
  delete_objects :: "word32 \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad" where
 "delete_objects ptr bits = do
     do_machine_op (freeMemory ptr bits);
     modify (detype {ptr..ptr + 2 ^ bits - 1})
  od"

text {* This is a placeholder function. We may wish to extend the specification
  with explicitly tagging kernel data regions in memory. *}
definition
  reserve_region :: "obj_ref \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "reserve_region ptr byteLength is_kernel \<equiv> return ()"

text {* Create 4096-byte frame objects that can be mapped into memory. These must be
cleared to prevent past contents being revealed. *}

definition
  create_word_objects :: "word32 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (unit,'z::state_ext) s_monad" where
  "create_word_objects ptr numObjects sz \<equiv>
  do
    byteLength \<leftarrow> return $ numObjects * 2 ^ sz;
    reserve_region ptr byteLength True;
    rst \<leftarrow>  return (map (\<lambda> n. (ptr + (n << sz))) [0  .e.  (of_nat numObjects) - 1]);
    do_machine_op $ mapM_x (\<lambda>x. clearMemory x (2 ^ sz)) rst
 od"

text {* Initialise architecture-specific objects. *}
definition
  init_arch_objects :: "apiobject_type \<Rightarrow> obj_ref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> obj_ref list \<Rightarrow> (unit,'z::state_ext) s_monad"
where
  "init_arch_objects new_type ptr num_objects obj_sz refs \<equiv> case new_type of
    ArchObject SmallPageObj \<Rightarrow> create_word_objects ptr num_objects 12
  | ArchObject LargePageObj \<Rightarrow> create_word_objects ptr num_objects 16
  | ArchObject SectionObj \<Rightarrow> create_word_objects ptr num_objects 20
  | ArchObject SuperSectionObj \<Rightarrow> create_word_objects ptr num_objects 24
  | ArchObject PageTableObj \<Rightarrow>
      do_machine_op $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + ((1::word32) << pt_bits) - 1)
                                                      (addrFromPPtr x)) refs
  | ArchObject PageDirectoryObj \<Rightarrow> do
      mapM_x copy_global_mappings refs;
      do_machine_op $ mapM_x (\<lambda>x. cleanCacheRange_PoU x (x + ((1::word32) << pd_bits) - 1)
                                                      (addrFromPPtr x)) refs
    od
  | _ \<Rightarrow> return ()"


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
