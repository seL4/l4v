(*
 * Copyright 2026, Proofcraft Pty Ltd
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory ArchHeapStateRelation
imports ArchBits_R
begin

context Arch begin arch_global_naming

abbreviation asid_pools_relation :: "'z::state_ext state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "asid_pools_relation s s' \<equiv> map_relation (asid_pools_of s) (asid_pools_of' s') asid_pool_relation"

definition vmpage_size_to_ptrs :: "obj_ref \<Rightarrow> vmpage_size \<Rightarrow> machine_word set" where
  "vmpage_size_to_ptrs p sz = { p + (n << pageBits) | n. n < 2 ^ (pageBitsForSize sz - pageBits) }"

definition data_pages_relation_2 ::
  "(obj_ref \<rightharpoonup> bool) \<Rightarrow> (obj_ref \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<Rightarrow> bool) \<Rightarrow> (machine_word \<Rightarrow> bool)
   \<Rightarrow> bool"
  where
  "data_pages_relation_2 flags sizes user_data_devices user_data \<equiv>
     (\<Union>p\<in>dom sizes. vmpage_size_to_ptrs p (the (sizes p)))
       = {p. user_data_devices p} \<union> {p. user_data p}
     \<and> (\<forall>p\<in>dom sizes. \<forall>ptr\<in>vmpage_size_to_ptrs p (the (sizes p)).
          \<forall>dev. flags p = Some dev \<longrightarrow> (if dev then user_data_devices ptr else user_data ptr))"

abbreviation data_pages_relation :: "'z::state_ext state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "data_pages_relation s s' \<equiv>
     data_pages_relation_2 (page_devs_of s) (page_sizes_of s)
                           (userDataDevice_at s') (userData_at s')"

lemmas data_pages_relation_def = data_pages_relation_2_def

definition ptr_to_pte_ptrs :: "obj_ref \<Rightarrow> machine_word set" where
  "ptr_to_pte_ptrs p = { p + (ucast y << pteBits) | y. y \<in> (UNIV :: pt_index set) }"

definition ptes_relation_2 :: "(obj_ref \<rightharpoonup> pt) \<Rightarrow> (machine_word \<rightharpoonup> pte) \<Rightarrow> bool" where
  "ptes_relation_2 pts ptes' \<equiv>
     (\<Union>p\<in>dom pts. ptr_to_pte_ptrs p) = dom ptes'
     \<and> (\<forall>p\<in>dom pts. \<forall>pt y pte'. pts p = Some pt \<and> ptes' (p + (ucast y << pteBits)) = Some pte'
                                \<longrightarrow> pte_relation' (pt y) pte')"

abbreviation ptes_relation :: "'z::state_ext state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "ptes_relation s s' \<equiv> ptes_relation_2 (pts_of s) (ptes_of' s')"

lemmas ptes_relation_def = ptes_relation_2_def

text \<open> We may prefer to instead use an _2 style definition with the @{const aobjs_of} heap.\<close>
definition aobjs_relation :: "'z::state_ext state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "aobjs_relation s s' \<equiv>
     data_pages_relation s s'
     \<and> ptes_relation s s'
     \<and> asid_pools_relation s s'"

lemma aobjs_relation_data_pages_relation[elim!]:
  "aobjs_relation s s' \<Longrightarrow> data_pages_relation s s'"
  by (simp add: aobjs_relation_def)

lemma aobjs_relation_ptes_relation[elim!]:
  "aobjs_relation s s' \<Longrightarrow> ptes_relation s s'"
  by (simp add: aobjs_relation_def)

lemma aobjs_relation_asid_pools_relation[elim!]:
  "aobjs_relation s s' \<Longrightarrow> asid_pools_relation s s'"
  by (simp add: aobjs_relation_def)

definition heap_ghost_relation_2 ::
  "(obj_ref \<rightharpoonup> vmpage_size) \<Rightarrow> (obj_ref \<rightharpoonup> nat) \<Rightarrow> (obj_ref \<rightharpoonup> cnode_contents)
   \<Rightarrow> (machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat) \<Rightarrow> bool"
  where
  "heap_ghost_relation_2 page_sizes cnode_sizes cnodes ups cns \<equiv>
     (\<forall>p sz. page_sizes p = Some sz \<longleftrightarrow> ups p = Some sz)
     \<and> (\<forall>p n. (\<exists>cs. cnode_sizes p = Some n \<and> cnodes p = Some cs \<and> well_formed_cnode_n n cs)
              \<longleftrightarrow> cns p = Some n)"

abbreviation heap_ghost_relation :: "'z::state_ext state \<Rightarrow> kernel_state \<Rightarrow> bool" where
  "heap_ghost_relation s s' \<equiv>
     heap_ghost_relation_2
       (page_sizes_of s) (cnode_sizes_of s) (cnode_contents_of s) (gsUserPages s') (gsCNodes s')"

lemmas heap_ghost_relation_def = heap_ghost_relation_2_def

\<comment> \<open>an analogue of @{const ghost_relation_wrapper_2}\<close>
definition heap_ghost_relation_wrapper_2 ::
  "(obj_ref \<rightharpoonup> arch_kernel_obj) \<Rightarrow> (obj_ref \<rightharpoonup> nat) \<Rightarrow> (obj_ref \<rightharpoonup> cnode_contents)
   \<Rightarrow> (machine_word \<rightharpoonup> vmpage_size) \<Rightarrow> (machine_word \<rightharpoonup> nat)
   \<Rightarrow> Arch.kernel_state \<Rightarrow> bool"
  where
  "heap_ghost_relation_wrapper_2 aobjs cnode_sizes cnodes ups cns as \<equiv>
     heap_ghost_relation_2 (aobjs |> page_of ||> snd) cnode_sizes cnodes ups cns"

(* inside Arch locale, we have no need for the wrapper *)
lemmas heap_ghost_relation_wrapper_def[simp] = heap_ghost_relation_wrapper_2_def

end

end
