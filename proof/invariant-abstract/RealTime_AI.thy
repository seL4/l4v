(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

theory RealTime_AI
imports VSpace_AI
begin

crunch invs[wp]: get_sched_context invs
crunch invs[wp]: get_reply invs

crunch invs[wp]: get_sched_context invs
crunch invs[wp]: get_sched_context invs

lemma refs_in_get_refs:
  "(x, ref) \<in> get_refs REF ntfn \<Longrightarrow> ref = REF"
  by (auto simp: get_refs_def split: option.splits)

crunch irq_node[wp]: set_reply "\<lambda>s. P (interrupt_irq_node s)"
  (simp: get_object_def)

lemma reply_remove_irq_node[wp]: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
  reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  sorry


crunch interrupt_states[wp]: set_sched_context "\<lambda>s. P (interrupt_states s)"
  (simp: get_object_def)

lemma reply_remove_interrupt_states[wp]: "\<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>
  reply_remove r \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace> "
  sorry

lemma reply_remove_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> reply_remove r \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  sorry

crunch irq_node[wp]: set_reply "\<lambda>s. P (interrupt_irq_node s)"
  (simp: get_object_def)

lemmas reply_remove_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF reply_remove_caps_of_state
                                  reply_remove_interrupt_states]

lemma reply_remove_pspace_in_kernel_window[wp]:
      "\<lbrace>pspace_in_kernel_window\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_in_kernel_window\<rbrace>"
  sorry

lemma reply_remove_pspace_respects_device_region[wp]:
      "\<lbrace>pspace_respects_device_region\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_respects_device_region\<rbrace>"
  sorry

lemma reply_remove_cap_refs_in_kernel_window[wp]:
      "\<lbrace>cap_refs_in_kernel_window\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  sorry


lemma reply_remove_valid_mdb[wp]:
      "\<lbrace>valid_mdb\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  sorry

lemma reply_remove_valid_global_refs[wp]:
      "\<lbrace>valid_global_refs\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_global_refs\<rbrace>"
   sorry

crunch arch [wp]: set_reply "\<lambda>s. P (arch_state s)"
  (simp: get_object_def)

lemma reply_remove_arch[wp]:
      "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. \<lambda>s. P (arch_state s)\<rbrace>"
  sorry


lemma reply_remove_valid_objs [wp]:
  "\<lbrace>valid_objs and reply_at r\<rbrace> reply_remove r \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  sorry

lemma reply_remove_pspace_aligned[wp]:
      "\<lbrace>pspace_aligned\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  sorry

lemma reply_remove_tcb_at[wp]:
      "\<lbrace>tcb_at t\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. tcb_at t\<rbrace>"
  sorry

lemma reply_remove_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> reply_remove r \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  sorry

lemma reply_remove_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> reply_remove r \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  sorry

lemma reply_remove_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> reply_remove r \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  sorry

lemma reply_remove_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> reply_remove r \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  sorry

lemma reply_remove_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> reply_remove r \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  sorry

lemma reply_remove_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> reply_remove r \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma reply_remove_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  reply_remove r
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  sorry

lemma reply_remove_valid_ioc[wp]:
      "\<lbrace>valid_ioc\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. valid_ioc\<rbrace>"
  sorry

(*
lemma reply_remove_[wp]:
      "\<lbrace>\<rbrace> reply_remove r
      \<lbrace>\<lambda>r. \<rbrace>"
*)
lemma set_sched_context_invs[wp]:
  "\<lbrace> invs and sc_at sc_ptr \<rbrace>
      set_sched_context sc_ptr sc \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: set_object_def set_simple_ko_def)
  sorry

lemma set_reply_invs[wp]:
  "\<lbrace> invs and reply_at rptr \<rbrace>
      set_reply rptr reply \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (simp add: set_simple_ko_def)
  sorry


lemma reply_unbind_sc_invs:
  "\<lbrace> invs and sc_at sc_ptr and reply_at rptr \<rbrace>
      reply_unbind_sc sc_ptr rptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_unbind_sc_def)
  sorry

lemma sched_context_unbind_tcb_invs:
  "\<lbrace> invs and sc_at sc_ptr \<rbrace>
      sched_context_unbind_tcb sc_ptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (simp add: sched_context_unbind_tcb_def)
  sorry

lemma sched_context_donate_invs:
  "\<lbrace> invs and sc_at sc_ptr and tcb_at tptr \<rbrace>
      sched_context_donate sc_ptr tptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (simp add: sched_context_donate_def)
  sorry

lemma reply_unbind_caller_invs[wp]:
  "\<lbrace> invs and tcb_at tptr and reply_at rptr \<rbrace>
      reply_unbind_caller tptr tptr \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_unbind_caller_def)
  sorry

lemma reply_remove_invs:
  "\<lbrace> invs and reply_at r \<rbrace> reply_remove r \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_remove_def | wpc)+
  sorry


lemma reply_push_invs:
  "\<lbrace> invs and reply_at r and tcb_at caller and tcb_at callee\<rbrace>
      reply_push caller callee rptr b \<lbrace> \<lambda>_. invs \<rbrace>"
  apply (wpsimp simp: reply_push_def)
  sorry


end