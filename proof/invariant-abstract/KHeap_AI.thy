(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory KHeap_AI
imports ArchKHeap_AI
begin

context begin interpretation Arch .

requalify_consts
  obj_is_device
  valid_vso_at
  non_vspace_obj
  vspace_obj_pred

requalify_facts
  pspace_in_kernel_window_atyp_lift
  valid_vspace_objs_lift_weak
  vs_lookup_vspace_obj_at_lift
  vs_lookup_pages_vspace_obj_at_lift
  valid_arch_caps_lift_weak
  valid_global_objs_lift_weak
  valid_asid_map_lift
  valid_ioports_lift
  valid_kernel_mappings_lift
  equal_kernel_mappings_lift
  valid_global_vspace_mappings_lift
  valid_machine_state_lift
  valid_vso_at_lift
  valid_vso_at_lift_aobj_at
  valid_arch_state_lift_aobj_at
  in_user_frame_lift
  in_user_frame_obj_pred_lift
  set_object_v_ker_map

  non_vspace_objs
  vspace_obj_predE
  vspace_pred_imp

  in_user_frame_obj_upd
  in_device_frame_obj_upd
  device_mem_obj_upd_dom
  user_mem_obj_upd_dom

  pspace_respects_region_cong
  cap_is_device_obj_is_device
  storeWord_device_state_inv

  state_hyp_refs_of_ep_update
  state_hyp_refs_of_ntfn_update
  state_hyp_refs_of_tcb_state_update
  state_hyp_refs_of_tcb_bound_ntfn_update
  arch_valid_obj_same_type
  default_arch_object_not_live
  default_tcb_not_live

  getActiveIRQ_neq_non_kernel
  dmo_getActiveIRQ_non_kernel

  valid_arch_tcb_same_type
  valid_arch_tcb_typ_at
  valid_tcb_arch_ref_lift

end

crunches getTouchedAddresses
  for inv[wp]: "P"

lemma dmo_getTouchedAddresses_inv[wp]:
 "do_machine_op getTouchedAddresses \<lbrace>P\<rbrace>"
  apply (wpsimp simp: simpler_do_machine_op_getTouchedAddresses_def in_gets)
  done

lemma touched_addresses_update_comp [simp]:
  "machine_state.touched_addresses_update f \<circ> machine_state.touched_addresses_update g =
    machine_state.touched_addresses_update (f \<circ> g)"
  apply (clarsimp simp: comp_def)
  done

lemma dmo_addTouchedAddresses_tainv[wp]:
 "do_machine_op (addTouchedAddresses S) \<lbrace>ignore_ta P\<rbrace>"
  apply (wpsimp simp: simpler_do_machine_op_addTouchedAddresses_def)
  done

crunches touch_object
  for tainv[wp]: "ignore_ta P"
  (ignore: do_machine_op)

interpretation touch_object_tainv:
  touched_addresses_inv _ "touch_object obj"
  by unfold_locales wpsimp

crunches touch_objects
  for tainv[wp]: "ignore_ta P"
  (ignore: do_machine_op)

interpretation touch_objects_tainv:
  touched_addresses_inv _ "touch_objects obj"
  by unfold_locales wpsimp

crunches get_object
  for tainv[wp]: "ignore_ta P"
  (ignore: do_machine_op)

interpretation get_object_tainv:
  touched_addresses_inv _ "get_object ta_f obj"
  by unfold_locales wpsimp

sublocale touched_addresses_inv \<subseteq> pspace_respects_device_region: touched_addresses_P_inv _ _
          pspace_respects_device_region
  apply unfold_locales
  apply (clarsimp simp: ta_agnostic_def pspace_respects_device_region_def)
  apply (subst user_mem_dom_cong)
   apply (clarsimp, rule refl)
  apply (subst device_mem_dom_cong)
   apply (clarsimp, rule refl)
  apply (rule refl)
  done

sublocale touched_addresses_inv \<subseteq> ifunsafe: touched_addresses_P_inv _ _ if_unsafe_then_cap
  by unfold_locales (simp add: agnostic_preserved ta_agnostic_def)+

lemmas cap_is_device_obj_is_device[simp] = cap_is_device_obj_is_device
lemmas storeWord_device_state_hoare[wp] = storeWord_device_state_inv

declare non_vspace_objs[intro]

context
  notes get_object_wp [wp]
begin

method get_simple_ko_method =
  (wpsimp simp: get_simple_ko_def partial_inv_def the_equality split: kernel_object.splits)

lemma get_simple_ko_wp:
  "\<lbrace>\<lambda>s. \<forall>ntfn. ko_at (f ntfn) ntfnptr s \<longrightarrow> P ntfn s\<rbrace>
   get_simple_ko f ntfnptr \<lbrace>P\<rbrace>"
  by get_simple_ko_method

lemma get_object_inv [wp]: "\<lbrace>P\<rbrace> get_object ta_f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by wpsimp


lemma get_tcb_rev:
  "f_kheap ta_f s p = Some (TCB t)\<Longrightarrow> get_tcb ta_f p s = Some t"
  by (clarsimp simp:get_tcb_def)

lemma get_tcb_obj_atE[elim!]:
  "\<lbrakk> get_tcb ta_f t s = Some tcb; get_tcb ta_f t s = Some tcb \<Longrightarrow> P (TCB tcb) \<rbrakk> \<Longrightarrow> obj_at P t s"
  by (clarsimp dest!: get_tcb_SomeD simp: obj_at_def ta_filter_def split:if_splits)


lemma a_type_TCB[simp]:
  "a_type (TCB x) = ATCB"
  by (simp add: a_type_def)

lemma pspace_aligned_obj_update:
  assumes obj: "obj_at P t s"
  assumes pa: "pspace_aligned s"
  assumes R: "\<And>k. P k \<Longrightarrow> a_type k = a_type k'"
  shows "pspace_aligned (s\<lparr>kheap := kheap s(t \<mapsto> k')\<rparr>)"
  using pa obj
  apply (simp add: pspace_aligned_def cong: conj_cong)
  apply (clarsimp simp: obj_at_def obj_bits_T dest!: R)
  apply (fastforce dest: bspec [OF _ domI])
  done


lemma cte_at_same_type:
  "\<lbrakk>cte_at t s; a_type k = a_type ko; kheap s p = Some ko\<rbrakk>
  \<Longrightarrow> cte_at t (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  apply (clarsimp simp: cte_at_cases del: disjCI)
  apply (elim exE disjE)
   apply (clarsimp simp: a_type_def well_formed_cnode_n_def length_set_helper
                  split: Structures_A.kernel_object.split_asm
                         if_split_asm)
  apply clarsimp
  done


lemma untyped_same_type:
  "\<lbrakk>valid_untyped (cap.UntypedCap dev r n f) s; a_type k = a_type ko; kheap s p = Some ko\<rbrakk>
  \<Longrightarrow> valid_untyped (cap.UntypedCap dev r n f) (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  unfolding valid_untyped_def
  by (clarsimp simp: obj_range_def obj_bits_T)

lemma valid_cap_same_type:
  "\<lbrakk> s \<turnstile> cap; a_type k = a_type ko; kheap s p = Some ko \<rbrakk>
  \<Longrightarrow> s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr> \<turnstile> cap"
  apply (simp add: valid_cap_def split: cap.split)
  apply (auto elim!: typ_at_same_type untyped_same_type
               simp: ntfn_at_typ ep_at_typ tcb_at_typ cap_table_at_typ
              split: option.split sum.split)
  by (intro hoare_to_pure_kheap_upd[OF valid_arch_cap_typ, simplified obj_at_def],
      assumption, auto)

lemma valid_obj_same_type:
  "\<lbrakk> valid_obj p' obj s; valid_obj p k s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_obj p' obj (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  apply (cases obj; simp)
      apply (clarsimp simp add: valid_obj_def valid_cs_def)
      apply (drule (1) bspec)
      apply (erule (2) valid_cap_same_type)
     apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_ntfn_def valid_arch_tcb_same_type)
     apply (fastforce elim: valid_cap_same_type typ_at_same_type
                      simp: valid_tcb_state_def ep_at_typ
                            ntfn_at_typ tcb_at_typ
                     split: Structures_A.thread_state.splits option.splits)
    apply (clarsimp simp add: valid_obj_def valid_ep_def)
    apply (fastforce elim: typ_at_same_type
                    simp: tcb_at_typ
                    split: Structures_A.endpoint.splits)
   apply (clarsimp simp add: valid_obj_def valid_ntfn_def valid_bound_tcb_def)
   apply (auto elim: typ_at_same_type
                   simp: tcb_at_typ
                  split: Structures_A.ntfn.splits option.splits)
  apply (clarsimp simp add: valid_obj_def)
  apply (auto intro: arch_valid_obj_same_type)
  done

lemma set_object_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_obj p k\<rbrace>
  set_object ta_f p k
  \<lbrace>\<lambda>r. valid_objs\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def)
  apply (clarsimp simp: valid_objs_def dom_def)
  apply (intro conjI impI; fastforce intro: valid_obj_same_type)
  done

lemma set_object_aligned[wp]:
  "set_object ta_f p k \<lbrace>pspace_aligned\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp elim!: pspace_aligned_obj_update)
  done


lemma assert_get_tcb:
  "\<lbrace> P \<rbrace> gets_the (get_tcb False t) \<lbrace> \<lambda>r. P and tcb_at t \<rbrace>"
  by (clarsimp simp: valid_def in_monad gets_the_def tcb_at_def)

(* This rule is not always safe. However, we make it [wp] while we're only doing proofs that don't
   involve extended state, and then remove it from [wp] in Deterministic_AI. *)
lemma dxo_wp_weak[wp]:
  assumes xopv: "\<And>s f. P (trans_state f s) = P s"
  shows "\<lbrace>P\<rbrace> do_extended_op x \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding do_extended_op_def
  apply (simp add: split_def)
  apply wp
  apply (clarsimp simp: mk_ef_def)
  apply (simp add: xopv[simplified trans_state_update'])
  done

crunch ct[wp]: set_thread_state "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps)

lemma sts_ep_at_inv[wp]:
  "\<lbrace> ep_at ep \<rbrace> set_thread_state t s \<lbrace> \<lambda>rv. ep_at ep \<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: touch_object_wp)
  apply (clarsimp simp: obj_at_def is_ep is_tcb get_tcb_def)
  done

lemma sts_ntfn_at_inv[wp]:
  "\<lbrace> ntfn_at ep \<rbrace> set_thread_state t s \<lbrace> \<lambda>rv. ntfn_at ep \<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp simp: set_object_def wp: touch_object_wp)
  apply (clarsimp simp: obj_at_def is_ntfn is_tcb get_tcb_def)
  done

lemma sbn_ep_at_inv[wp]:
  "\<lbrace> ep_at ep \<rbrace> set_bound_notification t ntfn \<lbrace> \<lambda>rv. ep_at ep \<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp simp: set_object_def wp: touch_object_wp)
  apply (clarsimp simp: obj_at_def is_ep is_tcb get_tcb_def)
  done

lemma sbn_ntfn_at_inv[wp]:
  "\<lbrace> ntfn_at ep \<rbrace> set_bound_notification t ntfn \<lbrace> \<lambda>rv. ntfn_at ep \<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wpsimp simp: set_object_def wp: touch_object_wp)
  apply (clarsimp simp: obj_at_def is_ntfn is_tcb get_tcb_def)
  done

lemma prefix_to_eq:
  "\<lbrakk> take n xs \<le> ys; length xs = length ys; drop n xs = drop n ys \<rbrakk>
     \<Longrightarrow> xs = ys"
  apply (induct n arbitrary: xs ys)
   apply simp
  apply (case_tac xs)
   apply simp
  apply (case_tac ys)
   apply simp
  apply simp
  done


lemma set_cdt_inv:
  assumes P: "\<And>s. P s \<Longrightarrow> P (cdt_update (\<lambda>_. m) s)"
  shows "\<lbrace>P\<rbrace> set_cdt m \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: set_cdt_def)
  apply wp
  apply (erule P)
  done


lemmas cte_wp_at_cdt = cdt_update.cte_wp_at_update
lemmas obj_at_cdt = cdt_update.obj_at_update
lemmas valid_cap_cdt = cdt_update.valid_cap_update


lemma set_object_at_obj3:
  "\<lbrace>K (P obj)\<rbrace> set_object ta_f p obj \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  by (wpsimp wp:set_object_wp simp: set_object_def obj_at_def valid_def in_monad)


lemma set_object_valid_cap:
  "set_object ta_f p ko \<lbrace>valid_cap c\<rbrace>"
  by (wpsimp wp: set_object_wp_strong simp: obj_at_def valid_cap_same_type)

lemma set_object_cte_at:
  "set_object ta_f p ko \<lbrace>cte_at c\<rbrace>"
  by (wpsimp wp: set_object_wp_strong simp: obj_at_def cte_at_same_type)


lemma obj_at_ko_atD:
  "obj_at P x s \<Longrightarrow> \<exists>k. ko_at k x s \<and> P k"
  by (clarsimp simp: obj_at_def)

lemma set_object_ko:
  "\<lbrace>ko_at obj ptr and K (x \<noteq> ptr)\<rbrace> set_object ta_f x ko \<lbrace>\<lambda>rv. ko_at obj ptr\<rbrace>"
  by (wpsimp wp:set_object_wp simp: valid_def set_object_def get_object_def in_monad obj_at_def)


lemma tcb_aligned: "\<lbrakk> invs s; tcb_at t s \<rbrakk> \<Longrightarrow> is_aligned t tcb_bits"
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                        pspace_aligned_def)
  apply (clarsimp simp: tcb_at_def, drule get_tcb_SomeD)
  apply (erule my_BallE [where y=t])
   apply clarsimp
  apply simp
  done


lemma set_object_ko_at:
  "\<lbrace>\<top>\<rbrace> set_object ta_f p ko \<lbrace>\<lambda>_. ko_at ko p\<rbrace>"
  by (wpsimp wp: set_object_wp simp: obj_at_def)

lemma get_simple_ko_sp:
  "\<lbrace>P\<rbrace> get_simple_ko f p \<lbrace>\<lambda>ep. ko_at (f ep) p and P\<rbrace>"
  by get_simple_ko_method

lemma get_simple_ko_inv[wp]: "\<lbrace>P\<rbrace> get_simple_ko f ep \<lbrace>\<lambda>rv. P\<rbrace>"
  by get_simple_ko_method

lemma get_simple_ko_actual_ko[wp]:
  "\<lbrace> obj_at (\<lambda>ko. bound (partial_inv f ko)) ep \<rbrace>
   get_simple_ko f ep
   \<lbrace> \<lambda>rv. obj_at (\<lambda>k. k = f rv) ep \<rbrace>"
   by (fastforce simp: get_simple_ko_def get_object_def bind_def partial_inv_def
                             valid_def gets_def get_def return_def in_fail
                             assert_def obj_at_def split_def the_equality
                             ta_filter_def obind_def
                   split: kernel_object.splits option.splits)

lemma get_object_valid [wp]:
  "\<lbrace>valid_objs\<rbrace> get_object ta_f oref \<lbrace> valid_obj oref \<rbrace>"
  apply (simp add: get_object_def)
  apply wp
  apply (clarsimp simp add: valid_pspace_def valid_objs_def dom_def ta_filter_def obind_def
    split: option.splits)
  apply fastforce
  done


lemma get_object_valid_obj_simple [wp]:
  notes valid_simple_obj_def[simp del]
  shows
  "\<lbrace>valid_objs\<rbrace> get_object ta_f oref \<lbrace> valid_simple_obj \<rbrace>"
  apply (simp add: get_object_def)
  apply wp
  apply (clarsimp simp: valid_pspace_def valid_objs_def dom_def ta_filter_def obind_def
                 intro!: valid_obj_imp_valid_simple split:option.splits)
  apply fastforce
  done

lemma get_object_valid_simple [wp]:
  "\<lbrace>valid_simple_objs\<rbrace> get_object ta_f oref \<lbrace> valid_simple_obj \<rbrace>"
  apply (simp add: get_object_def)
  apply wp
  apply (clarsimp simp add: valid_pspace_def valid_simple_objs_def dom_def ta_filter_def obind_def
    split: option.splits)
  apply fastforce
  done

lemma get_simple_ko_valid [wp]:
  "\<lbrace>valid_objs\<rbrace> get_simple_ko f oref \<lbrace> \<lambda>r s. valid_simple_obj (f r) s\<rbrace>"
  apply (simp add: get_simple_ko_def)
  apply (wpsimp)
  apply (drule valid_objs_imp_valid_simple_objs)
  apply (clarsimp simp: valid_simple_objs_def partial_inv_def obj_at_def the_equality split: if_splits)
  apply (drule_tac x=oref in bspec)
   apply (clarsimp simp: the_equality  split: kernel_object.splits)+
  done

lemma get_simple_ko_valid_obj[wp]:
  "\<lbrace> valid_objs and obj_at (\<lambda>ko. bound (partial_inv f ko)) ep \<rbrace>
   get_simple_ko f ep
   \<lbrace> \<lambda>r. valid_obj ep (f r) \<rbrace>"
  apply (simp add: get_simple_ko_def)
  apply (rule hoare_seq_ext)
   prefer 2
   apply (rule hoare_pre_imp [OF _ get_object_valid])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wpsimp simp: partial_inv_def the_equality valid_obj_def
               split: option.splits)
  done

lemma get_simple_ko_valid_simple_obj[wp]:
  notes valid_simple_obj_def[simp del]
  shows
  "\<lbrace> valid_objs and obj_at (\<lambda>ko. bound (partial_inv f ko)) ep \<rbrace>
   get_simple_ko f ep
   \<lbrace> \<lambda>r. valid_simple_obj (f r) \<rbrace>"
  apply (simp add: get_simple_ko_def)
  apply (rule hoare_seq_ext)
   prefer 2
   apply (rule hoare_pre_imp [OF _ get_object_valid])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wpsimp simp: partial_inv_def the_equality valid_obj_imp_valid_simple
              split: option.splits)
  done

lemma get_ntfn_valid_ntfn[wp]:
  "\<lbrace> valid_objs and ntfn_at ntfn \<rbrace>
   get_notification ntfn
   \<lbrace> valid_ntfn \<rbrace>"
  by (wpsimp simp: ntfn_at_def2 valid_ntfn_def2 simp_del: valid_simple_obj_def)

lemma get_ep_valid_ep[wp]:
  "\<lbrace> invs and ep_at ep \<rbrace>
   get_endpoint ep
   \<lbrace> valid_ep \<rbrace>"
  by (wpsimp simp: ep_at_def2 valid_ep_def2 simp_del: valid_simple_obj_def)


lemma set_simple_ko_valid_objs[wp]:
  "\<lbrace> valid_objs
     and valid_simple_obj (f v) and K (is_simple_type (f v))\<rbrace> set_simple_ko f ptr v \<lbrace>\<lambda>rv s. valid_objs s\<rbrace>"
  unfolding set_simple_ko_def
  by (wpsimp wp: set_object_valid_objs[THEN hoare_set_object_weaken_pre]
           simp: valid_obj_def obj_at_def a_type_def partial_inv_def valid_ntfn_def2 valid_ep_def2
          split: kernel_object.splits
       simp_del: valid_simple_obj_def)

method set_simple_ko_method uses wp_thm simp_thm =
  (unfold set_simple_ko_def;
    wpsimp wp: wp_thm
         simp: simp_thm valid_obj_def obj_at_def a_type_def partial_inv_def the_equality
        split: kernel_object.splits)

lemma set_simple_ko_aligned[wp]:
 "set_simple_ko f ptr v \<lbrace>pspace_aligned\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_aligned[THEN hoare_set_object_weaken_pre])


lemma set_simple_ko_typ_at [wp]:
  "set_simple_ko f p' ep \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_typ_at)

lemma set_simple_ko_cte_wp_at [wp]:
  "set_simple_ko f p' ep \<lbrace>cte_wp_at P p\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_wp simp_thm: cte_wp_at_cases; fastforce)

lemma get_simple_ko_ko_at:
  "\<lbrace>\<top>\<rbrace> get_simple_ko f ep \<lbrace>\<lambda>rv. ko_at (f rv) ep\<rbrace>"
  by get_simple_ko_method

lemma obj_set_prop_at:
  "\<lbrace>\<lambda>s. P obj \<rbrace> set_object ta_f p obj \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  apply (wpsimp simp: obj_at_def set_object_def wp: touch_object_wp)
  done

lemma simple_obj_set_prop_at:
  "\<lbrace>\<lambda>s. P (f v) \<rbrace> set_simple_ko f p v \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  by (set_simple_ko_method wp_thm: obj_set_prop_at)

lemma set_simple_ko_refs_of[wp]:
 "\<lbrace>\<lambda>s. P ((state_refs_of s) (ep := refs_of (f val)))\<rbrace>
    set_simple_ko f ep val
  \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (set_simple_ko_method  wp_thm: set_object_wp simp_thm: set_object_def)
  by (fastforce simp: state_refs_of_def elim!: rsubst[where P=P])

lemma set_ep_refs_of[wp]:
 "\<lbrace>\<lambda>s. P ((state_refs_of s) (ep := ep_q_refs_of val))\<rbrace>
    set_endpoint ep val
  \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp; fastforce simp: state_refs_of_def elim!: rsubst[where P=P])

lemma set_simple_ko_hyp_refs_of[wp]:
 "set_simple_ko f ep val \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (set_simple_ko_method wp_thm: set_object_wp_strong)
  apply (rule conjI; clarsimp elim!: rsubst[where P=P])
   apply (subst state_hyp_refs_of_ep_update[of ep, symmetric])
    apply (clarsimp simp: obj_at_def)
   apply (simp add: fun_upd_def)
  apply (subst state_hyp_refs_of_ntfn_update[of ep, symmetric])
   apply (clarsimp simp: obj_at_def)
  apply (simp add: fun_upd_def)
  done

lemma set_ntfn_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (ntfnptr := ntfn_q_refs_of (ntfn_obj ntfn) \<union> ntfn_bound_refs (ntfn_bound_tcb ntfn)))\<rbrace>
     set_notification ntfnptr ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  by (wp; fastforce simp: state_refs_of_def elim!: rsubst[where P=P])

lemma pspace_distinct_same_type:
  "\<lbrakk> kheap s t = Some ko; a_type ko = a_type ko';  pspace_distinct s\<rbrakk>
    \<Longrightarrow> pspace_distinct (s\<lparr>kheap := kheap s(t \<mapsto> ko')\<rparr>)"
  apply (clarsimp simp add: pspace_distinct_def obj_bits_T)
  apply fastforce
  done


lemma set_object_distinct[wp]:
  "set_object ta_f p ko' \<lbrace>pspace_distinct\<rbrace>"
  by (wpsimp wp: set_object_wp_strong simp: obj_at_def pspace_distinct_same_type)

lemma set_simple_ko_distinct[wp]:
  "set_simple_ko f ep v \<lbrace>pspace_distinct\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_distinct[THEN hoare_set_object_weaken_pre])


lemma set_simple_ko_cur_tcb[wp]:
  "set_simple_ko f ep v \<lbrace>cur_tcb\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_wp simp_thm: cur_tcb_def is_tcb is_ep; fastforce)

lemma assert_pre:
  "\<lbrace>P\<rbrace> do s <- get; assert (P s); f od \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: valid_def assert_def get_def bind_def return_def)

lemma set_object_pspace_in_kernel_window:
  "set_object ta_f p k \<lbrace>pspace_in_kernel_window\<rbrace>"
  unfolding set_object_def
  apply (rule assert_pre)
  apply (rule hoare_pre)
   apply (rule pspace_in_kernel_window_atyp_lift)
    apply (wpsimp simp: obj_at_def wp:touch_object_wp)+
  done

lemma set_object_pspace_respects_device_region:
  "set_object ta_f p k \<lbrace>pspace_respects_device_region\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply (clarsimp simp: pspace_respects_device_region_def
                        device_mem_obj_upd_dom user_mem_obj_upd_dom
                        obj_at_def in_user_frame_obj_upd in_device_frame_obj_upd
                 split: if_split_asm)
  done

lemma set_simple_ko_kernel_window[wp]:
  "set_simple_ko f ptr val \<lbrace>pspace_in_kernel_window\<rbrace>"
  by (set_simple_ko_method
        wp_thm: set_object_pspace_in_kernel_window[THEN hoare_set_object_weaken_pre])

lemma set_simple_ko_respect_device_region[wp]:
  "set_simple_ko f ptr val \<lbrace>pspace_respects_device_region\<rbrace>"
  by (set_simple_ko_method
        wp_thm: set_object_pspace_respects_device_region[THEN hoare_set_object_weaken_pre])

lemma swp_apply [simp]:
  "swp f x y = f y x" by (simp add: swp_def)

lemma hoare_cte_wp_caps_of_state_lift:
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. cte_wp_at P p s\<rbrace> f \<lbrace>\<lambda>r s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (rule c)
  done

lemma valid_mdb_lift:
  assumes c: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (caps_of_state s)\<rbrace>"
  assumes m: "\<And>P. \<lbrace>\<lambda>s. P (cdt s)\<rbrace> f \<lbrace>\<lambda>r s. P (cdt s)\<rbrace>"
  assumes r: "\<And>P. \<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> f \<lbrace>\<lambda>r s. P (is_original_cap s)\<rbrace>"
  shows "\<lbrace>valid_mdb\<rbrace> f \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  apply (clarsimp simp add: valid_def valid_mdb_def mdb_cte_at_def)
  apply (frule_tac P1="(=) (cdt s)" in use_valid [OF _  m], rule refl)
  apply (rule conjI)
   apply clarsimp
   apply (erule allE)+
   apply (erule (1) impE)
   apply clarsimp
   apply (rule conjI)
    apply (erule use_valid [OF _ c [THEN hoare_cte_wp_caps_of_state_lift]])
    apply simp
   apply (erule use_valid [OF _ c [THEN hoare_cte_wp_caps_of_state_lift]])
   apply simp
  apply (rule use_valid [OF _ c], assumption+)
  apply (rule use_valid [OF _ r], assumption)
  apply simp
  done

crunch no_cdt[wp]: set_simple_ko "\<lambda>s. P (cdt s)"
  (wp: crunch_wps)


lemma set_simple_ko_caps_of_state [wp]:
  "set_simple_ko f p ep \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  apply (set_simple_ko_method simp_thm: bind_assoc wp_thm: set_object_wp_strong)
  apply (rule conjI; clarsimp split: if_splits; subst cte_wp_caps_of_lift; assumption?)
   apply (auto simp: cte_wp_at_cases)
  done

lemma set_simple_ko_revokable [wp]:
  "set_simple_ko f p ep \<lbrace>\<lambda> s. P (is_original_cap s)\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_wp)


lemma set_ep_mdb [wp]:
  "set_simple_ko f p ep \<lbrace>valid_mdb\<rbrace>"
  by (wp valid_mdb_lift)


lemma cte_wp_at_after_update:
  "\<lbrakk> obj_at (same_caps val) p' s \<rbrakk>
    \<Longrightarrow> cte_wp_at P p (kheap_update (\<lambda>a b. if b = p' then Some val else kheap s b) s)
         = cte_wp_at P p s"
  by (fastforce simp: obj_at_def cte_wp_at_cases split: if_split_asm dest: bspec [OF _ ranI])

lemma cte_wp_at_after_update':
  "\<lbrakk> obj_at (same_caps val) p' s \<rbrakk>
    \<Longrightarrow> cte_wp_at P p (s\<lparr>kheap := kheap s(p' \<mapsto> val)\<rparr>)
         = cte_wp_at P p s"
  by (fastforce simp: obj_at_def cte_wp_at_cases split: if_split_asm dest: bspec [OF _ ranI])

lemma ex_cap_to_after_update:
  "\<lbrakk> ex_nonz_cap_to p s; obj_at (same_caps val) p' s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to p (kheap_update (\<lambda>a b. if b = p' then Some val else kheap s b) s)"
  by (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_after_update)

lemma ex_cap_to_after_update':
  "\<lbrakk> ex_nonz_cap_to p s; obj_at (same_caps val) p' s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to p (s\<lparr>kheap := kheap s(p' \<mapsto> val)\<rparr>)"
  by (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_after_update')

lemma ex_cte_cap_to_after_update:
  "\<lbrakk> ex_cte_cap_wp_to P p s; obj_at (same_caps val) p' s \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to P p (s \<lparr>kheap := (\<lambda>b. if b = p' then Some val else kheap s b)\<rparr>)"
  by (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_after_update)

lemma set_object_iflive:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and>
        (live val \<longrightarrow> ex_nonz_cap_to p s) \<and> obj_at (same_caps val) p s\<rbrace>
   set_object ta_f p val
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (wpsimp wp: set_object_wp)
  by (fastforce simp: if_live_then_nonz_cap_def obj_at_def elim!: ex_cap_to_after_update')

lemma set_object_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap and obj_at (same_caps val) p\<rbrace>
     set_object ta_f p val \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_object_def)
  apply (wp touch_object_wp')
  apply simp
  apply (clarsimp simp: if_unsafe_then_cap_def simp: cte_wp_at_after_update
                 dest!: caps_of_state_cteD)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (fastforce elim!: ex_cte_cap_to_after_update)
  done


lemma set_object_zombies[wp]:
  "\<lbrace>zombies_final and obj_at (same_caps val) p\<rbrace>
      set_object ta_f p val \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_object_def)
  apply (wp touch_object_wp)
  apply (clarsimp simp: zombies_final_def is_final_cap'_def2
                        cte_wp_at_after_update)
  done

lemma set_simple_ko_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> (live (f ep) \<longrightarrow> ex_nonz_cap_to p s)\<rbrace>
     set_simple_ko f p ep \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (set_simple_ko_method wp_thm: set_object_iflive[THEN hoare_set_object_weaken_pre])
  apply (rule conjI; clarsimp elim!: obj_at_weakenE
                              split: Structures_A.kernel_object.splits
                               simp: is_ep_def is_ntfn_def)
  done


lemma set_simple_ko_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_simple_ko f p val \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (set_simple_ko_method wp_thm: set_object_ifunsafe[THEN hoare_set_object_weaken_pre])
  by (clarsimp elim!: obj_at_weakenE
                simp: is_ep_def is_ntfn_def)


lemma set_simple_ko_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_simple_ko f p val \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (set_simple_ko_method wp_thm: set_object_zombies[THEN hoare_set_object_weaken_pre])
  by (clarsimp elim!: obj_at_weakenE
                simp: is_ep_def is_ntfn_def)

lemma set_object_cap_refs_in_kernel_window:
  "\<lbrace>cap_refs_in_kernel_window and obj_at (same_caps ko) p\<rbrace>
  set_object ta_f p ko
  \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_object_def, wp touch_object_wp)
  apply (clarsimp simp: cap_refs_in_kernel_window_def)
  apply (clarsimp simp: valid_refs_def cte_wp_at_after_update)
  done

lemma set_object_cap_refs_respects_device_region:
  "\<lbrace>cap_refs_respects_device_region and obj_at (same_caps ko) p\<rbrace>
  set_object ta_f p ko
  \<lbrace>\<lambda>r. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_object_def, wp touch_object_wp)
  apply (clarsimp simp: cap_refs_respects_device_region_def)
  apply (drule_tac x = a in spec)
  apply (drule_tac x = b in spec)
  apply (clarsimp simp: valid_refs_def cte_wp_at_after_update
    cap_range_respects_device_region_def)
  apply (erule notE)
  apply (erule cte_wp_at_weakenE)
  apply auto
  done


lemma get_object_ret:
  "\<lbrace>obj_at P addr\<rbrace> get_object ta_f addr \<lbrace>\<lambda>r s. P r\<rbrace>"
  unfolding get_object_def
  by (wp, clarsimp simp: ta_filter_def obind_def split: option.splits elim!: obj_atE)+


lemma captable_case_helper:
  "\<lbrakk> \<forall>sz cs. ob \<noteq> CNode sz cs \<rbrakk> \<Longrightarrow> (case ob of CNode sz cs \<Rightarrow> P sz cs | _ \<Rightarrow> Q) = Q"
  by (case_tac ob, simp_all add: not_ex[symmetric])


lemma null_filter_caps_of_stateD:
  "null_filter (caps_of_state s) p = Some c \<Longrightarrow>
  cte_wp_at (\<lambda>c'. c' = c \<and> c' \<noteq> cap.NullCap) p s"
  apply (simp add: null_filter_def split: if_split_asm)
  apply (drule caps_of_state_cteD)
  apply (simp add: cte_wp_at_def)
  done


lemma caps_of_state_after_update:
  "obj_at (same_caps val) p s \<Longrightarrow>
     (caps_of_state (kheap_update (\<lambda>a b. if b = p then Some val else kheap s b) s))
       = caps_of_state s"
  by (simp add: caps_of_state_cte_wp_at cte_wp_at_after_update
          cong: if_cong)


lemma elim_CNode_case:
  "\<lbrakk> (case x of CNode sz ct \<Rightarrow> False | _ \<Rightarrow> True) \<rbrakk>
     \<Longrightarrow> (case x of CNode sz ct \<Rightarrow> f sz ct | _ \<Rightarrow> k) = k"
  by (simp split: Structures_A.kernel_object.split_asm)


lemma no_fail_obj_at [wp]:
  "no_fail (obj_at \<top> ptr and obj_in_ta ptr) (get_object ta_f ptr)"
  apply (simp add: get_object_def)
  apply (rule no_fail_pre, wp)
  apply (clarsimp simp: obj_at_def ta_filter_def obind_def obj_in_ta_def)
  done



lemma do_machine_op_obj_at[wp]:
  "\<lbrace>\<lambda>s. P (obj_at Q p s)\<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. P (obj_at Q p s)\<rbrace>"
  by (clarsimp simp: do_machine_op_def split_def | wp)+


lemma dmo_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> do_machine_op f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
   apply (simp add: do_machine_op_def split_def)
   apply wp
   apply (clarsimp simp: cur_tcb_def)
   done


lemma valid_irq_states_machine_state_updateI:
  "(\<And>irq. interrupt_states s irq = IRQInactive \<Longrightarrow> irq_masks m irq) \<Longrightarrow>
   valid_irq_states (s\<lparr>machine_state := m\<rparr>)"
  apply(simp add: valid_irq_states_def valid_irq_masks_def)
  done

lemma valid_irq_statesE:
  "\<lbrakk>valid_irq_states s; (\<And> irq. interrupt_states s irq = IRQInactive \<Longrightarrow> irq_masks (machine_state s) irq) \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by(auto simp: valid_irq_states_def valid_irq_masks_def)

lemma cap_refs_respects_region_cong:
  "\<lbrakk>caps_of_state a  = caps_of_state b; device_state (machine_state a) = device_state (machine_state b)\<rbrakk>
  \<Longrightarrow> cap_refs_respects_device_region a = cap_refs_respects_device_region b"
  by (simp add: cap_refs_respects_device_region_def cte_wp_at_caps_of_state dom_def cap_range_respects_device_region_def)

lemmas device_region_congs[cong] = pspace_respects_region_cong cap_refs_respects_region_cong

lemma dmo_invs1:
  assumes valid_mf: "\<And>P. \<lbrace>\<lambda>ms.  P (device_state ms)\<rbrace> f \<lbrace>\<lambda>r ms.  P (device_state ms)\<rbrace>"
  shows "\<lbrace>(\<lambda>s. \<forall>m. \<forall>(r,m')\<in>fst (f m). m = machine_state s \<longrightarrow> (\<forall>p.
       in_user_frame p s  \<or> underlying_memory m' p = underlying_memory m p) \<and>
         ((\<forall>irq. (interrupt_states s irq = IRQInactive \<longrightarrow> irq_masks m' irq) \<or> (irq_masks m' irq = irq_masks m irq))))
    and invs\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>_. invs\<rbrace>"
   apply (simp add: do_machine_op_def split_def)
   apply wp

   apply (clarsimp simp: invs_def cur_tcb_def valid_state_def
                         valid_machine_state_def valid_irq_handlers_def
                   intro!: valid_irq_states_machine_state_updateI
                   elim: valid_irq_statesE)
   apply (frule_tac P1 = "(=) (device_state (machine_state s))" in use_valid[OF _ valid_mf])
    apply simp
   apply clarsimp
   apply (intro conjI)
    apply (fastforce simp: invs_def cur_tcb_def valid_state_def
                           valid_machine_state_def
                    intro: valid_irq_states_machine_state_updateI
                     elim: valid_irq_statesE)
   apply fastforce
   done

lemma dmo_invs:
  assumes valid_mf: "\<And>P. \<lbrace>\<lambda>ms.  P (device_state ms)\<rbrace> f \<lbrace>\<lambda>r ms.  P (device_state ms)\<rbrace>"
  shows "\<lbrace>(\<lambda>s. \<forall>m. \<forall>(r,m')\<in>fst (f m). (\<forall>p.
       in_user_frame p s  \<or> underlying_memory m' p = underlying_memory m p) \<and>
         ((\<forall>irq. m = machine_state s \<longrightarrow>
           (interrupt_states s irq = IRQInactive \<longrightarrow> irq_masks m' irq) \<or> (irq_masks m' irq = irq_masks m irq))))
    and invs\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs1 valid_mf)
  apply clarsimp
  apply (drule spec, drule(1) bspec)
  apply simp
  done

lemma kheap_update_rewrite [simp]:
 "kheap (ms_ta_update taf s) t = kheap s t"
  by simp

lemma ms_ta_update_fn_eq:
  "taf' = taf \<Longrightarrow>
  ms_ta_update taf' s = ms_ta_update taf s"
  by simp

lemma union_fixedpoint:
  "(\<union>) A \<circ> (\<union>) A = (\<union>) A"
  by fastforce

lemma as_user_bind[wp]:
  "as_user t (f >>= g) = (as_user t f) >>= (\<lambda>x. as_user t (g x))"
  apply (monad_eq simp: as_user_def select_f_def set_object_def get_object_def gets_the_def get_tcb_def touch_object_def2 simpler_do_machine_op_addTouchedAddresses_def)
  apply (clarsimp simp:ta_filter_def obind_def split: option.splits kernel_object.splits)
  apply (intro conjI impI allI;
         match premises in "kheap _ t = Some (TCB _)" \<Rightarrow> succeed \<bar> _ \<Rightarrow> fastforce)
    apply clarsimp
    apply (rename_tac value_g s tcb fail_g value_f fail_f)
    apply (rule_tac x="value_f" in exI)
    apply (rule_tac x="ms_ta_update ((\<union>) (obj_range t
                    (TCB (tcb\<lparr>tcb_arch :=
                                arch_tcb_context_set fail_f
                                 (tcb_arch tcb)\<rparr>))) \<circ>
             (\<union>) (obj_range t (TCB tcb))) s\<lparr>kheap := kheap s(t \<mapsto> TCB (tcb\<lparr>tcb_arch := arch_tcb_context_set fail_f (tcb_arch tcb)\<rparr>))\<rparr>" in exI)
    apply (intro conjI allI; clarsimp)
    apply (intro conjI)
     apply (rule_tac x="fail_f" in exI; clarsimp)
    apply (rule_tac x="fail_g" in exI; clarsimp)
    apply (clarsimp simp: obj_range_def union_fixedpoint)
   apply clarsimp
   apply (rename_tac value_g ta s tcb value_f fail_g ko)
   apply (drule_tac x="ko" in spec)
   apply clarsimp
   apply (case_tac ko; blast?)
   apply (rename_tac tcb_2)
   apply (drule_tac x=tcb_2 in spec)
   apply clarsimp
   apply (rule_tac x=ba in exI)
   apply (intro conjI impI)
    apply fastforce
   apply (clarsimp simp: obj_range_def union_fixedpoint)
  apply (rename_tac tcb_2)
  apply (case_tac "snd (f (arch_tcb_context_get (tcb_arch tcb_2)))")
   apply simp
  apply clarsimp
  apply (rule iffI)
   apply fastforce
  apply clarsimp
  apply (case_tac "kheap s' t = None")
   apply fastforce
  apply clarsimp
  apply (rename_tac ko)
  apply (case_tac ko; (solves auto)?)
  apply clarsimp
  apply blast
  done

lemma as_user_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> as_user t m \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  unfolding as_user_def
  apply (wpsimp wp: set_object_wp_strong touch_object_wp')
  apply (clarsimp simp: obj_at_def)
  done

lemma as_user_no_del_ntfn[wp]:
  "\<lbrace>ntfn_at p\<rbrace> as_user t m \<lbrace>\<lambda>rv. ntfn_at p\<rbrace>"
  by (simp add: ntfn_at_typ, rule as_user_typ_at)


lemma as_user_no_del_ep[wp]:
  "\<lbrace>ep_at p\<rbrace> as_user t m \<lbrace>\<lambda>rv. ep_at p\<rbrace>"
  by (simp add: ep_at_typ, rule as_user_typ_at)

lemma set_simple_ko_tcb[wp]:
  "set_simple_ko f ep v \<lbrace> tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ) wp


lemma set_simple_ko_pred_tcb_at [wp]:
  "set_simple_ko g ep v \<lbrace> pred_tcb_at proj f t \<rbrace>"
  by(set_simple_ko_method wp_thm: set_object_at_obj2 simp_thm: pred_tcb_at_def)


lemma set_endpoint_ep_at[wp]:
  "set_endpoint ptr val \<lbrace>ep_at ptr'\<rbrace>"
  by (simp add: ep_at_typ, wp)

lemma set_notification_ntfn_at[wp]:
  "set_notification ptr val \<lbrace>ntfn_at ptr'\<rbrace>"
  by (simp add: ntfn_at_typ, wp)


lemma cte_wp_at_neg2:
  "(\<not> cte_wp_at P p s) = (cte_at p s \<longrightarrow> cte_wp_at (\<lambda>cap. \<not> P cap) p s)"
  by (fastforce simp: cte_wp_at_def)


lemma cte_wp_at_neg:
  "cte_wp_at (\<lambda>cap. \<not> P cap) p s = (cte_at p s \<and> \<not> cte_wp_at P p s)"
  by (fastforce simp: cte_wp_at_def)


lemma valid_cte_at_neg_typ:
  assumes x: "\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<not> cte_at p s\<rbrace> f \<lbrace>\<lambda>rv s. \<not> cte_at p s\<rbrace>"
  apply (simp add: cte_at_typ)
  apply (rule hoare_vcg_conj_lift [OF x])
  apply (simp only: imp_conv_disj)
  apply (rule hoare_vcg_disj_lift [OF x])
  apply (rule hoare_vcg_prop)
  done


lemma ex_nonz_cap_to_pres:
  assumes y: "\<And>P p. \<lbrace>cte_wp_at P p\<rbrace> f \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  shows      "\<lbrace>ex_nonz_cap_to p\<rbrace> f \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp only: ex_nonz_cap_to_def not_ex)
  apply (intro hoare_vcg_disj_lift hoare_vcg_ex_lift
               y hoare_vcg_all_lift valid_cte_at_neg_typ)
  done


lemma set_simple_ko_ex_cap[wp]:
  "set_simple_ko f p' v \<lbrace>ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)


crunch it[wp]: set_simple_ko "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_simple_ko_idle[wp]:
  "\<lbrace>obj_at (\<lambda>ko. partial_inv f ko \<noteq> None) ptr and valid_idle\<rbrace>
   set_simple_ko f ptr ep \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  by (set_simple_ko_method simp_thm: obj_at_def valid_idle_def pred_tcb_at_def
                             wp_thm: set_object_wp)

(* FIXME-NTFN *)
lemma ep_redux_simps:
  "valid_ep (case xs of [] \<Rightarrow> Structures_A.IdleEP | y # ys \<Rightarrow> Structures_A.SendEP (y # ys))
        = (\<lambda>s. distinct xs \<and> (\<forall>t\<in>set xs. tcb_at t s))"
  "valid_ep (case xs of [] \<Rightarrow> Structures_A.IdleEP | y # ys \<Rightarrow> Structures_A.RecvEP (y # ys))
        = (\<lambda>s. distinct xs \<and> (\<forall>t\<in>set xs. tcb_at t s))"
  "valid_ntfn (ntfn\<lparr>ntfn_obj := (case xs of [] \<Rightarrow> Structures_A.IdleNtfn | y # ys \<Rightarrow> Structures_A.WaitingNtfn (y # ys))\<rparr>)
        = (\<lambda>s. distinct xs \<and> (\<forall>t\<in>set xs. tcb_at t s)
             \<and> (case ntfn_bound_tcb ntfn of
                 Some t \<Rightarrow> tcb_at t s \<and> (case xs of y # ys \<Rightarrow> xs = [t] | _ \<Rightarrow> True)
               | _ \<Rightarrow> True))"
  "ep_q_refs_of (case xs of [] \<Rightarrow> Structures_A.IdleEP | y # ys \<Rightarrow> Structures_A.SendEP (y # ys))
        = (set xs \<times> {EPSend})"
  "ep_q_refs_of (case xs of [] \<Rightarrow> Structures_A.IdleEP | y # ys \<Rightarrow> Structures_A.RecvEP (y # ys))
        = (set xs \<times> {EPRecv})"
  "ntfn_q_refs_of (case xs of [] \<Rightarrow> Structures_A.IdleNtfn | y # ys \<Rightarrow> Structures_A.WaitingNtfn (y # ys))
        = (set xs \<times> {NTFNSignal})"
  by (fastforce split: list.splits option.splits
                 simp: valid_ep_def valid_ntfn_def valid_bound_tcb_def)+


crunch arch[wp]: set_simple_ko "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)

crunch irq_node_inv[wp]: set_simple_ko "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma set_simple_ko_global_refs [wp]:
  "set_simple_ko f ntfn p \<lbrace>valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift; wpsimp)


lemma set_simple_ko_reply[wp]:
  "set_simple_ko f p ep \<lbrace>valid_reply_caps\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)

lemma set_simple_ko_reply_masters[wp]:
  "set_simple_ko f p ep \<lbrace>valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)

lemma obj_at_ko_atE:
  "\<lbrakk> obj_at P ptr s; ko_at k ptr s; P k \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (clarsimp simp: obj_at_def)

crunch interrupt_states[wp]: set_simple_ko "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma set_object_non_arch:
  "arch_obj_pred P' \<Longrightarrow>
   \<lbrace>(\<lambda>s. P (obj_at P' p' s)) and K(non_arch_obj ko) and obj_at non_arch_obj p \<rbrace>
    set_object ta_f p ko
   \<lbrace>\<lambda>r s. P (obj_at P' p' s)\<rbrace>"
  unfolding set_object_def
  apply (wp touch_object_wp')
  apply clarsimp
  apply (erule_tac P=P in rsubst)
  apply (clarsimp simp: obj_at_def)
  by (rule arch_obj_predE)

lemma set_object_non_pagetable:
  "vspace_obj_pred P' \<Longrightarrow>
   \<lbrace>(\<lambda>s. P (obj_at P' p' s)) and K(non_vspace_obj ko) and obj_at non_vspace_obj p \<rbrace>
    set_object ta_f p ko
   \<lbrace>\<lambda>r s. P (obj_at P' p' s)\<rbrace>"
  unfolding set_object_def
  apply (wp touch_object_wp)
  apply clarsimp
  apply (erule_tac P=P in rsubst)
  apply (clarsimp simp: obj_at_def)
  by (rule vspace_obj_predE)

lemma set_object_memory[wp]:
  "\<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace>
    set_object ta_f p ko
   \<lbrace>\<lambda>_ s. P (underlying_memory (machine_state s))\<rbrace>"
  unfolding set_object_def
  apply (wp touch_object_wp)
  by simp

end

locale non_aobj_op = fixes f
  assumes aobj_at: "\<And>P P' p. arch_obj_pred P' \<Longrightarrow>
                              \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>" and
          arch_state[wp]: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"

context non_aobj_op begin

lemma valid_arch_state[wp]:"\<lbrace>valid_arch_state\<rbrace> f \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift_aobj_at; wp aobj_at; simp)

end


locale non_vspace_op = fixes f
  assumes vsobj_at: "\<And>P P' p. vspace_obj_pred P' \<Longrightarrow>
                              \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (obj_at P' p s)\<rbrace>" and
          arch_state'[wp]: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"

sublocale non_aobj_op < non_vspace_op
  apply (unfold_locales)
  apply (auto simp: vspace_pred_imp arch_state aobj_at)
  done

context non_vspace_op begin

lemma valid_vspace_obj[wp]:"f \<lbrace>valid_vspace_objs\<rbrace>"
  by (rule valid_vspace_objs_lift_weak; wp vsobj_at; simp)

lemma vs_lookup[wp]: "f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  by (rule vs_lookup_vspace_obj_at_lift; wp vsobj_at; simp)

lemma vs_lookup_pages[wp]: "f \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace>"
  by (rule vs_lookup_pages_vspace_obj_at_lift; wp vsobj_at; simp)

lemma valid_global_objs[wp]: "f \<lbrace>valid_global_objs\<rbrace>"
  by (rule valid_global_objs_lift_weak, (wp vsobj_at)+)

lemma valid_global_vspace_mappings[wp]:
  "f \<lbrace>valid_global_vspace_mappings\<rbrace>"
  by (rule valid_global_vspace_mappings_lift, (wp vsobj_at)+)

lemma valid_asid_map[wp]: "f \<lbrace>valid_asid_map\<rbrace>"
  by (rule valid_asid_map_lift, (wp vsobj_at)+)

lemma valid_kernel_mappings[wp]: "f \<lbrace>valid_kernel_mappings\<rbrace>"
  by (rule valid_kernel_mappings_lift, (wp vsobj_at)+)

lemma equal_kernel_mappings[wp]: "f \<lbrace>equal_kernel_mappings\<rbrace>"
  by (rule equal_kernel_mappings_lift; wp vsobj_at)

lemma in_user_frame[wp]:"f \<lbrace>in_user_frame p\<rbrace>"
  by (rule in_user_frame_obj_pred_lift; wp vsobj_at; simp)

end

locale non_mem_op =
  fixes f
  assumes memory[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (underlying_memory (machine_state s))\<rbrace>"

(* non_vspace_op version *)
locale non_vspace_non_mem_op = non_vspace_op f + non_mem_op f for f
begin

lemma valid_machine_state[wp]: "\<lbrace>valid_machine_state\<rbrace> f \<lbrace>\<lambda>rv. valid_machine_state\<rbrace>"
  unfolding valid_machine_state_def
  by (wp hoare_vcg_disj_lift hoare_vcg_all_lift vsobj_at memory)

end


locale non_aobj_non_mem_op = non_aobj_op f + non_mem_op f for f

sublocale non_aobj_non_mem_op < non_vspace_non_mem_op ..

(* non_vspace_op version *)

locale non_cap_op =
  fixes f
  assumes caps[wp]: "\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"

locale non_vspace_non_cap_op = non_vspace_op f + non_cap_op f for f
begin

lemma valid_arch_caps[wp]: "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  by (rule valid_arch_caps_lift_weak[OF arch_state' vsobj_at caps])

end

locale non_aobj_non_cap_op = non_aobj_op f + non_cap_op f for f

sublocale non_aobj_non_cap_op < non_vspace_non_cap_op ..

(* non_vspace_op version *)
locale non_vspace_non_cap_non_mem_op = non_vspace_non_mem_op f + non_vspace_non_cap_op f for f
locale non_aobj_non_cap_non_mem_op = non_aobj_non_mem_op f + non_aobj_non_cap_op f for f

sublocale non_aobj_non_cap_non_mem_op < non_vspace_non_cap_non_mem_op ..

(* any monad that is `tainv` will of course hold the above properties too *)
sublocale touched_addresses_inv \<subseteq> non_aobj_non_cap_non_mem_op m
  by (unfold_locales; rule agnostic_preserved; clarsimp simp: ta_agnostic_def)


lemma shows
  sts_caps_of_state[wp]:
    "set_thread_state t st \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>" and
  set_bound_caps_of_state[wp]:
    "set_bound_notification t e \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>" and
  as_user_caps_of_state[wp]:
    "as_user p f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"

  unfolding set_thread_state_def set_bound_notification_def as_user_def set_object_def get_object_def
            set_mrs_def ta_filter_def obind_def
  apply (all \<open>(wp touch_object_wp' | wpc | simp)+ ; clarsimp, erule rsubst[where P=P], rule cte_wp_caps_of_lift\<close>)
  by (auto simp: cte_wp_at_cases2 tcb_cnode_map_def ta_filter_def dest!: get_tcb_SomeD
    split:option.splits)

lemma
  store_word_offs_caps_of_state[wp]:
   "store_word_offs a b c \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding store_word_offs_def do_machine_op_def[abs_def] touch_objects_def
  by wpsimp

lemma
  set_mrs_caps_of_state[wp]:
   "set_mrs thread buf msgs \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding set_mrs_def set_object_def[abs_def] get_object_def
  apply (wp mapM_x_inv_wp touch_object_wp' | wpc | simp add: zipWithM_x_mapM_x split del: if_split | clarsimp)+
  apply (safe; erule rsubst[where P=P], rule cte_wp_caps_of_lift)
  by (auto simp: cte_wp_at_cases2 tcb_cnode_map_def ta_filter_def dest!: get_tcb_SomeD)

interpretation
  set_simple_ko: non_aobj_non_cap_non_mem_op "set_simple_ko c p ep" +
  sts: non_aobj_non_cap_non_mem_op "set_thread_state p st" +
  sbn: non_aobj_non_cap_non_mem_op "set_bound_notification p b" +
  as_user: non_aobj_non_cap_non_mem_op "as_user p g" +
  thread_set: non_aobj_non_mem_op "thread_set f p" +
  set_cap: non_aobj_non_mem_op "set_cap cap p'"
  apply (all \<open>unfold_locales; (wp ; fail)?\<close>)
  unfolding set_simple_ko_def set_thread_state_def
            set_bound_notification_def thread_set_def set_cap_def[simplified split_def]
            as_user_def set_mrs_def
  apply -
  apply (all \<open>(wp set_object_non_arch[THEN hoare_set_object_weaken_pre] get_object_wp
           touch_object_wp' | wpc | simp split del: if_split)+\<close>)
  apply (auto simp: obj_at_def[abs_def] partial_inv_def the_equality
               split: Structures_A.kernel_object.splits)[1]
  by (fastforce simp: obj_at_def[abs_def] a_type_def
               split: Structures_A.kernel_object.splits)+

lemmas set_cap_arch[wp] = set_cap.arch_state

interpretation
  store_word_offs: non_aobj_non_cap_op "store_word_offs a b c"
  apply unfold_locales
  unfolding store_word_offs_def do_machine_op_def[abs_def] touch_objects_def
  by wpsimp+

lemma store_word_offs_obj_at_P[wp]:
  "store_word_offs a b c \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  unfolding store_word_offs_def touch_objects_def
  by (wp | fastforce)+

interpretation
  set_mrs: non_aobj_non_cap_op "set_mrs thread buf msgs"
  apply unfold_locales
    apply (all \<open>(wp touch_object_wp ; fail)?\<close>)
   unfolding set_mrs_def set_object_def get_object_def
   apply (all \<open>(wp mapM_x_inv_wp touch_object_wp | wpc | simp add: zipWithM_x_mapM_x split del: if_split | clarsimp)+\<close>)
  apply (rule drop_imp)
  apply (clarsimp simp: obj_at_def get_tcb_def ta_filter_def split: kernel_object.splits option.splits)
  subgoal for _ P' by (subst arch_obj_predE[where P="P'"]) auto
  done

lemma valid_irq_handlers_lift:
  assumes x: "\<And>P. f \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  assumes y: "\<And>P. f \<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace>"
  shows      "f \<lbrace>valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_use_eq [where f=caps_of_state, OF x y])
  done

lemmas set_simple_ko_valid_irq_handlers[wp]
    = valid_irq_handlers_lift [OF set_simple_ko_caps_of_state set_simple_ko_interrupt_states]


lemmas hoare_use_eq_irq_node = hoare_use_eq[where f=interrupt_irq_node]


lemma cap_table_at_lift_valid:
  "\<lbrakk> \<And>T. f \<lbrace>typ_at T p\<rbrace> \<rbrakk>
       \<Longrightarrow> f \<lbrace>cap_table_at n p\<rbrace>"
  by (simp add: cap_table_at_typ)


lemmas cap_table_at_lift_irq =
  hoare_use_eq_irq_node [OF _ cap_table_at_lift_valid]


lemma set_simple_ko_only_idle [wp]:
  "set_simple_ko f p ntfn \<lbrace>only_idle\<rbrace>"
  by (wp only_idle_lift)

lemma set_simple_ko_cap_refs_kernel_window[wp]:
  "set_simple_ko f p ep \<lbrace>cap_refs_in_kernel_window\<rbrace>"
  by (set_simple_ko_method
        wp_thm: set_object_cap_refs_in_kernel_window[THEN hoare_set_object_weaken_pre]
                get_object_wp
      simp_thm: is_ep_def is_ntfn_def)

lemma set_simple_ko_cap_refs_respects_device_region[wp]:
  "set_simple_ko f p ep \<lbrace>cap_refs_respects_device_region\<rbrace>"
  by (set_simple_ko_method
        wp_thm: set_object_cap_refs_respects_device_region[THEN hoare_set_object_weaken_pre]
                get_object_wp
      simp_thm: is_ep_def is_ntfn_def)


(* There are two wp rules for preserving valid_ioc over set_object.
   First, the more involved rule for CNodes and TCBs *)
lemma set_object_valid_ioc_caps:
  "\<lbrace>\<lambda>s. valid_ioc s \<and> typ_at (a_type obj) ptr s \<and>
    (\<forall>b. is_original_cap s (ptr,b) \<longrightarrow> null_filter (cap_of obj) b \<noteq> None)\<rbrace>
   set_object ta_f ptr obj
   \<lbrace>\<lambda>_ s. valid_ioc s\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong)
  apply (clarsimp simp add: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (case_tac "a=ptr", simp_all add: cte_wp_at_cases)
  apply (drule spec, erule impE, assumption)
  apply (erule disjE)
   apply (rule disjI1)
   apply (clarsimp simp add: obj_at_def a_type_simps)
   apply (fastforce simp: a_type_def cap_of_def
                         null_filter_def
                  split: Structures_A.kernel_object.splits if_split_asm)
  apply (rule disjI2)
  apply (clarsimp simp add: obj_at_def a_type_simps)
  apply (fastforce simp: a_type_def cap_of_def tcb_cnode_map_def null_filter_def
                 split: Structures_A.kernel_object.splits if_split_asm)
  done


(* Second, the simpler rule suitable for all objects except CNodes and TCBs. *)
lemma set_object_valid_ioc_no_caps:
  "\<lbrace>\<lambda>s. valid_ioc s \<and> typ_at (a_type obj) ptr s \<and> \<not> is_tcb obj \<and>
        (\<forall>n. \<not> is_cap_table n obj) \<rbrace>
   set_object ta_f ptr obj
   \<lbrace>\<lambda>_ s. valid_ioc s\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def)
  apply (clarsimp simp add: valid_ioc_def cte_wp_at_cases is_tcb)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (elim disjE)
   prefer 2
   apply (fastforce simp: obj_at_def a_type_def
                   split: Structures_A.kernel_object.splits if_split_asm)
  apply (fastforce simp: obj_at_def a_type_def is_cap_table_def well_formed_cnode_n_def
                  split: Structures_A.kernel_object.splits if_split_asm)
  done


lemma set_simple_ko_valid_ioc[wp]:
  "set_simple_ko f ptr val \<lbrace>valid_ioc\<rbrace>"
  by (set_simple_ko_method wp_thm: set_object_valid_ioc_no_caps[THEN hoare_set_object_weaken_pre]
                                   get_object_wp
           simp_thm: is_tcb_def is_cap_table_def)

lemma set_object_machine_state[wp]:
  "\<lbrace>\<lambda>s. P (machine_state (ms_ta_obj_update p ko s)) \<rbrace>
     set_object ta_f p ko \<lbrace>\<lambda>_ s. P (machine_state s)\<rbrace>"
  by (wpsimp wp: set_object_wp_strong)

lemma set_simple_ko_machine_state[wp]:
  "\<lbrace>\<lambda>s. P (machine_state (ms_ta_obj_update ptr (f val) s)) \<rbrace>
     set_simple_ko f ptr val \<lbrace>\<lambda>_ s. P (machine_state s)\<rbrace>"
  by (set_simple_ko_method wp_thm: get_object_wp)

lemma valid_irq_states_triv:
  assumes irqs: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace> f \<lbrace>\<lambda>_ s. P (interrupt_states s)\<rbrace>"
  assumes ms: "\<And>P. \<lbrace>\<lambda>s. P (machine_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (machine_state s)\<rbrace>"
  shows
  "\<lbrace> valid_irq_states \<rbrace> f \<lbrace>\<lambda>_. valid_irq_states \<rbrace>"
  apply(clarsimp simp: valid_def valid_irq_states_def valid_irq_masks_def)
  apply(case_tac "interrupt_states s irq = IRQInactive")
   apply(erule use_valid[OF _ ms])
   apply blast
  apply(drule_tac P1="\<lambda>x. x irq \<noteq> IRQInactive" in use_valid[OF _ irqs])
   apply assumption
  by blast

lemma set_object_valid_irq_states[wp]:
  "set_object ta_f p ko \<lbrace> valid_irq_states \<rbrace>"
  apply(clarsimp simp: valid_def valid_irq_states_def valid_irq_masks_def)
  apply(case_tac "interrupt_states s irq = IRQInactive")
   apply(erule use_valid[OF _ set_object_machine_state])
   apply simp
  apply(drule_tac P1="\<lambda>x. x irq \<noteq> IRQInactive" in use_valid[OF _ set_object_interrupt_states])
   apply assumption
  by blast

crunch valid_irq_states[wp]: set_simple_ko "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps rule: valid_irq_states_triv)

crunch valid_irq_states[wp]: set_cap "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)

sublocale touched_addresses_inv \<subseteq> valid_irq_states: touched_addresses_P_inv _ _ valid_irq_states
  by unfold_locales (clarsimp simp:valid_irq_states_def ta_agnostic_def)

crunch valid_irq_states[wp]: thread_set "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_irq_states[wp]: set_thread_state, set_bound_notification "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)

lemma set_ntfn_minor_invs:
  "\<lbrace>invs and ntfn_at ptr
         and obj_at (\<lambda>ko. refs_of ko = ntfn_q_refs_of (ntfn_obj val) \<union> ntfn_bound_refs (ntfn_bound_tcb val)) ptr
         and valid_ntfn val
         and (\<lambda>s. \<forall>typ. (idle_thread s, typ) \<notin> ntfn_q_refs_of (ntfn_obj val))
         and (\<lambda>s. live (Notification val) \<longrightarrow> ex_nonz_cap_to ptr s)\<rbrace>
     set_notification ptr val
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp set_simple_ko_valid_objs valid_irq_node_typ
                    valid_irq_handlers_lift valid_ioports_lift)
  apply (clarsimp simp: ntfn_at_def2
                  elim!: rsubst[where P=sym_refs]
                 intro!: ext
                  dest!: obj_at_state_refs_ofD)
  done

lemma do_machine_op_result[wp]:
  "\<lbrace>P\<rbrace> mop \<lbrace>\<lambda>rv s. Q rv\<rbrace> \<Longrightarrow>
   \<lbrace>\<lambda>s. P (machine_state s)\<rbrace> do_machine_op mop \<lbrace>\<lambda>rv s. Q rv\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply clarsimp
  apply (erule(2) use_valid)
  done


lemma dmo_zombies[wp]:
  "do_machine_op oper \<lbrace>zombies_final\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: zombies_final_pspaceI)
  done


lemma dmo_iflive[wp]:
  "do_machine_op oper \<lbrace>if_live_then_nonz_cap\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: iflive_pspaceI)
  done


lemma dmo_ifunsafe[wp]:
  "do_machine_op oper \<lbrace>if_unsafe_then_cap\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: ifunsafe_pspaceI)
  done


lemma dmo_refs_of[wp]:
  "do_machine_op oper \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: state_refs_of_pspaceI)
  done


lemma dmo_hyp_refs_of[wp]:
  "do_machine_op oper \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: state_hyp_refs_of_pspaceI)
  done

crunch it[wp]: do_machine_op "\<lambda>s. P (idle_thread s)"

crunch irq_node[wp]: do_machine_op "\<lambda>s. P (interrupt_irq_node s)"


crunch cte_wp_at[wp]: do_machine_op "\<lambda>s. P (cte_wp_at P' c s)"
 (wp: crunch_wps)


crunch valid_idle[wp]: do_machine_op "valid_idle"
  (wp: crunch_wps simp: crunch_simps)


crunch reply[wp]: do_machine_op "valid_reply_caps"

crunch reply_masters[wp]: do_machine_op "valid_reply_masters"

crunch valid_irq_handlers[wp]: do_machine_op "valid_irq_handlers"
  (simp: valid_irq_handlers_def)

crunch valid_global_objs[wp]: do_machine_op "valid_global_objs"

crunch valid_global_vspace_mappings[wp]: do_machine_op "valid_global_vspace_mappings"

crunch valid_arch_caps[wp]: do_machine_op "valid_arch_caps"


lemma dmo_cap_to[wp]:
  "do_machine_op mop \<lbrace>ex_nonz_cap_to p\<rbrace>"
  by (simp add: ex_nonz_cap_to_def, wp hoare_vcg_ex_lift)

lemma dmo_st_tcb [wp]:
  "do_machine_op f \<lbrace>pred_tcb_at proj P t\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done


crunch ct[wp]: do_machine_op "\<lambda>s. P (cur_thread s)" (wp: select_wp)

crunches do_machine_op
  for aobjs_of[wp]: "\<lambda>s. P (aobjs_of False s)"

lemma do_machine_op_valid_arch [wp]:
  "do_machine_op f \<lbrace>valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift; wpsimp)

lemma do_machine_op_vs_lookup [wp]:
  "do_machine_op f \<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace>"
  apply (rule vs_lookup_vspace_obj_at_lift)
  apply (simp add: do_machine_op_def split_def)
  apply (wp | simp)+
  done


lemma dmo_inv:
  assumes R: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  shows "\<lbrace>P\<rbrace> do_machine_op f \<lbrace>\<lambda>_. P\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_f_wp)
  apply (clarsimp simp del: )
  apply (drule in_inv_by_hoareD [OF R])
  apply simp
  done


lemma dom_objs [wp]:
  "do_machine_op f \<lbrace>valid_objs\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (fastforce intro: valid_objs_pspaceI)
  done


lemma tcb_cap_wp_at:
  "\<lbrakk>tcb_at t s; valid_objs s; ref \<in> dom tcb_cap_cases;
    \<forall>cap st getF setF restr.
    tcb_cap_cases ref = Some (getF, setF, restr) \<and> restr t st cap \<longrightarrow> Q cap\<rbrakk> \<Longrightarrow>
   cte_wp_at Q (t, ref) s"
  apply (clarsimp simp: cte_wp_at_cases tcb_at_def dest!: get_tcb_SomeD)
  apply (rename_tac getF setF restr)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp add: valid_obj_def valid_tcb_def ta_filter_def)
  apply (erule_tac x="(getF, setF, restr)" in ballE)
   apply (fastforce simp add: ranI)+
  done


lemma tcb_cap_valid_caps_of_stateD:
  "\<lbrakk> caps_of_state s p = Some cap; valid_objs s \<rbrakk> \<Longrightarrow> tcb_cap_valid cap p s"
  apply (rule cte_wp_tcb_cap_valid)
   apply (simp add: cte_wp_at_caps_of_state)
  apply assumption
  done


lemma add_mask_eq:
  "\<lbrakk>is_aligned (w::'a::len word) n; x \<le> 2 ^ n - 1; n < len_of TYPE('a)\<rbrakk>
   \<Longrightarrow> (w + x) && mask n = x"
  by (drule is_aligned_add_helper) auto


lemma thread_get_wp':
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at (TCB tcb) ptr s \<longrightarrow> P (f tcb) s\<rbrace> thread_get f ptr \<lbrace>P\<rbrace>"
  apply (simp add: thread_get_def)
  apply wp
  apply clarsimp
  apply (clarsimp simp: obj_at_def ta_filter_def dest!: get_tcb_SomeD split:if_splits)
  done


crunch valid_ioc[wp]: do_machine_op valid_ioc

crunch inv[wp]: get_irq_slot "P"

lemmas set_object_typ_ats [wp] = abs_typ_at_lifts [OF set_object_typ_at]

lemma typ_at_pspace_aligned:
  assumes type_invs: "\<And>T p. f \<lbrace>typ_at T p\<rbrace>"
  assumes dom_shrink: "\<And>x. f \<lbrace>\<lambda>s. x \<notin> dom (kheap s)\<rbrace>"
  shows "f \<lbrace>pspace_aligned\<rbrace>"
  apply (clarsimp simp: valid_def pspace_aligned_def)
  apply (drule_tac x = x in bspec)
   subgoal indom
    apply (rule ccontr)
    apply (drule(1) use_valid[OF _ dom_shrink])
    apply force
   done
  apply (frule(1) indom)
  apply (clarsimp simp: dom_def obj_bits_T)
  apply (drule use_valid[OF _ type_invs])
   apply (simp add: obj_at_def)
   apply (intro exI conjI, simp+)
  apply (simp add: obj_at_def)
  done

lemmas set_object_typ_at[wp] = set_object_typ_at[where P="\<lambda>x. x"]

lemma set_object_dom_shrink[wp]:
  "set_object ta_f pt obj \<lbrace>\<lambda>s. p \<notin> dom (kheap s)\<rbrace>"
  apply (wp set_object_typ_at get_object_wp touch_object_wp | simp add: set_object_def)+
  apply (clarsimp simp: obj_at_def split: if_split_asm)
  done

lemma set_aobject_zombies[wp]:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>\<lambda>s. zombies_final s\<rbrace>"
  apply (wp set_object_zombies[THEN hoare_set_object_weaken_pre])
  apply (clarsimp simp: obj_at_def same_caps_def a_type_def
                 split: kernel_object.split_asm if_split_asm)
  done

lemma set_aobject_state_refs[wp]:
  "set_object ta_f p (ArchObj obj) \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong
              simp: obj_at_def a_type_def
             split: kernel_object.split_asm if_split_asm)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  by (clarsimp simp: state_refs_of_def)

lemma set_aobject_caps_of_state [wp]:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  apply (wpsimp wp: set_object_wp_strong simp: obj_at_def a_type_def)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ y
  by (cases y, auto simp: cte_wp_at_cases a_type_def)
  done

lemma set_aobject_cte_wp_at:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply wp
  done

lemma set_object_is_original_cap[wp]:
  "set_object ta_f a b \<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace>"
  by (wpsimp wp: get_object_wp touch_object_wp simp: set_object_def)

lemma set_cap_is_original_cap[wp]:
  "set_cap a b \<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace>"
  by (wpsimp wp: get_object_wp touch_object_wp simp: set_cap_def)

lemma set_aobject_valid_mdb[wp]:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>\<lambda>s. valid_mdb s\<rbrace>"
  apply (rule valid_mdb_lift)
    apply (wp set_object_no_cdt)
  apply (clarsimp simp: set_object_def)
  apply (wp get_object_wp | simp)+
  done

lemma set_aobject_pred_tcb_at[wp]:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_object_def)
  apply (wp get_object_wp touch_object_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def a_type_def)
  done

lemma set_aobject_cur_tcb [wp]:
  "set_object ta_f ptr (ArchObj obj)  \<lbrace>\<lambda>s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]) wp+

lemma set_aobject_valid_idle[wp]:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>\<lambda>s. valid_idle s\<rbrace>"
  by (wpsimp wp: valid_idle_lift)

lemma set_aobject_reply_caps[wp]:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)

lemma set_aobject_reply_masters[wp]:
  "set_object ta_f ptr (ArchObj obj) \<lbrace>valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)

lemma dmo_ct_in_state:
  "do_machine_op f \<lbrace>ct_in_state P\<rbrace>"
  apply (simp add: ct_in_state_def)
  apply (rule hoare_lift_Pf [where f=cur_thread])
  by wp+

subsection "TA Agnostic for invs"

sublocale touched_addresses_inv \<subseteq> valid_pspace: touched_addresses_P_inv _ _ valid_pspace
                                + valid_irq_states: touched_addresses_P_inv _ _ valid_irq_states
                                + valid_machine_state: touched_addresses_P_inv _ _ valid_machine_state
                                + cte_wp_at: touched_addresses_P_inv _ _ "cte_wp_at P p"
  by unfold_locales (simp add:ta_agnostic_def valid_irq_states_def valid_machine_state_def)+

sublocale touched_addresses_inv \<subseteq> valid_state: touched_addresses_P_inv _ _ valid_state
  apply unfold_locales
  apply (clarsimp simp: valid_state_def)
  apply (intro ta_agnostic_predconj)
  apply (solves \<open>clarsimp | clarsimp simp: ta_agnostic_def valid_irq_handlers_def\<close>)+
  done

sublocale touched_addresses_inv \<subseteq> invs: touched_addresses_P_inv _ _ invs
  apply unfold_locales
  apply (simp only:invs_def)
  apply (intro ta_agnostic_predconj)
   apply simp
  apply (clarsimp simp: cur_tcb_def tcb_at_def get_tcb_def ta_agnostic_def)
  done

(* this is a bit of a hack to make lemmas like `invs.ta_agnostic` available
   without specifying a (meaningful) monad. so now we can use base.invs.ta_agnostic for
   example. *)
interpretation base:
  touched_addresses_inv _ "return ()"
  by unfold_locales wp

end
