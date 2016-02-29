(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory KHeap_AI
imports "./$L4V_ARCH/ArchKHeap_AI"
begin


unqualify_facts (in Arch)
  pspace_in_kernel_window_atyp_lift
  valid_arch_objs_lift_weak 
  vs_lookup_aobj_at_lift
  vs_lookup_pages_aobj_at_lift

lemma get_object_wp:
  "\<lbrace>\<lambda>s. \<forall>ko. ko_at ko p s \<longrightarrow> Q ko s\<rbrace> get_object p \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: get_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def)
  done

lemma get_ntfn_wp:
  "\<lbrace>\<lambda>s. \<forall>ntfn. ko_at (Notification ntfn) ntfnptr s \<longrightarrow> P ntfn s\<rbrace> get_notification ntfnptr \<lbrace>P\<rbrace>"
  apply (simp add: get_notification_def)
  apply (wp get_object_wp | wpc)+
  apply clarsimp
  done

lemma get_object_inv [wp]: "\<lbrace>P\<rbrace> get_object t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (wp get_object_wp) simp


lemma get_tcb_rev:
  "kheap s p = Some (TCB t)\<Longrightarrow> get_tcb p s = Some t"
  by (clarsimp simp:get_tcb_def)


lemma get_tcb_SomeD: "get_tcb t s = Some v \<Longrightarrow> kheap s t = Some (TCB v)"
  apply (case_tac "kheap s t", simp_all add: get_tcb_def)
  apply (case_tac a, simp_all)
  done


lemma get_tcb_obj_atE[elim!]:
  "\<lbrakk> get_tcb t s = Some tcb; get_tcb t s = Some tcb \<Longrightarrow> P (TCB tcb) \<rbrakk> \<Longrightarrow> obj_at P t s"
  by (clarsimp dest!: get_tcb_SomeD simp: obj_at_def)


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


lemma typ_at_same_type:
  assumes "typ_at T p s" "a_type k = a_type ko" "kheap s p' = Some ko"
  shows "typ_at T p (s\<lparr>kheap := kheap s(p' \<mapsto> k)\<rparr>)"
  using assms 
  by (clarsimp simp: obj_at_def)


lemma cte_at_same_type:
  "\<lbrakk>cte_at t s; a_type k = a_type ko; kheap s p = Some ko\<rbrakk>
  \<Longrightarrow> cte_at t (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  apply (clarsimp simp: cte_at_cases del: disjCI)
  apply (elim exE disjE)
   apply (clarsimp simp: a_type_def well_formed_cnode_n_def length_set_helper
                  split: Structures_A.kernel_object.split_asm
                         split_if_asm)
  apply (clarsimp simp: a_type_def
                 split: Structures_A.kernel_object.split_asm
                        split_if_asm)
  done


lemma untyped_same_type:
  "\<lbrakk>valid_untyped (cap.UntypedCap r n f) s; a_type k = a_type ko; kheap s p = Some ko\<rbrakk>
  \<Longrightarrow> valid_untyped (cap.UntypedCap r n f) (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  unfolding valid_untyped_def
  by (clarsimp simp: obj_range_def obj_bits_T)

lemma hoare_to_pure_kheap_upd:
  assumes hoare[rule_format]: "\<And>f. (\<forall>P p T. \<lbrace>\<lambda>s. P (atyp_at T p s)\<rbrace> f \<lbrace>\<lambda>r s. P (atyp_at T p s)\<rbrace>) \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>\<lambda>_. P\<rbrace>"
  assumes typ_eq: "a_type k = a_type ko"
  assumes valid: "P (s :: ('z :: state_ext) state)"
  assumes at: "ko_at ko p s"
  shows "P (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  apply (rule use_valid[where f="
      do
        s' <- get;
        assert (s' = s);
        (modify (\<lambda>s. s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>));
        return undefined
      od", OF _ hoare valid])
  apply (fastforce simp add: simpler_modify_def get_def bind_def assert_def return_def[abs_def] fail_def)[1]
  apply wp
  apply (insert typ_eq at)
  apply clarsimp
  apply (erule_tac P=P in rsubst)
  by (auto simp add: obj_at_def a_type_def split: kernel_object.splits if_splits)

lemma valid_cap_same_type:
  "\<lbrakk> s \<turnstile> cap; a_type k = a_type ko; kheap s p = Some ko \<rbrakk> 
  \<Longrightarrow> s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr> \<turnstile> cap"
  apply (simp add: valid_cap_def split: cap.split )
  apply (auto elim!: typ_at_same_type
                     untyped_same_type
               simp: ntfn_at_typ ep_at_typ tcb_at_typ cap_table_at_typ
               intro!: hoare_to_pure_kheap_upd[OF valid_arch_cap_atyp,simplified obj_at_def]  
              split: option.split sum.split)
  done


lemma valid_obj_same_type:
  "\<lbrakk> valid_obj p' obj s; valid_obj p k s; kheap s p = Some ko; a_type k = a_type ko \<rbrakk>
   \<Longrightarrow> valid_obj p' obj (s\<lparr>kheap := kheap s(p \<mapsto> k)\<rparr>)"
  apply (cases obj)
      apply (clarsimp simp add: valid_obj_def valid_cs_def)
      apply (drule (1) bspec)
      apply (erule (2) valid_cap_same_type)
     apply (clarsimp simp add: valid_obj_def valid_tcb_def valid_bound_ntfn_def)
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
  done


lemma valid_arch_obj_same_type:
  "\<lbrakk>valid_arch_obj ao s;  kheap s p = Some ko; a_type ko' = a_type ko\<rbrakk>
  \<Longrightarrow> valid_arch_obj ao (s\<lparr>kheap := kheap s(p \<mapsto> ko')\<rparr>)"
    apply (rule hoare_to_pure_kheap_upd[OF valid_arch_obj_atyp])
    by (auto simp: obj_at_def)


lemma set_object_valid_objs:
  "\<lbrace>valid_objs and valid_obj p k and obj_at (\<lambda>ko. a_type k = a_type ko) p\<rbrace> 
  set_object p k 
  \<lbrace>\<lambda>r. valid_objs\<rbrace>"
  apply (clarsimp simp: valid_def set_object_def in_monad obj_at_def)
  apply (clarsimp simp: valid_objs_def dom_def)
  apply (case_tac "ptr = p")
   apply clarsimp
   apply (rule valid_obj_same_type, assumption+)
  apply clarsimp
  apply (subgoal_tac "valid_obj ptr y s")
   prefer 2
   apply fastforce
  apply (erule(3) valid_obj_same_type)
  done
   

lemma set_object_aligned:
  "\<lbrace>pspace_aligned and obj_at (\<lambda>ko. a_type k = a_type ko) p\<rbrace> 
  set_object p k
  \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  apply (clarsimp simp: valid_def in_monad set_object_def)
  apply (erule (1) pspace_aligned_obj_update)
  apply simp
  done


lemma assert_get_tcb:
  "\<lbrace> P \<rbrace> gets_the (get_tcb t) \<lbrace> \<lambda>r. P and tcb_at t \<rbrace>"
  by (clarsimp simp: valid_def in_monad gets_the_def tcb_at_def)

lemma dxo_wp_weak[wp]:
assumes xopv: "\<And>s f. P (trans_state f s) = P s"
shows
"\<lbrace>P\<rbrace> do_extended_op x \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding do_extended_op_def
  apply (simp add: split_def)
  apply wp
  apply (clarsimp simp: mk_ef_def)
  apply (simp add: xopv[simplified trans_state_update'])
done

lemma sts_ep_at_inv[wp]:
  "\<lbrace> ep_at ep \<rbrace> set_thread_state t s \<lbrace> \<lambda>rv. ep_at ep \<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | simp add: set_object_def)+
  apply (clarsimp simp: obj_at_def is_ep is_tcb get_tcb_def)
  done

lemma sts_ntfn_at_inv[wp]:
  "\<lbrace> ntfn_at ep \<rbrace> set_thread_state t s \<lbrace> \<lambda>rv. ntfn_at ep \<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp | simp add: set_object_def)+
  apply (clarsimp simp: obj_at_def is_ntfn is_tcb get_tcb_def)
  done

lemma sbn_ep_at_inv[wp]:
  "\<lbrace> ep_at ep \<rbrace> set_bound_notification t ntfn \<lbrace> \<lambda>rv. ep_at ep \<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wp | simp add: set_object_def)+
  apply (clarsimp simp: obj_at_def is_ep is_tcb get_tcb_def)
  done

lemma sbn_ntfn_at_inv[wp]:
  "\<lbrace> ntfn_at ep \<rbrace> set_bound_notification t ntfn \<lbrace> \<lambda>rv. ntfn_at ep \<rbrace>"
  apply (simp add: set_bound_notification_def)
  apply (wp | simp add: set_object_def)+
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
  "\<lbrace>K (P obj)\<rbrace> set_object p obj \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  by (clarsimp simp: set_object_def obj_at_def valid_def in_monad)


lemma set_object_valid_cap:
  "\<lbrace>valid_cap c and obj_at (\<lambda>k. a_type ko = a_type k) p\<rbrace> set_object p ko \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp only: obj_at_def)
  apply (rule valid_cap_same_type)
    apply auto
  done


lemma set_object_cte_at:
  "\<lbrace>cte_at c and obj_at (\<lambda>k. a_type ko = a_type k) p\<rbrace> set_object p ko \<lbrace>\<lambda>rv. cte_at c\<rbrace>"
  apply (clarsimp simp: set_object_def in_monad valid_def obj_at_def)
  apply (erule(2) cte_at_same_type)
  done


lemma obj_at_ko_atD:
  "obj_at P x s \<Longrightarrow> \<exists>k. ko_at k x s \<and> P k"
  by (clarsimp simp: obj_at_def)


lemma get_object_sp:
  "\<lbrace>P\<rbrace> get_object p \<lbrace>\<lambda>r. P and ko_at r p\<rbrace>"
  apply (simp add: get_object_def)
  apply wp
  apply (auto simp add: obj_at_def)
  done


lemma get_endpoint_sp:
  "\<lbrace>P\<rbrace> get_endpoint p \<lbrace>\<lambda>ep. ko_at (Endpoint ep) p and P\<rbrace>"
  apply (simp add: get_endpoint_def)
  apply wp
   prefer 2
   apply (rule get_object_sp)
  apply (case_tac kobj)
  apply (simp|wp)+
  done


lemma set_object_ko:
  "\<lbrace>ko_at obj ptr and K (x \<noteq> ptr)\<rbrace> set_object x ko \<lbrace>\<lambda>rv. ko_at obj ptr\<rbrace>"
  by (clarsimp simp add: valid_def set_object_def in_monad obj_at_def)




lemma tcb_aligned: "\<lbrakk> invs s; tcb_at t s \<rbrakk> \<Longrightarrow> is_aligned t 9"
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                        pspace_aligned_def)
  apply (clarsimp simp: tcb_at_def, drule get_tcb_SomeD)
  apply (erule my_BallE [where y=t])
   apply clarsimp
  apply simp
  done


lemma set_object_ko_at:
  "\<lbrace>\<top>\<rbrace> set_object p ko \<lbrace>\<lambda>_. ko_at ko p\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (simp add: obj_at_def)
  done

lemma get_ep_inv[wp]: "\<lbrace>P\<rbrace> get_endpoint ep \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: get_endpoint_def)
  apply wp
   defer
   apply (rule get_object_inv)
  apply (case_tac kobj, simp_all)
  done


lemma get_ntfn_inv[wp]: "\<lbrace>P\<rbrace> get_notification ep \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: get_notification_def)
  apply wp
   defer
   apply (rule get_object_inv)
  apply (case_tac kobj, simp_all)
  done

lemma get_ep_actual_ep[wp]:
  "\<lbrace> invs and ep_at ep \<rbrace> 
   get_endpoint ep 
   \<lbrace> \<lambda>rv. obj_at (\<lambda>k. k = Endpoint rv) ep \<rbrace>"
   apply (clarsimp simp add: get_endpoint_def get_object_def bind_def 
                             valid_def gets_def get_def return_def fail_def 
                             assert_def obj_at_def is_ep_def)
   apply (case_tac y, simp_all add: return_def)
done

lemma get_object_valid [wp]:
  "\<lbrace>valid_objs\<rbrace> get_object oref \<lbrace> valid_obj oref \<rbrace>"
  apply (simp add: get_object_def)
  apply wp
  apply (clarsimp simp add: valid_pspace_def valid_objs_def dom_def)
  apply fastforce
  done  

lemma get_ep_valid_ep[wp]:
  "\<lbrace> invs and ep_at ep \<rbrace> 
   get_endpoint ep 
   \<lbrace> valid_ep \<rbrace>"
  apply (simp add: get_endpoint_def)
  apply (rule hoare_seq_ext)
   prefer 2
   apply (rule hoare_pre_imp [OF _ get_object_valid])
   apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (case_tac kobj, simp_all)
      apply (wp | simp add: valid_obj_def)+
done

lemma get_ntfn_actual_ntfn[wp]:
  "\<lbrace> ntfn_at ntfn \<rbrace> 
   get_notification ntfn 
   \<lbrace> \<lambda>rv. obj_at (\<lambda>k. k = Notification rv) ntfn \<rbrace>"
   apply (clarsimp simp add: get_notification_def get_object_def bind_def 
                             valid_def gets_def get_def return_def fail_def 
                             assert_def obj_at_def is_ntfn_def)
   apply (case_tac y, simp_all add: return_def)
done

lemma get_ntfn_valid_ntfn[wp]:
  "\<lbrace> valid_objs and ntfn_at ntfn \<rbrace> 
   get_notification ntfn 
   \<lbrace> valid_ntfn \<rbrace>"
  apply (simp add: get_notification_def)
  apply (rule hoare_seq_ext)
   prefer 2
   apply (rule hoare_pre_imp [OF _ get_object_valid])
   apply (simp add: valid_objs_def valid_state_def valid_pspace_def)
  apply (case_tac kobj, simp_all)
      apply (wp | simp add: valid_obj_def)+
done

lemma set_ep_valid_objs[wp]:
  "\<lbrace>valid_ep v and valid_objs\<rbrace> set_endpoint ep v \<lbrace>\<lambda>rv s. valid_objs s\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply (wp set_object_valid_objs)
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp add: valid_obj_def obj_at_def)
  apply (case_tac r, simp_all add: a_type_def)
  done


lemma set_ep_aligned[wp]:
 "\<lbrace>pspace_aligned\<rbrace> set_endpoint ep v \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply (wp set_object_aligned)
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp add: obj_at_def a_type_def)
  apply (case_tac r, simp_all)
  done


lemma set_endpoint_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_endpoint p' ep \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (case_tac r, simp_all)
  apply (clarsimp simp: obj_at_def a_type_def)
  done


lemma set_endpoint_cte_wp_at[wp]:
  "\<lbrace>cte_wp_at P p\<rbrace> set_endpoint ep v \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def get_object_def)
  apply wp
  apply (fastforce simp: cte_wp_at_cases)
  done


lemma set_ntfn_valid_objs:
  "\<lbrace>valid_objs and valid_ntfn ntfn\<rbrace>
  set_notification p ntfn
  \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp set_object_valid_objs)
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp: valid_obj_def obj_at_def is_ntfn)
  apply (case_tac r, simp_all add: a_type_def)
  done


lemma set_ntfn_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_notification p ntfn \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp set_object_aligned)
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp simp add: obj_at_def is_ntfn)
  apply (case_tac r, simp_all add: a_type_def)
  done


lemma set_notification_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_notification p' ntfn \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_notification_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (case_tac r, simp_all)
  apply (clarsimp simp: obj_at_def a_type_def)
  done


lemma set_notification_cte_wp_at[wp]:
  "\<lbrace>cte_wp_at P p\<rbrace> set_notification ep v \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: set_notification_def set_object_def get_object_def)
  apply wp
  apply (fastforce simp: cte_wp_at_cases)
  done


lemma get_ntfn_ko:
  "\<lbrace>\<top>\<rbrace> get_notification ep \<lbrace>\<lambda>rv. ko_at (Notification rv) ep\<rbrace>"
  apply (simp add: get_notification_def)
  apply wp
   prefer 2
   apply (rule get_object_sp)
  apply (case_tac kobj)
  apply (wp|simp)+
  done


lemma obj_set_prop_at:
  "\<lbrace>\<lambda>s. P obj \<rbrace> set_object p obj \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (simp add: obj_at_def)
  done


lemma get_ntfn_sp: 
  "\<lbrace>P\<rbrace> get_notification p \<lbrace>\<lambda>ntfn. ko_at (Notification ntfn) p and P\<rbrace>"
  apply wp
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule get_ntfn_ko)
   apply (rule get_ntfn_inv)
  apply simp
  done


lemma set_ep_refs_of[wp]:
 "\<lbrace>\<lambda>s. P ((state_refs_of s) (ep := ep_q_refs_of val))\<rbrace>
    set_endpoint ep val
  \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply wp
  apply (fastforce simp: state_refs_of_def elim!: rsubst[where P=P])
  done


lemma pspace_distinct_same_type:
  "\<lbrakk> kheap s t = Some ko; a_type ko = a_type ko';  pspace_distinct s\<rbrakk>
    \<Longrightarrow> pspace_distinct (s\<lparr>kheap := kheap s(t \<mapsto> ko')\<rparr>)"
  apply (clarsimp simp add: pspace_distinct_def obj_bits_T)
  apply fastforce
  done


lemma set_object_distinct:
  "\<lbrace>obj_at (\<lambda>ko. a_type ko = a_type ko') p and pspace_distinct\<rbrace>
     set_object p ko'
   \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def simp del: fun_upd_apply)
  apply (erule(2) pspace_distinct_same_type)
  done


lemma set_ep_distinct[wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_endpoint ep v \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply (wp set_object_distinct)
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp elim!: obj_at_weakenE)
  apply (case_tac ko, simp_all add: a_type_def)
  done

lemma set_ep_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> set_endpoint ep v \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (auto simp: cur_tcb_def obj_at_def is_tcb is_ep)
  done

lemma assert_pre:
  "\<lbrace>P\<rbrace> do s <- get; assert (P s); f od \<lbrace>Q\<rbrace> \<Longrightarrow> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"
  by (simp add: valid_def assert_def get_def bind_def return_def)

lemma set_object_pspace_in_kernel_window:
  "\<lbrace>pspace_in_kernel_window and obj_at (\<lambda>ko. a_type k = a_type ko) p\<rbrace>
  set_object p k
  \<lbrace>\<lambda>r. pspace_in_kernel_window\<rbrace>"
  unfolding set_object_def
  apply (rule assert_pre)
  apply (rule hoare_pre)
   apply (rule pspace_in_kernel_window_atyp_lift)
    apply (wp; clarsimp simp add: obj_at_def)+
  by simp

lemma set_ntfn_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_notification ptr val \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm)
  done

lemma set_ep_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm)
  done

lemma swp_apply [simp]:
  "swp f x y = f y x" by (simp add: swp_def)

lemma hoare_cte_wp_caps_of_state_lift:
  assumes c: "\<And>P p. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. cte_wp_at P p s\<rbrace> f \<lbrace>\<lambda>r s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (rule c)
  done

lemma valid_mdb_lift:
  assumes c: "\<And>P p. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (caps_of_state s)\<rbrace>"
  assumes m: "\<And>P. \<lbrace>\<lambda>s. P (cdt s)\<rbrace> f \<lbrace>\<lambda>r s. P (cdt s)\<rbrace>"
  assumes r: "\<And>P. \<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> f \<lbrace>\<lambda>r s. P (is_original_cap s)\<rbrace>"
  shows "\<lbrace>valid_mdb\<rbrace> f \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  apply (clarsimp simp add: valid_def valid_mdb_def mdb_cte_at_def)
  apply (frule_tac P1="op = (cdt s)" in use_valid [OF _  m], rule refl)
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
  apply (erule use_valid [OF _ r])
  apply simp
  done

crunch no_cdt[wp]: set_endpoint "\<lambda>s. P (cdt s)" 
  (wp: crunch_wps)


lemma set_ep_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_endpoint p ep \<lbrace>\<lambda>r s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_endpoint_def get_object_def bind_assoc set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  apply (case_tac y, auto simp: cte_wp_at_cases)
  done


lemma set_ep_revokable [wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> set_endpoint p ep \<lbrace>\<lambda>r s. P (is_original_cap s)\<rbrace>"
  apply (simp add: set_endpoint_def get_object_def bind_assoc set_object_def)
  apply wp
  apply simp
  done


lemma set_ep_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_endpoint p ep \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wp valid_mdb_lift)



lemma cte_wp_at_after_update:
  "\<lbrakk> obj_at (same_caps val) p' s \<rbrakk>
    \<Longrightarrow> cte_wp_at P p (kheap_update (\<lambda>a b. if b = p' then Some val else kheap s b) s)
         = cte_wp_at P p s" 
  by (fastforce simp: obj_at_def cte_wp_at_cases split: split_if_asm dest: bspec [OF _ ranI])


lemma ex_cap_to_after_update:
  "\<lbrakk> ex_nonz_cap_to p s; obj_at (same_caps val) p' s \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to p (kheap_update (\<lambda>a b. if b = p' then Some val else kheap s b) s)"
  by (clarsimp simp: ex_nonz_cap_to_def cte_wp_at_after_update)


lemma ex_cte_cap_to_after_update:
  "\<lbrakk> ex_cte_cap_wp_to P p s; obj_at (same_caps val) p' s \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to P p (kheap_update (\<lambda>a b. if b = p' then Some val else kheap s b) s)"
  by (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_after_update)


lemma set_object_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> (live val \<longrightarrow> ex_nonz_cap_to p s)
       \<and> obj_at (same_caps val) p s\<rbrace>
     set_object p val \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (fastforce simp: if_live_then_nonz_cap_def obj_at_def elim!: ex_cap_to_after_update)
  done


lemma set_object_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap and obj_at (same_caps val) p\<rbrace>
     set_object p val \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: if_unsafe_then_cap_def simp: cte_wp_at_after_update
                 dest!: caps_of_state_cteD)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (fastforce elim!: ex_cte_cap_to_after_update)
  done


lemma set_object_zombies[wp]:
  "\<lbrace>zombies_final and obj_at (same_caps val) p\<rbrace>
      set_object p val \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: zombies_final_def is_final_cap'_def2
                        cte_wp_at_after_update)
  done


lemma set_ep_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> (live (Endpoint ep) \<longrightarrow> ex_nonz_cap_to p s)\<rbrace>
     set_endpoint p ep \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp elim!: obj_at_weakenE
                  split: Structures_A.kernel_object.splits
                  simp: is_ep_def)
  done


lemma set_ep_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_endpoint p val \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp elim!: obj_at_weakenE simp: is_ep_def)
  done


lemma set_ep_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_endpoint p val \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp elim!: obj_at_weakenE simp: is_ep_def)
  done


lemma set_ntfn_distinct[wp]:
  "\<lbrace>pspace_distinct\<rbrace> 
  set_notification ntfn v 
  \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp set_object_distinct)
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply clarsimp
  apply (erule obj_at_weakenE)
  apply (case_tac ko, simp_all add: a_type_def)
  done

lemma set_ntfn_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (ntfnptr := ntfn_q_refs_of (ntfn_obj ntfn) \<union> ntfn_bound_refs (ntfn_bound_tcb ntfn)))\<rbrace>
     set_notification ntfnptr ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_notification_def set_object_def)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply wp
  apply (clarsimp simp: state_refs_of_def
                 elim!: rsubst [where P=P]
                intro!: ext)
  done

lemma set_ntfn_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> set_notification ntfn v \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  apply (simp add: set_notification_def set_object_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (auto simp: cur_tcb_def obj_at_def is_tcb is_ntfn)
  done


lemma set_ntfn_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_notification p ntfn \<lbrace>\<lambda>r s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_notification_def get_object_def bind_assoc set_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  apply (case_tac y, auto simp: cte_wp_at_cases)
  done


lemma set_object_cap_refs_in_kernel_window:
  "\<lbrace>cap_refs_in_kernel_window and obj_at (same_caps ko) p\<rbrace> 
  set_object p ko
  \<lbrace>\<lambda>r. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply (clarsimp simp: cap_refs_in_kernel_window_def)
  apply (clarsimp simp: valid_refs_def cte_wp_at_after_update)
  done


crunch no_cdt[wp]: set_notification "\<lambda>s. P (cdt s)" 
  (wp: crunch_wps)


crunch no_revokable[wp]: set_notification "\<lambda>s. P (is_original_cap s)" 
  (wp: crunch_wps)


lemma set_ntfn_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_notification p ep \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  by (wp valid_mdb_lift)


lemma set_ntfn_iflive[wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s \<and> (live (Notification ntfn) \<longrightarrow> ex_nonz_cap_to p s)\<rbrace>
     set_notification p ntfn \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_notification_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp elim!: obj_at_weakenE simp: is_ntfn_def
                  split: Structures_A.kernel_object.splits)
  done


lemma set_ntfn_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_notification p val \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_notification_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp elim!: obj_at_weakenE simp: is_ntfn_def)
  done


lemma set_ntfn_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_notification p val \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_notification_def)
  apply wp
  apply (rule hoare_strengthen_post [OF get_object_sp])
  apply (clarsimp elim!: obj_at_weakenE simp: is_ntfn_def)
  done


lemma get_object_ret:
  "\<lbrace>obj_at P addr\<rbrace> get_object addr \<lbrace>\<lambda>r s. P r\<rbrace>"
  unfolding get_object_def
  by (wp, clarsimp elim!: obj_atE)+


lemma mask_in_range:
  "is_aligned ptr bits \<Longrightarrow>
    (ptr' && (~~ mask bits) = ptr) = (ptr' \<in> {ptr .. ptr + 2 ^ bits - 1})"
  apply (erule is_aligned_get_word_bits)
   defer
   apply (simp add: power_overflow mask_def)
  apply (rule iffI)
   apply (drule sym)
   apply (simp add: word_and_le2)
   apply (subst field_simps[symmetric], subst mask_2pm1[symmetric])
   apply (subst word_plus_and_or_coroll)
    apply (rule word_eqI, clarsimp simp: word_ops_nth_size)
   apply (subgoal_tac "ptr' && ~~ mask bits || mask bits = ptr' || mask bits")
    apply (simp add: le_word_or2)
   apply (rule word_eqI, clarsimp simp: word_ops_nth_size word_size)
   apply fastforce
  apply (subgoal_tac "\<exists>x. ptr' = ptr || x \<and> x && mask bits = x")
   apply (rule word_eqI)
   apply (clarsimp simp: word_ops_nth_size word_size is_aligned_mask)
   apply (drule_tac x=n in word_eqD)+
   apply (simp add: word_ops_nth_size word_size
                    is_aligned_mask)
   apply safe[1]
  apply (subgoal_tac "\<exists>x. ptr' = ptr + x")
   apply clarsimp
   apply (drule(1) word_le_minus_mono_left[where x=ptr])
   apply simp
   apply (subst conj_commute)
   apply (rule exI, rule context_conjI[OF _ word_plus_and_or_coroll])
    apply (subst mask_eq_iff_w2p_alt)
     apply (simp add: word_bits_conv word_size)
    apply (rule minus_one_helper5)
     apply simp
    apply simp
   apply (simp add: is_aligned_mask)
   apply (rule word_eqI)
   apply (drule_tac x=n in word_eqD)+
   apply (clarsimp simp: word_ops_nth_size word_size)
  apply (rule exI[where x="ptr' - ptr"])
  apply simp
  done


lemma captable_case_helper:
  "\<lbrakk> \<forall>sz cs. ob \<noteq> CNode sz cs \<rbrakk> \<Longrightarrow> (case ob of CNode sz cs \<Rightarrow> P sz cs | _ \<Rightarrow> Q) = Q"
  by (case_tac ob, simp_all add: not_ex[symmetric])


lemma null_filter_caps_of_stateD:
  "null_filter (caps_of_state s) p = Some c \<Longrightarrow>
  cte_wp_at (\<lambda>c'. c' = c \<and> c' \<noteq> cap.NullCap) p s"
  apply (simp add: null_filter_def split: split_if_asm)
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
  "no_fail (obj_at \<top> ptr) (get_object ptr)"
  apply (simp add: get_object_def)
  apply (rule no_fail_pre, wp)
  apply (fastforce simp: obj_at_def)
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

lemma dmo_invs:
  "\<lbrace>(\<lambda>s. \<forall>m. \<forall>(r,m')\<in>fst (f m). (\<forall>p.
       in_user_frame p s \<or> underlying_memory m' p = underlying_memory m p) \<and>
         (m = machine_state s \<longrightarrow> (\<forall>irq. (interrupt_states s irq = IRQInactive \<longrightarrow> irq_masks m' irq) \<or> (irq_masks m' irq = irq_masks m irq))))
    and invs\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>_. invs\<rbrace>"
   apply (simp add: do_machine_op_def split_def)
   apply wp
   apply clarsimp
   apply (drule_tac x="machine_state s" in spec)
   apply (drule_tac x="(a,b)" in bspec;simp)
   apply clarsimp
   by (fastforce simp: invs_def cur_tcb_def valid_state_def
                          valid_machine_state_def
                    intro!: valid_irq_states_machine_state_updateI
                    elim:  valid_irq_statesE)


lemma as_user_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> as_user t m \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: as_user_def split_def set_object_def)
  apply wp
  apply (clarsimp simp: obj_at_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: a_type_def)
  done


lemma as_user_no_del_ntfn[wp]: 
  "\<lbrace>ntfn_at p\<rbrace> as_user t m \<lbrace>\<lambda>rv. ntfn_at p\<rbrace>"
  by (simp add: ntfn_at_typ, wp)


lemma as_user_no_del_ep[wp]: 
  "\<lbrace>ep_at p\<rbrace> as_user t m \<lbrace>\<lambda>rv. ep_at p\<rbrace>"
  by (simp add: ep_at_typ, wp)

lemma set_ep_tcb[wp]: 
  "\<lbrace> tcb_at t \<rbrace>
   set_endpoint ep v 
   \<lbrace> \<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ) wp

lemma set_ntfn_tcb[wp]:
  "\<lbrace> tcb_at t \<rbrace>
   set_notification e v 
   \<lbrace> \<lambda>rv. tcb_at t \<rbrace>"
  by (simp add: tcb_at_typ) wp


lemma set_ep_pred_tcb_at [wp]:
  "\<lbrace> pred_tcb_at proj f t \<rbrace> 
   set_endpoint ep v 
   \<lbrace> \<lambda>rv. pred_tcb_at proj f t \<rbrace>"
  apply (simp add: set_endpoint_def pred_tcb_at_def)
  apply wp
    defer
    apply (rule assert_sp)
   apply (rule get_object_sp)
  apply simp
  apply (case_tac obj, simp_all)
  apply (rule set_object_at_obj2 [unfolded pred_conj_def])
  apply clarsimp
  done

lemma set_endpoint_ep_at[wp]:
  "\<lbrace>ep_at ptr'\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>rv. ep_at ptr'\<rbrace>"
  by (simp add: ep_at_typ, wp)


lemma set_endpoint_obj_at:
  "\<lbrace>\<lambda>s. P (Endpoint ep)\<rbrace> set_endpoint ptr ep \<lbrace>\<lambda>rv. obj_at P ptr\<rbrace>"
  apply (simp add: set_endpoint_def)
  apply (wp obj_set_prop_at)
  apply (rule hoare_drop_imps, wp)
  done


lemma set_notification_obj_at:
  "\<lbrace>\<lambda>s. P (Notification ep)\<rbrace> set_notification ptr ep \<lbrace>\<lambda>rv. obj_at P ptr\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp obj_set_prop_at)
  apply (rule hoare_drop_imps, wp)
  done


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


lemma set_ep_ex_cap[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_endpoint p' v \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)


lemma set_ntfn_st_tcb [wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_notification ntfn x \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_notification_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_ntfn)
  done


crunch it[wp]: set_notification "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)


lemma set_notification_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_notification p' val \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)


lemma set_endpoint_idle[wp]:
  "\<lbrace>valid_idle and ep_at ptr\<rbrace>
   set_endpoint ptr ep \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_endpoint_def set_object_def get_object_def)
  apply (wp hoare_drop_imp)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_ep_def)
  done


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
                 simp: valid_ep_def valid_ntfn_def valid_bound_tcb_def
               intro!: ext)+

crunch it[wp]: set_notification "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)


crunch arch[wp]: set_notification "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)


lemma set_notification_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_notification ntfn p \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp


crunch irq_node_inv[wp]: set_notification "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)


lemma set_notification_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_notification ntfn p \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp


lemma set_notification_idle[wp]:
  "\<lbrace>ntfn_at p and valid_idle\<rbrace>
   set_notification p ep
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_notification_def set_object_def get_object_def)
  apply (wp hoare_drop_imp)
  apply (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def is_ntfn_def)
  done


lemma set_notification_reply[wp]:
  "\<lbrace>valid_reply_caps\<rbrace>
   set_notification p ep
   \<lbrace>\<lambda>_. valid_reply_caps\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_notification_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace> set_notification p ep \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)


lemma obj_at_ko_atE:
  "\<lbrakk> obj_at P ptr s; ko_at k ptr s; P k \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (clarsimp simp: obj_at_def)


crunch arch[wp]: set_endpoint "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps simp: crunch_simps)


lemma set_endpoint_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_endpoint ep p \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp


crunch irq_node_inv[wp]: set_endpoint "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)


crunch it[wp]: set_endpoint "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)


lemma set_ep_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_endpoint ep p \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp


lemma set_endpoint_reply[wp]:
  "\<lbrace>valid_reply_caps\<rbrace> set_endpoint ep p \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)


lemma set_endpoint_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace> set_endpoint p ep \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)


crunch interrupt_states[wp]: set_endpoint "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)


context ARM begin

lemma set_object_neg_lookup:
  "\<lbrace>\<lambda>s. \<not> (\<exists>rs. (rs \<rhd> p') s) \<and> aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p s \<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. \<not> (\<exists>rs. (rs \<rhd> p') s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule_tac x=rs in allE)
  apply (erule notE)
  apply (erule vs_lookup_stateI)
   apply (clarsimp simp: aobj_at_def split: split_if_asm)
  apply simp
  done


lemma set_object_vs_lookup:
  "\<lbrace>\<lambda>s. aobj_at (\<lambda>ko'. vs_refs ko = vs_refs ko') p s \<and> P (vs_lookup s) \<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_sub)
    apply (clarsimp simp: aobj_at_def)
   apply simp
  apply (rule vs_lookup_sub)
   apply (clarsimp simp: aobj_at_def split: split_if_asm)
  apply simp
  done


lemma set_object_pt_not_vs_lookup_pages:
  "\<lbrace>\<lambda>s. \<not>(ref \<unrhd> p') s
    \<and> ((\<exists>\<unrhd>p) s \<longrightarrow> (\<forall>x. case pte_ref_pages (pt x) of
              Some ptr \<Rightarrow> 
                aobj_at (\<lambda>ko. vs_refs_pages ko = {}) ptr s \<and>
                ptr \<noteq> p'
            | None \<Rightarrow> True))\<rbrace>
   set_object p (ArchObj (PageTable pt))
   \<lbrace>\<lambda>_ s. \<not>(ref \<unrhd> p') s\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: aobj_at_def)
   apply (case_tac "(\<exists>\<unrhd>p) s")
   apply (erule notE)
   apply clarsimp
   apply (subst (asm) vs_lookup_pages_def)
   apply clarsimp
   apply (erule vs_lookup_pagesI)
   apply (erule converse_rtrancl_induct)
    apply simp
   apply (drule vs_lookup_pages1D)
   apply (clarsimp simp: aobj_at_def split:split_if_asm)
   apply (case_tac "pa=p")
    apply (clarsimp simp: vs_refs_pages_def graph_of_def)
    apply (erule_tac x=ab in allE)
    apply (drule_tac R="vs_lookup_pages1 s" in rtranclD)
    apply clarsimp
    apply (drule tranclD)
    apply clarsimp
    apply (drule vs_lookup_pages1D)
    apply (clarsimp simp: aobj_at_def vs_refs_pages_def)
   apply clarsimp
   apply (erule rtrancl_trans[OF r_into_rtrancl, rotated])
   apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
  apply clarsimp
  apply (erule notE)
  apply (subst (asm) vs_lookup_pages_def)
  apply clarsimp
  apply (rule vs_lookup_pagesI, assumption)
  apply (erule rtrancl_induct)
   apply simp
  apply (drule vs_lookup_pages1D)
  apply (clarsimp simp: aobj_at_def split:split_if_asm)
  apply (case_tac "pa=p")
   apply (clarsimp simp: vs_refs_pages_def graph_of_def)
   apply (erule_tac x=rs in allE)
   apply (clarsimp simp: vs_lookup_pages_def)
   apply (drule(1) ImageI, erule (1) notE)
  apply clarsimp
  apply (erule rtrancl_trans[OF _ r_into_rtrancl])
  apply (clarsimp simp: vs_lookup_pages1_def obj_at_def)
  done


lemma set_object_vs_lookup_pages:
  "\<lbrace>\<lambda>s. aobj_at (\<lambda>ko'. vs_refs_pages ko = vs_refs_pages ko') p s \<and> P (vs_lookup_pages s) \<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (rule order_antisym)
   apply (rule vs_lookup_pages_sub)
    apply (clarsimp simp: aobj_at_def)
   apply simp
  apply (rule vs_lookup_pages_sub)
   apply (clarsimp simp: aobj_at_def split: split_if_asm)
  apply simp
  done

lemma set_object_neg_ako:
  "\<lbrace>not ako_at ko' p' and K (p = p' \<longrightarrow> ko \<noteq> ko')\<rbrace> 
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_ s. \<not> ako_at ko' p' s\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (simp add: pred_neg_def aobj_at_def)
  done

lemma set_object_neg_ko:
  "\<lbrace>not ko_at ko' p' and K (p = p' \<longrightarrow> ko \<noteq> ko')\<rbrace> 
  set_object p ko 
  \<lbrace>\<lambda>_ s. \<not> ko_at ko' p' s\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (simp add: pred_neg_def obj_at_def)
  done


lemma set_object_typ_at:
  "\<lbrace>\<lambda>s. typ_at (a_type ko) p s \<and> P (typ_at T p' s)\<rbrace> 
  set_object p ko \<lbrace>\<lambda>rv s. P (typ_at T p' s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: obj_at_def)
  done

lemma set_object_atyp_at:
  "\<lbrace>\<lambda>s. atyp_at (aa_type ko) p s \<and> P (atyp_at T p' s)\<rbrace> 
  set_object p (ArchObj ko) \<lbrace>\<lambda>rv s. P (atyp_at T p' s)\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply clarsimp
  apply (erule rsubst [where P=P])
  apply (clarsimp simp: aobj_at_def)
  done


lemma set_object_arch_objs:
  "\<lbrace>valid_arch_objs and atyp_at (aa_type ko) p and 
    aobj_at (\<lambda>ko'. vs_refs ko \<subseteq> vs_refs ko') p  and
    (\<lambda>s. (\<exists>\<rhd>p)s \<longrightarrow> valid_arch_obj ko s)\<rbrace>
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: valid_arch_objs_def)
  apply (subst imp_conv_disj)+
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift set_object_neg_lookup set_object_neg_ako 
            valid_arch_obj_typ2 [where Q="atyp_at (aa_type ko) p"] set_object_atyp_at)
  apply (clarsimp simp: pred_neg_def aobj_at_def)
  apply fastforce
  done



end

lemma set_object_non_arch:
  "\<lbrace>(\<lambda>s. P (aobj_at P' p' s)) and K(non_arch_obj ko) and obj_at non_arch_obj p \<rbrace>
    set_object p ko
   \<lbrace>\<lambda>r s. P (aobj_at P' p' s)\<rbrace>"
  unfolding set_object_def
  apply wp
  apply clarsimp
  apply (erule_tac P=P in rsubst)
  apply (clarsimp simp: aobj_at_def obj_at_def)
  by fastforce


lemma set_object_arch_objs_non_arch:
  "\<lbrace>valid_arch_objs and K (non_arch_obj ko) and obj_at non_arch_obj p\<rbrace>
  set_object p ko
  \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (rule assert_pre)
  apply (rule hoare_pre)
  apply (rule valid_arch_objs_lift_weak)
  apply (wp set_object_non_arch | clarsimp)+
  done

context ARM begin

lemma set_object_valid_kernel_mappings:
  "\<lbrace>\<lambda>s. valid_kernel_mappings s
           \<and> valid_kernel_mappings_if_pd
                (set (arm_global_pts (arch_state s)))
                    ko\<rbrace>
     set_object ptr ko
   \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: set_object_def)
  apply wp
  apply (clarsimp simp: valid_kernel_mappings_def
                 elim!: ranE split: split_if_asm)
  apply fastforce
  done

lemma valid_vs_lookup_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  shows "\<lbrace>valid_vs_lookup\<rbrace> f \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (rule hoare_lift_Pf [where f=vs_lookup_pages])
   apply (rule hoare_lift_Pf [where f=arch_caps_of_state])
    apply (rule hoare_lift_Pf [where f="\<lambda>s. arm_global_pts (arch_state s)"])
     apply (wp lookup cap pts)
  done

lemma valid_table_caps_lift:
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>aobj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. aobj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_table_caps\<rbrace> f \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  unfolding valid_table_caps_def
   apply (rule hoare_lift_Pf [where f=arch_caps_of_state])
    apply (rule hoare_lift_Pf [where f="\<lambda>s. arm_global_pts (arch_state s)"])
     apply (wp cap pts hoare_vcg_all_lift hoare_vcg_const_imp_lift obj)
  done


lemma valid_arch_caps_lift:
  assumes lookup: "\<And>P. \<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  assumes obj: "\<And>S p. \<lbrace>aobj_at (empty_table S) p\<rbrace> f \<lbrace>\<lambda>rv. aobj_at (empty_table S) p\<rbrace>"
  shows "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  unfolding valid_arch_caps_def
  apply (rule hoare_pre)
   apply (wp valid_vs_lookup_lift valid_table_caps_lift lookup cap pts obj)
  apply simp
  done

lemma valid_arch_caps_lift_weak:
  assumes cap: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes obj: "\<And>P P' p. \<lbrace>\<lambda>s. P (aobj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' p s)\<rbrace>"
  shows "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  apply (rule valid_arch_caps_lift[OF _ cap arch obj])
  apply (rule vs_lookup_pages_aobj_at_lift[OF obj arch])
  done

unqualify_facts valid_arch_caps_lift_weak

lemma valid_global_objs_lift':
  assumes pts: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pts (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pts (arch_state s))\<rbrace>"
  assumes pd: "\<And>P. \<lbrace>\<lambda>s. P (arm_global_pd (arch_state s))\<rbrace> f \<lbrace>\<lambda>_ s. P (arm_global_pd (arch_state s))\<rbrace>"
  assumes obj: "\<And>p. \<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  assumes ko: "\<And>ao p. \<lbrace>ako_at ao p\<rbrace> f \<lbrace>\<lambda>_. ako_at ao p\<rbrace>"
  assumes emp: "\<And>pd S. 
       \<lbrace>\<lambda>s. (v \<longrightarrow> pd = arm_global_pd (arch_state s) \<and> S = set (arm_global_pts (arch_state s)) \<and> P s)
            \<and> aobj_at (empty_table S) pd s\<rbrace>
                 f \<lbrace>\<lambda>rv. aobj_at (empty_table S) pd\<rbrace>"
  shows "\<lbrace>\<lambda>s. valid_global_objs s \<and> (v \<longrightarrow> P s)\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  unfolding valid_global_objs_def
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f="\<lambda>s. arm_global_pts (arch_state s)", OF pts])
   apply (rule hoare_use_eq [where f="\<lambda>s. arm_global_pd (arch_state s)", OF pd]) 
   apply (wp obj ko emp hoare_vcg_const_Ball_lift hoare_ex_wp)
  apply clarsimp
  done


lemmas valid_global_objs_lift
    = valid_global_objs_lift' [where v=False, simplified]



lemma valid_global_objs_lift_weak:
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes aobj_at: "\<And>P P' pd. \<lbrace>\<lambda>s. P (aobj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' pd s)\<rbrace>"
  shows "\<lbrace>valid_global_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (rule valid_global_objs_lift)
      apply (wp arch)
    apply (simp add: valid_ao_at_def)
    apply (rule hoare_vcg_ex_lift)
    apply (rule hoare_vcg_conj_lift)
     apply (wp aobj_at valid_arch_obj_atyp)
  done

lemma valid_asid_map_lift:
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes aobj_at: "\<And>P P' pd. \<lbrace>\<lambda>s. P (aobj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' pd s)\<rbrace>"
  shows "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (simp add: pd_at_asid_def)
  by (rule vs_lookup_aobj_at_lift[OF aobj_at arch])
  
lemma valid_kernel_mappings_lift:
  assumes arch: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  assumes aobj_at: "\<And>P P' pd. \<lbrace>\<lambda>s. P (aobj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' pd s)\<rbrace>"
  shows "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. valid_kernel_mappings\<rbrace>"
  apply (simp add: valid_kernel_mappings_def)
  apply (rule hoare_lift_Pf[where f="arch_state", OF _ arch])
  apply (simp add: valid_kernel_mappings_if_pd_def ran_def)
  apply (rule hoare_vcg_all_lift)
  apply (case_tac "\<exists>ao. xa = ArchObj ao")
   apply (rule hoare_convert_imp)
    apply clarsimp
    apply (rule hoare_vcg_all_lift)
    subgoal for ao a
    by (rule aobj_at[where P=Not and P'="\<lambda>x. x = ao", simplified aobj_at_def, simplified])
   apply clarsimp
   apply (case_tac ao; simp add: hoare_vcg_prop)
  apply clarsimp
  apply (case_tac xa; simp add: hoare_vcg_prop)
  apply blast
  done

lemma equal_kernel_mappings_lift:
  assumes aobj_at: "\<And>P P' pd. \<lbrace>\<lambda>s. P (aobj_at P' pd s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' pd s)\<rbrace>"
  shows "\<lbrace>equal_kernel_mappings\<rbrace> f \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: equal_kernel_mappings_def)
  apply (rule hoare_vcg_all_lift)+
  apply (rule hoare_convert_imp)
   apply simp
   apply (rule hoare_convert_imp)
    apply (wp aobj_at)
  done
  

lemma valid_ao_at_lift:
  assumes z: "\<And>P p T. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
      and y: "\<And>ao. \<lbrace>\<lambda>s. ako_at ao p s\<rbrace> f \<lbrace>\<lambda>rv s. ako_at ao p s\<rbrace>"
  shows      "\<lbrace>valid_ao_at p\<rbrace> f \<lbrace>\<lambda>rv. valid_ao_at p\<rbrace>"
  unfolding valid_ao_at_def
  by (wp hoare_vcg_ex_lift y valid_arch_obj_typ z)

unqualify_facts 
  valid_global_objs_lift_weak
  valid_asid_map_lift
  valid_kernel_mappings_lift
  equal_kernel_mappings_lift

end

locale non_arch_op = fixes f
  assumes aobj_at: "\<And>P P' p. \<lbrace>\<lambda>s. P (aobj_at P' p s)\<rbrace> f \<lbrace>\<lambda>r s. P (aobj_at P' p s)\<rbrace>" and
          arch_state: "\<And>P. \<lbrace>\<lambda>s. P (arch_state s)\<rbrace> f \<lbrace>\<lambda>r s. P (arch_state s)\<rbrace>"
begin

lemma valid_arch_obj[wp]:"\<lbrace>valid_arch_objs\<rbrace> f \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
by (rule valid_arch_objs_lift_weak[OF aobj_at arch_state])

lemma vs_lookup[wp]: "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
by (rule vs_lookup_aobj_at_lift[OF aobj_at arch_state])

lemma vs_lookup_pages[wp]: "\<lbrace>\<lambda>s. P (vs_lookup_pages s)\<rbrace> f \<lbrace>\<lambda>_ s. P (vs_lookup_pages s)\<rbrace>"
by (rule vs_lookup_pages_aobj_at_lift[OF aobj_at arch_state])

lemma valid_global_objs[wp]: "\<lbrace>valid_global_objs\<rbrace> f \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
by (rule valid_global_objs_lift_weak[OF arch_state aobj_at])

lemma valid_asid_map[wp]: "\<lbrace>valid_asid_map\<rbrace> f \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
by (rule valid_asid_map_lift[OF arch_state aobj_at])

lemma valid_kernel_mappings[wp]: "\<lbrace>valid_kernel_mappings\<rbrace> f \<lbrace>\<lambda>_. valid_kernel_mappings\<rbrace>"
by (rule valid_kernel_mappings_lift[OF arch_state aobj_at])

lemma equal_kernel_mappings[wp]: "\<lbrace>equal_kernel_mappings\<rbrace> f \<lbrace>\<lambda>_. equal_kernel_mappings\<rbrace>"
by (rule equal_kernel_mappings_lift[OF aobj_at])

end

locale non_arch_non_cap_op = non_arch_op f for f +
  assumes caps: "\<And>P. \<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
begin

lemma valid_arch_caps[wp]: "\<lbrace>valid_arch_caps\<rbrace> f \<lbrace>\<lambda>_. valid_arch_caps\<rbrace>"
  by (rule valid_arch_caps_lift_weak[OF caps arch_state aobj_at])

end

lemma arch_caps_to_caps_of_state:
  assumes caps: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  shows "\<lbrace>\<lambda>s. P (arch_caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (arch_caps_of_state s)\<rbrace>"
  unfolding arch_caps_of_state_def2
  by (rule caps)


lemma sts_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  unfolding set_thread_state_def set_object_def
  apply (wp | simp)+
  apply clarsimp
  apply (erule rsubst[where P=P])
  apply (rule cte_wp_caps_of_lift)
  by (auto simp: cte_wp_at_cases2 tcb_cnode_map_def dest!: get_tcb_SomeD)

lemma set_bound_caps_of_state[wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_bound_notification t st \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  unfolding set_bound_notification_def set_object_def
  apply (wp | simp)+
  apply clarsimp
  apply (erule rsubst[where P=P])
  apply (rule cte_wp_caps_of_lift)
  by (auto simp: cte_wp_at_cases2 tcb_cnode_map_def dest!: get_tcb_SomeD)


interpretation
   set_endpoint: non_arch_non_cap_op "set_endpoint p ep" + 
   set_notification: non_arch_non_cap_op "set_notification p ntfn" +
   sts: non_arch_non_cap_op "set_thread_state p st" +
   sbm: non_arch_non_cap_op "set_bound_notification p b" +
   thread_set: non_arch_op "thread_set f p" +
   set_cap: non_arch_op "set_cap cap p'"
   apply (all \<open>unfold_locales; (rule arch_caps_to_caps_of_state; wp ; fail)?\<close>)
  unfolding set_endpoint_def set_notification_def set_thread_state_def 
            set_bound_notification_def thread_set_def set_cap_def[simplified split_def]
  apply -
  apply (all \<open>unfold_locales;(wp set_object_non_arch get_object_wp | wpc | simp)+\<close>)
  by (fastforce simp: obj_at_def a_type_def 
                  split: Structures_A.kernel_object.splits)+
  

lemma valid_irq_handlers_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  assumes y: "\<And>P. \<lbrace>\<lambda>s. P (interrupt_states s)\<rbrace> f \<lbrace>\<lambda>rv s. P (interrupt_states s)\<rbrace>"
  shows      "\<lbrace>valid_irq_handlers\<rbrace> f \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_use_eq [where f=caps_of_state, OF x y])
  done


lemmas set_endpoint_valid_irq_handlers[wp]
    = valid_irq_handlers_lift [OF set_ep_caps_of_state set_endpoint_interrupt_states]


crunch irq_node[wp]: set_notification "\<lambda>s. P (interrupt_irq_node s)"


lemmas hoare_use_eq_irq_node = hoare_use_eq[where f=interrupt_irq_node]


lemma cap_table_at_lift_valid:
  "\<lbrakk> \<And>T. \<lbrace>typ_at T p\<rbrace> f \<lbrace>\<lambda>rv. typ_at T p\<rbrace> \<rbrakk>
       \<Longrightarrow> \<lbrace>cap_table_at n p\<rbrace> f \<lbrace>\<lambda>rv. cap_table_at n p\<rbrace>"
  by (simp add: cap_table_at_typ)


lemmas cap_table_at_lift_irq =
  hoare_use_eq_irq_node [OF _ cap_table_at_lift_valid]


crunch interrupt_states[wp]: set_notification "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)


lemmas set_notification_irq_handlers[wp] =
    valid_irq_handlers_lift [OF set_ntfn_caps_of_state set_notification_interrupt_states]


lemma set_notification_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_notification p ntfn \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)


lemma set_endpoint_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_endpoint p ntfn \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift)

context ARM begin

lemmas set_object_v_ker_map
    = set_object_valid_kernel_mappings
            [unfolded valid_kernel_mappings_if_pd_def]


crunch v_ker_map[wp]: set_notification "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_object_asid_map:
  "\<lbrace>valid_asid_map and
    aobj_at (\<lambda>ko'. vs_refs ko' \<subseteq> vs_refs ko) p\<rbrace>
  set_object p (ArchObj ko) 
  \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: valid_asid_map_def set_object_def)
  apply wp
  apply (clarsimp simp: pd_at_asid_def simp del: fun_upd_apply)
  apply (drule bspec, blast)
  apply clarsimp
  apply (rule vs_lookup_stateI, assumption)
   apply (clarsimp simp: aobj_at_def)
   apply blast
  apply simp
  done

lemma set_object_equal_mappings:
  "\<lbrace>\<lambda>s. equal_kernel_mappings s
          \<and> (\<forall>pd. ko = ArchObj (PageDirectory pd)
                \<longrightarrow> (\<forall>x pd'. ako_at (PageDirectory pd') x s
                         \<longrightarrow> (\<forall>w \<in> kernel_mapping_slots. pd w = pd' w)))\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply (clarsimp simp: equal_kernel_mappings_def aobj_at_def
             split del: split_if)
  apply (simp split: split_if_asm)
  done

lemma valid_global_pd_mappings_pres:
  "\<lbrakk> valid_global_pd_mappings s;
     \<And>pd. ako_at (PageDirectory pd) (arm_global_pd (arch_state s)) s
            \<Longrightarrow> ako_at (PageDirectory pd) (arm_global_pd (arch_state s)) s';
     \<And>pt p. \<lbrakk> ako_at (PageTable pt) p s;
               valid_global_objs s \<Longrightarrow> p \<in> set (arm_global_pts (arch_state s)) \<rbrakk>
            \<Longrightarrow> ako_at (PageTable pt) p s';
     arm_global_pd (arch_state s') = arm_global_pd (arch_state s);
     arm_kernel_vspace (arch_state s') = arm_kernel_vspace (arch_state s) \<rbrakk>
        \<Longrightarrow> valid_global_pd_mappings s'"
  apply atomize
  apply (clarsimp simp: valid_global_pd_mappings_def aobj_at_def)
  apply (clarsimp simp: valid_pd_kernel_mappings_def
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.split_asm)
  apply (drule_tac x=x in spec)
  apply (clarsimp simp: valid_pde_kernel_mappings_def aobj_at_def
                        valid_pt_kernel_mappings_def pde_ref_def
                 split: Arch_Structs_A.ARM.pde.split_asm)
  apply (simp split: Structures_A.kernel_object.split_asm
                     arch_kernel_obj.split_asm)
  apply (drule spec, drule spec, drule(1) mp)
  apply (drule mp)
   apply (clarsimp simp: valid_global_objs_def obj_at_def empty_table_def)
   apply (drule_tac x=x in spec)
   apply (simp add: pde_ref_def)[1]
  apply clarsimp
  done

lemma valid_global_pd_mappings_arch_update[simp]:
  "arm_global_pd (f (arch_state s)) = arm_global_pd (arch_state s)
   \<and> arm_kernel_vspace (f (arch_state s)) = arm_kernel_vspace (arch_state s)
     \<Longrightarrow> valid_global_pd_mappings (arch_state_update f s) = valid_global_pd_mappings s"
  by (simp add: valid_global_pd_mappings_def)

lemma set_object_global_pd_mappings:
  "\<lbrace>valid_global_pd_mappings
            and (\<lambda>s. (page_directory_at p s \<or> page_table_at p s)
                       \<longrightarrow> valid_global_objs s \<and> p \<notin> global_refs s)\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>"
  apply (simp add: set_object_def, wp)
  apply clarsimp
  apply (erule valid_global_pd_mappings_pres)
     apply (clarsimp simp: aobj_at_def a_type_def aa_type_def global_refs_def)+
  done

end







lemma set_ntfn_global_pd_mappings[wp]:
  "\<lbrace>valid_global_pd_mappings and valid_global_objs\<rbrace>
     set_notification p ep
   \<lbrace>\<lambda>rv. valid_global_pd_mappings\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp set_object_global_pd_mappings get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_def
                 split: Structures_A.kernel_object.split_asm)
  done

lemma set_ntfn_cap_refs_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_notification p ep \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  apply (clarsimp simp: obj_at_def is_ntfn
                 split: Structures_A.kernel_object.split_asm)
  done

(* There are two wp rules for preserving valid_ioc over set_object.
   First, the more involved rule for CNodes and TCBs *)
lemma set_object_valid_ioc_caps:
  "\<lbrace>\<lambda>s. valid_ioc s \<and> typ_at (a_type obj) ptr s \<and>
    (\<forall>b. is_original_cap s (ptr,b) \<longrightarrow> null_filter (cap_of obj) b \<noteq> None)\<rbrace>
   set_object ptr obj
   \<lbrace>\<lambda>_ s. valid_ioc s\<rbrace>"
  apply (clarsimp simp: set_object_def valid_def
                        get_def put_def bind_def return_def)
  apply (clarsimp simp add: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (case_tac "a=ptr", simp_all add: cte_wp_at_cases)
  apply (drule spec, erule impE, assumption)
  apply (erule disjE)
   apply (rule disjI1)
   apply (clarsimp simp add: obj_at_def a_type_simps)
   apply (fastforce simp: a_type_def cap_of_def
                         null_filter_def
                  split: Structures_A.kernel_object.splits split_if_asm)
  apply (rule disjI2)
  apply (clarsimp simp add: obj_at_def a_type_simps)
  apply (fastforce simp: a_type_def cap_of_def tcb_cnode_map_def null_filter_def
                 split: Structures_A.kernel_object.splits split_if_asm)
  done


(* Second, the simpler rule suitable for all objects except CNodes and TCBs. *)
lemma set_object_valid_ioc_no_caps:
  "\<lbrace>\<lambda>s. valid_ioc s \<and> typ_at (a_type obj) ptr s \<and> \<not> is_tcb obj \<and>
        (\<forall>n. \<not> is_cap_table n obj) \<rbrace>
   set_object ptr obj
   \<lbrace>\<lambda>_ s. valid_ioc s\<rbrace>"
  apply (clarsimp simp: set_object_def valid_def
                        get_def put_def bind_def return_def)
  apply (clarsimp simp add: valid_ioc_def cte_wp_at_cases is_tcb)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (elim disjE)
   prefer 2
   apply (fastforce simp: obj_at_def a_type_def
                   split: Structures_A.kernel_object.splits split_if_asm)
  apply (fastforce simp: obj_at_def a_type_def is_cap_table_def well_formed_cnode_n_def
                  split: Structures_A.kernel_object.splits split_if_asm)
  done


lemma set_notification_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_notification ptr val \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_notification_def)
  apply (wp set_object_valid_ioc_no_caps get_object_inv)
  by (clarsimp simp: valid_def get_object_def simpler_gets_def assert_def
          return_def fail_def bind_def
          a_type_simps obj_at_def is_tcb is_cap_table
       split: Structures_A.kernel_object.splits arch_kernel_obj.splits)


lemma set_object_machine_state[wp]:
  "\<lbrace>\<lambda>s. P (machine_state s)\<rbrace> set_object p ko \<lbrace>\<lambda>_ s. P (machine_state s)\<rbrace>"
  by (simp add: set_object_def, wp, simp)


lemma set_notification_valid_machine_state[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_notification ptr val \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: valid_machine_state_def in_user_frame_def obj_at_def
                   set_notification_def set_object_def pred_conj_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def  split: Structures_A.kernel_object.splits)
  apply (drule_tac x=p in spec)
  apply clarsimp
  apply (rule_tac x=sz in exI)
  apply (clarsimp simp: a_type_simps)
  done

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

crunch valid_irq_states[wp]: set_object "valid_irq_states"
  (wp: valid_irq_states_triv)

crunch valid_irq_states[wp]: set_notification "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_irq_states[wp]: set_endpoint "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)

crunch valid_irq_states[wp]: set_cap "valid_irq_states"
  (wp: crunch_wps simp: crunch_simps)

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
  apply (rule hoare_pre,
         wp set_ntfn_valid_objs valid_irq_node_typ
            valid_irq_handlers_lift set_object_global_pd_mappings)
  apply (clarsimp elim!: rsubst[where P=sym_refs]
                 intro!: ext
                  dest!: obj_at_state_refs_ofD)
  done

lemma set_endpoint_arch_caps [wp]:
  "\<lbrace>valid_arch_caps\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (rule valid_arch_caps_lift)
     apply wp
  apply (simp add: set_endpoint_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def empty_table_def split: Structures_A.kernel_object.split)
  done


lemma set_endpoint_global_objs [wp]:
  "\<lbrace>valid_global_objs\<rbrace> set_endpoint ptr val \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  apply (rule valid_global_objs_lift)
      apply (wp valid_ao_at_lift)
    apply (simp_all add: set_endpoint_def set_object_def)
    apply (wp get_object_wp)
    apply (clarsimp simp: obj_at_def)
   apply (wp get_object_wp)
   apply (clarsimp simp: obj_at_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def empty_table_def)
  apply (case_tac ko, simp_all)
  done


lemma set_ep_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_endpoint p ep \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  unfolding set_endpoint_def
  apply (wp set_object_asid_map get_object_wp)
  apply (clarsimp simp: vs_refs_def obj_at_def 
                  split: Structures_A.kernel_object.splits)
  done


lemma set_cap_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_cap cap p \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  unfolding set_cap_def split_def
  apply (rule hoare_pre)
   apply (wp set_object_asid_map get_object_wp|wpc)+
  apply (clarsimp simp: vs_refs_def obj_at_def simp del: fun_upd_apply)
  done


lemma thread_set_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> thread_set f p \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  unfolding thread_set_def split_def
  apply (rule hoare_pre)
   apply (wp set_object_asid_map|wpc)+
  apply (clarsimp simp: vs_refs_def obj_at_def get_tcb_def 
                  split: option.splits Structures_A.kernel_object.splits)
  done


lemma sts_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> set_thread_state p st \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  unfolding set_thread_state_def
  apply (rule hoare_pre)
   apply (wp set_object_asid_map|wpc|simp)+
  apply (clarsimp simp: vs_refs_def obj_at_def get_tcb_def 
                  split: option.splits Structures_A.kernel_object.splits)
  done

crunch asid_map[wp]: set_bound_notification "valid_asid_map"
  (simp: vs_refs_def)


lemma dmo_aligned[wp]:
  "\<lbrace>pspace_aligned\<rbrace> do_machine_op f \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: pspace_aligned_def)
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
  "\<lbrace>zombies_final\<rbrace> do_machine_op oper \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: zombies_final_pspaceI)
  done


lemma dmo_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> do_machine_op oper \<lbrace>\<lambda>_. if_live_then_nonz_cap\<rbrace>" 
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: iflive_pspaceI)
  done


lemma dmo_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> do_machine_op oper \<lbrace>\<lambda>_. if_unsafe_then_cap\<rbrace>" 
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: ifunsafe_pspaceI)
  done


lemma dmo_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     do_machine_op oper
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp elim!: state_refs_of_pspaceI)
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

crunch valid_global_objs[wp]: do_machine_op "valid_global_objs"

crunch valid_arch_caps[wp]: do_machine_op "valid_arch_caps"


lemma dmo_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> do_machine_op mop \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (simp add: ex_nonz_cap_to_def, wp hoare_vcg_ex_lift)

lemma dmo_st_tcb [wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> do_machine_op f \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
  done


crunch ct[wp]: do_machine_op "\<lambda>s. P (cur_thread s)" (wp: select_wp)


lemma do_machine_op_cur_tcb [wp]:
  "\<lbrace>cur_tcb\<rbrace> do_machine_op f \<lbrace>\<lambda>_. cur_tcb\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (clarsimp simp: cur_tcb_def)
  done


lemma do_machine_op_arch [wp]:
  "\<lbrace>\<lambda>s. P (arch_state s)\<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. P (arch_state s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply simp
  done
  

lemma do_machine_op_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) wp


lemma do_machine_op_vs_lookup [wp]:
  "\<lbrace>\<lambda>s. P (vs_lookup s)\<rbrace> do_machine_op f \<lbrace>\<lambda>_ s. P (vs_lookup s)\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply simp
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
  "\<lbrace>valid_objs\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply (wp select_wp)
  apply (fastforce intro: valid_objs_pspaceI)
  done


lemma do_machine_op_arch_objs [wp]:
  "\<lbrace>valid_arch_objs\<rbrace> do_machine_op f \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply simp
  done


lemma empty_table_lift:
  assumes S: "\<And>P. \<lbrace>\<lambda>s. P (S s)\<rbrace> f \<lbrace>\<lambda>_ s. P (S s)\<rbrace>"
  assumes o: "\<And>P. \<lbrace>obj_at P p and Q\<rbrace> f \<lbrace>\<lambda>_. obj_at P p\<rbrace>"
  shows "\<lbrace>\<lambda>s. obj_at (empty_table (S s)) p s \<and> Q s\<rbrace> 
         f \<lbrace>\<lambda>_ s. obj_at (empty_table (S s)) p s\<rbrace>"
  apply (rule hoare_lift_Pf2 [where f="S"])
   apply (wp o S|simp)+
  done


lemma tcb_cap_wp_at: 
  "\<lbrakk>tcb_at t s; valid_objs s; ref \<in> dom tcb_cap_cases;
    \<forall>cap st getF setF restr.
    tcb_cap_cases ref = Some (getF, setF, restr) \<and> restr t st cap \<longrightarrow> Q cap\<rbrakk> \<Longrightarrow>
   cte_wp_at Q (t, ref) s"
  apply (clarsimp simp: cte_wp_at_cases tcb_at_def dest!: get_tcb_SomeD)
  apply (rename_tac getF setF restr)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp add: valid_obj_def valid_tcb_def)
  apply (erule_tac x="(getF, setF, restr)" in ballE)
   apply fastforce+
  done


lemma as_user_arch_obj:
  "\<lbrace>valid_arch_objs\<rbrace> as_user f t \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (simp add: as_user_def)
  apply (wp set_object_arch_objs hoare_drop_imps|simp add: split_def)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def vs_refs_def)
  done


lemma tcb_cap_valid_caps_of_stateD:
  "\<lbrakk> caps_of_state s p = Some cap; valid_objs s \<rbrakk> \<Longrightarrow> tcb_cap_valid cap p s"
  apply (rule cte_wp_tcb_cap_valid)
   apply (simp add: cte_wp_at_caps_of_state)
  apply assumption
  done


lemma valid_table_caps_ptD:
  "\<lbrakk> caps_of_state s p = Some (cap.ArchObjectCap (arch_cap.PageTableCap p' None));
     page_table_at p' s; valid_table_caps s \<rbrakk> \<Longrightarrow> 
    \<exists>pt. ko_at (ArchObj (PageTable pt)) p' s \<and> valid_arch_obj (PageTable pt) s"
  apply (clarsimp simp: valid_table_caps_def simp del: split_paired_All)
  apply (erule allE)+
  apply (erule (1) impE)  
  apply (clarsimp simp add: is_pt_cap_def cap_asid_def)
  apply (erule impE, rule refl)
  apply (clarsimp simp: obj_at_def empty_table_def)
  done


lemma store_pde_pred_tcb_at:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def
                   get_pd_def bind_assoc)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply (case_tac x, simp_all)
  apply (rename_tac arch_kernel_obj)
  apply (case_tac arch_kernel_obj, simp_all)
  apply (rule hoare_seq_ext [OF _ get_object_sp])
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def)
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
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done


lemma as_user_asid_map:
  "\<lbrace>valid_asid_map\<rbrace> as_user f t \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: as_user_def split_def set_object_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: valid_asid_map_def pd_at_asid_def)
  apply (drule bspec, blast)
  apply clarsimp
  apply (drule vs_lookup_2ConsD)
  apply clarsimp
  apply (erule vs_lookup_atE)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (rule vs_lookupI)
   apply (fastforce simp add: vs_asid_refs_def graph_of_def)
  apply (rule r_into_rtrancl)
  apply (rule_tac ko=ko in vs_lookup1I)
    apply (clarsimp simp: obj_at_def vs_refs_def)
   apply assumption
  apply simp
  done


crunch valid_ioc[wp]: do_machine_op valid_ioc

end
