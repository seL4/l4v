(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
CSpace invariants
*)

theory CSpaceInv_AI
imports ArchCSpaceInvPre_AI
begin

arch_requalify_consts
  cap_master_arch_cap
  replaceable_final_arch_cap
  replaceable_non_final_arch_cap
  unique_table_refs

arch_requalify_facts
  aobj_ref_acap_rights_update
  arch_obj_size_acap_rights_update
  valid_arch_cap_acap_rights_update
  cap_master_arch_inv
  unique_table_refs_def
  valid_ipc_buffer_cap_def
  acap_rights_update_idem
  valid_acap_rights_update_id
  cap_master_arch_cap_rights
  is_nondevice_page_cap_simps
  set_cap_hyp_refs_of
  state_hyp_refs_of_revokable
  set_cap_hyp_refs_of
  is_valid_vtable_root_is_arch_cap

lemma is_valid_vtable_root_simps[simp]:
  "\<not> is_valid_vtable_root (UntypedCap a b c d)"
  "\<not> is_valid_vtable_root (ThreadCap tcb_ref)"
  "\<not> is_valid_vtable_root (CNodeCap cnode_ref sz guard)"
  "\<not> is_valid_vtable_root (EndpointCap ep_ref badge R)"
  "\<not> is_valid_vtable_root (NotificationCap ep_ref badge R)"
  "\<not> is_valid_vtable_root (ReplyCap tcb_ref master R)"
  "\<not> is_valid_vtable_root (Zombie e f g)"
  "\<not> is_valid_vtable_root (NullCap)"
  "\<not> is_valid_vtable_root (DomainCap)"
  by (fastforce dest: is_valid_vtable_root_is_arch_cap simp: is_cap_simps)+

lemmas [simp] = aobj_ref_acap_rights_update arch_obj_size_acap_rights_update
  valid_validate_vm_rights cap_master_arch_inv acap_rights_update_idem
  cap_master_arch_cap_rights valid_acap_rights_update_id state_hyp_refs_of_revokable

lemmas [intro] = valid_arch_cap_acap_rights_update
lemmas [intro!] = valid_acap_rights_update_id
lemmas [wp] = set_cap_hyp_refs_of

lemma remove_rights_cap_valid[simp]:
  "s \<turnstile> c \<Longrightarrow> s \<turnstile> remove_rights S c"
  using valid_validate_vm_rights
  apply (cases c; simp add: remove_rights_def cap_rights_update_def
                            valid_cap_def cap_aligned_def
                     split: bool.splits)
  by fastforce


lemma get_thread_state_inv [simp]:
  "\<lbrace> P \<rbrace> get_thread_state t \<lbrace> \<lambda>r. P \<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def gets_the_def)
  apply wp
  apply simp
  done

lemma get_bound_notification_inv[simp]:
  "\<lbrace>P\<rbrace> get_bound_notification t \<lbrace>\<lambda>r. P\<rbrace>"
  apply (simp add: get_bound_notification_def thread_get_def gets_the_def)
  apply (wp, simp)
  done

lemma gets_the_sp:
  "\<lbrace> Q \<rbrace> gets_the f \<lbrace>\<lambda>rv s. f s = Some rv \<and> Q s\<rbrace>"
  by wpsimp

lemma gets_the_get_tcb_sp:
  "\<lbrace> Q \<rbrace> gets_the (get_tcb thread) \<lbrace>\<lambda>t. Q and ko_at (TCB t) thread\<rbrace>"
  by wpsimp

lemma assert_get_tcb_sp:
  assumes "\<And>s. Q s \<Longrightarrow> valid_objs s"
  shows "\<lbrace> Q \<rbrace> gets_the (get_tcb thread)
         \<lbrace>\<lambda>t. Q and ko_at (TCB t) thread and valid_tcb thread t \<rbrace>"
  apply (rule hoare_strengthen_post[OF gets_the_get_tcb_sp])
  apply (clarsimp simp: obj_at_def)
  apply (erule (1) valid_objsE[where x=thread, OF assms])
  apply (clarsimp simp: valid_obj_def)
  done

crunch get_cap
  for inv[wp]: "P"
  (simp: crunch_simps)


lemma rab_inv[wp]:
  "\<lbrace>P\<rbrace> resolve_address_bits slot \<lbrace>\<lambda>rv. P\<rbrace>"
unfolding resolve_address_bits_def
proof (induct slot rule: resolve_address_bits'.induct)
  case (1 z cap cref)
  show ?case
  apply (clarsimp simp add: valid_def)
  apply (subst (asm) resolve_address_bits'.simps)
  apply (cases cap)
            apply (auto simp: in_monad)[5]
       defer
       apply (auto simp: in_monad)[6]
  apply (rename_tac obj_ref nat list)
  apply (simp only: cap.simps)
  apply (case_tac "nat + length list = 0")
   apply (simp add: fail_def)
  apply (simp only: if_False)
  apply (case_tac a)
   apply (simp only: K_bind_def)
   apply (drule in_bindE_L, elim disjE conjE exE)+
       apply (simp only: split: if_split_asm)
        apply (simp add: returnOk_def return_def)
       apply (drule in_bindE_L, elim disjE conjE exE)+
        apply (simp only: split: if_split_asm)
         prefer 2
         apply (clarsimp simp: in_monad)
        apply (drule (8) 1)
        apply (clarsimp simp: in_monad)
        apply (drule in_inv_by_hoareD [OF get_cap_inv])
        apply (auto simp: in_monad valid_def)[1]
       apply (clarsimp simp: in_monad)
      apply (clarsimp simp: in_monad)
     apply (clarsimp simp: in_monad)
    apply (clarsimp simp: in_monad)
   apply (clarsimp simp: in_monad)
  apply (simp only: K_bind_def in_bindE_R)
  apply (elim conjE exE)
  apply (simp only: split: if_split_asm)
   apply (simp add: in_monad split: if_split_asm)
  apply (simp only: K_bind_def in_bindE_R)
  apply (elim conjE exE)
  apply (simp only: split: if_split_asm)
   prefer 2
   apply (clarsimp simp: in_monad)
   apply (drule in_inv_by_hoareD [OF get_cap_inv])
   apply simp
  apply (drule (8) "1")
  apply (clarsimp simp: in_monad valid_def)
  apply (drule in_inv_by_hoareD [OF get_cap_inv])
  apply (auto simp: in_monad)
  done
qed

crunch lookup_slot_for_thread
  for inv[wp]: P


crunch lookup_cap
  for inv[wp]: P


lemma cte_at_tcb_update:
  "tcb_at t s \<Longrightarrow> cte_at slot (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>) = cte_at slot s"
  by (clarsimp simp add: cte_at_cases obj_at_def is_tcb)


lemma valid_cap_tcb_update [simp]:
  "tcb_at t s \<Longrightarrow> (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>) \<turnstile> cap = s \<turnstile> cap"
  apply (clarsimp simp: is_tcb elim!: obj_atE)
  apply (subgoal_tac "a_type (TCB tcba) = a_type (TCB tcb)")
   apply (rule iffI)
    apply (drule(1) valid_cap_same_type[where p=t])
     apply simp
    apply (simp add: fun_upd_idem)
   apply (erule(2) valid_cap_same_type[OF _ sym])
  apply (simp add: a_type_def)
  done


lemma obj_at_tcb_update:
  "\<lbrakk> tcb_at t s; \<And>x y. P (TCB x) = P (TCB y)\<rbrakk> \<Longrightarrow>
  obj_at P t' (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>) = obj_at P t' s"
  apply (simp add: obj_at_def is_tcb_def)
  apply clarsimp
  apply (case_tac ko)
  apply simp_all
  done


lemma valid_thread_state_tcb_update:
  "\<lbrakk> tcb_at t s \<rbrakk> \<Longrightarrow>
  valid_tcb_state ts (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>) = valid_tcb_state ts s"
  apply (unfold valid_tcb_state_def)
  apply (case_tac ts)
  apply (simp_all add: obj_at_tcb_update is_ep_def is_tcb_def is_ntfn_def)
  done


lemma valid_objs_tcb_update:
  "\<lbrakk>tcb_at t s; valid_tcb t tcb s; valid_objs s \<rbrakk>
  \<Longrightarrow> valid_objs (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>)"
  apply (clarsimp simp: valid_objs_def dom_def
                 elim!: obj_atE)
  apply (intro conjI impI)
   apply (rule valid_obj_same_type)
      apply (simp add: valid_obj_def)+
   apply (clarsimp simp: a_type_def is_tcb)
  apply clarsimp
  apply (rule valid_obj_same_type)
     apply (drule_tac x=ptr in spec, simp)
    apply (simp add: valid_obj_def)
   apply assumption
  apply (clarsimp simp add: a_type_def is_tcb)
  done


lemma obj_at_update:
  "obj_at P t' (s \<lparr>kheap := (kheap s)(t \<mapsto> v)\<rparr>) =
  (if t = t' then P v else obj_at P t' s)"
  by (simp add: obj_at_def)


lemma iflive_tcb_update:
  "\<lbrakk> if_live_then_nonz_cap s; live (TCB tcb) \<longrightarrow> ex_nonz_cap_to t s;
           obj_at (same_caps (TCB tcb)) t s \<rbrakk>
  \<Longrightarrow> if_live_then_nonz_cap (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>)"
  unfolding fun_upd_def
  apply (simp add: if_live_then_nonz_cap_def, erule allEI)
  apply safe
   apply (clarsimp simp add: obj_at_def elim!: ex_cap_to_after_update
                   split: if_split_asm | (erule notE, erule ex_cap_to_after_update))+
  done


lemma ifunsafe_tcb_update:
  "\<lbrakk> if_unsafe_then_cap s; obj_at (same_caps (TCB tcb)) t s \<rbrakk>
  \<Longrightarrow> if_unsafe_then_cap (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>)"
  apply (simp add: if_unsafe_then_cap_def, elim allEI)
  apply (clarsimp dest!: caps_of_state_cteD
                   simp: cte_wp_at_after_update fun_upd_def)
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        ex_cte_cap_to_after_update)
  done


lemma zombies_tcb_update:
  "\<lbrakk> zombies_final s; obj_at (same_caps (TCB tcb)) t s \<rbrakk>
   \<Longrightarrow> zombies_final (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB tcb)\<rparr>)"
  apply (simp add: zombies_final_def is_final_cap'_def2, elim allEI)
  apply (clarsimp simp: cte_wp_at_after_update fun_upd_def)
  done



lemma valid_idle_tcb_update:
  "\<lbrakk>valid_idle s; ko_at (TCB t) p s;
    tcb_state t = tcb_state t'; tcb_bound_notification t = tcb_bound_notification t';
    tcb_iarch t = tcb_iarch t';
    valid_tcb p t' s \<rbrakk>
   \<Longrightarrow> valid_idle (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB t')\<rparr>)"
  by (clarsimp simp: valid_idle_def pred_tcb_at_def obj_at_def)


lemma valid_reply_caps_tcb_update:
  "\<lbrakk>valid_reply_caps s; ko_at (TCB t) p s; tcb_state t = tcb_state t';
    same_caps (TCB t) (TCB t') \<rbrakk>
   \<Longrightarrow> valid_reply_caps (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB t')\<rparr>)"
  apply (frule_tac P'="same_caps (TCB t')" in obj_at_weakenE, simp)
  apply (fastforce simp: valid_reply_caps_def has_reply_cap_def
                        pred_tcb_at_def obj_at_def fun_upd_def
                        cte_wp_at_after_update caps_of_state_after_update)
  done


lemma valid_reply_masters_tcb_update:
  "\<lbrakk>valid_reply_masters s; ko_at (TCB t) p s; tcb_state t = tcb_state t';
    same_caps (TCB t) (TCB t') \<rbrakk>
   \<Longrightarrow> valid_reply_masters (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB t')\<rparr>)"
  by (clarsimp simp: valid_reply_masters_def fun_upd_def is_tcb
                     cte_wp_at_after_update obj_at_def)

lemma tcb_state_same_cte_wp_at:
  "\<lbrakk> ko_at (TCB t) p s; \<forall>(getF, v) \<in> ran tcb_cap_cases. getF t = getF t' \<rbrakk>
     \<Longrightarrow> \<forall>P p'. cte_wp_at P p' (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB t')\<rparr>)
             = cte_wp_at P p' s"
  apply (clarsimp simp add: cte_wp_at_cases obj_at_def)
  apply (case_tac "tcb_cap_cases b")
   apply simp
  apply (drule bspec, erule ranI)
  apply clarsimp
  done


lemma valid_tcb_state_update:
  "\<lbrakk> valid_tcb p t s; valid_tcb_state st s;
     case st of
                Structures_A.Inactive \<Rightarrow> True
              | Structures_A.BlockedOnReceive e data \<Rightarrow>
                     tcb_caller t = cap.NullCap
                   \<and> is_master_reply_cap (tcb_reply t)
                   \<and> obj_ref_of (tcb_reply t) = p
                   \<and> AllowGrant \<in> cap_rights (tcb_reply t)
              | _ \<Rightarrow> is_master_reply_cap (tcb_reply t)
                   \<and> obj_ref_of (tcb_reply t) = p
                   \<and> AllowGrant \<in> cap_rights (tcb_reply t) \<rbrakk> \<Longrightarrow>
   valid_tcb p (t\<lparr>tcb_state := st\<rparr>) s"
  by (simp add: valid_tcb_def valid_tcb_state_def ran_tcb_cap_cases
         split: Structures_A.thread_state.splits)


lemma valid_tcb_if_valid_state:
  assumes vs: "valid_state s"
  assumes somet: "get_tcb thread s = Some y"
  shows "valid_tcb thread y s"
proof -
  from somet have inran: "kheap s thread = Some (TCB y)"
    by (clarsimp simp: get_tcb_def
                split: option.splits Structures_A.kernel_object.splits)
  from vs have "(\<forall>ptr\<in>dom (kheap s). \<exists>obj. kheap s ptr = Some obj \<and> valid_obj ptr obj s)"
    by (simp add: valid_state_def valid_pspace_def valid_objs_def)
  with inran have "valid_obj thread (TCB y) s" by (fastforce simp: dom_def)
  thus ?thesis by (simp add: valid_tcb_def valid_obj_def)
qed


lemma assert_get_tcb_ko:
  shows "\<lbrace> P \<rbrace> gets_the (get_tcb thread) \<lbrace>\<lambda>t. ko_at (TCB t) thread \<rbrace>"
  by (clarsimp simp: valid_def in_monad gets_the_def get_tcb_def
                     obj_at_def
               split: option.splits Structures_A.kernel_object.splits)


lemma gts_st_tcb_at: "\<lbrace>st_tcb_at P t\<rbrace> get_thread_state t \<lbrace>\<lambda>rv s. P rv\<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_def is_tcb)
  done


lemma gts_st_tcb:
  "\<lbrace>\<top>\<rbrace> get_thread_state t \<lbrace>\<lambda>rv. st_tcb_at (\<lambda>st. rv = st) t\<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def)
  done

lemma gbn_bound_tcb:
  "\<lbrace>\<top>\<rbrace> get_bound_notification t \<lbrace>\<lambda>rv. bound_tcb_at (\<lambda>ntfn. rv = ntfn) t\<rbrace>"
  apply (simp add: get_bound_notification_def thread_get_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def)
  done


definition
  cap_master_cap :: "cap \<Rightarrow> cap"
where
 "cap_master_cap cap \<equiv> case cap of
   cap.EndpointCap ref bdg rghts \<Rightarrow> cap.EndpointCap ref 0 UNIV
 | cap.NotificationCap ref bdg rghts \<Rightarrow> cap.NotificationCap ref 0 UNIV
 | cap.CNodeCap ref bits gd \<Rightarrow> cap.CNodeCap ref bits []
 | cap.ThreadCap ref \<Rightarrow> cap.ThreadCap ref
 | cap.DomainCap \<Rightarrow> cap.DomainCap
 | cap.ReplyCap ref master rghts \<Rightarrow> cap.ReplyCap ref True UNIV
 | cap.UntypedCap dev ref n f \<Rightarrow> cap.UntypedCap dev ref n 0
 | cap.ArchObjectCap acap \<Rightarrow> cap.ArchObjectCap (cap_master_arch_cap acap)
 | _ \<Rightarrow> cap"


lemma cap_master_cap_eqDs1:
  "cap_master_cap cap = cap.EndpointCap ref bdg rghts
     \<Longrightarrow> bdg = 0 \<and> rghts = UNIV
          \<and> (\<exists>bdg rghts. cap = cap.EndpointCap ref bdg rghts)"
  "cap_master_cap cap = cap.NotificationCap ref bdg rghts
     \<Longrightarrow> bdg = 0 \<and> rghts = UNIV
          \<and> (\<exists>bdg rghts. cap = cap.NotificationCap ref bdg rghts)"
  "cap_master_cap cap = cap.CNodeCap ref bits gd
     \<Longrightarrow> gd = [] \<and> (\<exists>gd. cap = cap.CNodeCap ref bits gd)"
  "cap_master_cap cap = cap.ThreadCap ref
     \<Longrightarrow> cap = cap.ThreadCap ref"
  "cap_master_cap cap = cap.DomainCap
     \<Longrightarrow> cap = cap.DomainCap"
  "cap_master_cap cap = cap.NullCap
     \<Longrightarrow> cap = cap.NullCap"
  "cap_master_cap cap = cap.IRQControlCap
     \<Longrightarrow> cap = cap.IRQControlCap"
  "cap_master_cap cap = cap.IRQHandlerCap irq
     \<Longrightarrow> cap = cap.IRQHandlerCap irq"
  "cap_master_cap cap = cap.Zombie ref tp n
     \<Longrightarrow> cap = cap.Zombie ref tp n"
  "cap_master_cap cap = cap.UntypedCap dev ref bits 0
     \<Longrightarrow> \<exists>f. cap = cap.UntypedCap dev ref bits f"
  "cap_master_cap cap = cap.ReplyCap ref master rghts
     \<Longrightarrow> master = True \<and> rghts = UNIV
          \<and> (\<exists>master rghts. cap = cap.ReplyCap ref master rghts)"
  by (clarsimp simp: cap_master_cap_def
              split: cap.split_asm)+

lemma cap_master_cap_arch_eqD:
    "cap_master_cap cap = ArchObjectCap acap
     \<Longrightarrow> \<exists>ac. cap = ArchObjectCap ac \<and> acap = cap_master_arch_cap ac"
       by (clarsimp simp: cap_master_cap_def
              split: cap.split_asm)+

lemmas cap_master_cap_eqDs =
  cap_master_cap_eqDs1 cap_master_cap_arch_eqD
  cap_master_cap_eqDs1 [OF sym] cap_master_cap_arch_eqD [OF sym]


definition
  cap_badge :: "cap \<rightharpoonup> badge"
where
 "cap_badge cap \<equiv> case cap of
    cap.EndpointCap r badge rights \<Rightarrow> Some badge
  | cap.NotificationCap r badge rights \<Rightarrow> Some badge
  | _ \<Rightarrow> None"

lemma cap_badge_simps [simp]:
 "cap_badge (cap.EndpointCap r badge rights)       = Some badge"
 "cap_badge (cap.NotificationCap r badge rights)   = Some badge"
 "cap_badge (cap.UntypedCap dev p n f)             = None"
 "cap_badge (cap.NullCap)                          = None"
 "cap_badge (cap.DomainCap)                        = None"
 "cap_badge (cap.CNodeCap r bits guard)            = None"
 "cap_badge (cap.ThreadCap r)                      = None"
 "cap_badge (cap.DomainCap)                        = None"
 "cap_badge (cap.ReplyCap r master rights)         = None"
 "cap_badge (cap.IRQControlCap)                    = None"
 "cap_badge (cap.IRQHandlerCap irq)                = None"
 "cap_badge (cap.Zombie r b n)                     = None"
 "cap_badge (cap.ArchObjectCap cap)                = None"
  by (auto simp: cap_badge_def)




lemma cdt_parent_of_def:
  "m \<turnstile> p cdt_parent_of c \<equiv> m c = Some p"
  by (simp add: cdt_parent_rel_def is_cdt_parent_def)


lemmas cdt_parent_defs = cdt_parent_of_def is_cdt_parent_def cdt_parent_rel_def


lemma valid_mdb_no_null:
  "\<lbrakk> valid_mdb s; caps_of_state s p = Some cap.NullCap \<rbrakk> \<Longrightarrow>
  \<not> cdt s \<Turnstile> p \<rightarrow> p' \<and> \<not> cdt s \<Turnstile> p' \<rightarrow> p"
  apply (simp add: valid_mdb_def mdb_cte_at_def cte_wp_at_caps_of_state)
  apply (cases p, cases p')
  apply (rule conjI)
   apply (fastforce dest!: tranclD simp: cdt_parent_defs)
  apply (fastforce dest!: tranclD2 simp: cdt_parent_defs)
  done


lemma x_sym: "(s = t) = r \<Longrightarrow> (t = s) = r" by auto

lemma set_inter_not_emptyD1: "\<lbrakk>A \<inter> B = {}; A \<noteq> {}; B \<noteq> {}\<rbrakk> \<Longrightarrow> \<not> B \<subseteq> A"
  by blast


lemma set_inter_not_emptyD2: "\<lbrakk>A \<inter> B = {}; A \<noteq> {}; B \<noteq> {}\<rbrakk> \<Longrightarrow> \<not> A \<subseteq> B"
  by blast


lemma set_inter_not_emptyD3: "\<lbrakk>A \<inter> B = {}; A \<noteq> {}; B \<noteq> {}\<rbrakk> \<Longrightarrow> A \<noteq> B"
  by blast


lemma untyped_range_in_cap_range: "untyped_range x \<subseteq> cap_range x"
  by(simp add: cap_range_def)


lemma set_object_cte_wp_at:
  "\<lbrace>\<lambda>s. cte_wp_at P p (kheap_update (\<lambda>ps. (kheap s)(ptr \<mapsto> ko)) s)\<rbrace>
  set_object ptr ko
  \<lbrace>\<lambda>uu. cte_wp_at P p\<rbrace>"
  by (wpsimp wp: set_object_wp_strong)



lemma set_cap_cte_wp_at:
  "\<lbrace>(\<lambda>s. if p = ptr then P cap else cte_wp_at P p s) and cte_at ptr\<rbrace>
  set_cap cap ptr
  \<lbrace>\<lambda>uu s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp set_cap_caps_of_state)
  apply clarsimp
  done


lemma set_cap_cte_wp_at':
  "\<lbrace>\<lambda>s. if p = ptr then (P cap \<and> cte_at ptr s) else cte_wp_at P p s\<rbrace>
  set_cap cap ptr
  \<lbrace>\<lambda>uu s. cte_wp_at P p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp set_cap_caps_of_state)
  apply clarsimp
  done


lemma set_cap_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
   set_cap cap p'
   \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: set_object_typ_at get_object_wp simp: set_cap_def)


lemma set_cap_a_type_inv:
  "((), t) \<in> fst (set_cap cap slot s) \<Longrightarrow> typ_at T p t = typ_at T p s"
  apply (subgoal_tac "EX x. typ_at T p s = x")
   apply (elim exE)
   apply (cut_tac P="(=) x" in set_cap_typ_at[of _ T p cap slot])
   apply (fastforce simp: valid_def)
  apply fastforce
  done


lemma set_cap_tcb:
  "\<lbrace>tcb_at p'\<rbrace> set_cap cap  p \<lbrace>\<lambda>rv. tcb_at p'\<rbrace>"
  by (clarsimp simp: tcb_at_typ intro!: set_cap_typ_at)


lemma set_cap_sets:
  "\<lbrace>\<top>\<rbrace> set_cap cap p \<lbrace>\<lambda>rv s. cte_wp_at (\<lambda>c. c = cap) p s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp set_cap_caps_of_state)
  apply clarsimp
  done


lemma set_cap_valid_cap:
  "\<lbrace>valid_cap c\<rbrace> set_cap x p \<lbrace>\<lambda>_. valid_cap c\<rbrace>"
  by (simp add: valid_cap_typ set_cap_typ_at)


lemma set_cap_cte_at:
  "\<lbrace>cte_at p'\<rbrace> set_cap x p \<lbrace>\<lambda>_. cte_at p'\<rbrace>"
  by (simp add: valid_cte_at_typ set_cap_typ_at [where P="\<lambda>x. x"])


lemma set_cap_valid_objs:
  "\<lbrace>(valid_objs::'state_ext::state_ext state \<Rightarrow> bool) and valid_cap x
        and tcb_cap_valid x p\<rbrace>
      set_cap x p \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (rule bind_wp [OF _ get_object_sp])
  apply (case_tac obj, simp_all split del: if_split)
   apply clarsimp
   apply (wp set_object_valid_objs)
   apply (clarsimp simp: obj_at_def a_type_def wf_cs_upd)
   apply (erule(1) valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_cs_def
                         valid_cs_size_def wf_cs_upd)
   apply (clarsimp simp: ran_def split: if_split_asm)
   apply blast
  apply (rule hoare_pre, wp set_object_valid_objs)
  apply (clarsimp simp: obj_at_def a_type_def tcb_cap_valid_def
                        is_tcb_def)
  apply (erule(1) valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def
                        ran_tcb_cap_cases)
  apply (intro conjI impI, simp_all add: pred_tcb_at_def obj_at_def)
  done


lemma set_cap_aligned [wp]:
 "\<lbrace>pspace_aligned\<rbrace>
  set_cap c p
  \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wp set_object_aligned get_object_wp | wpc)+
  apply (auto simp: a_type_def obj_at_def wf_cs_upd fun_upd_def[symmetric])
  done


lemma set_cap_refs_of [wp]:
 "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_cap cp p
  \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (auto elim!: rsubst[where P=P]
               simp: state_refs_of_def obj_at_def
             intro!: ext
             split: if_split_asm)
  done


lemma set_cap_distinct [wp]:
 "\<lbrace>pspace_distinct\<rbrace> set_cap c p \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wp set_object_distinct get_object_wp | wpc)+
  apply (auto simp: a_type_def obj_at_def wf_cs_upd fun_upd_def[symmetric])
  done


lemma set_cap_cur [wp]:
 "\<lbrace>cur_tcb\<rbrace> set_cap c p \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb)
  done

lemma set_cap_pred_tcb [wp]:
 "\<lbrace>pred_tcb_at proj P t\<rbrace> set_cap c p \<lbrace>\<lambda>rv. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_cap_def set_object_def split_def)
  apply (wp get_object_wp | wpc)+
  apply (auto simp: pred_tcb_at_def obj_at_def tcb_to_itcb_def)
  done


lemma set_cap_live[wp]:
  "\<lbrace>\<lambda>s. P (obj_at live p' s)\<rbrace>
     set_cap cap p \<lbrace>\<lambda>rv s. P (obj_at live p' s)\<rbrace>"
  apply (simp add: set_cap_def split_def set_object_def)
  apply (wp get_object_wp | wpc)+
  by (fastforce simp: obj_at_def live_def)


lemma set_cap_cap_to:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap'. p'\<notin>(zobj_refs cap' - zobj_refs cap)) p s
         \<and> ex_nonz_cap_to p' s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p'\<rbrace>"
  apply (simp add: ex_nonz_cap_to_def cte_wp_at_caps_of_state)
  apply wp
  apply simp
  apply (elim conjE exE)
  apply (case_tac "(a, b) = p")
   apply fastforce
  apply fastforce
  done


crunch set_cap
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)


lemma set_cap_cte_cap_wp_to:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap'. p' \<in> cte_refs cap' (interrupt_irq_node s) \<and> P cap'
                           \<longrightarrow> p' \<in> cte_refs cap (interrupt_irq_node s) \<and> P cap) p s
        \<and> ex_cte_cap_wp_to P p' s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p'\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state del: split_paired_Ex)
  apply (wp hoare_vcg_ex_lift)
  apply clarify
  by (metis fun_upd_other fun_upd_same option.sel)


lemma set_cap_iflive:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap'. \<forall>p'\<in>(zobj_refs cap' - zobj_refs cap). obj_at (Not \<circ> live) p' s) p s
        \<and> if_live_then_nonz_cap s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: if_live_then_nonz_cap_def)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre, wp hoare_vcg_all_lift hoare_vcg_disj_lift set_cap_cap_to)
  apply (clarsimp simp: cte_wp_at_def)
  apply (rule ccontr)
  apply (drule bspec)
   apply simp
  apply (clarsimp simp: obj_at_def)
  done


lemma update_cap_iflive:
  "\<lbrace>cte_wp_at (\<lambda>cap'. zobj_refs cap' = zobj_refs cap) p
      and if_live_then_nonz_cap\<rbrace>
     set_cap cap p \<lbrace>\<lambda>rv s. if_live_then_nonz_cap s\<rbrace>"
  apply (wp set_cap_iflive)
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done


lemma set_cap_ifunsafe:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap'. \<forall>p'. p' \<in> cte_refs cap' (interrupt_irq_node s)
                            \<and> (p' \<notin> cte_refs cap (interrupt_irq_node s)
                                   \<or> (\<exists>cp. appropriate_cte_cap cp cap'
                                            \<and> \<not> appropriate_cte_cap cp cap))
                            \<longrightarrow>
                             (p' \<noteq> p \<longrightarrow> cte_wp_at ((=) cap.NullCap) p' s)
                           \<and> (p' = p \<longrightarrow> cap = cap.NullCap)) p s
        \<and> if_unsafe_then_cap s
        \<and> (cap \<noteq> cap.NullCap \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s)\<rbrace>
     set_cap cap p \<lbrace>\<lambda>rv s. if_unsafe_then_cap s\<rbrace>"
  apply (simp add: if_unsafe_then_cap_def)
  apply (wp set_cap_cte_cap_wp_to hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (rule ccontr, clarsimp)
   apply (drule spec, drule spec, drule(1) mp [OF _ conjI])
    apply auto[2]
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (fastforce simp: Ball_def)
  done


lemma update_cap_ifunsafe:
  "\<lbrace>cte_wp_at (\<lambda>cap'. cte_refs cap' = cte_refs cap
                      \<and> (\<forall>cp. appropriate_cte_cap cp cap'
                                 = appropriate_cte_cap cp cap)) p
      and if_unsafe_then_cap
      and (\<lambda>s. cap \<noteq> cap.NullCap \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s)\<rbrace>
     set_cap cap p \<lbrace>\<lambda>rv s. if_unsafe_then_cap s\<rbrace>"
  apply (wp set_cap_ifunsafe)
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done


crunch set_cap
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)


lemma set_cap_refs [wp]:
  "\<lbrace>\<lambda>x. P (global_refs x)\<rbrace> set_cap cap p \<lbrace>\<lambda>_ x. P (global_refs x)\<rbrace>"
  by (rule global_refs_lift) wp+

lemma set_cap_globals [wp]:
  "\<lbrace>valid_global_refs and (\<lambda>s. global_refs s \<inter> cap_range cap = {})\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: valid_global_refs_def valid_refs_def2 Ball_def)
  apply (wp set_cap_caps_of_state hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply (clarsimp simp: ran_def)
  apply blast
  done


lemma set_cap_pspace:
  assumes x: "\<And>s f'. f (kheap_update f' s) = f s"
  shows      "\<lbrace>\<lambda>s. P (f s)\<rbrace> set_cap p cap \<lbrace>\<lambda>rv s. P (f s)\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (rule bind_wp [OF _ get_object_sp])
  apply (case_tac obj, simp_all split del: if_split cong: if_cong)
   apply (wpsimp wp: set_object_wp simp: x)+
  done


lemma set_cap_rvk_cdt_ct_ms[wp]:
  "\<lbrace>\<lambda>s. P (is_original_cap s)\<rbrace> set_cap p cap \<lbrace>\<lambda>rv s. P (is_original_cap s)\<rbrace>"
  "\<lbrace>\<lambda>s. Q (cur_thread s)\<rbrace> set_cap p cap \<lbrace>\<lambda>rv s. Q (cur_thread s)\<rbrace>"
  "\<lbrace>\<lambda>s. R (machine_state s)\<rbrace> set_cap p cap \<lbrace>\<lambda>rv s. R (machine_state s)\<rbrace>"
  "\<lbrace>\<lambda>s. S (cdt s)\<rbrace> set_cap p cap \<lbrace>\<lambda>rv s. S (cdt s)\<rbrace>"
  "\<lbrace>\<lambda>s. T (idle_thread s)\<rbrace> set_cap p cap \<lbrace>\<lambda>rv s. T (idle_thread s)\<rbrace>"
  "\<lbrace>\<lambda>s. U (arch_state s)\<rbrace> set_cap p cap \<lbrace>\<lambda>rv s. U (arch_state s)\<rbrace>"
  by (rule set_cap_pspace | simp)+


lemma obvious:
  "\<lbrakk> S = {a}; x \<noteq> y; x \<in> S; y \<in> S \<rbrakk> \<Longrightarrow> P"
  by blast


lemma obvious2:
  "\<lbrakk> x \<in> S; \<And>y. y \<noteq> x \<Longrightarrow> y \<notin> S \<rbrakk> \<Longrightarrow> \<exists>x. S = {x}"
  by blast


lemma is_final_cap'_def3:
  "is_final_cap' cap = (\<lambda>s. \<exists>cref. cte_wp_at (\<lambda>c. gen_obj_refs cap \<inter> gen_obj_refs c \<noteq> {}) cref s
                                \<and> (\<forall>cref'. (cte_at cref' s \<and> cref' \<noteq> cref)
                                      \<longrightarrow> cte_wp_at (\<lambda>c. gen_obj_refs cap \<inter> gen_obj_refs c = {}) cref' s))"
  apply (clarsimp simp: is_final_cap'_def2
                intro!: ext arg_cong[where f=Ex])
  apply (subst iff_conv_conj_imp)
  apply (clarsimp simp: all_conj_distrib conj_comms)
  apply (rule rev_conj_cong[OF _ refl])
  apply (rule arg_cong[where f=All] ext)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply fastforce
  done


lemma final_cap_at_eq:
  "cte_wp_at (\<lambda>c. is_final_cap' c s) p s =
    (\<exists>cp. cte_wp_at (\<lambda>c. c = cp) p s \<and> (gen_obj_refs cp \<noteq> {})
       \<and> (\<forall>p'. (cte_at p' s \<and> p' \<noteq> p) \<longrightarrow>
                   cte_wp_at (\<lambda>c. gen_obj_refs cp \<inter> gen_obj_refs c = {}) p' s))"
  apply (clarsimp simp: is_final_cap'_def3 cte_wp_at_caps_of_state
                  simp del: split_paired_Ex split_paired_All)
  apply (rule iffI)
   apply (clarsimp simp del: split_paired_Ex split_paired_All)
   apply (rule conjI)
    apply clarsimp
   apply (subgoal_tac "(a, b) = p")
    apply (erule allEI)
    apply clarsimp
   apply (erule_tac x=p in allE)
   apply fastforce
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
  apply (rule_tac x=p in exI)
  apply (clarsimp simp del: split_paired_Ex split_paired_All)
  done


lemma zombie_has_refs:
  "is_zombie cap \<Longrightarrow> gen_obj_refs cap \<noteq> {}"
  by (clarsimp simp: is_cap_simps cap_irqs_def cap_irq_opt_def
                     gen_obj_refs_def
              split: sum.split_asm)


lemma zombie_cap_irqs:
  "is_zombie cap \<Longrightarrow> cap_irqs cap = {}"
  by (clarsimp simp: is_cap_simps)

lemma zombie_cap_arch_gen_obj_refs:
  "is_zombie cap \<Longrightarrow> arch_gen_refs cap = {}"
  by (clarsimp simp: is_cap_simps)

lemma zombies_final_def2:
  "zombies_final = (\<lambda>s. \<forall>p p' cap cap'. (cte_wp_at ((=) cap) p s \<and> cte_wp_at ((=) cap') p' s
                                          \<and> (obj_refs cap \<inter> obj_refs cap' \<noteq> {}) \<and> p \<noteq> p')
                                      \<longrightarrow> (\<not> is_zombie cap \<and> \<not> is_zombie cap'))"
  unfolding zombies_final_def
  apply (rule ext)
  apply (rule iffI)
   apply (intro allI impI conjI notI)
    apply (elim conjE)
    apply (simp only: simp_thms conj_commute final_cap_at_eq cte_wp_at_def)
    apply (elim allE, drule mp, rule exI, erule(1) conjI)
    apply (elim exE conjE)
    apply (drule spec, drule mp, rule conjI, erule not_sym)
     apply simp
    apply (clarsimp simp: gen_obj_refs_Int)
   apply (elim conjE)
   apply (simp only: simp_thms conj_commute final_cap_at_eq cte_wp_at_def)
   apply (elim allE, drule mp, rule exI, erule(1) conjI)
   apply (elim exE conjE)
   apply (drule spec, drule mp, erule conjI)
    apply simp
   apply (clarsimp simp: Int_commute gen_obj_refs_Int)
  apply (clarsimp simp: final_cap_at_eq cte_wp_at_def
                        zombie_has_refs gen_obj_refs_Int
                        zombie_cap_irqs
                  simp del: split_paired_Ex)
  apply (rule ccontr)
  apply (elim allE, erule impE, (erule conjI)+)
   apply (clarsimp simp: is_cap_simps)
  apply clarsimp
  done


lemma zombies_finalD2:
  "\<lbrakk> fst (get_cap p s) = {(cap, s)}; fst (get_cap p' s) = {(cap', s)};
     p \<noteq> p'; zombies_final s; obj_refs cap \<inter> obj_refs cap' \<noteq> {} \<rbrakk>
     \<Longrightarrow> \<not> is_zombie cap \<and> \<not> is_zombie cap'"
  by (simp only: zombies_final_def2 cte_wp_at_def simp_thms conj_comms)

lemma zombies_finalD3:
  "\<lbrakk> cte_wp_at P p s; cte_wp_at P' p' s; p \<noteq> p'; zombies_final s;
     \<And>cap cap'. \<lbrakk> P cap; P' cap' \<rbrakk> \<Longrightarrow> obj_refs cap \<inter> obj_refs cap' \<noteq> {} \<rbrakk>
     \<Longrightarrow> cte_wp_at (Not \<circ> is_zombie) p s \<and> cte_wp_at (Not \<circ> is_zombie) p' s"
  apply (clarsimp simp: cte_wp_at_def)
  apply (erule(3) zombies_finalD2)
  apply simp
  done


lemma set_cap_final_cap_at:
  "\<lbrace>\<lambda>s. is_final_cap' cap' s \<and>
     cte_wp_at (\<lambda>cap''. (gen_obj_refs cap'' \<inter> gen_obj_refs cap' \<noteq> {})
                            = (gen_obj_refs cap \<inter> gen_obj_refs cap' \<noteq> {})) p s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. is_final_cap' cap'\<rbrace>"
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state)
  apply wp
  apply (elim conjE exEI allEI)
  apply (clarsimp simp: Int_commute)
  done


lemma set_cap_zombies':
  "\<lbrace>\<lambda>s. zombies_final s
         \<and> cte_wp_at (\<lambda>cap'. \<forall>p' cap''. (cte_wp_at ((=) cap'') p' s \<and> p \<noteq> p'
                            \<and> (obj_refs cap \<inter> obj_refs cap'' \<noteq> {})
                             \<longrightarrow> (\<not> is_zombie cap \<and> \<not> is_zombie cap''))) p s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: zombies_final_def2 cte_wp_at_caps_of_state)
  apply (rule hoare_pre, wp)
  apply clarsimp
  apply (metis Int_commute prod.inject)
  done

fun ex_zombie_refs :: "(cap \<times> cap) \<Rightarrow> obj_ref set"
where
  "ex_zombie_refs (c1, c2) =
     (case c1 of
       cap.Zombie p b n \<Rightarrow>
         (case c2 of
           cap.Zombie p' b' n' \<Rightarrow>
             (obj_refs (cap.Zombie p b n) - obj_refs (cap.Zombie p' b' n'))
           | _ \<Rightarrow>
             obj_refs (cap.Zombie p b n))
       | _ \<Rightarrow> obj_refs c1 - obj_refs c2)"

declare ex_zombie_refs.simps [simp del]

lemmas ex_zombie_refs_simps [simp]
    = ex_zombie_refs.simps[split_simps cap.split, simplified]

lemma ex_zombie_refs_def2:
 "ex_zombie_refs (cap, cap') =
    (if is_zombie cap
     then if is_zombie cap'
       then obj_refs cap - obj_refs cap'
       else obj_refs cap
     else obj_refs cap - obj_refs cap')"
  by (simp add: is_zombie_def split: cap.splits split del: if_split)

lemma set_cap_zombies:
  "\<lbrace>\<lambda>s. zombies_final s
         \<and> cte_wp_at (\<lambda>cap'. \<forall>r\<in>ex_zombie_refs (cap, cap'). \<forall>p'.
                              (p \<noteq> p' \<and> cte_wp_at (\<lambda>cap''. r \<in> obj_refs cap'') p' s)
                                \<longrightarrow> (cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap)) p s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (wp set_cap_zombies')
  apply (clarsimp simp: cte_wp_at_def elim!: nonemptyE)
  apply (subgoal_tac "x \<in> obj_refs capa \<longrightarrow> \<not> is_zombie cap'' \<and> \<not> is_zombie capa")
   prefer 2
   apply (rule impI)
   apply (drule(3) zombies_finalD2)
    apply clarsimp
    apply blast
   apply simp
  apply (simp only: ex_zombie_refs_def2 split: if_split_asm)
    apply simp
    apply (drule bspec, simp)
    apply (elim allE, erule disjE, erule(1) notE)
    apply simp
   apply simp
   apply (drule(1) bspec, elim allE, erule disjE, erule(1) notE)
   apply simp
  apply simp
  apply (erule impCE)
   apply (drule bspec, simp)
   apply (elim allE, erule impE, erule conjI)
    apply simp
   apply simp
  apply simp
  done


lemma set_cap_obj_at_other:
  "\<lbrace>\<lambda>s. P (obj_at P' p s) \<and> p \<noteq> fst p'\<rbrace> set_cap cap p' \<lbrace>\<lambda>rv s. P (obj_at P' p s)\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (rule bind_wp [OF _ get_object_inv])
  apply (case_tac obj, simp_all split del: if_split)
   apply (wpsimp wp: set_object_wp simp: obj_at_def)+
  done


lemma new_cap_iflive:
  "\<lbrace>cte_wp_at ((=) cap.NullCap) p
      and if_live_then_nonz_cap\<rbrace>
     set_cap cap p \<lbrace>\<lambda>rv s. if_live_then_nonz_cap s\<rbrace>"
  by (wp set_cap_iflive, clarsimp elim!: cte_wp_at_weakenE)


lemma new_cap_ifunsafe:
  "\<lbrace>cte_wp_at ((=) cap.NullCap) p
      and if_unsafe_then_cap and ex_cte_cap_wp_to (appropriate_cte_cap cap) p\<rbrace>
     set_cap cap p \<lbrace>\<lambda>rv s. if_unsafe_then_cap s\<rbrace>"
  by (wp set_cap_ifunsafe, clarsimp elim!: cte_wp_at_weakenE)


lemma ex_zombie_refs_Null[simp]:
  "ex_zombie_refs (c, cap.NullCap) = obj_refs c"
  by (simp add: ex_zombie_refs_def2)


lemma new_cap_zombies:
  "\<lbrace>\<lambda>s. cte_wp_at ((=) cap.NullCap) p s \<and>
        (\<forall>r\<in>obj_refs cap. \<forall>p'. p \<noteq> p' \<and> cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') p' s
                                   \<longrightarrow> (cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap))
        \<and> zombies_final s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (wp set_cap_zombies)
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done


lemma new_cap_valid_pspace:
  "\<lbrace>cte_wp_at ((=) cap.NullCap) p and valid_cap cap
      and tcb_cap_valid cap p and valid_pspace
      and (\<lambda>s. \<forall>r\<in>obj_refs cap. \<forall>p'. p \<noteq> p' \<and> cte_wp_at (\<lambda>cap'. r \<in> obj_refs cap') p' s
                                     \<longrightarrow> (cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap))\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (simp add: valid_pspace_def)
  apply (wp set_cap_valid_objs new_cap_iflive new_cap_ifunsafe new_cap_zombies)
  apply (auto simp: cte_wp_at_caps_of_state)
  done




lemma gen_obj_refs_distinct_or_equal_corl:
  "\<lbrakk> x \<in> gen_obj_refs cap; x \<in> gen_obj_refs cap' \<rbrakk>
     \<Longrightarrow> gen_obj_refs cap = gen_obj_refs cap'"
  by (blast intro!: gen_obj_refs_distinct_or_equal)


lemma obj_refs_cap_irqs_not_both:
  "obj_refs cap \<noteq> {} \<longrightarrow> cap_irqs cap = {} \<and> arch_gen_refs cap = {}"
  apply (intro impI conjI)
   apply (clarsimp simp: cap_irqs_def cap_irq_opt_def split: cap.split sum.split_asm)
  by (clarsimp simp: ex_in_conv[symmetric] obj_ref_not_arch_gen_ref)


lemma not_final_another:
  "\<lbrakk> \<not> is_final_cap' cap s; fst (get_cap p s) = {(cap, s)};
       r \<in> gen_obj_refs cap \<rbrakk>
      \<Longrightarrow> \<exists>p' cap'. p' \<noteq> p \<and> fst (get_cap p' s) = {(cap', s)}
                         \<and> gen_obj_refs cap' = gen_obj_refs cap
                         \<and> \<not> is_final_cap' cap' s"
  apply (erule(1) not_final_another')
  apply clarsimp
  done


lemma delete_no_untyped:
  "\<lbrakk> ((), s') \<in> fst (set_cap cap.NullCap p s);
     \<not> (\<exists>cref. cte_wp_at (\<lambda>c. p' \<in> untyped_range c) cref s) \<rbrakk> \<Longrightarrow>
     \<not> (\<exists>cref. cte_wp_at (\<lambda>c. p' \<in> untyped_range c) cref s')"
  apply (simp only: cte_wp_at_caps_of_state)
  apply (erule use_valid, wp)
  apply clarsimp
  done


lemma get_cap_caps_of_state:
  "(fst (get_cap p s) = {(cap, s)}) = (Some cap = caps_of_state s p)"
  by (clarsimp simp: caps_of_state_def eq_commute)

(* generic consequence of architecture-specific details *)
lemma (in Arch) abj_ref_none_no_refs:
  "obj_refs c = {} \<Longrightarrow> table_cap_ref c = None"
  unfolding table_cap_ref_def
  apply (cases c; simp)
  subgoal for ac by (cases ac; simp)
  done

requalify_facts Arch.abj_ref_none_no_refs

lemma no_cap_to_obj_with_diff_ref_Null:
  "no_cap_to_obj_with_diff_ref NullCap S = \<top>"
  by (rule ext, clarsimp simp: no_cap_to_obj_with_diff_ref_def
                               cte_wp_at_caps_of_state abj_ref_none_no_refs)

definition
  replaceable :: "'z::state_ext state \<Rightarrow> cslot_ptr \<Rightarrow> cap \<Rightarrow> cap \<Rightarrow> bool"
where
 "replaceable s sl newcap \<equiv> \<lambda>cap.
    (cap = newcap)
  \<or> (\<not> is_final_cap' cap s
      \<and> newcap = NullCap
      \<and> replaceable_non_final_arch_cap s sl newcap cap)
  \<or> (is_final_cap' cap s
      \<and> (\<forall>p\<in>zobj_refs cap - zobj_refs newcap. obj_at (Not \<circ> live) p s)
      \<and> (\<forall>p'. p' \<in> cte_refs cap (interrupt_irq_node s)
               \<and> (p' \<notin> cte_refs newcap (interrupt_irq_node s)
                    \<or> (\<exists>cp. appropriate_cte_cap cp cap
                             \<and> \<not> appropriate_cte_cap cp newcap))
             \<longrightarrow>
                 (p' \<noteq> sl \<longrightarrow> cte_wp_at ((=) cap.NullCap) p' s)
               \<and> (p' = sl \<longrightarrow> newcap = cap.NullCap))
      \<and> (gen_obj_refs newcap \<subseteq> gen_obj_refs cap)
      \<and> (newcap \<noteq> cap.NullCap \<longrightarrow> cap_range newcap = cap_range cap)
      \<and> (is_master_reply_cap cap \<longrightarrow> newcap = cap.NullCap)
      \<and> (is_reply_cap cap \<longrightarrow> newcap = cap.NullCap)
      \<and> (\<not> is_master_reply_cap cap \<longrightarrow>
         tcb_cap_valid cap sl s \<longrightarrow> tcb_cap_valid newcap sl s)
      \<and> \<not> is_untyped_cap newcap \<and> \<not> is_master_reply_cap newcap
      \<and> \<not> is_reply_cap newcap
      \<and> newcap \<noteq> cap.IRQControlCap
      \<and> (newcap \<noteq> cap.NullCap \<longrightarrow> cap_class newcap = cap_class cap \<and> cap_is_device newcap = cap_is_device cap)
      \<and> replaceable_final_arch_cap s sl newcap cap)"

lemma range_not_empty_is_physical:
  "valid_cap cap s \<Longrightarrow> (cap_class cap = PhysicalClass) = (cap_range cap \<noteq> {})"
  apply (case_tac cap)
   by (simp_all add: cap_range_def valid_cap_simps cap_aligned_def is_aligned_no_overflow physical_arch_cap_has_ref)

lemma zombies_finalE:
  "\<lbrakk> \<not> is_final_cap' cap s; is_zombie cap; zombies_final s;
     cte_wp_at ((=) cap) p s \<rbrakk>
     \<Longrightarrow> P"
  apply (frule(1) zombies_finalD)
   apply simp
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma delete_duplicate_iflive:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap. \<not> is_final_cap' cap s) p s
      \<and> if_live_then_nonz_cap s \<and> zombies_final s\<rbrace>
     set_cap cap.NullCap p \<lbrace>\<lambda>rv s. if_live_then_nonz_cap s\<rbrace>"
  apply (clarsimp simp: if_live_then_nonz_cap_def ex_nonz_cap_to_def)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre,
         wp hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_ex_lift
            set_cap_cte_wp_at)
  apply (clarsimp simp: cte_wp_at_def)
  apply (drule spec, drule(1) mp)
  apply clarsimp
  apply (case_tac "(a, b) = p")
   apply (clarsimp simp: zobj_refs_to_obj_refs)
   apply (drule(2) not_final_another[OF _ _ obj_ref_is_gen_obj_ref])
   apply (simp, elim exEI, clarsimp simp: gen_obj_refs_eq)
   apply (erule(2) zombies_finalE)
   apply (simp add: cte_wp_at_def)
  apply (intro exI, erule conjI, clarsimp)
  done


lemma non_unsafe_set_cap:
  "\<lbrace>\<lambda>s. \<not> cte_wp_at ((\<noteq>) cap.NullCap) p' s\<rbrace>
     set_cap cap.NullCap p''
   \<lbrace>\<lambda>rv s. \<not> cte_wp_at ((\<noteq>) cap.NullCap) p' s\<rbrace>"
  by (simp add: cte_wp_at_caps_of_state | wp)+


lemma cte_refs_obj_refs_elem:
  "x \<in> cte_refs cap y \<Longrightarrow> fst x \<in> obj_refs cap
                            \<or> (\<exists>irq. cap = cap.IRQHandlerCap irq)"
  by (cases cap, simp_all split: sum.split, fastforce+)


lemma get_cap_valid_objs_valid_cap:
  "\<lbrakk> fst (get_cap p s) = {(cap, s)}; valid_objs s \<rbrakk>
     \<Longrightarrow> valid_cap cap s"
  apply (rule cte_wp_at_valid_objs_valid_cap[where P="(=) cap", simplified])
   apply (simp add: cte_wp_at_def)
  apply assumption
  done


lemma not_final_not_zombieD:
  "\<lbrakk> \<not> is_final_cap' cap s; fst (get_cap p s) = {(cap, s)};
     zombies_final s \<rbrakk> \<Longrightarrow> \<not> is_zombie cap"
  apply (rule notI)
  apply (erule(2) zombies_finalE)
  apply (simp add: cte_wp_at_def)
  done


lemma appropriate_cte_cap_irqs:
  "(\<forall>cp. appropriate_cte_cap cp cap = appropriate_cte_cap cp cap')
       = ((cap_irqs cap = {}) = (cap_irqs cap' = {}))"
  apply (rule iffI)
   apply (drule_tac x="cap.IRQControlCap" in spec)
   apply (clarsimp simp add: appropriate_cte_cap_def)
  apply (simp add: appropriate_cte_cap_def split: cap.splits)
  done

lemma not_final_another_cte:
  "\<lbrakk> \<not> is_final_cap' cap s; fst (get_cap p s) = {(cap, s)};
       x \<in> cte_refs cap y; valid_objs s; zombies_final s \<rbrakk>
      \<Longrightarrow> \<exists>p' cap'. p' \<noteq> p \<and> fst (get_cap p' s) = {(cap', s)}
                         \<and> (\<forall>y. cte_refs cap' y = cte_refs cap y)
                         \<and> (\<forall>cp. appropriate_cte_cap cp cap'
                                     = appropriate_cte_cap cp cap)
                         \<and> \<not> is_final_cap' cap' s"
  apply (frule cte_refs_obj_refs_elem)
  apply (frule(1) not_final_another')
   subgoal by (auto simp: gen_obj_refs_def cap_irqs_def cap_irq_opt_def)
  apply (elim exEI, clarsimp)
  apply (drule(2) not_final_not_zombieD)+
  apply (drule(1) get_cap_valid_objs_valid_cap)+
  by (auto simp: is_zombie_def valid_cap_def
                        obj_at_def is_obj_defs
                        a_type_def gen_obj_refs_eq
                        option_set_singleton_eq
                        appropriate_cte_cap_irqs
                 dest:  obj_ref_is_arch
                 split: cap.split_asm if_split_asm)


lemma delete_duplicate_ifunsafe:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap. \<not> is_final_cap' cap s) p s
      \<and> if_unsafe_then_cap s \<and> valid_objs s \<and> zombies_final s\<rbrace>
     set_cap cap.NullCap p \<lbrace>\<lambda>rv s. if_unsafe_then_cap s\<rbrace>"
  apply (clarsimp simp: if_unsafe_then_cap_def ex_cte_cap_wp_to_def)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre,
         wp hoare_vcg_all_lift hoare_vcg_disj_lift
            hoare_vcg_ex_lift)
   apply (rule hoare_use_eq [where f=interrupt_irq_node])
    apply (wp set_cap_cte_wp_at)+
  apply simp
  apply (elim conjE allEI)
  apply (clarsimp del: disjCI intro!: disjCI2)
  apply (case_tac "(a, b) = p")
   apply (simp cong: conj_cong add: cte_wp_at_weakenE [OF _ TrueI])
   apply (simp add: cte_wp_at_def | elim exE conjE)+
   apply (frule(4) not_final_another_cte)
   apply (simp, elim exEI, clarsimp)
  apply (fastforce elim!: cte_wp_at_weakenE)
  done


lemma cte_wp_at_conj:
  "cte_wp_at (\<lambda>c. P c \<and> Q c) p s = (cte_wp_at P p s \<and> cte_wp_at Q p s)"
  by (fastforce simp: cte_wp_at_def)


lemma cte_wp_at_disj:
  "cte_wp_at (\<lambda>c. P c \<or> Q c) p s = (cte_wp_at P p s \<or> cte_wp_at Q p s)"
  by (fastforce simp: cte_wp_at_def)


lemma gen_obj_refs_Null[simp]:
  "gen_obj_refs cap.NullCap = {}"
  by (simp add: gen_obj_refs_def)


lemma delete_duplicate_valid_pspace:
  "\<lbrace>\<lambda>s. valid_pspace s \<and> cte_wp_at (\<lambda>cap. \<not> is_final_cap' cap s) p s \<and>
        tcb_cap_valid cap.NullCap p s\<rbrace>
  set_cap cap.NullCap p
  \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (simp add: valid_pspace_def)
  apply (wp set_cap_valid_objs delete_duplicate_iflive delete_duplicate_ifunsafe
            set_cap_zombies, auto elim!: cte_wp_at_weakenE)
  done


lemma set_cap_valid_pspace:
  "\<lbrace>\<lambda>s. cte_wp_at (\<lambda>cap'. (\<forall>p'\<in>zobj_refs cap' - zobj_refs cap. obj_at (Not \<circ> live) p' s)
                        \<and> (\<forall>r\<in>ex_zombie_refs (cap, cap'). \<forall>p'.
                              p \<noteq> p' \<and> cte_wp_at (\<lambda>cap''. r \<in> obj_refs cap'') p' s
                                \<longrightarrow> (cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap))) p s
     \<and> valid_cap cap s \<and> tcb_cap_valid cap p s \<and> valid_pspace s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (simp add: valid_pspace_def)
  apply (wp set_cap_valid_objs set_cap_iflive set_cap_zombies)
  apply (clarsimp elim!: cte_wp_at_weakenE | rule conjI)+
  done


lemma set_object_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and>
     (\<forall>t t'. ko_at (TCB t) p s
             \<and> ko = (TCB t')
             \<and> idle (tcb_state t)
             \<and> tcb_bound_notification t = None
             \<and> valid_arch_idle (tcb_iarch t)
             \<longrightarrow> idle (tcb_state t')
                 \<and> tcb_bound_notification t' = None
                 \<and> valid_arch_idle (tcb_iarch t'))\<rbrace>
     set_object p ko
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wpsimp wp: set_object_wp_strong simp: obj_at_def valid_idle_def pred_tcb_at_def)

lemma set_cap_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
   set_cap cap p
  \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: valid_idle_def set_cap_def set_object_def split_def)
  apply (wp get_object_wp|wpc)+
  apply (auto simp: pred_tcb_at_def obj_at_def is_tcb_def)
  done

lemma set_cap_cte_at_neg[wp]:
  "\<lbrace>\<lambda>s. \<not> cte_at sl s\<rbrace> set_cap cap sl' \<lbrace>\<lambda>rv s. \<not> cte_at sl s\<rbrace>"
  apply (simp add: cte_at_typ)
  apply (wp set_cap_typ_at)
  done

lemma set_cap_cte_wp_at_neg:
  "\<lbrace>\<lambda>s. cte_at sl' s \<and> (if sl = sl' then \<not> P cap else \<not> cte_wp_at P sl s)\<rbrace>
     set_cap cap sl'
   \<lbrace>\<lambda>rv s. \<not> cte_wp_at P sl s\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply wpsimp
  done

lemma set_cap_reply[wp]:
  notes split_paired_Ex[simp del] split_paired_All[simp del]
  shows
  "\<lbrace>valid_reply_caps and cte_at dest and
      (\<lambda>s. \<forall>t rights. cap = cap.ReplyCap t False rights \<longrightarrow>
               st_tcb_at awaiting_reply t s \<and>
               (\<not> has_reply_cap t s \<or>
                cte_wp_at (is_reply_cap_to t) dest s))\<rbrace>
     set_cap cap dest
   \<lbrace>\<lambda>_. valid_reply_caps\<rbrace>"
  apply (simp add: valid_reply_caps_def has_reply_cap_def)
  apply (wpsimp wp: hoare_vcg_imp_lift hoare_vcg_all_lift set_cap_cte_wp_at_neg)
  apply (clarsimp simp: is_reply_cap_to_def)
  apply (rule conjI, fastforce)
  (* Merging the simp and the fastforce fails miserably. I've no clue why *)
  apply (simp add:unique_reply_caps_def)
  apply (fastforce simp: is_cap_simps reply_cap_get_tcb_def cte_wp_at_caps_of_state)
  done


lemma set_cap_reply_masters [wp]:
  "\<lbrace>valid_reply_masters and cte_at ptr and
       (\<lambda>s. \<forall>x. (\<exists> rights. cap = cap.ReplyCap x True rights) \<longrightarrow>
                fst ptr = x \<and> snd ptr = tcb_cnode_index 2) \<rbrace>
   set_cap cap ptr \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  apply (simp add: valid_reply_masters_def cte_wp_at_caps_of_state is_master_reply_cap_to_def)
  apply wp
  apply clarsimp
  done

crunch cap_insert
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_cap_irq_handlers:
 "\<lbrace>\<lambda>s. valid_irq_handlers s
      \<and> cte_wp_at (\<lambda>cap'. \<forall>irq \<in> cap_irqs cap - cap_irqs cap'. irq_issued irq s) ptr s\<rbrace>
    set_cap cap ptr
  \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def Ball_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_imp_lift)
  apply (clarsimp simp: cte_wp_at_caps_of_state elim!: ranE split: if_split_asm)
   apply auto
  done

lemma arch_obj_caps_of:
  "caps_of (ArchObj ko) = {}"
  by (simp add: caps_of_def cap_of_def)

lemma get_cap_wp:
  "\<lbrace>\<lambda>s. \<forall>cap. cte_wp_at ((=) cap) p s \<longrightarrow> Q cap s\<rbrace> get_cap p \<lbrace>Q\<rbrace>"
  apply (clarsimp simp: valid_def cte_wp_at_def)
  apply (frule in_inv_by_hoareD [OF get_cap_inv])
  apply (drule get_cap_det)
  apply simp
  done

lemma cap_irqs_must_be_irqhandler: "irq \<in> cap_irqs cap \<Longrightarrow> cap = IRQHandlerCap irq"
  by (simp add: cap_irqs_def cap_irq_opt_def split: cap.splits)

lemma cap_insert_irq_handlers[wp]:
  shows "\<lbrace>\<lambda>s. valid_irq_handlers s
      \<and> cte_wp_at (\<lambda>cap'. \<forall>irq \<in> cap_irqs cap - cap_irqs cap'. irq_issued irq s) src s\<rbrace>
    cap_insert cap src dest
  \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: cap_insert_def set_untyped_cap_as_full_def
                   update_cdt_def set_cdt_def set_original_def)
  apply (wp | simp split del: if_split)+
      apply (wp set_cap_irq_handlers get_cap_wp)+
      apply (clarsimp simp: is_cap_simps)
      apply (wp set_cap_cte_wp_at get_cap_wp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_irq_handlers_def)
  apply (clarsimp simp: free_index_update_def
                 dest!: cap_irqs_must_be_irqhandler
                 split: cap.splits)
  apply (rename_tac irq irq')
  apply (case_tac "irq = irq'"; simp)
   apply (drule_tac x=cap in bspec; clarsimp simp: ranI)
  done

lemma final_cap_duplicate:
  "\<lbrakk> fst (get_cap p s) = {(cap', s)};
     fst (get_cap p' s) = {(cap'', s)};
     p \<noteq> p'; is_final_cap' cap s; r \<in> gen_obj_refs cap;
     r \<in> gen_obj_refs cap'; r \<in> gen_obj_refs cap'' \<rbrakk>
     \<Longrightarrow> P"
  apply (clarsimp simp add: is_final_cap'_def
                            gen_obj_refs_Int_not)
  apply (erule(1) obvious)
   apply simp
   apply blast
  apply simp
  apply blast
  done

lemma gen_obj_refs_subset:
  "(gen_obj_refs cap \<subseteq> gen_obj_refs cap')
       = (obj_refs cap \<subseteq> obj_refs cap'
             \<and> cap_irqs cap \<subseteq> cap_irqs cap'
             \<and> arch_gen_refs cap \<subseteq> arch_gen_refs cap')"
  apply (simp add: gen_obj_refs_def)
  apply (subgoal_tac "\<forall>x y. Inl x \<noteq> Inr y")
   apply blast
  apply simp
  done

lemma set_cap_same_valid_pspace:
  "\<lbrace>cte_wp_at (\<lambda>c. c = cap) p and valid_pspace\<rbrace> set_cap cap p \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (wp set_cap_valid_pspace)
  apply (clarsimp simp: cte_wp_at_caps_of_state ex_zombie_refs_def2)
  apply (clarsimp simp: caps_of_state_valid_cap valid_pspace_def
                        cte_wp_tcb_cap_valid [OF caps_of_state_cteD])
  done

lemma replace_cap_valid_pspace:
  "\<lbrace>\<lambda>s. valid_pspace s \<and> cte_wp_at (replaceable s p cap) p s
          \<and> s \<turnstile> cap \<and> tcb_cap_valid cap p s\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. valid_pspace\<rbrace>"
  apply (simp only: replaceable_def cte_wp_at_disj
                    conj_disj_distribL conj_disj_distribR)
  apply (rule hoare_strengthen_post)
   apply (rule hoare_vcg_disj_lift)
    apply (rule hoare_pre, rule set_cap_same_valid_pspace)
    apply simp
   apply (rule hoare_vcg_disj_lift)
    apply (cases "cap = cap.NullCap")
     apply simp
     apply (rule hoare_pre, rule delete_duplicate_valid_pspace)
     apply (fastforce simp: cte_wp_at_caps_of_state)
    apply (simp add: cte_wp_at_caps_of_state)
   apply (rule hoare_pre, rule set_cap_valid_pspace)
   apply (clarsimp simp: cte_wp_at_def)
   apply (clarsimp simp: ex_zombie_refs_def2 split: if_split_asm)
     apply (erule(3) final_cap_duplicate,
            erule subsetD, erule obj_ref_is_gen_obj_ref,
            erule subsetD, erule obj_ref_is_gen_obj_ref,
            erule obj_ref_is_gen_obj_ref)+
  apply simp
  done

lemma replace_cap_ifunsafe:
  "\<lbrace>\<lambda>s. cte_wp_at (replaceable s p cap) p s
       \<and> if_unsafe_then_cap s \<and> valid_objs s \<and> zombies_final s
       \<and> (cap \<noteq> cap.NullCap \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s)\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp only: replaceable_def cte_wp_at_disj conj_disj_distribR)
  apply (intro hoare_vcg_disj_lift[where Q=Q and Q'=Q for Q, simplified])
    apply (wp set_cap_ifunsafe)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (cases "cap = cap.NullCap")
    apply simp
    apply (wp delete_duplicate_ifunsafe)
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (simp add: cte_wp_at_caps_of_state)
  apply (wp set_cap_ifunsafe)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma thread_set_mdb:
  assumes c: "\<And>t getF v. (getF, v) \<in> ran tcb_cap_cases
                    \<Longrightarrow> getF (f t) = getF t"
  shows "\<lbrace>valid_mdb\<rbrace> thread_set f p \<lbrace>\<lambda>r. valid_mdb\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply (rule valid_mdb_lift)
    apply wp
    apply clarsimp
    apply (subst caps_of_state_after_update)
     apply (clarsimp simp: c)
    apply simp
   apply (wp | simp)+
  done

lemma set_cap_caps_of_state2:
  "\<lbrace>\<lambda>s. P ((caps_of_state s)(p \<mapsto> cap)) (cdt s) (is_original_cap s)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv s. P (caps_of_state s) (cdt s) (is_original_cap s)\<rbrace>"
  apply (rule_tac Q'="\<lambda>rv s. \<exists>m mr. P (caps_of_state s) m mr
                                  \<and> (cdt s = m) \<and> (is_original_cap s = mr)"
           in hoare_post_imp)
   apply simp
  apply (wp hoare_vcg_ex_lift)
  apply (rule_tac x="cdt s" in exI)
  apply (rule_tac x="is_original_cap s" in exI)
  apply (simp add: fun_upd_def)
  done

lemma gen_obj_refs_empty:
  "(gen_obj_refs cap = {}) =
         (cap_irqs cap = {} \<and> obj_refs cap = {}
            \<and> arch_gen_refs cap = {})"
  by (simp add: gen_obj_refs_def conj_comms)

lemma final_NullCap:
  "is_final_cap' NullCap = \<bottom>"
  by (rule ext, simp add: is_final_cap'_def)

lemma set_cap_only_idle [wp]:
  "set_cap cap p \<lbrace>only_idle\<rbrace>"
  by (wp only_idle_lift set_cap_typ_at)

lemma set_cap_kernel_window[wp]:
  "set_cap cap p \<lbrace>pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def)
  done

lemma set_cap_pspace_respects_device[wp]:
  "set_cap cap p \<lbrace>pspace_respects_device_region\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wp set_object_pspace_respects_device_region get_object_wp | wpc)+
  apply (clarsimp simp: obj_at_def)
  done

lemma set_cap_cap_refs_respects_device_region:
  "\<lbrace>cap_refs_respects_device_region
     and (\<lambda>s. \<exists>ptr. cte_wp_at (\<lambda>c. cap_range cap \<subseteq> cap_range c \<and>((cap_range cap \<noteq> {}) \<longrightarrow> cap_is_device cap = cap_is_device c)) ptr s)\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: cap_refs_respects_device_region_def cap_range_respects_device_region_def)
  apply (rule hoare_pre)
  apply wps
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp hoare_vcg_all_lift)
  apply clarsimp
  apply (rule conjI)
   apply (rule impI)
   apply (drule_tac x = a in spec)
   apply (drule_tac x = b in spec)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply fastforce
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma set_cap_cap_refs_respects_device_region_spec:
  "\<lbrace>cap_refs_respects_device_region
     and (\<lambda>s. cte_wp_at (\<lambda>c. cap_range cap \<subseteq> cap_range c \<and> ((cap_range cap \<noteq> {}) \<longrightarrow> cap_is_device cap = cap_is_device c)) ptr s)\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (wp set_cap_cap_refs_respects_device_region)
  apply fastforce
  done

lemma set_cap_cap_refs_respects_device_region_NullCap:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
     set_cap NullCap p
   \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: cap_refs_respects_device_region_def cap_range_respects_device_region_def)
  apply (rule hoare_pre)
  apply wps
  apply (simp add: cte_wp_at_caps_of_state )
  apply (wp hoare_vcg_all_lift)
  apply (clarsimp simp: cap_range_def)
  apply (drule_tac x = x in spec)
  apply (drule_tac x = xa in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma replaceable_cap_range:
 "replaceable s p cap c \<Longrightarrow> cap_range cap \<subseteq> cap_range c"
 apply (simp add: replaceable_def)
 apply (elim disjE,simp_all)
  apply (clarsimp simp: cap_range_def)
 apply (case_tac cap,simp_all add: is_cap_simps cap_range_def)
 done

lemma replaceable_cap_is_device_cap:
 "\<lbrakk>replaceable s p cap c; cap \<noteq> NullCap\<rbrakk>\<Longrightarrow> cap_is_device cap = cap_is_device c"
 apply (simp add: replaceable_def is_cap_simps is_final_cap'_def)
 apply (elim disjE,simp_all add: is_cap_simps)
 done

lemma set_cap_cap_refs_respects_device_region_replaceable:
  "\<lbrace>cap_refs_respects_device_region and (\<lambda>s. cte_wp_at (replaceable s p cap) p s)\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (case_tac "cap = NullCap")
   apply (wp set_cap_cap_refs_respects_device_region_NullCap | simp)+
  apply (wp set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply clarsimp
  apply (erule cte_wp_at_weakenE)
  apply (simp add: replaceable_cap_is_device_cap replaceable_cap_range)
  done

lemma set_cap_valid_ioc[wp]:
  notes hoare_pre [wp_pre del]
  shows "\<lbrace>valid_ioc and (\<lambda>s. p = cap.NullCap \<longrightarrow> \<not> is_original_cap s pt)\<rbrace>
   set_cap p pt
   \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_cap_def split_def)
  apply (wp set_object_valid_ioc_caps get_object_sp)
   prefer 2
   apply (rule get_object_sp)
  apply (rule hoare_conjI)
   apply (clarsimp simp: valid_def return_def fail_def split_def
                         a_type_simps obj_at_def valid_ioc_def
                  split: Structures_A.kernel_object.splits)
  apply (rule hoare_conjI)
   apply (clarsimp simp: valid_def return_def fail_def split_def
                         a_type_simps obj_at_def valid_ioc_def
                  split: Structures_A.kernel_object.splits)
   apply (auto simp: wf_unique wf_cs_upd)[1]
  apply (clarsimp simp: valid_def return_def fail_def split_def
                        null_filter_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        obj_at_def valid_ioc_def cte_wp_at_cases
                 split: Structures_A.kernel_object.splits)
  apply (intro conjI allI impI)
             apply fastforce
            apply fastforce
           apply (rule ccontr, clarsimp)
           apply (drule spec, frule spec, erule impE, assumption)
           apply (drule_tac x="snd pt" in spec)
           apply (case_tac pt)
           apply (clarsimp simp: tcb_cap_cases_def  split: if_split_asm)
          apply fastforce
         apply (rule ccontr, clarsimp)
         apply (drule spec, frule spec, erule impE, assumption)
         apply (drule_tac x="snd pt" in spec)
         apply (case_tac pt)
         apply (clarsimp simp: tcb_cap_cases_def  split: if_split_asm)
        apply fastforce
       apply (rule ccontr, clarsimp)
       apply (drule spec, frule spec, erule impE, assumption)
       apply (drule_tac x="snd pt" in spec)
       apply (case_tac pt)
       apply (clarsimp simp: tcb_cap_cases_def  split: if_split_asm)
      apply fastforce
     apply (rule ccontr, clarsimp)
     apply (drule spec, frule spec, erule impE, assumption)
     apply (drule_tac x="snd pt" in spec)
     apply (case_tac pt)
     apply (clarsimp simp: tcb_cap_cases_def  split: if_split_asm)
    apply fastforce
   apply (rule ccontr, clarsimp)
   apply (drule spec, frule spec, erule impE, assumption)
   apply (drule_tac x="snd pt" in spec)
   apply (case_tac pt)
   apply (clarsimp simp: tcb_cap_cases_def  split: if_split_asm)
  apply fastforce
  done

lemma descendants_inc_minor:
  "\<lbrakk>descendants_inc m cs; mdb_cte_at (\<lambda>p. \<exists>c. cs p = Some c \<and> cap.NullCap \<noteq> c) m;
   \<forall>x\<in> dom cs. cap_class (the (cs' x)) = cap_class (the (cs x)) \<and> cap_range (the (cs' x)) = cap_range (the (cs x))\<rbrakk>
  \<Longrightarrow> descendants_inc m cs'"
  apply (simp add: descendants_inc_def del: split_paired_All)
  apply (intro impI allI)
  apply (drule spec)+
  apply (erule(1) impE)
  apply (clarsimp simp: descendants_of_def)
  apply (frule tranclD)
  apply (drule tranclD2)
  apply (simp add: cdt_parent_rel_def is_cdt_parent_def)
  apply (elim conjE exE)
  apply (drule(1) mdb_cte_atD)+
  apply (elim conjE exE)
  apply (drule_tac m1 = cs in bspec[OF _ domI,rotated],assumption)+
  apply simp
  done


crunch set_cdt
  for cte_wp_at: "cte_wp_at P p"


lemma set_cdt_cdt_ct_ms_rvk[wp]:
  "\<lbrace>\<lambda>s. P m\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  "\<lbrace>\<lambda>s. Q (is_original_cap s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. Q (is_original_cap s)\<rbrace>"
  "\<lbrace>\<lambda>s. R (cur_thread s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. R (cur_thread s)\<rbrace>"
  "\<lbrace>\<lambda>s. S (machine_state s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. S (machine_state s)\<rbrace>"
  "\<lbrace>\<lambda>s. T (idle_thread s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. T (idle_thread s)\<rbrace>"
  "\<lbrace>\<lambda>s. U (arch_state s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. U (arch_state s)\<rbrace>"
  by (simp add: set_cdt_def | wp)+


lemma set_original_wp[wp]:
  "\<lbrace>\<lambda>s. Q () (s \<lparr> is_original_cap := ((is_original_cap s) (p := v))\<rparr>)\<rbrace>
     set_original p v
   \<lbrace>Q\<rbrace>"
  by (simp add: set_original_def, wp)


lemma set_cdt_typ_at:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (rule set_cdt_inv)
  apply (simp add: obj_at_def)
  done


lemma set_untyped_cap_as_full_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>
   set_untyped_cap_as_full src_cap a b
   \<lbrace>\<lambda>ya s. P (typ_at T p s)\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def)
  apply (wp set_cap_typ_at hoare_drop_imps | simp split del: if_split)+
  done


lemma cap_insert_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> cap_insert a b c \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: cap_insert_def update_cdt_def)
  apply (wp set_cap_typ_at set_cdt_typ_at hoare_drop_imps
         |simp split del: if_split)+
  done

crunch cap_insert
  for cur[wp]: cur_tcb (wp: hoare_drop_imps)


lemma update_cdt_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> update_cdt f \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (clarsimp elim!: ifunsafe_pspaceI)
  done


lemma ex_cap_revokable[simp]:
  "ex_nonz_cap_to p (s\<lparr>is_original_cap := m\<rparr>) = ex_nonz_cap_to p s"
  by (simp add: ex_nonz_cap_to_def)


lemma zombies_final_revokable[simp]:
  "zombies_final (is_original_cap_update f s) = zombies_final s"
  by (fastforce elim!: zombies_final_pspaceI)


lemma update_cdt_ex_cap[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> update_cdt f \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (simp add: ex_nonz_cap_to_def)
  done


lemma update_cdt_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> update_cdt f \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (simp add: if_live_then_nonz_cap_def ex_nonz_cap_to_def)
  done


lemma update_cdt_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> update_cdt m \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (clarsimp elim!: zombies_final_pspaceI)
  done


lemma cap_insert_zombies:
  "\<lbrace>zombies_final and
    (\<lambda>s. (\<forall>r\<in>obj_refs cap. \<forall>p'.
           cte_wp_at (\<lambda>c. r \<in> obj_refs c) p' s
             \<longrightarrow> cte_wp_at (Not \<circ> is_zombie) p' s \<and> \<not> is_zombie cap))\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: cap_insert_def set_untyped_cap_as_full_def)
  apply (wp| simp split del: if_split)+
      apply (wp new_cap_zombies get_cap_wp set_cap_cte_wp_at)+
      apply (rule hoare_vcg_conj_lift)
       apply (clarsimp simp: is_cap_simps)
       apply (wp set_cap_zombies get_cap_wp set_cap_cte_wp_at hoare_allI)+
  apply (clarsimp simp: is_cap_simps free_index_update_def cte_wp_at_caps_of_state | rule conjI)+
  done


definition masked_as_full :: "cap \<Rightarrow> cap \<Rightarrow> cap" where
  "masked_as_full src_cap new_cap \<equiv>
   if is_untyped_cap src_cap \<and> is_untyped_cap new_cap \<and>
      obj_ref_of src_cap = obj_ref_of new_cap \<and>
      cap_bits_untyped src_cap = cap_bits_untyped new_cap
   then (max_free_index_update src_cap) else src_cap"


lemma set_untyped_cap_as_full_cte_wp_at:
  "\<lbrace>\<lambda>s. (dest \<noteq> src \<and> cte_wp_at P dest s \<or>
         dest = src \<and> cte_wp_at (\<lambda>a. P (masked_as_full a cap)) src s) \<and>
        cte_wp_at ((=) src_cap) src s\<rbrace>
   set_untyped_cap_as_full src_cap cap src
   \<lbrace>\<lambda>ya s. (cte_wp_at P dest s)\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def)
  apply (intro impI conjI allI)
    apply (wp set_cap_cte_wp_at)
      apply (clarsimp simp: free_index_update_def cte_wp_at_caps_of_state is_cap_simps
                            max_free_index_def masked_as_full_def)
    apply (intro conjI,elim disjE)
      apply clarsimp+
  apply wp
  apply (auto simp: is_cap_simps cte_wp_at_caps_of_state masked_as_full_def)
  done

lemma valid_cap_free_index_update[simp]:
  "valid_cap cap s \<Longrightarrow> valid_cap (max_free_index_update cap) s"
  apply (case_tac cap)
  apply (simp_all add: free_index_update_def split: cap.splits )
  apply (clarsimp simp: valid_cap_def cap_aligned_def valid_untyped_def max_free_index_def)
  done


lemma cap_insert_ex_cap:
  "\<lbrace>ex_nonz_cap_to p\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wp|simp split del: if_split)+
        apply (wp set_cap_cap_to get_cap_wp set_cap_cte_wp_at set_untyped_cap_as_full_cte_wp_at)+
     apply (clarsimp simp: set_untyped_cap_as_full_def split del: if_split)
     apply (wp set_cap_cap_to get_cap_wp)+
  apply (clarsimp elim!: cte_wp_at_weakenE simp: is_cap_simps cte_wp_at_caps_of_state)
  apply (simp add: masked_as_full_def)
  done


lemma cap_insert_iflive:
  "\<lbrace>if_live_then_nonz_cap\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: cap_insert_def set_untyped_cap_as_full_def)
  apply (wp get_cap_wp set_cap_cte_wp_at | simp split del: if_split)+
      apply (rule new_cap_iflive)
     apply (wp set_cap_iflive set_cap_cte_wp_at get_cap_wp)+
  apply (clarsimp simp: is_cap_simps cte_wp_at_caps_of_state)
  done


lemma untyped_cap_update_ex_cte_cap_wp_to:
  "\<lbrakk>if_unsafe_then_cap s; caps_of_state s src = Some src_cap;
    is_untyped_cap src_cap; is_untyped_cap cap\<rbrakk>
   \<Longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) src s"
  apply (case_tac src)
  apply (simp add: if_unsafe_then_cap_def)
  apply (drule spec)+
  apply (drule(1) mp)+
  apply (clarsimp simp: is_cap_simps)
  apply (erule ex_cte_cap_wp_to_weakenE)
  apply (clarsimp simp: appropriate_cte_cap_def)
  done

lemma ex_cte_cap_wo_to_more_update[simp]:
  "ex_cte_cap_wp_to P src (trans_state f s) = ex_cte_cap_wp_to P src s"
  by (simp add: ex_cte_cap_wp_to_def)

lemma if_unsafe_then_cap_more_update[iff]:
  "if_unsafe_then_cap (trans_state f s) = if_unsafe_then_cap s"
  by (simp add: if_unsafe_then_cap_def)

lemma cap_insert_ifunsafe:
  "\<lbrace>if_unsafe_then_cap and
    ex_cte_cap_wp_to (appropriate_cte_cap cap) dest\<rbrace>
     cap_insert cap src dest
   \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: cap_insert_def)
  apply (wp get_cap_wp | simp split del: if_split)+
      apply (rule new_cap_ifunsafe)
     apply (simp add: set_untyped_cap_as_full_def split del: if_split)
     apply (wp set_cap_cte_wp_at set_cap_ifunsafe set_cap_cte_cap_wp_to get_cap_wp)+
  apply (clarsimp simp: is_cap_simps cte_wp_at_caps_of_state)
  apply (rule untyped_cap_update_ex_cte_cap_wp_to)
     apply (simp add: free_index_update_def)+
  done


lemma cap_insert_tcb:
 "\<lbrace>tcb_at t\<rbrace>
  cap_insert cap src dest
  \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: cap_insert_typ_at [where P="\<lambda>x. x"] tcb_at_typ)


lemma set_cdt_caps_of_state:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_cdt m \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: set_cdt_def)
  apply wp
  apply clarsimp
  done


crunch set_cdt
  for cos_ioc: "\<lambda>s. P (caps_of_state s) (is_original_cap s)"


crunch set_cdt
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"


lemmas set_cdt_caps_irq_node[wp]
  = hoare_use_eq[where f=interrupt_irq_node, OF set_cdt_irq_node, OF set_cdt_caps_of_state]

lemmas set_cap_caps_irq_node[wp]
  = hoare_use_eq[where f=interrupt_irq_node, OF set_cap_irq_node, OF set_cap_caps_of_state]


lemma cap_insert_cap_wp_to[wp]:
  "\<lbrace> K_bind(\<forall>x. P x = P (x\<lparr>free_index:=y\<rparr>)) and ex_cte_cap_wp_to P p\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  apply (simp add: cap_insert_def ex_cte_cap_wp_to_def set_untyped_cap_as_full_def
                   cte_wp_at_caps_of_state update_cdt_def)
  apply (wp get_cap_wp | simp split del: if_split)+
  apply (rule allI)
  apply (clarsimp, rule conjI)
    apply (clarsimp simp: is_cap_simps cte_wp_at_caps_of_state)
    apply (rule_tac x = a in exI)
    apply (rule_tac x = b in exI)
    apply (clarsimp simp: cte_wp_at_caps_of_state | rule conjI)+
  apply (rule_tac x = a in exI)
  apply (rule_tac x = b in exI)
  apply clarsimp
  done


lemma ex_cte_cap_to_cnode_always_appropriate_strg:
  "ex_cte_cap_wp_to is_cnode_cap p s
    \<longrightarrow> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s"
  by (clarsimp elim!: ex_cte_cap_wp_to_weakenE
                simp: is_cap_simps appropriate_cte_cap_def
               split: cap.splits)


lemma update_cdt_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> update_cdt f \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (clarsimp elim!: state_refs_of_pspaceI)
  done


lemma update_cdt_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace> update_cdt f \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: update_cdt_def set_cdt_def)
  apply wp
  apply (clarsimp elim!: state_hyp_refs_of_pspaceI)
  done


lemma state_refs_of_revokable[simp]:
  "state_refs_of (s \<lparr> is_original_cap := m \<rparr>) = state_refs_of s"
  by (simp add: state_refs_of_def)

crunch cap_insert
  for state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  (wp: crunch_wps)

crunch set_untyped_cap_as_full
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps)

crunch cap_insert
  for state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  (wp: crunch_wps)

crunch cap_insert
  for aligned[wp]: pspace_aligned
  (wp: hoare_drop_imps)


crunch cap_insert
  for "distinct"[wp]: pspace_distinct
  (wp: hoare_drop_imps)


lemma is_arch_cap_max_free_index[simp]:
  "is_arch_cap (x\<lparr>free_index:=y\<rparr>) = is_arch_cap x"
  by (auto simp: is_cap_simps free_index_update_def split: cap.splits)


lemma tcb_cap_valid_update_free_index[simp]:
  "tcb_cap_valid (cap\<lparr>free_index:=a\<rparr>) slot s = tcb_cap_valid cap slot s"
  apply (rule iffI)
  apply (clarsimp simp: tcb_cap_valid_def)
  apply (intro conjI impI allI)
    apply (clarsimp simp: tcb_at_def pred_tcb_at_def is_tcb_def obj_at_def
                   dest!: get_tcb_SomeD)
    apply (clarsimp simp: tcb_cap_cases_def free_index_update_def is_cap_simps
                          is_nondevice_page_cap_simps
                   dest!: is_valid_vtable_root_is_arch_cap
                   split: if_splits cap.split_asm Structures_A.thread_state.split_asm)
   apply (clarsimp simp: pred_tcb_at_def obj_at_def is_cap_simps free_index_update_def
                         is_nondevice_page_cap_simps
                  split: cap.split_asm)
  apply (clarsimp simp: tcb_cap_valid_def)
  apply (intro conjI impI allI)
   apply (clarsimp simp: tcb_at_def pred_tcb_at_def is_tcb_def obj_at_def
                  dest!: get_tcb_SomeD)
   apply (clarsimp simp: tcb_cap_cases_def free_index_update_def is_cap_simps
                         is_nondevice_page_cap_simps
                  dest!: is_valid_vtable_root_is_arch_cap
                  split: if_splits cap.split_asm Structures_A.thread_state.split_asm)
  apply (clarsimp simp: pred_tcb_at_def obj_at_def is_cap_simps free_index_update_def
                        valid_ipc_buffer_cap_def
                 split: cap.splits)
  done


lemma set_untyped_cap_full_valid_objs:
  "\<lbrace>valid_objs and cte_wp_at ((=) cap) slot\<rbrace>
   set_untyped_cap_as_full cap cap_new slot
   \<lbrace>\<lambda>r. valid_objs\<rbrace>"
  apply (simp add: set_untyped_cap_as_full_def split del: if_split)
  apply (wp set_cap_valid_objs)
  apply (clarsimp simp: tcb_cap_valid_caps_of_stateD cte_wp_at_caps_of_state caps_of_state_valid_cap)
  done


lemma set_untyped_cap_as_full_valid_cap:
  "\<lbrace>valid_cap cap\<rbrace>
   set_untyped_cap_as_full src_cap cap src
   \<lbrace>\<lambda>rv. valid_cap cap\<rbrace>"
  by (clarsimp simp:set_untyped_cap_as_full_def) (wp set_cap_valid_cap)


lemma set_untyped_cap_as_full_tcb_cap_valid:
  "\<lbrace>tcb_cap_valid cap dest\<rbrace>
   set_untyped_cap_as_full src_cap cap src
   \<lbrace>\<lambda>rv s. tcb_cap_valid cap dest s\<rbrace>"
  apply (clarsimp simp: set_untyped_cap_as_full_def valid_def tcb_cap_valid_def)
  apply (intro conjI impI allI ballI)
    apply (case_tac "tcb_at (fst dest) s")
      apply clarsimp
      apply (intro conjI impI allI)
      apply (drule use_valid[OF _ set_cap_pred_tcb],simp+)
        apply (clarsimp simp: valid_ipc_buffer_cap_def is_cap_simps)
        apply (fastforce simp: tcb_at_def obj_at_def is_tcb)
    apply (clarsimp simp: tcb_at_typ)
    apply (drule use_valid[OF _ set_cap_typ_at])
      apply (assumption)
      apply simp
  apply (clarsimp simp: return_def)
  done


lemma cap_insert_objs [wp]:
 "\<lbrace>valid_objs and valid_cap cap and tcb_cap_valid cap dest\<rbrace>
  cap_insert cap src dest
  \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (simp add: cap_insert_def set_cdt_def update_cdt_def)
  apply (wp set_cap_valid_objs set_cap_valid_cap set_untyped_cap_as_full_valid_cap
    set_untyped_cap_full_valid_objs get_cap_wp set_untyped_cap_as_full_tcb_cap_valid
    | simp split del: if_split)+
  done

crunch cap_insert, set_cdt
  for pred_tcb_at[wp]: "pred_tcb_at proj P t"
  (wp: hoare_drop_imps)


crunch cap_insert
  for ct[wp]: "\<lambda>s. P (cur_thread s)"
  (wp: crunch_wps simp: crunch_simps)


lemma cap_insert_valid_cap[wp]:
  "\<lbrace>valid_cap c\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma cap_rights_update_idem [simp]:
  "cap_rights_update R (cap_rights_update R' cap) = cap_rights_update R cap"
  by (force simp: cap_rights_update_def split: cap.splits bool.splits)


lemma cap_master_cap_rights [simp]:
  "cap_master_cap (cap_rights_update R cap) = cap_master_cap cap"
  by (force simp: cap_master_cap_def cap_rights_update_def split: cap.splits bool.splits)


lemma cap_insert_obj_at_other:
  "\<lbrace>\<lambda>s. P' (obj_at P p s) \<and> p \<noteq> fst src \<and> p \<noteq> fst dest\<rbrace> cap_insert cap src dest \<lbrace>\<lambda>_ s. P' (obj_at P p s)\<rbrace>"
  apply (simp add: cap_insert_def update_cdt_def set_cdt_def set_untyped_cap_as_full_def)
  apply (rule hoare_pre)
   apply (wp set_cap_obj_at_other get_cap_wp|simp split del: if_split)+
  done

lemma only_idle_tcb_update:
  "\<lbrakk>only_idle s; ko_at (TCB t) p s; tcb_state t = tcb_state t' \<or> \<not>idle (tcb_state t') \<rbrakk>
    \<Longrightarrow> only_idle (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB t')\<rparr>)"
  by (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def)

lemma as_user_only_idle :
  "\<lbrace>only_idle\<rbrace> as_user t m \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: as_user_def set_object_def get_object_def split_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply)
  apply (erule only_idle_tcb_update)
   apply (drule get_tcb_SomeD)
   apply (fastforce simp: obj_at_def)
  by (simp add: get_tcb_rev)

lemma cap_rights_update_id [intro!, simp]:
  "valid_cap c s \<Longrightarrow> cap_rights_update (cap_rights c) c = c"
  unfolding cap_rights_update_def
  by (cases c; fastforce simp: valid_cap_def split: bool.splits)


end
