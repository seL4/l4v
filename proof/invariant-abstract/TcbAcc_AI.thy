(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory TcbAcc_AI
imports ArchCSpace_AI
begin

arch_requalify_facts
  valid_arch_arch_tcb_context_set
  as_user_inv
  getRegister_inv
  user_getreg_inv
  set_cap_valid_arch_caps_simple
  set_cap_kernel_window_simple
  state_hyp_refs_of_tcb_sched_context_update
  state_hyp_refs_of_tcb_yield_to_update
  global_refs_kheap

declare user_getreg_inv[wp]
declare valid_arch_arch_tcb_context_set[simp]

lemma gets_the_thread_read:
  "gets_the (thread_read f t) = thread_get f t"
  by (clarsimp simp: thread_read_def thread_get_def oliftM_def)

lemma thread_read_SomeD:
  "thread_read f tp s = Some p \<Longrightarrow> \<exists>tcb. kheap s tp = Some (TCB tcb) \<and> f tcb = p"
  by (clarsimp simp: thread_read_def oliftM_def dest!: get_tcb_SomeD)

lemma read_tcb_obj_ref_SomeD:
  "read_tcb_obj_ref f tp s = Some p \<Longrightarrow> \<exists>tcb. kheap s tp = Some (TCB tcb) \<and> f tcb = p"
  by (clarsimp simp: read_tcb_obj_ref_def dest!: thread_read_SomeD)

lemma read_tcb_obj_ref_NoneD:
  "read_tcb_obj_ref f tp s = None
   \<Longrightarrow> \<not> (\<exists>tcb. kheap s tp = Some (TCB tcb))"
  by (clarsimp simp: read_tcb_obj_ref_def oliftM_def obind_def thread_read_def get_tcb_def
              split: option.split_asm)

declare global_refs_kheap[simp]

locale TcbAcc_AI_storeWord_invs =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes storeWord_invs[wp]:
    "\<And> p w.
      \<lbrace>in_user_frame p and invs :: 'state_ext state \<Rightarrow> bool\<rbrace>
        do_machine_op (storeWord p w)
      \<lbrace>\<lambda>rv. invs\<rbrace>"

(* FIXME: move to Invariatns? *)
lemma symreftype_inverse':
  "symreftype ref = ref' \<Longrightarrow> ref = symreftype ref'"
  by (cases ref) simp_all

lemmas gts_inv[wp] = get_thread_state_inv

lemmas gbn_inv[wp] = get_tcb_obj_ref_inv

lemma gts_sp:
  "\<lbrace>P\<rbrace> get_thread_state t \<lbrace>\<lambda>st. st_tcb_at (\<lambda>x. st = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gts_st_tcb)
   apply (rule gts_inv)
  apply simp
  done

lemma gbn_sp:
  "\<lbrace>P\<rbrace> get_tcb_obj_ref tcb_bound_notification t \<lbrace>\<lambda>ntfn. bound_tcb_at (\<lambda>x. ntfn = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gbn_bound_tcb)
   apply (rule gbn_inv)
  apply simp
  done

lemma gsc_sp:
  "\<lbrace>P\<rbrace> get_tcb_obj_ref tcb_sched_context t \<lbrace>\<lambda>sc. bound_sc_tcb_at (\<lambda>x. sc = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gbsc_bound_tcb)
   apply (rule gbn_inv)
  apply simp
  done

lemma gyt_sp:
  "\<lbrace>P\<rbrace> get_tcb_obj_ref tcb_yield_to t \<lbrace>\<lambda>sc. bound_yt_tcb_at (\<lambda>x. sc = x) t and P\<rbrace>"
  apply (simp add: pred_conj_def)
  apply (rule hoare_weaken_pre)
   apply (rule hoare_vcg_conj_lift)
    apply (rule gbyt_bound_tcb)
   apply (rule gbn_inv)
  apply simp
  done

lemma red_univ_get_wp[simp]:
  "(\<forall>(rv, s') \<in> fst (f s). s = s' \<longrightarrow> (rv, s') \<in> fst (f s'))"
  by clarsimp


lemma thread_get_inv [wp]: "\<lbrace>P\<rbrace> thread_get f t \<lbrace>\<lambda>rv. P\<rbrace>"
  by (simp add: thread_get_def | wp)+

locale TcbAcc_AI_arch_tcb_context_set_eq =
  assumes arch_tcb_context_set_eq[simp]:
    "\<And> t. arch_tcb_context_set (arch_tcb_context_get t) t = t"

lemma (in TcbAcc_AI_arch_tcb_context_set_eq) thread_get_as_user:
  "thread_get (arch_tcb_context_get o tcb_arch) t = as_user t get"
  apply (simp add: thread_get_def as_user_def)
  apply (rule bind_cong [OF refl])
  apply (clarsimp simp: gets_the_member set_object_def get_object_def in_monad bind_assoc
                        gets_def put_def bind_def get_def return_def select_f_def
                        gets_the_def assert_opt_def get_tcb_def
                 split: option.split_asm kernel_object.split_asm)
  apply (rename_tac v s; subgoal_tac "(kheap s)(t \<mapsto> TCB v) = kheap s", simp)
  apply fastforce
  done

lemma thread_set_as_user:
  "thread_set (\<lambda>tcb. tcb \<lparr> tcb_arch := arch_tcb_context_set (f $ arch_tcb_context_get (tcb_arch tcb)) (tcb_arch tcb) \<rparr>) t
    = as_user t (modify f)"
proof -
  have P: "\<And>f. det (modify f)"
    by (simp add: modify_def)
  thus ?thesis
    apply (simp add: as_user_def P thread_set_def)
    apply (clarsimp simp add: select_f_def simpler_modify_def bind_def image_def)
    done
qed

lemma ball_tcb_cap_casesI:
  "\<lbrakk> P (tcb_ctable, tcb_ctable_update, (\<lambda>_ _. \<top>));
     P (tcb_vtable, tcb_vtable_update, (\<lambda>_ _. is_valid_vtable_root or ((=) cap.NullCap)));
     P (tcb_ipcframe, tcb_ipcframe_update, (\<lambda>_ _. is_nondevice_page_cap or ((=) cap.NullCap)));
     P (tcb_fault_handler, tcb_fault_handler_update, \<lambda>_ _. valid_fault_handler);
     P (tcb_timeout_handler, tcb_timeout_handler_update, \<lambda>_ _. valid_fault_handler) \<rbrakk>
    \<Longrightarrow> \<forall>x \<in> ran tcb_cap_cases. P x"
  by (simp add: tcb_cap_cases_def)

lemma valid_fault_handler_Null[simp, intro!]:
  "valid_fault_handler NullCap"
  by (simp add: valid_fault_handler_def)

lemma thread_set_typ_at[wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> thread_set f p' \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def a_type_def)
  done


lemma thread_set_tcb[wp]:
  "\<lbrace>tcb_at t\<rbrace> thread_set t' f \<lbrace>\<lambda>rv. tcb_at t\<rbrace>"
  by (simp add: thread_set_typ_at [where P="\<lambda>s. s"] tcb_at_typ)

lemma thread_set_no_change_tcb_pred_gen:
  assumes "\<And>tcb. proj (tcb_to_itcb (f tcb)) = proj (tcb_to_itcb tcb)"
  shows "thread_set f t' \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (wpsimp simp: thread_set_def pred_tcb_at_def obj_at_def wp: set_object_wp)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: assms)
  done

lemmas thread_set_no_change_tcb_pred = thread_set_no_change_tcb_pred_gen[where Q="\<lambda>x. x"]

lemmas thread_set_no_change_tcb_state=thread_set_no_change_tcb_pred[where proj="itcb_state",simplified]

lemmas thread_set_no_change_tcb_bound_notification = thread_set_no_change_tcb_pred[where proj="itcb_bound_notification", simplified]

lemmas thread_set_no_change_tcb_sched_context =
   thread_set_no_change_tcb_pred[where proj="itcb_sched_context", simplified]

lemmas thread_set_no_change_tcb_yield_to =
   thread_set_no_change_tcb_pred[where proj="itcb_yield_to", simplified]

lemmas thread_set_no_change_tcb_pred_converse = thread_set_no_change_tcb_pred_gen[where Q="\<lambda>x. \<not>x"]

lemmas thread_set_no_change_tcb_state_converse=
  thread_set_no_change_tcb_pred_converse[where proj="itcb_state", simplified]

lemmas thread_set_no_change_tcb_bound_notification_converse =
  thread_set_no_change_tcb_pred_converse[where proj="itcb_bound_notification", simplified]

lemmas thread_set_no_change_tcb_sched_context_converse =
  thread_set_no_change_tcb_pred_converse[where proj="itcb_sched_context", simplified]

lemmas thread_set_no_change_tcb_yield_to_converse =
  thread_set_no_change_tcb_pred_converse[where proj="itcb_yield_to", simplified]

lemma thread_set_pred_tcb_at_sets_true:
  assumes "\<And>tcb. P (proj (tcb_to_itcb (f tcb)))"
  shows "\<lbrace>\<lambda>s. t \<noteq> t' \<longrightarrow> pred_tcb_at proj P t s\<rbrace>
         thread_set f t'
         \<lbrace>\<lambda>rv s. (pred_tcb_at proj P t s)\<rbrace>"
  apply (wpsimp simp: thread_set_def pred_tcb_at_def obj_at_def wp: set_object_wp)
  by (auto simp: assms)

lemma pspace_valid_objsE:
  assumes p: "kheap s p = Some ko"
  assumes v: "valid_objs s"
  assumes Q: "\<lbrakk>kheap s p = Some ko; valid_obj p ko s\<rbrakk> \<Longrightarrow> Q"
  shows "Q"
proof -
  from p have "ko_at ko p s" by (simp add: obj_at_def)
  with v show Q by (auto elim: obj_at_valid_objsE simp: Q)
qed


schematic_goal tcb_ipcframe_in_cases:
  "(tcb_ipcframe, ?x) \<in> ran tcb_cap_cases"
  by (fastforce simp add: ran_tcb_cap_cases)


lemmas valid_ipc_buffer_cap_simps= valid_ipc_buffer_cap_def[split_simps cap.split]

locale TcbAcc_AI_valid_ipc_buffer_cap_0 =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes valid_ipc_buffer_cap_0[simp]:
    "\<And>cap buf. valid_ipc_buffer_cap cap buf \<Longrightarrow> valid_ipc_buffer_cap cap 0"
  assumes thread_set_hyp_refs_trivial:
    "(\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb) \<Longrightarrow>
        (\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb) \<Longrightarrow>
         \<lbrace>\<lambda>(s::'state_ext state). P (state_hyp_refs_of s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  assumes thread_set_valid_arch_state:
    "(\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases. getF (f tcb) = getF tcb) \<Longrightarrow>
       \<lbrace>\<lambda>s::'state_ext state. valid_arch_state s\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. valid_arch_state s\<rbrace>"

context TcbAcc_AI_valid_ipc_buffer_cap_0 begin

lemma thread_set_valid_objs_triv:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  assumes z: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  assumes w: "\<And>tcb. tcb_ipc_buffer (f tcb) = tcb_ipc_buffer tcb
                        \<or> (tcb_ipc_buffer (f tcb) = 0)"
  assumes a: "\<And>tcb. tcb_fault (f tcb) = tcb_fault tcb"
  assumes b: "\<And>tcb. tcb_bound_notification (f tcb) \<noteq> tcb_bound_notification tcb
                       \<longrightarrow> tcb_bound_notification (f tcb) = None"
  assumes b': "\<And>tcb. tcb_sched_context (f tcb) \<noteq> tcb_sched_context tcb
                       \<longrightarrow> tcb_sched_context (f tcb) = None"
  assumes b'': "\<And>tcb. tcb_yield_to(f tcb) \<noteq> tcb_yield_to tcb
                       \<longrightarrow> tcb_yield_to (f tcb) = None"
  assumes c: "\<And>tcb s::'z::state_ext state.
                     valid_arch_tcb (tcb_arch (f tcb)) s = valid_arch_tcb (tcb_arch tcb) s"
  shows "\<lbrace>valid_objs\<rbrace> thread_set f t \<lbrace>\<lambda>rv. valid_objs :: 'z::state_ext state \<Rightarrow> bool\<rbrace>"
  using bspec [OF x, OF tcb_ipcframe_in_cases]
  apply (simp add: thread_set_def)
  apply wp
  apply clarsimp
  apply (drule get_tcb_SomeD)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp add: valid_obj_def valid_tcb_def valid_bound_obj_def z
                            split_paired_Ball obj_at_def c
                            a_type_def bspec_split[OF x])
  apply (rule conjI)
   apply (elim allEI)
   apply auto[1]
  apply (rule conjI)
   apply (cut_tac tcb = y in w)
   apply (auto simp: valid_ipc_buffer_cap_simps)[1]
  apply (cut_tac tcb=y in a)
  apply (cut_tac tcb=y in b)
  apply (cut_tac tcb=y in b')
  apply (cut_tac tcb=y in b'')
  by auto[1]

end


lemma thread_set_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> thread_set f t \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_aligned)
  apply (clarsimp simp: a_type_def)
  done


lemma thread_set_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> thread_set f t \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_distinct)
  apply clarsimp
  done


lemma thread_set_cur_tcb[wp]:
  "thread_set f t \<lbrace>cur_tcb\<rbrace>"
  apply (clarsimp simp: thread_set_def set_object_def get_object_def in_monad
                        valid_def cur_tcb_def)
  apply (clarsimp dest!: get_tcb_SomeD simp: obj_at_def is_tcb)
  done

lemma thread_set_cur_sc_tcb[wp]:
  "thread_set f t \<lbrace> cur_sc_tcb\<rbrace>"
  by (wpsimp simp: thread_set_def set_object_def cur_sc_tcb_def sc_tcb_sc_at_def
                   obj_at_def get_tcb_def get_object_def)

lemma thread_set_iflive_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  assumes z: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  assumes y: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes w: "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes t: "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  assumes a: "\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb"
  shows      "\<lbrace>if_live_then_nonz_cap\<rbrace> thread_set f t \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_iflive)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def get_tcb_def
                        split_paired_Ball
                        bspec_split [OF x])
  apply (subgoal_tac "live (TCB y)")
   apply (fastforce elim: if_live_then_nonz_capD2)
  apply (clarsimp simp: live_def hyp_live_tcb_def z y w t a)
  done

lemma thread_set_obj_at_impossible:
  "\<lbrakk> \<And>tcb. \<not> P' (TCB tcb) \<rbrakk> \<Longrightarrow> thread_set f t \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def)
  done

lemma thread_set_wp:
  "\<lbrace> \<lambda>s. \<forall>tcb. get_tcb t s = Some tcb \<longrightarrow> Q (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (f tcb))\<rparr>) \<rbrace>
    thread_set f t
   \<lbrace> \<lambda>_. Q \<rbrace>"
  by (wpsimp simp: thread_set_def wp: set_object_wp)

lemma tcb_agnostic_predE:
  "P (P' (TCB tcb)) \<Longrightarrow> tcb_agnostic_pred P' \<Longrightarrow> P (P' (TCB tcb'))"
  by (fastforce simp: tcb_agnostic_pred_def)

global_interpretation thread_set: tcb_op "thread_set f t_ptr"
  by unfold_locales (wpsimp wp: thread_set_wp simp: obj_at_def get_tcb_ko_at tcb_agnostic_predE)

lemma sts_obj_at_impossible':
  "(\<And>tcb. \<not> P' (TCB tcb)) \<Longrightarrow> set_thread_state t st \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  unfolding set_thread_state_def
  by (wpsimp wp: thread_set_obj_at_impossible get_object_wp
           simp: set_object_def obj_at_def get_tcb_def
          split: kernel_object.splits option.splits)

lemmas sts_obj_at_impossible = sts_obj_at_impossible'[where P= id, simplified]

global_interpretation set_thread_state: non_reply_op "set_thread_state t st"
  by unfold_locales (fastforce simp: reply_at_ppred_def intro: sts_obj_at_impossible')

lemma (in non_reply_op) non_reply_ko_at_Reply[wp]:
  "f \<lbrace> \<lambda>s. P (ko_at (Reply reply_obj) reply_ptr s) \<rbrace>"
  by (wpsimp simp: simple_obj_at_ko_at[symmetric])

lemma thread_set_valid_replies_trivial:
  assumes st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  shows "thread_set f t \<lbrace> valid_replies_pred P \<rbrace>"
  supply get_tcb_SomeD[dest!]
  by (wpsimp wp: valid_replies_lift thread_set_wp
           simp: sk_obj_at_pred_def obj_at_def pred_tcb_at_def st)

lemma thread_set_fault_tcbs_valid_states_trivial:
  assumes st: "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  assumes f: "\<And>tcb. tcb_fault (f tcb) = tcb_fault tcb"
  shows "thread_set f t \<lbrace> fault_tcbs_valid_states \<rbrace>"
  supply get_tcb_SomeD[dest!]
  by (wpsimp wp: fault_tcbs_valid_states_lift thread_set_wp
           simp: sk_obj_at_pred_def obj_at_def pred_tcb_at_def st f)

lemma thread_set_fault_tcbs_valid_states_trivial':
  assumes st: "\<And>tcb. (\<exists>f'. tcb_fault (f tcb) = Some f')
                        \<longrightarrow> fault_tcb_states (tcb_state (f tcb))"
  shows "thread_set f t \<lbrace> fault_tcbs_valid_states \<rbrace>"
  supply get_tcb_SomeD[dest!]
  by (wpsimp wp: thread_set_wp
           simp: sk_obj_at_pred_def obj_at_def pred_tcb_at_def st fault_tcbs_valid_states_def)

lemma thread_set_ifunsafe_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows      "\<lbrace>if_unsafe_then_cap\<rbrace> thread_set f t \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_ifunsafe)
  apply (clarsimp simp: x)
  done


lemma thread_set_zombies_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows      "\<lbrace>zombies_final\<rbrace> thread_set f t \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: thread_set_def)
  apply wp
  apply (clarsimp simp: x)
  done


(* FIXME-NTFN: possible need for assumption on tcb_bound_notification *)
lemma thread_set_refs_trivial:
  assumes x: "\<And>tcb. tcb_state  (f tcb) = tcb_state  tcb"
  assumes y: "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes w: "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes t: "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  shows      "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: state_refs_of_def get_tcb_def x y w t
                 elim!: rsubst[where P=P]
                intro!: ext)
  done


lemma thread_set_valid_idle_trivial:
  assumes "\<And>tcb. tcb_state (f tcb) = tcb_state tcb"
  assumes "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  assumes "\<And>tcb. tcb_iarch (f tcb) = tcb_iarch tcb"
  shows "thread_set f t \<lbrace>valid_idle\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def valid_idle_def)
  apply wp
  apply (clarsimp simp: assms get_tcb_def pred_tcb_at_def obj_at_def)
  done


crunch thread_set
  for it[wp]: "\<lambda>s. P (idle_thread s)"


lemma thread_set_caps_of_state_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows      "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp elim!: rsubst[where P=P]
                 intro!: ext
                  dest!: get_tcb_SomeD)
  apply (subst caps_of_state_after_update)
   apply (clarsimp simp: obj_at_def get_tcb_def bspec_split [OF x])
  apply simp
  done



crunch thread_set
  for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"


lemma thread_set_global_refs_triv:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows "\<lbrace>valid_global_refs\<rbrace> thread_set f t \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (rule valid_global_refs_cte_lift)
     apply (wp thread_set_caps_of_state_trivial x)+
  done

crunch thread_set
  for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"

lemma tcb_not_empty_table:
  "\<not> empty_table S (TCB tcb)"
  by (simp add: empty_table_def)

lemmas thread_set_arch_caps_trivial
  = valid_arch_caps_lift_weak[OF thread_set.arch_state thread_set.vsobj_at
                                 thread_set_caps_of_state_trivial, simplified]

lemma thread_set_only_idle:
  "\<lbrace>only_idle and K (\<forall>tcb. tcb_state (f tcb) = tcb_state tcb \<or> \<not>idle (tcb_state (f tcb)))\<rbrace>
  thread_set f t \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def)
  apply (drule get_tcb_SomeD)
  apply force
  done


lemma thread_set_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> thread_set f t \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_pspace_in_kernel_window)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

crunch thread_set
  for pspace_respects_device_region[wp]: "pspace_respects_device_region"
  (wp: set_object_pspace_respects_device_region)

lemma thread_set_cap_refs_in_kernel_window:
  assumes y: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> thread_set f t \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_cap_refs_in_kernel_window)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (drule bspec[OF y])
  apply simp
  apply (erule sym)
  done

lemma thread_set_cap_refs_respects_device_region:
  assumes y: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows
  "\<lbrace>cap_refs_respects_device_region\<rbrace> thread_set f t \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wp set_object_cap_refs_respects_device_region)
  apply (clarsimp simp: obj_at_def)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (drule bspec[OF y])
  apply simp
  apply (erule sym)
  done

(* NOTE: The function "thread_set f p" updates a TCB at p using function f.
   It should not be used to change capabilities, though. *)
lemma thread_set_valid_ioc_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows "\<lbrace>valid_ioc\<rbrace> thread_set f p \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: thread_set_def, wp set_object_valid_ioc_caps)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (cut_tac tcb=y in x)
  apply (clarsimp simp: cte_wp_at_cases get_tcb_def cap_of_def null_filter_def
                        split_def tcb_cnode_map_tcb_cap_cases
                 split: option.splits Structures_A.kernel_object.splits)
  apply (drule_tac x="(get,set,restr)" in bspec)
   apply (fastforce simp: ranI)+
  done

context TcbAcc_AI_valid_ipc_buffer_cap_0 begin

lemma thread_set_invs_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  assumes z:  "\<And>tcb. tcb_state     (f tcb) = tcb_state tcb"
  assumes z': "\<And>tcb. tcb_bound_notification (f tcb) = tcb_bound_notification tcb"
  assumes y: "\<And>tcb. tcb_sched_context (f tcb) = tcb_sched_context tcb"
  assumes t: "\<And>tcb. tcb_yield_to (f tcb) = tcb_yield_to tcb"
  assumes z'': "\<And>tcb. tcb_iarch (f tcb) = tcb_iarch tcb"
  assumes w: "\<And>tcb. tcb_ipc_buffer (f tcb) = tcb_ipc_buffer tcb
                        \<or> (tcb_ipc_buffer (f tcb) = 0)"
  assumes a: "\<And>tcb. tcb_fault (f tcb) = tcb_fault tcb"
  assumes arch: "\<And>tcb. tcb_arch_ref (f tcb) = tcb_arch_ref tcb"
  shows      "\<lbrace>invs::'state_ext state \<Rightarrow> bool\<rbrace> thread_set f t \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_weaken_pre)
   apply (wp thread_set_valid_objs_triv thread_set_valid_arch_state
             thread_set_refs_trivial
             thread_set_hyp_refs_trivial
             thread_set_iflive_trivial
             thread_set_mdb
             thread_set_ifunsafe_trivial
             thread_set_cur_tcb
             thread_set_cur_sc_tcb
             thread_set_zombies_trivial
             thread_set_valid_idle_trivial
             thread_set_global_refs_triv
             thread_set_valid_ioc_trivial
             thread_set_valid_replies_trivial
             thread_set_fault_tcbs_valid_states_trivial
             valid_irq_node_typ valid_irq_handlers_lift
             thread_set_caps_of_state_trivial
             thread_set_arch_caps_trivial thread_set_only_idle
             thread_set_cap_refs_in_kernel_window
             thread_set_cap_refs_respects_device_region
             thread_set_aligned
             | rule x z z' z'' y w t a arch valid_tcb_arch_ref_lift [THEN fun_cong]
             | erule bspec_split [OF x] | simp add: z' y t)+
  apply (simp add: z)
  done

lemma thread_set_fault_None_fault_tcbs_valid_states:
  shows "thread_set (tcb_fault_update Map.empty) t \<lbrace> fault_tcbs_valid_states \<rbrace>"
  supply get_tcb_SomeD[dest!]
  by (wpsimp wp: thread_set_wp
           simp: sk_obj_at_pred_def obj_at_def pred_tcb_at_def fault_tcbs_valid_states_def) fastforce

lemma thread_set_fault_fault_tcbs_valid_states_except_set:
  shows "thread_set (tcb_fault_update f) t \<lbrace> fault_tcbs_valid_states_except_set {t} \<rbrace>"
  supply get_tcb_SomeD[dest!]
  by (wpsimp wp: thread_set_wp
           simp: sk_obj_at_pred_def obj_at_def pred_tcb_at_def fault_tcbs_valid_states_except_set_def)

lemma thread_set_fault_valid_objs:
  assumes a: "\<And>fault. (case f fault of None \<Rightarrow> True
                                      | Some fault' \<Rightarrow> valid_fault fault')"
  shows "\<lbrace>valid_objs\<rbrace> thread_set (tcb_fault_update f) t \<lbrace>\<lambda>rv. valid_objs :: 'z::state_ext state \<Rightarrow> bool\<rbrace>"
  apply (simp add: thread_set_def)
  apply (wpsimp wp: set_object_valid_objs)
  apply (drule get_tcb_SomeD)
  apply (erule (1) pspace_valid_objsE)
  by (clarsimp simp add: valid_obj_def valid_tcb_def obj_at_def ran_tcb_cap_cases a)

lemma thread_set_invs_fault_None[wp]:
  "\<lbrace>invs::'state_ext state \<Rightarrow> bool\<rbrace>
   thread_set (tcb_fault_update Map.empty) t
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_weaken_pre)
   by (wp thread_set_fault_valid_objs thread_set_valid_arch_state
          thread_set_refs_trivial thread_set_hyp_refs_trivial
          thread_set_iflive_trivial thread_set_mdb
          thread_set_ifunsafe_trivial thread_set_zombies_trivial
          thread_set_valid_idle_trivial thread_set_global_refs_triv
          thread_set_valid_ioc_trivial thread_set_valid_replies_trivial
          thread_set_fault_None_fault_tcbs_valid_states
          valid_irq_node_typ valid_irq_handlers_lift
          thread_set_caps_of_state_trivial thread_set_only_idle
          thread_set_arch_caps_trivial thread_set_cap_refs_in_kernel_window
          thread_set_cap_refs_respects_device_region
       | rule valid_tcb_arch_ref_lift [THEN fun_cong]
       | fastforce simp: ran_tcb_cap_cases)+

lemma thread_set_invs_but_fault_tcbs:
  assumes a: "\<And>fault. (case f fault of None \<Rightarrow> True
                                      | Some fault' \<Rightarrow> valid_fault fault')"
  shows
    "\<lbrace>invs::'state_ext state \<Rightarrow> bool\<rbrace>
     thread_set (tcb_fault_update f) t
     \<lbrace>\<lambda>rv. all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {t}\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (rule hoare_weaken_pre)
   by (wp thread_set_fault_valid_objs thread_set_valid_arch_state
          thread_set_refs_trivial thread_set_hyp_refs_trivial
          thread_set_iflive_trivial thread_set_mdb
          thread_set_ifunsafe_trivial thread_set_zombies_trivial
          thread_set_valid_idle_trivial thread_set_global_refs_triv
          thread_set_valid_ioc_trivial thread_set_valid_replies_trivial
          thread_set_fault_fault_tcbs_valid_states_except_set
          valid_irq_node_typ valid_irq_handlers_lift
          thread_set_caps_of_state_trivial thread_set_only_idle
          thread_set_arch_caps_trivial thread_set_cap_refs_in_kernel_window
          thread_set_cap_refs_respects_device_region a
       | rule valid_tcb_arch_ref_lift [THEN fun_cong]
       | fastforce simp: ran_tcb_cap_cases )+

end

lemma thread_set_cte_wp_at_trivial:
  assumes x: "\<And>tcb. \<forall>(getF, v) \<in> ran tcb_cap_cases.
                  getF (f tcb) = getF tcb"
  shows "\<lbrace>\<lambda>s. Q (cte_wp_at P p s)\<rbrace> thread_set f t \<lbrace>\<lambda>rv s. Q (cte_wp_at P p s)\<rbrace>"
  by (auto simp: cte_wp_at_caps_of_state
          intro: thread_set_caps_of_state_trivial [OF x])


lemma det_query_twice:
  assumes x: "\<And>P. \<lbrace>P\<rbrace> f \<lbrace>\<lambda>x. P\<rbrace>"
  assumes y: "det f"
  shows      "do x \<leftarrow> f; y :: tcb \<leftarrow> f; g x y od
               = do x \<leftarrow> f; g x x od"
  apply (subgoal_tac "\<exists>fn. f = (\<lambda>s. ({(fn s, s)}, False))")
   apply clarsimp
   apply (rule bind_cong [OF refl])
   apply (simp add: bind_def)
  apply (rule_tac x="\<lambda>s. fst (THE x. x \<in> fst (f s))" in exI)
  apply (rule ext)
  apply (insert y, simp add: det_def)
  apply (erule_tac x=s in allE)
  apply clarsimp
  apply (rule sym)
  apply (rule state_unchanged [OF x])
  apply simp
  done

lemma as_user_wp_thread_set_helper:
  assumes x: "
         \<lbrace>P\<rbrace> do
                tcb \<leftarrow> gets_the (get_tcb t);
                p \<leftarrow> select_f (m (arch_tcb_context_get (tcb_arch tcb)));
                thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set (snd p) (tcb_arch tcb)\<rparr>) t
         od \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> as_user t m \<lbrace>\<lambda>rv. Q\<rbrace>"
proof -
  have P: "\<And>P Q a b c f.
           \<lbrace>P\<rbrace> do x \<leftarrow> a; y \<leftarrow> b x; z \<leftarrow> c x y; return (f x y z) od \<lbrace>\<lambda>rv. Q\<rbrace>
         = \<lbrace>P\<rbrace> do x \<leftarrow> a; y \<leftarrow> b x; c x y od \<lbrace>\<lambda>rv. Q\<rbrace>"
    apply (simp add: valid_def bind_def return_def split_def)
    done
  have Q: "do
             tcb \<leftarrow> gets_the (get_tcb t);
             p \<leftarrow> select_f (m (arch_tcb_context_get (tcb_arch tcb)));
             thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_context_set (snd p) (tcb_arch tcb)\<rparr>) t
           od
         = do
             tcb \<leftarrow> gets_the (get_tcb t);
             p \<leftarrow> select_f (m (arch_tcb_context_get (tcb_arch tcb)));
             set_object t (TCB (tcb \<lparr>tcb_arch := arch_tcb_context_set (snd p) (tcb_arch tcb)\<rparr>))
           od"
    apply (simp add: thread_set_def)
    apply (rule ext)
    apply (rule bind_apply_cong [OF refl])+
    apply (simp add: select_f_def in_monad gets_the_def gets_def)
    apply (clarsimp simp add: get_def bind_def return_def assert_opt_def)
    done
  show ?thesis
    apply (simp add: as_user_def split_def)
    apply (simp add: P x [simplified Q])
    done
qed

context TcbAcc_AI_valid_ipc_buffer_cap_0 begin

lemma as_user_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> as_user a f \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  apply (wp as_user_wp_thread_set_helper
            thread_set_valid_objs_triv)
  apply (wpsimp simp: ran_tcb_cap_cases valid_arch_arch_tcb_context_set)+
  done

end

crunch as_user
  for pspace_distinct[wp]: pspace_distinct
  and pspace_aligned[wp]: pspace_aligned
  and valid_idle[wp]: valid_idle
  and if_live_then_nonz_cap[wp]: if_live_then_nonz_cap
  and if_unsafe_then_cap[wp]: if_unsafe_then_cap
  and zombies_final[wp]: zombies_final
  and refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  and cur_tcb[wp]: cur_tcb
  and cte_wp_at[wp]: "\<lambda>s. P (cte_wp_at P' c s)"
  and pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"
  (rule: as_user_wp_thread_set_helper
   wp: thread_set_valid_idle_trivial thread_set_iflive_trivial thread_set_ifunsafe_trivial
       thread_set_zombies_trivial thread_set_refs_trivial thread_set_cte_wp_at_trivial
       thread_set_no_change_tcb_pred_gen
       ball_tcb_cap_casesI
   simp: tcb_to_itcb_def)

lemma as_user_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> as_user t f \<lbrace>\<lambda>_. valid_irq_handlers\<rbrace>"
  by (wpsimp wp: as_user_wp_thread_set_helper valid_irq_handlers_lift
                 thread_set_caps_of_state_trivial ball_tcb_cap_casesI)

crunch as_user
  for it[wp]: "\<lambda>s. P (idle_thread s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and valid_global_refs[wp]: valid_global_refs
  and cur_thread[wp]: "\<lambda>s. P (cur_thread s)"
  and ex_nonz_cap_to[wp]: "ex_nonz_cap_to p"
  and ct_in_state[wp]: "ct_in_state P"
  and fault_tcbs_valid_states_except_set[wp]: "fault_tcbs_valid_states_except_set TS"
  (rule: valid_global_refs_cte_lift ex_nonz_cap_to_pres ct_in_state_thread_state_lift
         fault_tcbs_valid_states_lift
   simp: crunch_simps)

lemma set_object_ntfn_at:
  "\<lbrace> ntfn_at p and tcb_at r \<rbrace> set_object r obj \<lbrace> \<lambda>rv. ntfn_at p \<rbrace>"
  apply (rule set_object_at_obj2)
  apply (clarsimp simp: is_obj_defs)
  done

lemma gts_wf[wp]: "\<lbrace>tcb_at t and invs\<rbrace> get_thread_state t \<lbrace>valid_tcb_state\<rbrace>"
  apply (simp add: get_thread_state_def thread_get_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_pspace_def
                        valid_objs_def get_tcb_def dom_def
                  split: option.splits Structures_A.kernel_object.splits)
  apply (erule allE, erule impE, blast)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  done

lemma idle_thread_idle[wp]:
  "\<lbrace>\<lambda>s. valid_idle s \<and> t = idle_thread s\<rbrace> get_thread_state t \<lbrace>\<lambda>r s. idle r\<rbrace>"
  apply (clarsimp simp: valid_def get_thread_state_def thread_get_def bind_def return_def
                        gets_the_def gets_def get_def assert_opt_def get_tcb_def
                        fail_def valid_idle_def obj_at_def pred_tcb_at_def
                 split: option.splits Structures_A.kernel_object.splits)
  done

crunch set_thread_state_act
  for valid_objs[wp]: valid_objs

lemma set_thread_state_valid_objs[wp]:
 "\<lbrace>valid_objs and valid_tcb_state st\<rbrace>
  set_thread_state thread st
  \<lbrace>\<lambda>r. valid_objs\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_valid_objs)
  apply (clarsimp simp: obj_at_def get_tcb_def
                 split: Structures_A.kernel_object.splits option.splits)
  apply (simp add: valid_objs_def dom_def)
  apply (erule allE, erule impE, blast)
  apply (simp add: valid_obj_def valid_tcb_def a_type_def tcb_cap_cases_def)
  done

lemma set_bound_notification_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_ntfn ntfn\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_objs, simp)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb
                  split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

lemma set_tcb_sched_context_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_sc sc\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_objs, simp)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb
                  split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

lemma set_tcb_yield_to_valid_objs[wp]:
  "\<lbrace>valid_objs and valid_bound_sc sc\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_objs, simp)
  apply (clarsimp simp: obj_at_def get_tcb_def is_tcb
                  split: option.splits kernel_object.splits)
  apply (erule (1) valid_objsE)
  apply (auto simp: valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

crunch set_thread_state
 for aligned[wp]: pspace_aligned

lemma set_tcb_obj_ref_aligned[wp]:
 "\<lbrace>pspace_aligned\<rbrace>
  set_tcb_obj_ref f thread ntfn
  \<lbrace>\<lambda>r. pspace_aligned\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_aligned)
  apply clarsimp
  done

crunch set_tcb_obj_ref
 for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"

lemma set_tcb_obj_ref_tcb_at[wp]:
  "set_tcb_obj_ref f t' obj \<lbrace>\<lambda>s. P (tcb_at t s)\<rbrace>"
  by (wpsimp simp: tcb_at_typ)

lemma set_thread_state_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_thread_state st p' \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  by (wp hoare_cte_wp_caps_of_state_lift)

lemma set_bound_notification_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (auto simp: cte_wp_at_cases tcb_cap_cases_def)
  done

lemma set_tcb_sched_context_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (auto simp: cte_wp_at_cases tcb_cap_cases_def)
  done

lemma set_tcb_sched_yield_to_cte_wp_at [wp]:
  "\<lbrace>cte_wp_at P c\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. cte_wp_at P c\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (auto simp: cte_wp_at_cases tcb_cap_cases_def)
  done

lemma set_object_tcb_at [wp]:
  "\<lbrace> tcb_at t' \<rbrace> set_object t (TCB x) \<lbrace>\<lambda>_. tcb_at t'\<rbrace>"
  by (rule set_object_at_obj1) (simp add: is_tcb)

lemma as_user_tcb [wp]: "\<lbrace>\<lambda>s. P (tcb_at t' s)\<rbrace> as_user t m \<lbrace>\<lambda>rv s. P (tcb_at t' s)\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (wp set_object_wp)
  apply (clarsimp simp: get_tcb_def tcb_at_def)
  done


lemma fold_fun_upd:
  "distinct keys \<Longrightarrow>
   foldl (\<lambda>s (k, v). s(k := v)) s (zip keys vals) key
   = (if key \<in> set (take (length vals) keys)
      then vals ! (the_index keys key)
      else s key)"
  apply (induct keys arbitrary: vals s)
   apply simp
  apply (case_tac vals, simp_all split del: if_split)
  apply (case_tac "key = a", simp_all split del: if_split)
   apply clarsimp
   apply (drule in_set_takeD)
   apply simp
  apply clarsimp
  done

lemma load_word_offs_P[wp]:
  "\<lbrace>P\<rbrace> load_word_offs a x \<lbrace>\<lambda>_. P\<rbrace>"
  unfolding load_word_offs_def
  by (wp dmo_inv loadWord_inv)

lemma valid_tcb_objs:
  assumes vs: "valid_objs s"
  assumes somet: "get_tcb thread s = Some y"
  shows "valid_tcb thread y s"
proof -
  from somet have inran: "kheap s thread = Some (TCB y)"
    by (clarsimp simp: get_tcb_def
                split: option.splits Structures_A.kernel_object.splits)
  with vs have "valid_obj thread (TCB y) s"
    by (fastforce simp: valid_objs_def dom_def)
  thus ?thesis by (simp add: valid_tcb_def valid_obj_def)
qed


locale TcbAcc_AI_get_cap_valid_ipc =
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes get_cap_valid_ipc:
    "\<And>v t.
      \<lbrace>valid_objs and obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> tcb_ipc_buffer tcb = v) t\<rbrace>
        get_cap (t, tcb_cnode_index 2)
      \<lbrace>\<lambda>rv (s::'state_ext state). valid_ipc_buffer_cap rv v\<rbrace>"


lemma get_cap_aligned:
  "\<lbrace>valid_objs\<rbrace> get_cap slot \<lbrace>\<lambda>rv s. cap_aligned rv\<rbrace>"
  apply (rule hoare_strengthen_post, rule get_cap_valid)
  apply (clarsimp simp: valid_cap_def)
  done


lemma shiftr_eq_mask_eq:
  "a && ~~ mask b = c && ~~ mask b \<Longrightarrow> a >> b = c >> b"
  apply (rule word_eqI)
  apply (drule_tac x="b + n" in word_eqD)
  apply (case_tac "b + n < size a")
   apply (simp add: nth_shiftr word_size word_ops_nth_size)
  apply (auto dest!: test_bit_size simp: word_size)
  done


lemma thread_get_wp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> P (f tcb) s) ptr s\<rbrace>
    thread_get f ptr
   \<lbrace>P\<rbrace>"
  apply (clarsimp simp: valid_def obj_at_def)
  apply (frule in_inv_by_hoareD [OF thread_get_inv])
  apply (clarsimp simp: thread_get_def bind_def gets_the_def
                        assert_opt_def split_def return_def fail_def
                        gets_def get_def
                 split: option.splits
                 dest!: get_tcb_SomeD)
  done

lemma thread_get_pred_tcb_at_wp:
  "\<lbrace>\<lambda>s. \<forall>f. pred_tcb_at proj ((=) f) t s \<longrightarrow> P f s \<rbrace> thread_get (proj \<circ> tcb_to_itcb) t \<lbrace>P\<rbrace>"
  apply (wp thread_get_wp')
  apply clarsimp
  apply (drule spec, erule mp)
  by (simp add: pred_tcb_at_def obj_at_def)

lemma thread_get_ret:
  "\<lbrace>\<top>\<rbrace> thread_get (proj \<circ> tcb_to_itcb) t \<lbrace>\<lambda>rv. pred_tcb_at proj ((=) rv) t\<rbrace>"
  apply (simp add: thread_get_def)
  apply wp
  by (clarsimp simp: pred_tcb_at_def)

lemmas thread_get_mcpriority_wp =
  thread_get_pred_tcb_at_wp[where proj=itcb_mcpriority, simplified comp_def, simplified]

lemmas thread_get_mcpriority_ret =
  thread_get_ret[where proj=itcb_mcpriority, simplified comp_def, simplified]

lemmas thread_get_fault_wp =
  thread_get_pred_tcb_at_wp[where proj=itcb_fault, simplified comp_def, simplified]

lemma thread_get_sp:
  "\<lbrace>P\<rbrace> thread_get f ptr
   \<lbrace>\<lambda>rv. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> f tcb = rv) ptr and P\<rbrace>"
  apply (clarsimp simp: valid_def obj_at_def)
  apply (frule in_inv_by_hoareD [OF thread_get_inv])
  apply (clarsimp simp: thread_get_def bind_def gets_the_def
                        assert_opt_def split_def return_def fail_def
                        gets_def get_def
                 split: option.splits
                 dest!: get_tcb_SomeD)
  done

lemma gbn_wp:
  "\<lbrace>\<lambda>s. obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> P (f tcb) s) ptr s \<rbrace>
     get_tcb_obj_ref f ptr
   \<lbrace>P\<rbrace>"
  apply (simp add: get_tcb_obj_ref_def)
  apply (wp thread_get_wp | clarsimp)+
  done

lemmas thread_get_obj_at_eq = thread_get_sp[where P=\<top>, simplified]


lemma wf_cs_0:
  "well_formed_cnode_n sz cn \<Longrightarrow> \<exists>n. n \<in> dom cn \<and> bl_to_bin n = 0"
  unfolding well_formed_cnode_n_def
  apply clarsimp
  apply (rule_tac x = "replicate sz False" in exI)
  apply (simp add: bl_to_bin_rep_False)
  done


lemma ct_active_st_tcb_at_weaken:
  "\<lbrakk> st_tcb_at P (cur_thread s) s;
     \<And>st. P st \<Longrightarrow> active st\<rbrakk>
  \<Longrightarrow> ct_active s"
  apply (unfold ct_in_state_def)
  apply (erule pred_tcb_weakenE)
  apply auto
  done

lemma ct_in_state_decomp:
  assumes x: "\<lbrace>\<lambda>s. t = (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv s. t = (cur_thread s)\<rbrace>"
  assumes y: "\<lbrace>Pre\<rbrace> f \<lbrace>\<lambda>rv. st_tcb_at Prop t\<rbrace>"
  shows      "\<lbrace>\<lambda>s. Pre s \<and> t = (cur_thread s)\<rbrace> f \<lbrace>\<lambda>rv. ct_in_state Prop\<rbrace>"
  apply (rule hoare_post_imp[where Q'="\<lambda>rv s. t = cur_thread s \<and> st_tcb_at Prop t s"])
   apply (clarsimp simp add: ct_in_state_def)
  apply (rule hoare_weaken_pre)
   apply (wp x y)
  apply simp
  done

(**********************************************************
  !@!@!@!@!@!@!@! UNINTERLEAVE SBA STUFF !@!@!@!@!@!@!@!@!
**********************************************************)

lemma sts_st_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. st_tcb_at (\<lambda>r. r = ts) t\<rbrace>"
  by (simp add: set_thread_state_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma sbn_bound_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. bound_tcb_at (\<lambda>r. r = ntfn) t\<rbrace>"
  by (simp add: set_tcb_obj_ref_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma ssc_bound_sc_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. bound_sc_tcb_at (\<lambda>r. r = sc) t\<rbrace>"
  by (simp add: set_tcb_obj_ref_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma ssc_bound_yt_tcb_at:
  "\<lbrace>\<top>\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. bound_yt_tcb_at (\<lambda>r. r = sc) t\<rbrace>"
  by (simp add: set_tcb_obj_ref_def pred_tcb_at_def | wp set_object_at_obj3)+

lemma sts_st_tcb_at'[wp]:
  "\<lbrace>K (P ts)\<rbrace> set_thread_state t ts \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule sts_st_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

lemma set_thread_state_pred_tcb_at:
  "\<forall>tcb ts. proj (tcb_to_itcb tcb) = proj (tcb_to_itcb (tcb\<lparr>tcb_state := ts\<rparr>))
   \<Longrightarrow> set_thread_state ref ts \<lbrace>\<lambda>s. pred_tcb_at proj P t s\<rbrace>"
  unfolding set_thread_state_def set_object_def get_object_def
  apply (wpsimp simp: pred_tcb_at_def)
  by (clarsimp simp: obj_at_def get_tcb_def)

(* This rule can cause problems with the simplifier if rule unification chooses a
   P' that does not specify proj. If necessary, this can be worked around by
   manually specifying proj. *)
lemma set_thread_state_pred_tcb_at':
  "\<forall>tcb ts. proj (tcb_to_itcb tcb) = proj (tcb_to_itcb (tcb\<lparr>tcb_state := ts\<rparr>))
   \<Longrightarrow> set_thread_state ref ts \<lbrace>\<lambda>s. P' (pred_tcb_at proj P t s)\<rbrace>"
  unfolding set_thread_state_def set_object_def get_object_def
  apply (wpsimp simp: pred_tcb_at_def)
  by (clarsimp simp: obj_at_def get_tcb_def split: option.splits kernel_object.splits)

lemma sbn_bound_tcb_at':
  "\<lbrace>K (P ntfn)\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. bound_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule sbn_bound_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

lemma ssc_bound_tcb_at':
  "\<lbrace>K (P sc)\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. bound_sc_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule ssc_bound_sc_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

lemma syt_bound_tcb_at':
  "\<lbrace>K (P sc)\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. bound_yt_tcb_at P t\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (rule hoare_chain)
    apply (rule ssc_bound_yt_tcb_at)
   apply simp
  apply (clarsimp elim!: pred_tcb_weakenE)
  done

crunch set_thread_state_act
 for valid_idle[wp]: valid_idle

lemma sts_valid_idle [wp]:
  "\<lbrace>valid_idle and
     (\<lambda>s. t = idle_thread s \<longrightarrow> idle ts)\<rbrace>
   set_thread_state t ts
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (auto simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma sbn_valid_idle [wp]:
  "\<lbrace>valid_idle and
     (\<lambda>s. t = idle_thread s \<longrightarrow> \<not> bound ntfn)\<rbrace>
   set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (auto simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma ssc_valid_idle [wp]:
  "\<lbrace>valid_idle and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wp
  apply (clarsimp cong: if_cong
                  simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

crunch set_thread_state, set_tcb_obj_ref
  for distinct[wp]: pspace_distinct

lemma syt_valid_idle [wp]:
  "\<lbrace>valid_idle and (\<lambda>s. t \<noteq> idle_thread s)\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>_. valid_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wp
  apply (clarsimp cong: if_cong
                  simp: valid_idle_def pred_tcb_at_def obj_at_def get_tcb_def)
  done

lemma cur_tcb_scheduler_action[simp]:
  "cur_tcb (scheduler_action_update f s) = cur_tcb s"
  by (simp add: cur_tcb_def)

crunch set_thread_state_act
 for cur_tcb[wp]: cur_tcb

lemma set_thread_state_act_cur_sc_tcb [wp]:
  "\<lbrace>cur_sc_tcb\<rbrace> set_thread_state_act tcb_ptr \<lbrace>\<lambda>_. cur_sc_tcb\<rbrace>"
  by (wpsimp simp: set_thread_state_act_def set_scheduler_action_def
                   cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def)

lemma sts_cur_tcb [wp]:
  "set_thread_state t st \<lbrace>\<lambda>s. cur_tcb s\<rbrace>"
  unfolding set_thread_state_def set_object_def get_object_def
  apply wpsimp
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
  done

lemma sts_cur_sc_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_sc_tcb s\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. cur_sc_tcb s\<rbrace>"
  unfolding set_thread_state_def set_object_def get_object_def
  by (wpsimp simp: cur_sc_tcb_def sc_tcb_sc_at_def obj_at_def get_tcb_def)

lemma sbn_cur_tcb [wp]:
  "set_tcb_obj_ref f t ntfn \<lbrace>\<lambda>s. cur_tcb s\<rbrace>"
  apply (clarsimp simp: set_tcb_obj_ref_def set_object_def gets_the_def
                        valid_def in_monad get_object_def)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: cur_tcb_def obj_at_def is_tcb_def)
  done

lemma sbn_cur_sc_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_sc_tcb s\<rbrace> set_tcb_obj_ref f t ntfn \<lbrace>\<lambda>rv s. cur_sc_tcb s\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def get_object_def cur_sc_tcb_def sc_tcb_sc_at_def
                   obj_at_def get_tcb_def)

crunch set_thread_state_act
 for iflive[wp]: if_live_then_nonz_cap

lemma sts_iflive[wp]:
  "\<lbrace>\<lambda>s. (\<not> halted st \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_thread_state t st
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_iflive)
  by (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                simp: tcb_cap_cases_def live_def
                split: Structures_A.thread_state.splits)

lemma sbn_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound ntfn \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply wpsimp
  apply (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                   simp: tcb_cap_cases_def live_def
                  split: thread_state.splits)
  done

lemma ssc_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound sc \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply wpsimp
  apply (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                   simp: tcb_cap_cases_def live_def
                  split: Structures_A.thread_state.splits)
  done

lemma syt_iflive[wp]:
  "\<lbrace>\<lambda>s. (bound sc \<longrightarrow> ex_nonz_cap_to t s)
         \<and> if_live_then_nonz_cap s\<rbrace>
     set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wpsimp wp: set_object_iflive)
  apply (fastforce dest: get_tcb_SomeD if_live_then_nonz_capD2
                   simp: tcb_cap_cases_def live_def
                  split: Structures_A.thread_state.splits)
  done

crunch set_thread_state_act
  for ifunsafe[wp]: if_unsafe_then_cap

lemma sts_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wp|simp)+
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma sbn_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma ssc_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma syt_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap\<rbrace> set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

crunch set_thread_state
  for zombies[wp]: zombies_final
  (simp: tcb_cap_cases_def)

lemma sbn_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_tcb_obj_ref tcb_bound_notification_update f ntfn \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma ssc_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_tcb_obj_ref tcb_sched_context_update f sc \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma syt_zombies[wp]:
  "\<lbrace>zombies_final\<rbrace> set_tcb_obj_ref tcb_yield_to_update f sc \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp, simp)
  apply (fastforce simp: tcb_cap_cases_def)
  done

lemma sts_refs_of_helper: "
          {r. (r \<in> tcb_st_refs_of ts \<or>
               r \<in> get_refs TCBBound ntfnptr \<or>
               r \<in> get_refs TCBSchedContext sc \<or>
               r \<in> get_refs TCBYieldTo yt) \<and>
              (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)} =
          get_refs TCBBound ntfnptr \<union>
          get_refs TCBSchedContext sc \<union>
          get_refs TCBYieldTo yt"
  by (auto simp: tcb_st_refs_of_def get_refs_def
          split: thread_state.splits option.splits)

declare scheduler_action_update.state_refs_update[simp]

crunch set_thread_state_act
  for refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  and hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"

lemma sts_refs_of[wp]:
  "\<lbrace>\<lambda>s. P ((state_refs_of s) (t := tcb_st_refs_of st
                         \<union> {r. r \<in> state_refs_of s t \<and>
                 (snd r = TCBBound \<or> snd r = TCBSchedContext \<or> snd r = TCBYieldTo)}))\<rbrace>
    set_thread_state t st
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD
                   simp: state_refs_of_def
                 intro!: ext)
  apply (simp add: get_tcb_def sts_refs_of_helper)
  apply auto
  done

lemma kheap_Some_state_hyp_refs_ofD:
  "kheap s p = Some ko \<Longrightarrow> state_hyp_refs_of s p = hyp_refs_of ko"
  by (rule ko_at_state_hyp_refs_ofD; simp add: obj_at_def)

lemma sts_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_thread_state t st
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp | simp del: fun_upd_apply)+
  apply (clarsimp simp: get_tcb_def split: option.splits kernel_object.splits
                  simp del: fun_upd_apply)
  apply (subst state_hyp_refs_of_tcb_state_update; assumption)
  done

lemma sbn_refs_of_helper:
          "{r. (r \<in> tcb_st_refs_of ts \<or>
               r \<in> get_refs TCBBound ntfnptr) \<and>
              snd r \<noteq> TCBBound} =
          tcb_st_refs_of ts"
  by (auto simp add: tcb_st_refs_of_def get_refs_def split: thread_state.splits option.splits)

lemma sbn_refs_of[wp]:
  "\<lbrace>(\<lambda>s. P ((state_refs_of s)(t:= (case ntfn of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, TCBBound)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = TCBBound}))))\<rbrace>
   set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (auto elim!: rsubst[where P=P] dest!: get_tcb_SomeD
           simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def
           intro!: ext split: option.splits if_splits thread_state.splits)


lemma sbn_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp del: fun_upd_apply)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp del: fun_upd_apply
                  intro!: ext)
  apply (subst state_hyp_refs_of_tcb_bound_ntfn_update; auto simp: get_tcb_def)
  done

lemma ssc_refs_of[wp]:
  "\<lbrace>(\<lambda>s. P ((state_refs_of s)(t:= (case sc of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, TCBSchedContext)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = TCBSchedContext}))))\<rbrace>
   set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (auto elim!: rsubst[where P=P] dest!: get_tcb_SomeD
           simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def
           intro!: ext split: option.splits if_splits thread_state.splits)

lemma ssc_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp del: fun_upd_apply)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp del: fun_upd_apply
                  intro!: ext)
  apply (subst state_hyp_refs_of_tcb_sched_context_update; auto simp: get_tcb_def)
  done

lemma syt_refs_of[wp]:
  "\<lbrace>(\<lambda>s. P ((state_refs_of s)(t:= (case sc of None \<Rightarrow> {} | Some new \<Rightarrow> {(new, TCBYieldTo)}) \<union>
          (state_refs_of s t - {x \<in> state_refs_of s t. snd x = TCBYieldTo}))))\<rbrace>
   set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (auto elim!: rsubst[where P=P] dest!: get_tcb_SomeD
           simp: state_refs_of_def get_refs_def2 tcb_st_refs_of_def
           intro!: ext split: option.splits if_splits thread_state.splits)

lemma syt_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
    set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp del: fun_upd_apply)
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD simp del: fun_upd_apply
                  intro!: ext)
  apply (subst state_hyp_refs_of_tcb_yield_to_update; auto simp: get_tcb_def)
  done

lemma set_thread_state_thread_set:
  "set_thread_state p st = (do thread_set (tcb_state_update (\<lambda>_. st)) p;
                               set_thread_state_act p
                            od)"
  by (simp add: set_thread_state_def thread_set_def bind_assoc)

lemma set_tcb_obj_ref_thread_set:
  "set_tcb_obj_ref f p sc = thread_set (f (\<lambda>_. sc)) p"
  by (simp add: set_tcb_obj_ref_def thread_set_def bind_assoc)

crunch set_thread_state_act
 for pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P t s)"

lemma sts_st_tcb_at_neq:
  "\<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s) \<and> (t\<noteq>t')\<rbrace> set_thread_state t' st \<lbrace>\<lambda>_ s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (simp add: pred_tcb_at_def obj_at_def)
  done

lemma sbn_st_tcb_at_neq:
  "\<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s) \<and> (t\<noteq>t')\<rbrace> set_tcb_obj_ref f t' new \<lbrace>\<lambda>_ s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp cong: if_cong)
  apply (drule get_tcb_SomeD)
  apply (simp add: pred_tcb_at_def obj_at_def)
  done

lemma sts_st_tcb_at_cases_strong:
  "\<lbrace>\<lambda>s. tcb_at t s \<longrightarrow> (t = t' \<longrightarrow> P (P' ts)) \<and> (t \<noteq> t' \<longrightarrow> P (st_tcb_at P' t' s))\<rbrace>
     set_thread_state t ts
   \<lbrace>\<lambda>rv s. P (st_tcb_at P' t' s) \<rbrace>"
  by (wpsimp simp: set_thread_state_def wp: set_object_wp)
     (fastforce simp: get_tcb_ko_at pred_tcb_at_def obj_at_def is_tcb)

lemma sts_st_tcb_at_cases:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> P ts) \<and> (t \<noteq> t' \<longrightarrow> st_tcb_at P t' s)\<rbrace>
     set_thread_state t ts
   \<lbrace>\<lambda>rv. st_tcb_at P t'\<rbrace>"
  by (wpsimp wp: sts_st_tcb_at_cases_strong)

lemma sbn_bound_tcb_at_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> P ntfn) \<and> ((t \<noteq> t') \<longrightarrow> bound_tcb_at P t' s)\<rbrace>
     set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>rv. bound_tcb_at P t'\<rbrace>"
  apply (cases "t = t'", simp_all)
   apply (wp sbn_bound_tcb_at')
   apply simp
  apply (wp sbn_st_tcb_at_neq)
  apply simp
  done

lemma ssc_bound_tcb_at_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> P sc) \<and> ((t \<noteq> t') \<longrightarrow> bound_sc_tcb_at P t' s)\<rbrace>
     set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>rv. bound_sc_tcb_at P t'\<rbrace>"
  apply (cases "t = t'", simp_all)
   apply (wp ssc_bound_tcb_at')
   apply simp
  apply (wp sbn_st_tcb_at_neq)
  apply simp
  done

lemma syt_bound_tcb_at_cases:
  "\<lbrace>\<lambda>s. ((t = t') \<longrightarrow> P sc) \<and> ((t \<noteq> t') \<longrightarrow> bound_yt_tcb_at P t' s)\<rbrace>
     set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>rv. bound_yt_tcb_at P t'\<rbrace>"
  apply (cases "t = t'", simp_all)
   apply (wp syt_bound_tcb_at')
   apply simp
  apply (wp sbn_st_tcb_at_neq)
  apply simp
  done

lemma sbn_st_tcb_at[wp]:
  "set_tcb_obj_ref tcb_bound_notification_update tcb ntfn \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wpsimp
  apply (auto simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma ssc_st_tcb_at[wp]:
  "set_tcb_obj_ref tcb_sched_context_update tcb ntfn \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wpsimp
  apply (auto simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma syt_st_tcb_at[wp]:
  "set_tcb_obj_ref tcb_yield_to_update tcb ntfn \<lbrace>\<lambda>s. Q (st_tcb_at P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wpsimp
  apply (auto simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma sbn_fault_tcb_at[wp]:
  "set_tcb_obj_ref tcb_bound_notification_update tcb ntfn \<lbrace>\<lambda>s. Q (fault_tcb_at P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wpsimp
  apply (auto simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma ssc_fault_tcb_at[wp]:
  "set_tcb_obj_ref tcb_sched_context_update tcb ntfn \<lbrace>\<lambda>s. Q (fault_tcb_at P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wpsimp
  apply (auto simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

lemma syt_fault_tcb_at[wp]:
  "set_tcb_obj_ref tcb_yield_to_update tcb ntfn \<lbrace>\<lambda>s. Q (fault_tcb_at P t s)\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply wpsimp
  apply (auto simp: pred_tcb_at_def obj_at_def dest!: get_tcb_SomeD)
  done

crunch set_thread_state
  for cdt[wp]: "\<lambda>s. P (cdt s)"
  and ioc[wp]: "\<lambda>s. P (is_original_cap s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"

lemma set_thread_state_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_thread_state p st \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  by (rule valid_mdb_lift; wp)

lemma set_bound_notification_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_mdb)
   apply (fastforce simp: tcb_cap_cases_def)
  apply assumption
  done

lemma set_tcb_sched_cotnext_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_tcb_obj_ref tcb_sched_context_update p sc \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_mdb)
   apply (fastforce simp: tcb_cap_cases_def)
  apply assumption
  done

lemma set_tcb_yield_to_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> set_tcb_obj_ref tcb_yield_to_update p sc \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_mdb)
   apply (fastforce simp: tcb_cap_cases_def)
  apply assumption
  done

lemma set_thread_state_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_thread_state p st \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift; wp)

lemma set_bound_notification_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_global_refs_triv|clarsimp simp: tcb_cap_cases_def)+
  done

lemma set_tcb_sched_context_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_tcb_obj_ref tcb_sched_context_update p ntfn \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_global_refs_triv|clarsimp simp: tcb_cap_cases_def)+
  done

lemma set_tcb_yield_to_global_refs [wp]:
  "\<lbrace>valid_global_refs\<rbrace> set_tcb_obj_ref tcb_yield_to_update p ntfn \<lbrace>\<lambda>_. valid_global_refs\<rbrace>"
  apply (simp add: set_tcb_obj_ref_thread_set)
  apply (wp thread_set_global_refs_triv|clarsimp simp: tcb_cap_cases_def)+
  done

crunch set_thread_state, set_tcb_obj_ref
 for arch[wp]: "\<lambda>s. P (arch_state s)"


lemma st_tcb_ex_cap:
  "\<lbrakk> st_tcb_at P t s; if_live_then_nonz_cap s;
      \<And>st. P st \<Longrightarrow> \<not> halted st\<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to t s"
  unfolding pred_tcb_at_def
  by (erule (1) if_live_then_nonz_capD, fastforce simp: live_def)

lemma bound_tcb_ex_cap:
  "\<lbrakk> bound_tcb_at P t s; if_live_then_nonz_cap s;
      \<And>ntfn. P ntfn \<Longrightarrow> bound ntfn \<rbrakk>
     \<Longrightarrow> ex_nonz_cap_to t s"
  unfolding pred_tcb_at_def
  by (erule (1) if_live_then_nonz_capD, fastforce simp: live_def)

locale TcbAcc_AI_pred_tcb_cap_wp_at =
  fixes proj :: "itcb \<Rightarrow> 'proj"
  fixes state_ext_t :: "'state_ext::state_ext itself"
  assumes pred_tcb_cap_wp_at:
    "\<And>P t (s::'state_ext state) ref Q.
      \<lbrakk> pred_tcb_at proj P t s; valid_objs s;
        ref \<in> dom tcb_cap_cases;
        \<forall>cap. (pred_tcb_at proj P t s \<and> tcb_cap_valid cap (t, ref) s) \<longrightarrow> Q cap\<rbrakk>
      \<Longrightarrow> cte_wp_at Q (t, ref) s"

locale TcbAcc_AI_st_tcb_at_cap_wp_at = TcbAcc_AI_pred_tcb_cap_wp_at itcb_state state_ext_t
  for state_ext_t :: "'state_ext::state_ext itself"


context TcbAcc_AI_st_tcb_at_cap_wp_at begin

lemma dom_tcb_cap_cases:
  "tcb_cnode_index 0 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 1 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 2 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 3 \<in> dom tcb_cap_cases"
  "tcb_cnode_index 4 \<in> dom tcb_cap_cases"
  by clarsimp+

end

lemma set_thread_state_interrupt_irq_node[wp]: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace>
  set_thread_state param_a param_b \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace> "
  apply (simp add: set_thread_state_def)
  apply (wp|simp add: set_object_def)+
  done
(*crunch irq_node[wp]: set_thread_state "\<lambda>s. P (interrupt_irq_node s)"*)

crunch set_tcb_obj_ref
 for irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"

crunch set_tcb_obj_ref, set_thread_state
 for interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"

lemmas set_thread_state_caps_of_state = sts_caps_of_state

lemmas set_thread_state_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_thread_state_caps_of_state
                                  set_thread_state_interrupt_states]

lemmas set_bound_notification_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_bound_caps_of_state
                                  set_tcb_obj_ref_interrupt_states]

lemmas set_tcb_sched_context_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_tcb_sc_caps_of_state
                                  set_tcb_obj_ref_interrupt_states]

lemmas set_tcb_yield_to_valid_irq_nodes[wp]
    = valid_irq_handlers_lift [OF set_tcb_yt_caps_of_state
                                  set_tcb_obj_ref_interrupt_states]

lemma sbn_obj_at_impossible':
  "(\<And>tcb. \<not> P' (TCB tcb)) \<Longrightarrow> set_tcb_obj_ref f t ntfn \<lbrace>\<lambda>s. P (obj_at P' p s)\<rbrace>"
  unfolding set_tcb_obj_ref_thread_set
  by (wp thread_set_obj_at_impossible, simp)

lemmas sbn_obj_at_impossible = sbn_obj_at_impossible'[where P= id, simplified]

crunch set_thread_state_act
  for only_idle[wp]: only_idle
  and fault_tcbs_valid_states_except_set[wp]: "fault_tcbs_valid_states_except_set TS"

lemma sts_only_idle:
  "\<lbrace>only_idle and (\<lambda>s. idle st \<longrightarrow> t = idle_thread s)\<rbrace>
  set_thread_state t st \<lbrace>\<lambda>_. only_idle\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def)
  done

lemma sts_fault_tcbs_valid_states:
  "\<lbrace>fault_tcbs_valid_states_except_set TS and
    (\<lambda>s. \<not> fault_tcb_states st \<longrightarrow> fault_tcb_at ((=) None) t s)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. fault_tcbs_valid_states_except_set TS\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply wpsimp
  apply (auto simp: fault_tcbs_valid_states_except_set_def pred_tcb_at_def
                    obj_at_def get_tcb_rev)
  done

lemma sts_fault_tcbs_valid_states_except_set':
  "\<lbrace>fault_tcbs_valid_states_except_set {t} and
    (\<lambda>s. \<not> fault_tcb_states st \<longrightarrow> fault_tcb_at ((=) None) t s)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. fault_tcbs_valid_states\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply wpsimp+
  apply (auto simp: fault_tcbs_valid_states_except_set_def pred_tcb_at_def obj_at_def get_tcb_rev)
  done

lemma sts_fault_tcbs_valid_states_except_set:
  "\<lbrace>fault_tcbs_valid_states_except_set {t} and K (fault_tcb_states st)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. fault_tcbs_valid_states\<rbrace>"
  by (wpsimp wp: sts_fault_tcbs_valid_states_except_set')

lemma sbn_only_idle[wp]:
  "set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>only_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def get_tcb_def
                  split:option.splits kernel_object.splits)
  done

lemma ssc_only_idle[wp]:
  "set_tcb_obj_ref tcb_sched_context_update t ntfn \<lbrace>only_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def get_tcb_def
                  split:option.splits kernel_object.splits)
  done

lemma syt_only_idle[wp]:
  "set_tcb_obj_ref tcb_yield_to_update t ntfn \<lbrace>only_idle\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def set_object_def get_object_def)
  apply (wp, simp)
  apply (clarsimp simp: only_idle_def pred_tcb_at_def obj_at_def get_tcb_def
                  split:option.splits kernel_object.splits)
  done

lemma set_thread_state_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace>
      set_thread_state p st \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (rule pspace_in_kernel_window_atyp_lift)
   apply wp+
  done

crunch set_thread_state
  for pspace_respects_device_region[wp]: pspace_respects_device_region
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  (wp: set_object_pspace_respects_device_region simp: tcb_cap_cases_def)

lemma set_tcb_obj_ref_pspace_in_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace>
      set_tcb_obj_ref f p ntfn \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set, wp)

crunch set_tcb_obj_ref
 for pspace_respects_device_region[wp]: pspace_respects_device_region
  (wp: set_object_pspace_respects_device_region)

lemma set_bound_nofitication_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace>
      set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_in_kernel_window
                ball_tcb_cap_casesI)+

lemma set_tcb_sched_context_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update p ntfn \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_in_kernel_window
                ball_tcb_cap_casesI)+

lemma set_tcb_yield_to_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update p ntfn \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_in_kernel_window
                ball_tcb_cap_casesI)+

lemma set_bound_notification_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
      set_tcb_obj_ref tcb_bound_notification_update p ntfn \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_respects_device_region
                ball_tcb_cap_casesI)+

lemma set_tcb_sched_context_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
      set_tcb_obj_ref tcb_sched_context_update p ntfn \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_respects_device_region
                ball_tcb_cap_casesI)+

lemma set_tcb_yield_to_cap_refs_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace>
      set_tcb_obj_ref tcb_yield_to_update p ntfn \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  by (simp add: set_tcb_obj_ref_thread_set
           | wp thread_set_cap_refs_respects_device_region
                ball_tcb_cap_casesI)+

lemma valid_ioc_sched_act_update[simp]:
  "valid_ioc (scheduler_action_update f s) = valid_ioc s"
  by (simp add: valid_ioc_def)

crunch set_thread_state_act
 for valid_ioc[wp]: valid_ioc

lemma set_thread_state_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_thread_state t st \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_thread_state_def)
  apply (wpsimp wp: set_object_valid_ioc_caps)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

lemma set_bound_notification_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_tcb_obj_ref tcb_bound_notification_update t ntfn \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_ioc_caps, simp)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

lemma set_tcb_sched_context_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_tcb_obj_ref tcb_sched_context_update t ntfn \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_ioc_caps, simp)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

lemmas [wp] = sts.valid_arch_state sbn.valid_arch_state

lemma set_tcb_yield_to_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_tcb_obj_ref tcb_yield_to_update t ntfn \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_valid_ioc_caps, simp)
  apply (intro impI conjI, clarsimp+)
  apply (clarsimp simp: valid_ioc_def)
  apply (drule spec, drule spec, erule impE, assumption)
  apply (clarsimp simp: get_tcb_def cap_of_def tcb_cnode_map_tcb_cap_cases
                        null_filter_def cte_wp_at_cases tcb_cap_cases_def
                 split: option.splits Structures_A.kernel_object.splits
                        if_split_asm)
  done

global_interpretation set_scheduler_action: non_heap_op "set_scheduler_action a"
  by unfold_locales wp

global_interpretation set_thread_state_act: non_heap_op "set_thread_state_act t"
  by unfold_locales wp

definition replies_blocked_upd_tcb_st ::
  "thread_state \<Rightarrow> obj_ref \<Rightarrow> (obj_ref \<times> obj_ref) set \<Rightarrow> (obj_ref \<times> obj_ref) set"
  where
  "replies_blocked_upd_tcb_st st t rs_blocked \<equiv>
    {(r,t'). if t' = t then st = BlockedOnReply r else (r,t') \<in> rs_blocked}"

lemma replies_blocked_upd_tcb_st:
  "replies_blocked (s\<lparr>kheap := (kheap s)(t \<mapsto> TCB (tcb\<lparr>tcb_state := st\<rparr>))\<rparr>)
    = replies_blocked_upd_tcb_st st t (replies_blocked s)"
  by (fastforce simp: replies_blocked_upd_tcb_st_def replies_blocked_def st_tcb_at_def obj_at_def)

lemma sts_valid_replies:
  "\<lbrace> \<lambda>s. P (replies_with_sc s) (replies_blocked_upd_tcb_st st t (replies_blocked s)) \<rbrace>
    set_thread_state t st
   \<lbrace> \<lambda>rv. valid_replies_pred P \<rbrace>"
  by (rule hoare_lift_Pf2[where f=replies_with_sc, rotated]
      ; wpsimp simp: set_thread_state_def replies_blocked_upd_tcb_st
                 wp: replies_with_sc_lift set_object_wp
      ; fastforce simp: sc_replies_sc_at_def get_tcb_ko_at obj_at_def)

lemma obj_at_split:
  "obj_at P p s \<Longrightarrow> obj_at Q p s \<Longrightarrow> obj_at (\<lambda>st. P st \<and> Q st) p s"
  by (auto simp: obj_at_def)

lemma pred_tcb_at_split:
  "pred_tcb_at proj P t s \<Longrightarrow> pred_tcb_at proj Q t s \<Longrightarrow> pred_tcb_at proj (\<lambda>st. P st \<and> Q st) t s"
  by (auto simp: pred_tcb_at_def obj_at_def)

lemma pred_tcb_at_constE:
  "pred_tcb_at proj P p s \<Longrightarrow> (\<And>st. P st \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (clarsimp simp: pred_tcb_at_def obj_at_def)

lemma pred_tcb_at_eq_commute:
  "pred_tcb_at proj ((=) v) = pred_tcb_at proj (\<lambda>x. x = v)"
  by (intro ext) (auto simp: pred_tcb_at_def obj_at_def)

lemma tcb_st_refs_of_eq_BlockedOnReply:
  assumes "tcb_st_refs_of st' = tcb_st_refs_of st"
  shows "st' = BlockedOnReply reply \<longleftrightarrow> st = BlockedOnReply reply"
  using assms by (cases st'; cases st; clarsimp split: if_splits)

lemma replies_blocked_upd_tcb_st_trivial:
  assumes st: "st_tcb_at P t s"
  assumes eq: "\<And>st'. P st' \<Longrightarrow> tcb_st_refs_of st' = tcb_st_refs_of st"
  shows "replies_blocked_upd_tcb_st st t (replies_blocked s) = replies_blocked s"
proof -
  obtain tcb where
    tcb: "kheap s t = Some (TCB tcb)" and
    st': "tcb_st_refs_of (tcb_state tcb) = tcb_st_refs_of st"
    using assms by (clarsimp simp: pred_tcb_at_def obj_at_def)
  show ?thesis
    by (rule set_eqI[OF iffI]
        ; clarsimp simp: tcb tcb_st_refs_of_eq_BlockedOnReply[OF st']
                         replies_blocked_upd_tcb_st_def replies_blocked_def
                         pred_tcb_at_def obj_at_def
                  split: if_splits)
qed

lemma sts_invs_minor:
  "\<lbrace>st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = tcb_st_refs_of st) t
     and (\<lambda>s. \<not> halted st \<longrightarrow> ex_nonz_cap_to t s)
     and (\<lambda>s. t \<noteq> idle_thread s)
     and (\<lambda>s. st_tcb_at (\<lambda>st. \<not> halted st) t s \<or> halted st \<or> st = Restart)
     and (\<lambda>s. \<forall>typ. (idle_thread s, typ) \<notin> tcb_st_refs_of st)
     and K (\<not>idle st)
     and (\<lambda>s. \<not> fault_tcb_states st \<longrightarrow> fault_tcb_at ((=) None) t s)
     and invs\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ sts_only_idle sts_valid_replies sts_fault_tcbs_valid_states)
  apply (clarsimp simp: replies_blocked_upd_tcb_st_trivial)
  apply (rule conjI, simp add: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def doubleton_eq_iff
                  split: thread_state.splits if_split_asm)
  apply (thin_tac "_ \<and> _ \<and> st \<noteq> _ \<longrightarrow> _")
  apply (clarsimp elim!: rsubst[where P=sym_refs]
                 intro!: ext
                  dest!: st_tcb_at_state_refs_ofD)
  by (auto simp: get_refs_def fault_tcbs_valid_states_def split: option.splits)

lemma sts_invs_minor2':
  "\<lbrace>st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = tcb_st_refs_of st \<and> \<not> awaiting_reply st') t
    and all_invs_but_fault_tcbs and fault_tcbs_valid_states_except_set {t}
    and ex_nonz_cap_to t and (\<lambda>s. t \<noteq> idle_thread s)
    and (\<lambda>s. \<not> fault_tcb_states st \<longrightarrow> fault_tcb_at ((=) None) t s)
    and K (\<not> awaiting_reply st \<and> \<not>idle st)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ sts_only_idle sts_valid_replies
            sts_fault_tcbs_valid_states_except_set')
  apply clarsimp
  apply (intro conjI, simp add: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
    apply (clarsimp simp: valid_obj_def valid_tcb_def valid_tcb_state_def doubleton_eq_iff
                   split: thread_state.splits if_split_asm)
   apply (subst replies_blocked_upd_tcb_st_trivial, simp)
    apply (clarsimp simp: obj_at_def is_tcb pred_tcb_at_def)+
  apply (clarsimp elim!: rsubst[where P=sym_refs]
                 intro!: ext)
  apply (auto simp: state_refs_of_def get_refs_def2)
  done

lemma sts_invs_minor2:
  "\<lbrace>st_tcb_at (\<lambda>st'. tcb_st_refs_of st' = tcb_st_refs_of st \<and> \<not> awaiting_reply st') t
    and invs and ex_nonz_cap_to t and (\<lambda>s. t \<noteq> idle_thread s)
    and (\<lambda>s. \<not> fault_tcb_states st \<longrightarrow> fault_tcb_at ((=) None) t s)
    and K (\<not> awaiting_reply st \<and> \<not>idle st)\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  by (wpsimp wp: sts_invs_minor2' simp: invs_def valid_state_def valid_pspace_def)
     auto

global_interpretation set_tcb_bound_notification:
  tcb_op "set_tcb_obj_ref tcb_bound_notification_update t ntfn"
  apply unfold_locales
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (clarsimp simp: get_tcb_ko_at obj_at_def tcb_agnostic_predE)

global_interpretation set_tcb_sc:
  tcb_op "set_tcb_obj_ref tcb_sched_context_update t sc"
  apply unfold_locales
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (clarsimp simp: get_tcb_ko_at obj_at_def tcb_agnostic_predE)

global_interpretation set_tcb_yt:
  tcb_op "set_tcb_obj_ref tcb_yield_to_update t yt"
  apply unfold_locales
  apply (wpsimp simp: set_tcb_obj_ref_def wp: set_object_wp)
  by (clarsimp simp: get_tcb_ko_at obj_at_def tcb_agnostic_predE)

lemma set_tcb_bound_ntfn_valid_replies[wp]:
  "set_tcb_obj_ref tcb_bound_notification_update t sc \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma set_tcb_sc_valid_replies[wp]:
  "set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma set_tcb_yt_valid_replies[wp]:
  "set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace> valid_replies_pred P \<rbrace>"
  by (wpsimp wp: valid_replies_lift)

lemma set_tcb_bound_ntfn_fault_tcbs_valid_states[wp]:
  "set_tcb_obj_ref tcb_bound_notification_update t sc \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (wpsimp wp: fault_tcbs_valid_states_lift)

lemma set_tcb_sc_fault_tcbs_valid_states[wp]:
  "set_tcb_obj_ref tcb_sched_context_update t sc \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (wpsimp wp: fault_tcbs_valid_states_lift)

lemma set_tcb_yt_fault_tcbs_valid_states[wp]:
  "set_tcb_obj_ref tcb_yield_to_update t sc \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (wpsimp wp: fault_tcbs_valid_states_lift)

lemma sbn_invs_minor:
  "\<lbrace>bound_tcb_at (\<lambda>ntfn'. get_refs TCBBound ntfn' = get_refs TCBBound ntfn) t
    and (\<lambda>s. bound ntfn \<longrightarrow> ex_nonz_cap_to t s)
    and (\<lambda>s. t \<noteq> idle_thread s)
    and invs \<rbrace>
    set_tcb_obj_ref tcb_bound_notification_update t ntfn
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ sts_only_idle sts_fault_tcbs_valid_states)
  apply clarsimp
  apply (simp add: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
  apply (rule conjI)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def
                 split: option.splits)
  apply (erule delta_sym_refs)
   apply (clarsimp split: if_split_asm option.splits simp: state_refs_of_def)
   apply (clarsimp split: if_split_asm option.splits thread_state.split_asm
            simp: obj_at_def get_refs_def2 tcb_st_refs_of_def
            dest!: state_refs_of_elemD)
  done

lemma ssc_invs_minor:
  "\<lbrace>bound_sc_tcb_at (\<lambda>sc'. get_refs TCBSchedContext sc' = get_refs TCBSchedContext sc) t
    and (\<lambda>s. bound sc \<longrightarrow> ex_nonz_cap_to t s)
    and (\<lambda>s. t \<noteq> idle_thread s)
    and invs \<rbrace>
    set_tcb_obj_ref tcb_sched_context_update t sc
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ)
  apply (clarsimp simp: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
  apply (rule conjI)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def
                 split: option.splits)
  apply (erule delta_sym_refs)
   apply (clarsimp split: if_split_asm option.splits simp: state_refs_of_def)
   apply (clarsimp split: if_split_asm option.splits thread_state.split_asm
            simp: obj_at_def get_refs_def2 tcb_st_refs_of_def
            dest!: state_refs_of_elemD)
  done

lemma syt_invs_minor:
  "\<lbrace>bound_yt_tcb_at (\<lambda>sc'. get_refs TCBYieldTo sc' = get_refs TCBYieldTo sc) t
    and (\<lambda>s. bound sc \<longrightarrow> ex_nonz_cap_to t s)
    and (\<lambda>s. t \<noteq> idle_thread s)
    and invs \<rbrace>
    set_tcb_obj_ref tcb_yield_to_update t sc
   \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def)
  apply (wp valid_irq_node_typ)
  apply (clarsimp simp: pred_tcb_at_def, erule(1) obj_at_valid_objsE)
  apply (rule conjI)
   apply (clarsimp simp: valid_obj_def valid_tcb_def valid_bound_obj_def
                 split: option.splits)
  apply (erule delta_sym_refs)
   apply (clarsimp split: if_split_asm option.splits simp: state_refs_of_def)
   apply (clarsimp split: if_split_asm option.splits thread_state.split_asm
            simp: obj_at_def get_refs_def2 tcb_st_refs_of_def
            dest!: state_refs_of_elemD)
  done

lemma thread_set_valid_cap[wp]:
  "\<lbrace>valid_cap c\<rbrace> thread_set t p \<lbrace>\<lambda>rv. valid_cap c\<rbrace>"
  by (wp valid_cap_typ)


lemma thread_set_cte_at[wp]:
  "\<lbrace>cte_at c\<rbrace> thread_set t p \<lbrace>\<lambda>rv. cte_at c\<rbrace>"
  by (wp valid_cte_at_typ)

lemma set_thread_state_ko':
  "\<lbrace>\<lambda>s. P (ko_at obj ptr s) \<and> \<not>is_tcb obj\<rbrace>
   set_thread_state x st
   \<lbrace>\<lambda>rv s. P (ko_at obj ptr s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply wpsimp
  apply (rule bool_to_bool_cases[of P]; clarsimp simp: obj_at_def is_tcb)
  done

lemmas set_thread_state_ko =
  set_thread_state_ko'[where P=id, simplified]
  set_thread_state_ko'[where P=Not, simplified]

lemma set_tcb_obj_ref_ko:
  "\<lbrace>ko_at obj ptr and K (\<not>is_tcb obj)\<rbrace> set_tcb_obj_ref f x ntfn \<lbrace>\<lambda>rv. ko_at obj ptr\<rbrace>"
  apply (simp add: set_tcb_obj_ref_def)
  apply (wp set_object_ko, clarsimp)
  apply (drule get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def is_tcb)
  done

lemmas set_thread_state_valid_cap = set_thread_state_typ_ats(17)

crunch set_tcb_obj_ref
 for valid_cap: "valid_cap c"

crunch set_tcb_obj_ref
 for cte_at: "cte_at p"

lemma as_user_mdb [wp]:
  "\<lbrace>valid_mdb\<rbrace> as_user f t \<lbrace>\<lambda>_. valid_mdb\<rbrace>"
  apply (simp add: as_user_def split_def)
  apply (rule valid_mdb_lift)
    prefer 2
    apply wp
    apply simp
   prefer 2
   apply (simp add: set_object_def get_object_def)
   apply wpsimp
  apply (simp add: set_object_def get_object_def)
  apply wp
  apply clarsimp
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  apply (simp add: cte_wp_at_cases)
  apply (drule get_tcb_SomeD)
  apply (auto simp: tcb_cap_cases_def)
  done


lemma dmo_mapM:
  assumes "\<And>x. empty_fail (m x)"
  shows "do_machine_op (mapM m xs) = mapM (do_machine_op \<circ> m) xs"
  by (rule submonad_mapM [OF submonad_do_machine_op submonad_do_machine_op,
                             simplified]) fact+

lemma dmo_mapM_x:
  assumes "\<And>x. empty_fail (m x)"
  shows "do_machine_op (mapM_x m xs) = mapM_x (do_machine_op \<circ> m) xs"
  by (rule submonad_mapM_x [OF submonad_do_machine_op submonad_do_machine_op,
                             simplified]) fact+

lemma sts_ex_nonz_cap_to[wp]:
  "\<lbrace>ex_nonz_cap_to p\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma set_tcb_obj_ref_ex_nonz_cap_to[wp]:
  "\<lbrace>(\<lambda>s. ex_nonz_cap_to p s
      \<and> obj_at (same_caps (TCB (f (\<lambda>y. new) (the (get_tcb p s))))) p s)\<rbrace>
   set_tcb_obj_ref f p new
   \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wpsimp simp: set_tcb_obj_ref_def set_object_def get_object_def ex_cap_to_after_update)

lemma set_bound_notification_ex_nonz_cap_to[wp]:
  "\<lbrace>\<lambda>s. ex_nonz_cap_to p s\<rbrace>
   set_tcb_obj_ref tcb_bound_notification_update t new
   \<lbrace>\<lambda>_. ex_nonz_cap_to p\<rbrace>"
  by (wp ex_nonz_cap_to_pres)

lemma ct_in_state_sched_act_update[simp]:
  "ct_in_state P (scheduler_action_update f s) = ct_in_state P s"
  by (simp add: ct_in_state_def)

crunch set_thread_state_act
 for ct_in_state[wp]: "\<lambda>s. Q (ct_in_state P s)"

lemma ct_in_state_set:
  "P st \<Longrightarrow> \<lbrace>\<lambda>s. cur_thread s = t\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. ct_in_state P \<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  by (wp|simp add: ct_in_state_def pred_tcb_at_def obj_at_def)+

lemma ct_in_state_weaken:
  "\<lbrakk> ct_in_state Q s; \<And>st. Q st \<Longrightarrow> P st \<rbrakk> \<Longrightarrow> ct_in_state P s"
  by (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)

lemma set_thread_state_ct_st:
  "\<lbrace>\<lambda>s. if thread = cur_thread s then Q (P st) else Q (ct_in_state P s)\<rbrace>
   set_thread_state thread st
   \<lbrace>\<lambda>rv s. Q (ct_in_state P s)\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: ct_in_state_def pred_tcb_at_def obj_at_def)
  done

lemma sts_ctis_neq:
  "\<lbrace>\<lambda>s. (cur_thread s \<noteq> t \<or> P st) \<and> ct_in_state P s\<rbrace>
   set_thread_state t st
   \<lbrace>\<lambda>_. ct_in_state P\<rbrace>"
  by (wpsimp wp: set_thread_state_ct_st)

lemma set_thread_state_ct_in_state:
  "\<lbrace>\<lambda>s. Q (ct_in_state P s) \<and> Q (P st)\<rbrace>
   set_thread_state thread st
   \<lbrace>\<lambda>rv s. Q (ct_in_state P s)\<rbrace>"
  by (wpsimp wp: set_thread_state_ct_st)

lemma valid_running [simp]:
  "valid_tcb_state Structures_A.Running = \<top>"
  by (rule ext, simp add: valid_tcb_state_def)

lemma valid_inactive [simp]:
  "valid_tcb_state Structures_A.Inactive = \<top>"
  by (rule ext, simp add: valid_tcb_state_def)

lemma valid_restart [simp]:
  "valid_tcb_state Structures_A.Restart = \<top>"
  by (rule ext, simp add: valid_tcb_state_def)

lemma ntfn_queued_st_tcb_at:
  "\<And>P. \<lbrakk>ko_at (Notification ep) ptr s; (t, rt) \<in> ntfn_q_refs_of (ntfn_obj ep);
         valid_objs s; sym_refs (state_refs_of s);
         \<And>ref. P (Structures_A.BlockedOnNotification ref) \<rbrakk>
   \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac "ntfn_obj ep", simp_all)
  apply (frule(1) sym_refs_ko_atD)
  apply (clarsimp)
  apply (erule_tac y="(t,NTFNSignal)" in my_BallE)
   apply (clarsimp simp: pred_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

lemma ep_queued_st_tcb_at:
  "\<And>P. \<lbrakk>ko_at (Endpoint ep) ptr s; (t, rt) \<in> ep_q_refs_of ep;
         valid_objs s; sym_refs (state_refs_of s);
         \<And>ref pl r data. P (Structures_A.BlockedOnSend ref pl) \<and>
                         P (Structures_A.BlockedOnReceive ref r data) \<rbrakk>
    \<Longrightarrow> st_tcb_at P t s"
  apply (case_tac ep, simp_all)
  apply (frule(1) sym_refs_ko_atD, clarsimp, erule (1) my_BallE,
         clarsimp simp: pred_tcb_at_def refs_of_rev elim!: obj_at_weakenE)+
  done

lemma bound_sc_tcb_bound_sc_at:
  "\<lbrakk>sym_refs (state_refs_of s); valid_objs s; kheap s scptr = Some (SchedContext sc a);
    bound_sc_tcb_at (\<lambda>ptr. ptr = (Some scptr)) tcbptr s \<rbrakk>
  \<Longrightarrow> sc_tcb sc = Some tcbptr"
  apply (drule_tac x=tcbptr in sym_refsD[rotated])
   apply (fastforce simp: state_refs_of_def pred_tcb_at_def obj_at_def)
  apply (auto simp: pred_tcb_at_def obj_at_def valid_obj_def valid_sched_context_def
                    is_tcb state_refs_of_def refs_of_rev
          simp del: refs_of_simps)
  done

lemma thread_set_ct_in_state:
  "(\<And>tcb. tcb_state (f tcb) = tcb_state tcb) \<Longrightarrow>
  \<lbrace>ct_in_state st\<rbrace> thread_set f t \<lbrace>\<lambda>rv. ct_in_state st\<rbrace>"
  apply (simp add: ct_in_state_def)
  apply (rule hoare_lift_Pf [where f=cur_thread])
   apply (wp thread_set_no_change_tcb_state; simp)
  apply (simp add: thread_set_def set_object_def get_object_def)
  apply wp
  apply simp
  done


lemmas thread_set_caps_of_state_trivial2
  = thread_set_caps_of_state_trivial [OF ball_tcb_cap_casesI]

lemmas sts_typ_ats = abs_typ_at_lifts [OF set_thread_state_typ_at]


lemma sts_tcb_ko_at:
  "\<lbrace>\<lambda>s. \<forall>v'. v = (if t = t' then v' \<lparr>tcb_state := ts\<rparr> else v')
              \<longrightarrow> ko_at (TCB v') t' s \<longrightarrow> P v\<rbrace>
      set_thread_state t ts
   \<lbrace>\<lambda>rv s. ko_at (TCB v) t' s \<longrightarrow> P v\<rbrace>"
  apply (simp add: set_thread_state_def set_object_def get_object_def)
  apply (wp|simp)+
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done


lemma sts_tcb_cap_valid_cases:
  "\<lbrace>\<lambda>s. (t = t' \<longrightarrow> (case tcb_cap_cases ref of
                         None \<Rightarrow> True
                       | Some (getF, setF, restr) \<Rightarrow> restr t ts cap)
                   \<and> (ref = tcb_cnode_index 2 \<longrightarrow>
                        (\<forall>tcb. ko_at (TCB tcb) t' s \<longrightarrow>
                             valid_ipc_buffer_cap cap (tcb_ipc_buffer tcb)))) \<and>
        (t \<noteq> t' \<longrightarrow> tcb_cap_valid cap (t', ref) s)\<rbrace>
   set_thread_state t ts
   \<lbrace>\<lambda>_ s. tcb_cap_valid cap (t', ref) s\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: tcb_cap_valid_def tcb_at_typ)
   apply (subst imp_conv_disj)
   apply (wp hoare_vcg_disj_lift sts_st_tcb_at_cases
             hoare_vcg_const_imp_lift sts_tcb_ko_at
             hoare_vcg_all_lift)
  apply (clarsimp simp: tcb_at_typ tcb_cap_valid_def split: option.split)
  done


lemmas set_mrs_redux =
   set_mrs_def bind_assoc[symmetric]
   thread_set_def[simplified, symmetric]

locale TcbAcc_AI_arch_tcb_context_get_eq =
    assumes arch_tcb_context_get_eq[simp]:
      "\<And> t uc. arch_tcb_context_get (arch_tcb_context_set uc t) = uc"

locale TcbAcc_AI
  = TcbAcc_AI_storeWord_invs state_ext_t
  + TcbAcc_AI_valid_ipc_buffer_cap_0 state_ext_t
  + TcbAcc_AI_get_cap_valid_ipc state_ext_t
  + TcbAcc_AI_st_tcb_at_cap_wp_at state_ext_t
  + TcbAcc_AI_arch_tcb_context_set_eq
  + TcbAcc_AI_arch_tcb_context_get_eq
  for state_ext_t :: "'state_ext::state_ext itself"


context TcbAcc_AI begin

lemma as_user_invs[wp]: "\<lbrace>invs:: 'state_ext state \<Rightarrow> bool\<rbrace> as_user t m \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule as_user_wp_thread_set_helper)
  apply (rule hoare_pre)
  apply (wp thread_set_invs_trivial ball_tcb_cap_casesI | simp)+
  done

lemma set_mrs_invs[wp]:
  "\<And>receiver recv_buf mrs.
    \<lbrace> invs and tcb_at receiver :: 'state_ext state \<Rightarrow> bool \<rbrace>
      set_mrs receiver recv_buf mrs
    \<lbrace>\<lambda>rv. invs \<rbrace>"
  by (wpsimp wp: mapM_wp' storeWord_invs thread_set_invs_trivial hoare_vcg_imp_lift
           simp: set_mrs_redux zipWithM_x_mapM store_word_offs_def ran_tcb_cap_cases
      split_del: if_split)

crunch thread_set_domain, thread_set_priority
  for valid_arch_state[wp]: "valid_arch_state :: 'state_ext state \<Rightarrow> _"
  (simp: tcb_cap_cases_def)

end


lemma set_mrs_thread_set_dmo:
  assumes ts: "\<And>c. \<lbrace>P\<rbrace> thread_set (\<lambda>tcb. tcb\<lparr>tcb_arch := arch_tcb_set_registers (c tcb) (tcb_arch tcb)\<rparr>) r \<lbrace>\<lambda>rv. Q\<rbrace>"
  assumes dmo: "\<And>x y. \<lbrace>Q\<rbrace> do_machine_op (storeWord x y) \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> set_mrs r t mrs \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: set_mrs_redux)
  apply (case_tac t)
   apply simp
   apply (wp ts)
  apply (simp add: zipWithM_x_mapM store_word_offs_def split_def
              split del: if_split)
  apply (wpsimp wp: ts mapM_wp' dmo)
  done

lemma set_mrs_pred_tcb_at [wp]:
  "set_mrs r t' mrs \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  apply (rule set_mrs_thread_set_dmo)
   apply (rule thread_set_no_change_tcb_pred_gen)
   apply (simp add: tcb_to_itcb_def)
  apply wp
  done

lemma get_tcb_ko_atD:
  "get_tcb t s = Some tcb \<Longrightarrow> ko_at (TCB tcb) t s"
  by auto

lemma live_tcb_domain_update[simp]:
  "live (TCB (tcb_domain_update f t)) = live (TCB t)"
  by (simp add: live_def)

lemma live_tcb_priority_update[simp]:
  "live (TCB (tcb_priority_update f t)) = live (TCB t)"
  by (simp add: live_def)

context TcbAcc_AI_valid_ipc_buffer_cap_0 begin

crunch thread_set_domain, thread_set_priority
  for aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
  and valid_irq_states[wp]: valid_irq_states
  and pspace_in_kernel_window[wp]: pspace_in_kernel_window
  and pspace_respects_device_region[wp]: pspace_respects_device_region
  and cur_tcb[wp]: cur_tcb
  and cur_sc_tcb[wp]: cur_sc_tcb
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and cap_refs_in_kernel_window[wp]: cap_refs_in_kernel_window
  and cap_refs_respects_device_region[wp]: cap_refs_respects_device_region
  and only_idle[wp]: only_idle
  and valid_arch_state[wp]: "valid_arch_state ::'state_ext state \<Rightarrow> _"
  and valid_global_objs[wp]: valid_global_objs
  and valid_kernel_mappings[wp]: valid_kernel_mappings
  and equal_kernel_mappings[wp]: equal_kernel_mappings
  and valid_global_vspace_mappings[wp]: valid_global_vspace_mappings
  and valid_vspace_objs[wp]: valid_vspace_objs
  and valid_machine_state[wp]: valid_machine_state
  and valid_asid_map[wp]: valid_asid_map
  and global_refs[wp]: "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps simp: crunch_simps tcb_cap_cases_def)

lemmas thread_set_domain_typ_ats[wp] = abs_typ_at_lifts[OF thread_set_domain_typ_at]
lemmas thread_set_priority_typ_ats[wp] = abs_typ_at_lifts[OF thread_set_priority_typ_at]

lemma thread_set_domain_caps_of_state[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def set_object_def get_object_def
  apply wpsimp
  apply (erule rsubst[of P])
  apply (rule cte_wp_caps_of_lift)
  apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_cte_wp_at[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (cte_wp_at Q p s)\<rbrace>"
  by (wpsimp simp: cte_wp_at_caps_of_state)

lemma thread_set_domain_valid_objs[wp]:
  "thread_set_domain t d \<lbrace>valid_objs\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply (wpsimp wp: set_object_valid_objs)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (drule (1) bspec)
  by (auto simp: tcb_cap_cases_def)

lemma thread_set_domain_if_live_then_nonz_cap[wp]:
  "thread_set_domain t d \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply wpsimp
  apply (auto simp: if_live_then_nonz_cap_def obj_at_def tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_zombies_final[wp]:
  "thread_set_domain t d \<lbrace>zombies_final\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def) auto

lemma thread_set_domain_refs_of[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def set_object_def get_object_def
  apply (wpsimp simp: state_refs_of_def)
  apply (erule rsubst[of P])
  apply (rule ext)
  apply (clarsimp split: option.splits dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_hyp_refs_of[wp]:
  "thread_set_domain t d \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding thread_set_domain_def thread_set_def set_object_def get_object_def
  supply fun_upd_apply [simp del]
  apply wpsimp
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  apply (subst state_hyp_refs_of_tcb_domain_update; auto simp: get_tcb_def)
  done

lemma thread_set_domain_valid_idle[wp]:
  "thread_set_domain t d \<lbrace>valid_idle\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  apply wpsimp
  apply (auto simp: obj_at_def valid_idle_def pred_tcb_at_def dest!: get_tcb_SomeD)
  done

lemma thread_set_domain_if_unsafe_then_cap[wp]:
  "thread_set_domain t d \<lbrace>if_unsafe_then_cap\<rbrace>"
  unfolding thread_set_domain_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def) auto

lemma thread_set_domain_valid_irq_node[wp]:
  "thread_set_domain t d \<lbrace>valid_irq_node\<rbrace>"
  apply (wpsimp simp: valid_irq_node_def wp: hoare_vcg_all_lift)
   apply (rule hoare_lift_Pf[where f="interrupt_irq_node"]; wp cap_table_at_typ_at)
  apply simp
  done

lemma thread_set_domain_valid_irq_handlers[wp]:
  "thread_set_domain t d \<lbrace>valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_lift_Pf[where f="caps_of_state"]; wp)
  done

lemma thread_set_domain_valid_arch_caps[wp]:
  "thread_set_domain t d \<lbrace>valid_arch_caps\<rbrace>"
  unfolding thread_set_domain_def
  by (wpsimp wp: thread_set_arch_caps_trivial simp: tcb_cap_cases_def) auto

global_interpretation thread_set_domain: tcb_op "thread_set_domain t d"
  by (simp add: thread_set_domain_def thread_set.tcb_op_axioms)

lemma thread_set_domain_valid_replies[wp]:
  "thread_set_domain t d \<lbrace> valid_replies_pred P \<rbrace>"
  by (simp add: thread_set_domain_def thread_set_valid_replies_trivial)

lemma thread_set_domain_fault_tcbs_valid_states[wp]:
  "thread_set_domain t d \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (simp add: thread_set_domain_def thread_set_fault_tcbs_valid_states_trivial)

lemma thread_set_domain_invs[wp]:
  "thread_set_domain t d \<lbrace>invs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_mdb_lift hoare_vcg_all_lift hoare_vcg_imp_lift
           simp: valid_ioc_def valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)

lemma thread_set_priority_caps_of_state[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def set_object_def get_object_def
  apply wpsimp
  apply (erule rsubst[of P])
  apply (rule cte_wp_caps_of_lift)
  apply (clarsimp simp: cte_wp_at_cases tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_cte_wp_at[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (cte_wp_at Q p s)\<rbrace>"
  by (wpsimp simp: cte_wp_at_caps_of_state)

lemma thread_set_priority_valid_objs[wp]:
  "thread_set_priority t d \<lbrace>valid_objs\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply (wpsimp wp: set_object_valid_objs)
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  apply (erule (1) pspace_valid_objsE)
  apply (clarsimp simp: valid_obj_def valid_tcb_def)
  apply (drule (1) bspec)
  by (auto simp: tcb_cap_cases_def)

lemma thread_set_priority_if_live_then_nonz_cap[wp]:
  "thread_set_priority t d \<lbrace>if_live_then_nonz_cap\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply wpsimp
  apply (auto simp: if_live_then_nonz_cap_def obj_at_def tcb_cap_cases_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_zombies_final[wp]:
  "thread_set_priority t d \<lbrace>zombies_final\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def) auto

lemma thread_set_priority_refs_of[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def set_object_def get_object_def
  apply (wpsimp simp: state_refs_of_def)
  apply (erule rsubst[of P])
  apply (rule ext)
  apply (clarsimp split: option.splits dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_hyp_refs_of[wp]:
  "thread_set_priority t d \<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>"
  unfolding thread_set_priority_def thread_set_def set_object_def get_object_def
  supply fun_upd_apply [simp del]
  apply wpsimp
  apply (clarsimp elim!: rsubst[where P=P] dest!: get_tcb_SomeD)
  apply (subst state_hyp_refs_of_tcb_priority_update; auto simp: get_tcb_def)
  done

lemma thread_set_priority_valid_idle[wp]:
  "thread_set_priority t d \<lbrace>valid_idle\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  apply wpsimp
  apply (auto simp: obj_at_def valid_idle_def pred_tcb_at_def dest!: get_tcb_SomeD)
  done

lemma thread_set_priority_if_unsafe_then_cap[wp]:
  "thread_set_priority t d \<lbrace>if_unsafe_then_cap\<rbrace>"
  unfolding thread_set_priority_def thread_set_def
  by (wpsimp simp: tcb_cap_cases_def) auto

lemma thread_set_priority_valid_irq_node[wp]:
  "thread_set_priority t d \<lbrace>valid_irq_node\<rbrace>"
  apply (wpsimp simp: valid_irq_node_def wp: hoare_vcg_all_lift)
   apply (rule hoare_lift_Pf[where f="interrupt_irq_node"]; wp cap_table_at_typ_at)
  apply simp
  done

lemma thread_set_priority_valid_irq_handlers[wp]:
  "thread_set_priority t d \<lbrace>valid_irq_handlers\<rbrace>"
  apply (wpsimp simp: valid_irq_handlers_def irq_issued_def)
  apply (rule hoare_lift_Pf[where f="caps_of_state"]; wp)
  done

lemma thread_set_priority_valid_arch_caps[wp]:
  "thread_set_priority t d \<lbrace>valid_arch_caps\<rbrace>"
  unfolding thread_set_priority_def
  by (wpsimp wp: thread_set_arch_caps_trivial simp: tcb_cap_cases_def) auto

global_interpretation thread_set_priority: tcb_op "thread_set_priority t p"
  by (simp add: thread_set_priority_def thread_set.tcb_op_axioms)

lemma thread_set_priority_valid_replies[wp]:
  "thread_set_priority t d \<lbrace> valid_replies_pred P \<rbrace>"
  by (simp add: thread_set_priority_def thread_set_valid_replies_trivial)

lemma thread_set_priority_fault_tcbs_valid_states[wp]:
  "thread_set_priority t d \<lbrace> fault_tcbs_valid_states \<rbrace>"
  by (simp add: thread_set_priority_def thread_set_fault_tcbs_valid_states_trivial)

lemma thread_set_priority_invs[wp]:
  "thread_set_priority t d \<lbrace>invs :: 'state_ext state \<Rightarrow> _\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  by (wpsimp wp: valid_mdb_lift hoare_vcg_all_lift hoare_vcg_imp_lift
           simp: valid_ioc_def valid_global_refs_def valid_refs_def cte_wp_at_caps_of_state)

end

lemma gts_wp:
  "\<lbrace>\<lambda>s. \<forall>st. st_tcb_at ((=) st) t s \<longrightarrow> P st s\<rbrace> get_thread_state t \<lbrace>P\<rbrace>"
  unfolding get_thread_state_def
  by (wpsimp wp: thread_get_wp' simp: pred_tcb_at_def obj_at_def)

lemma replies_blocked_upd_tcb_st_not_BlockedonReply:
  "\<lbrakk>kheap s t = Some (TCB tcb); \<not> is_blocked_on_reply (tcb_state tcb);
    \<not> is_blocked_on_reply st\<rbrakk> \<Longrightarrow>
  replies_blocked_upd_tcb_st st t (replies_blocked s) = replies_blocked s"
  apply (rule set_eqI[OF iffI])
   apply (clarsimp simp: replies_blocked_upd_tcb_st_def split: if_splits)
  apply (clarsimp simp: replies_blocked_upd_tcb_st_def replies_blocked_def
                        pred_tcb_at_def obj_at_def)
  done

global_interpretation set_thread_state: non_sc_op "set_thread_state t st"
  by unfold_locales (wpsimp simp: sc_at_pred_n_def wp: sts_obj_at_impossible')

text \<open>set_thread_state_act and possible_switch_to invariants\<close>

lemma (in pspace_update_eq) ex_nonz_cap_to_update[iff]:
  "ex_nonz_cap_to p (f s) = ex_nonz_cap_to p s"
  by (simp add: ex_nonz_cap_to_def)

crunch set_thread_state_act, tcb_sched_action, reschedule_required, possible_switch_to
  for aligned[wp]: pspace_aligned
  and it[wp]: "\<lambda>s. P (idle_thread s)"
  and distinct[wp]: pspace_distinct
  and tcb_at[wp]: "\<lambda>s. P (tcb_at tptr s)"
  and pred_tcb_at[wp]: "\<lambda>s. Q (pred_tcb_at proj P tptr s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  and no_revokable[wp]: "\<lambda>s. P (is_original_cap s)"
  and valid_irq_states[wp]: "valid_irq_states"
  and pspace_in_kernel_window[wp]: "pspace_in_kernel_window"
  and pspace_respects_device_region[wp]: "pspace_respects_device_region"
  and cur_tcb[wp]: "cur_tcb"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  and interrupt_states[wp]: "\<lambda>s. P (interrupt_states s)"
  and valid_objs[wp]: valid_objs
  and iflive[wp]: "if_live_then_nonz_cap"
  and nonz_cap_to[wp]: "ex_nonz_cap_to p"
  and valid_mdb[wp]: valid_mdb
  and zombies[wp]: zombies_final
  and valid_irq_handlers[wp]: "valid_irq_handlers"
  and valid_ioc[wp]: "valid_ioc"
  and valid_idle[wp]: valid_idle
  and cap_refs_in_kernel_window[wp]: "cap_refs_in_kernel_window"
  and cap_refs_respects_device_region[wp]: "cap_refs_respects_device_region"
  and valid_arch[wp]: "valid_arch_state"
  and ifunsafe[wp]: "if_unsafe_then_cap"
  and only_idle[wp]: "only_idle"
  and valid_global_objs[wp]: "valid_global_objs"
  and valid_global_vspace_mappings[wp]: "valid_global_vspace_mappings"
  and valid_arch_caps[wp]: "valid_arch_caps"
  and v_ker_map[wp]: "valid_kernel_mappings"
  and equal_mappings[wp]: "equal_kernel_mappings"
  and vms[wp]: "valid_machine_state"
  and valid_vspace_objs[wp]: "valid_vspace_objs"
  and valid_global_refs[wp]: "valid_global_refs"
  and valid_asid_map[wp]: "valid_asid_map"
  and state_hyp_refs_of[wp]: "\<lambda>s. P (state_hyp_refs_of s)"
  and state_refs_of[wp]: "\<lambda>s. P (state_refs_of s)"
  and cte_wp_at[wp]: "cte_wp_at P c"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and arch_state[wp]: "\<lambda>s. P (arch_state s)"
  and aligned[wp]: pspace_aligned
  and distinct[wp]: pspace_distinct
  and valid_objs[wp]: valid_objs
  and cte_wp_at[wp]: "cte_wp_at P c"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and no_cdt[wp]: "\<lambda>s. P (cdt s)"
  (simp: Let_def Let_def
   wp: hoare_drop_imps hoare_vcg_if_lift2 mapM_wp)

crunch arch_thread_get
  for inv[wp]: "P"

lemma arch_thread_get_wp:
  "\<lbrace>\<lambda>s. \<forall>tcb. ko_at (TCB tcb) t s \<longrightarrow> Q (f (tcb_arch tcb)) s\<rbrace> arch_thread_get f t \<lbrace>Q\<rbrace>"
  apply (wpsimp simp: arch_thread_get_def)
  apply (auto dest!: get_tcb_ko_atD)
  done

lemma arch_thread_get_obj_at:
  "\<lbrace>\<top>\<rbrace>
   arch_thread_get f p
   \<lbrace>\<lambda>rv s. \<exists>t. obj_at (\<lambda>tcb. tcb = (TCB t) \<and> rv = f (tcb_arch t)) p s\<rbrace>"
  apply (simp add: arch_thread_get_def)
  apply wp
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

lemma arch_thread_set_is_thread_set:
  "arch_thread_set f t = thread_set (tcb_arch_update f) t"
  by (simp add: thread_set_def arch_thread_set_def cong: tcb.fold_congs)

(* arch_thread_set invariants *)
lemma arch_thread_set_wp:
  "\<lbrace>\<lambda>s. get_tcb p s \<noteq> None \<longrightarrow>
          Q (s\<lparr>kheap := (kheap s)(p \<mapsto> TCB (the (get_tcb p s)\<lparr>tcb_arch := f (tcb_arch (the (get_tcb p s)))\<rparr>))\<rparr>)\<rbrace>
   arch_thread_set f p
   \<lbrace>\<lambda>_. Q\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_wp)
  apply simp
  done

lemma arch_thread_set_caps_of_state[wp]:
  "arch_thread_set f t \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  apply (wpsimp simp: arch_thread_set_def wp: set_object_wp)
  apply (clarsimp simp: fun_upd_def)
  apply (frule get_tcb_ko_atD)
  apply (auto simp: caps_of_state_after_update obj_at_def tcb_cap_cases_def)
  done

lemma arch_thread_set_final_cap[wp]:
  "arch_thread_set f t \<lbrace>is_final_cap' cap\<rbrace>"
  by (wpsimp simp: is_final_cap'_def2 cte_wp_at_caps_of_state)

crunch arch_thread_set
  for typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps set_object_typ_at)

lemmas arch_thread_set_typ_ats[wp] = abs_typ_at_lifts[OF arch_thread_set_typ_at]

interpretation
  arch_thread_set: non_aobj_non_cap_non_mem_op "arch_thread_set f t"
  by (unfold_locales;
        ((wpsimp)?;
        wpsimp wp: set_object_non_arch simp: non_arch_objs arch_thread_set_def)?)

lemma arch_thread_set_cur_tcb[wp]:
  "arch_thread_set f t \<lbrace>cur_tcb\<rbrace>"
  unfolding cur_tcb_def[abs_def]
  apply (rule hoare_lift_Pf [where f=cur_thread])
   apply (simp add: tcb_at_typ)
   apply wp
  apply (simp add: arch_thread_set_def)
  apply (wp hoare_drop_imp)
  apply simp
  done

lemma cte_wp_at_update_some_tcb:
  "\<lbrakk>kheap s v = Some (TCB tcb) ; tcb_cnode_map tcb = tcb_cnode_map (f tcb)\<rbrakk>
  \<Longrightarrow> cte_wp_at P p (s\<lparr>kheap := (kheap s)(v \<mapsto> TCB (f tcb))\<rparr>) = cte_wp_at P p s"
  apply (clarsimp simp: cte_wp_at_cases2 dest!: get_tcb_SomeD)
  done

lemma arch_tcb_update_aux2:
  "(\<lambda>tcb. tcb\<lparr> tcb_arch := f (tcb_arch tcb) \<rparr>) = tcb_arch_update f"
  by (rule ext, simp)

lemma arch_tcb_update_aux3:
  "tcb\<lparr>tcb_arch := f (tcb_arch tcb)\<rparr> = tcb_arch_update f tcb"
  by (simp)

lemma arch_thread_set_cap_refs_respects_device_region[wp]:
  "arch_thread_set f t \<lbrace>cap_refs_respects_device_region\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp dest!: get_tcb_SomeD simp del: fun_upd_apply)
  apply (subst cap_refs_respects_region_cong)
    prefer 3
    apply assumption
   apply (rule cte_wp_caps_of_lift)
   apply (subst arch_tcb_update_aux3)
   apply (rule_tac cte_wp_at_update_some_tcb, assumption)
   apply (simp add: tcb_cnode_map_def)+
  done

lemma arch_thread_set_pspace_respects_device_region[wp]:
  "arch_thread_set f t \<lbrace>pspace_respects_device_region\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp get_object_wp set_object_pspace_respects_device_region)
  apply clarsimp
  done

lemma arch_thread_set_cap_refs_in_kernel_window[wp]:
  "arch_thread_set f t \<lbrace>cap_refs_in_kernel_window\<rbrace>"
  unfolding cap_refs_in_kernel_window_def[abs_def]
  apply (rule hoare_lift_Pf [where f="\<lambda>s. not_kernel_window s"])
  apply (rule valid_refs_cte_lift)
  apply wp+
  done

crunch arch_thread_set
  for valid_irq_states[wp]: valid_irq_states
  and interrupt_state[wp]: "\<lambda>s. P (interrupt_states s)"
  and interrupt_irq_node[wp]: "\<lambda>s. P (interrupt_irq_node s)"
  and idle_thread[wp]: "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas arch_thread_set_valid_irq_handlers[wp]
  = valid_irq_handlers_lift[OF arch_thread_set.caps arch_thread_set_interrupt_state]

lemmas arch_thread_set_valid_irq_node[wp]
  = valid_irq_node_typ[OF arch_thread_set_typ_at arch_thread_set_interrupt_irq_node]

lemma arch_thread_set_valid_global_refs[wp]:
  "arch_thread_set f t \<lbrace>valid_global_refs\<rbrace>"
  by (rule valid_global_refs_cte_lift) wp+

lemma arch_thread_set_pred_tcb_at[wp_unsafe]:
  "\<lbrace>pred_tcb_at proj P t and K (proj_not_field proj tcb_arch_update)\<rbrace>
   arch_thread_set f t'
   \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp: pred_tcb_at_def obj_at_def get_tcb_rev
                  dest!: get_tcb_SomeD)
  done

lemma arch_thread_set_if_unsafe_then_cap[wp]:
  "arch_thread_set f t \<lbrace>if_unsafe_then_cap\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp get_object_wp set_object_ifunsafe)
  apply (clarsimp simp: ran_tcb_cap_cases)
  done

lemma arch_thread_set_only_idle[wp]:
  "arch_thread_set f t \<lbrace>only_idle\<rbrace>"
  by (wpsimp wp: only_idle_lift arch_thread_set_pred_tcb_at)

lemma arch_thread_set_valid_ioc[wp]:
  "arch_thread_set f t \<lbrace>valid_ioc\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def get_object_def)
  apply (wp set_object_valid_ioc_caps)
  apply (clarsimp simp add: valid_ioc_def
                  simp del: fun_upd_apply
                  dest!: get_tcb_SomeD)
  apply (subst arch_tcb_update_aux3)
  apply (subst cte_wp_at_update_some_tcb,assumption)
   apply (clarsimp simp: tcb_cnode_map_def)+
  done

lemma arch_thread_set_valid_mdb[wp]:
  "arch_thread_set f t \<lbrace>valid_mdb\<rbrace>"
  by (wpsimp wp: valid_mdb_lift get_object_wp simp: arch_thread_set_def)

lemma arch_thread_set_zombies_final[wp]:
  "arch_thread_set f t \<lbrace>zombies_final\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp get_object_wp set_object_zombies)
  apply (clarsimp dest!: get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def tcb_cap_cases_def)
  done

lemma arch_thread_set_if_live_then_nonz_cap':
  "\<forall>y. hyp_live (TCB (y\<lparr>tcb_arch := f (tcb_arch y)\<rparr>)) \<longrightarrow> hyp_live (TCB y) \<Longrightarrow>
   \<lbrace>if_live_then_nonz_cap\<rbrace> arch_thread_set f t \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_iflive)
  apply (clarsimp simp: ex_nonz_cap_to_def if_live_then_nonz_cap_def
                  dest!: get_tcb_SomeD)
  apply (clarsimp simp: obj_at_def tcb_cap_cases_def)
  apply (erule_tac x=t in allE, drule mp; assumption?)
  apply (clarsimp simp: live_def)
  done

lemma arch_thread_set_valid_idle':
  "\<lbrace>valid_idle and
    (\<lambda>s. t \<noteq> idle_thread s \<or>
         (\<forall>atcb. valid_arch_idle (arch_tcb_to_iarch_tcb atcb) \<longrightarrow>
                   valid_arch_idle (arch_tcb_to_iarch_tcb (f atcb))))\<rbrace>
   arch_thread_set f t
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  by (wpsimp wp: arch_thread_set_wp
           simp: valid_idle_def get_tcb_def pred_tcb_at_def obj_at_def)

lemma arch_thread_set_valid_objs':
  "\<lbrace>\<lambda>s. valid_objs s \<and> (\<forall>atcb. valid_arch_tcb atcb s \<longrightarrow> valid_arch_tcb (f atcb) s)\<rbrace>
   arch_thread_set f t
   \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_valid_objs)
  apply (clarsimp simp: Ball_def obj_at_def valid_objs_def dest!: get_tcb_SomeD)
  apply (erule_tac x=t in allE)
  apply (clarsimp simp: dom_def)
  apply (clarsimp simp:valid_obj_def valid_tcb_def tcb_cap_cases_def)
  done

lemma arch_thread_set_valid_objs_context[wp]:
  "arch_thread_set (arch_tcb_context_set uc) t \<lbrace>valid_objs\<rbrace>"
  by (wpsimp wp: arch_thread_set_valid_objs')

lemma arch_thread_set_pspace_in_kernel_window[wp]:
  "arch_thread_set f t \<lbrace>pspace_in_kernel_window\<rbrace>"
  by (rule pspace_in_kernel_window_atyp_lift, wp+)

lemma arch_thread_set_pspace_distinct[wp]:
  "arch_thread_set f t\<lbrace>pspace_distinct\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_distinct)
  apply (clarsimp simp: get_object_def obj_at_def
                  dest!: get_tcb_SomeD)
  done

lemma arch_thread_set_pspace_aligned[wp]:
  "arch_thread_set f t \<lbrace>pspace_aligned\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_aligned)
  apply (clarsimp simp: obj_at_def get_object_def
                  dest!: get_tcb_SomeD)
  done

lemma sym_refs_update_some_tcb:
  "\<lbrakk>kheap s v = Some (TCB tcb) ; refs_of (TCB tcb) = refs_of (TCB (f tcb))\<rbrakk>
  \<Longrightarrow> sym_refs (state_refs_of (s\<lparr>kheap := (kheap s)(v \<mapsto> TCB (f tcb))\<rparr>)) = sym_refs (state_refs_of s)"
  apply (rule_tac f=sym_refs in arg_cong)
  apply (rule all_ext)
  apply (clarsimp simp: sym_refs_def state_refs_of_def)
  done

lemma arch_thread_sym_refs[wp]:
  "arch_thread_set f t \<lbrace>\<lambda>s. sym_refs (state_refs_of s)\<rbrace>"
  apply (simp add: arch_thread_set_def set_object_def get_object_def)
  apply wp
  apply (clarsimp simp del: fun_upd_apply dest!: get_tcb_SomeD)
  apply (subst arch_tcb_update_aux3)
  apply (subst sym_refs_update_some_tcb[where f="tcb_arch_update f"])
    apply assumption
   apply (clarsimp simp: refs_of_def)
  apply assumption
  done

lemma arch_thread_set_cte_wp_at[wp]:
  "arch_thread_set f t \<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: arch_thread_set_def)
  apply (wp set_object_wp)
  apply (clarsimp dest!: get_tcb_SomeD simp del: fun_upd_apply)
  apply (subst arch_tcb_update_aux3)
  apply (subst cte_wp_at_update_some_tcb[where f="tcb_arch_update f"])
    apply (clarsimp simp: tcb_cnode_map_def)+
  done

lemma arch_thread_set_inv_neq:
  "\<lbrace>obj_at P p and K (t \<noteq> p)\<rbrace> arch_thread_set f t \<lbrace>\<lambda>rv. obj_at P p\<rbrace>"
  unfolding arch_thread_set_def by (wpsimp wp: set_object_wp) (simp add: obj_at_def)

lemma caps_of_state_tcb_arch_update:
  "ko_at (TCB y) t' s \<Longrightarrow> caps_of_state (s\<lparr>kheap := (kheap s)(t' \<mapsto> TCB (y\<lparr>tcb_arch := f (tcb_arch y)\<rparr>))\<rparr>) = caps_of_state s"
  by (rule ext) (auto simp: caps_of_state_cte_wp_at cte_wp_at_cases obj_at_def tcb_cap_cases_def)

lemma arch_thread_set_ex_nonz_cap_to[wp]:
  "arch_thread_set f t' \<lbrace>ex_nonz_cap_to t\<rbrace>"
  apply (wp arch_thread_set_wp)
  apply clarsimp
  apply (clarsimp simp: ex_nonz_cap_to_def get_tcb_Some_ko_at cte_wp_at_caps_of_state
                        caps_of_state_tcb_arch_update)
  done

crunch arch_thread_set
  for scheduler_action[wp]: "\<lambda>s. P (scheduler_action s)"
  and cur_domain[wp]: "\<lambda>s. P (cur_domain s)"
  and ready_queues[wp]: "\<lambda>s. P (ready_queues s)"
  and exst[wp]: "\<lambda>s. P (exst s)"
  (wp: set_object_wp)

end
