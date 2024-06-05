(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch generic lemmas that should be moved into theory files before Refine *)

theory Move_R
imports
  "AInvs.AInvs"

begin

lemma zip_map_rel:
  assumes "(x,y) \<in> set (zip xs ys)" "map f xs = map g ys"
  shows "f x = g y"
  using assms by (induct xs arbitrary: x y ys; cases ys) auto

lemma fold_K:
  "(P and (\<lambda> s. Q)) = (P and K Q)"
  by simp

(* Move to lib *)
lemmas FalseI = notE[where R=False]

(* Move to Lib *)
lemma nonempty_cross_distinct_singleton_elim:
  "\<lbrakk> x \<times> {a} = y \<times> {b};
     x \<noteq> {} \<or> y \<noteq> {};
     a \<noteq> b \<rbrakk>
   \<Longrightarrow> P"
  by blast

lemma no_other_bits_set:
  "\<lbrakk> (w::'a::len word) && ~~ (2 ^ n) = 0 ; n' \<noteq> n ; n < size w ; n' < size w \<rbrakk>
   \<Longrightarrow>  \<not> w !! n'"
  by (fastforce dest!: word_eqD simp: word_ops_nth_size word_size nth_w2p)

lemma mask_out_0:
  "\<lbrakk>x \<le> 2^n-1; n < LENGTH('a)\<rbrakk> \<Longrightarrow> (x::'a::len word) && ~~ mask n = 0"
  by (clarsimp simp: mask_out_sub_mask less_mask_eq)

lemma mask_out_first_mask_some_eq:
  "\<lbrakk> x && ~~ mask n = y && ~~ mask n; n \<le> m \<rbrakk> \<Longrightarrow> x && ~~ mask m = y && ~~ mask m"
  apply (rule word_eqI, rename_tac n')
  apply (drule_tac x=n' in word_eqD)
  apply (auto simp: word_ops_nth_size word_size)
  done

lemma unaligned_helper:
  "\<lbrakk>is_aligned x n; y\<noteq>0; y < 2 ^ n\<rbrakk> \<Longrightarrow> \<not> is_aligned (x + y) n"
  apply (simp (no_asm_simp) add: is_aligned_mask)
  apply (simp add: mask_add_aligned)
  apply (cut_tac mask_eq_iff_w2p[of n y], simp_all add: word_size)
  apply (rule ccontr)
  apply (simp add: not_less power_overflow word_bits_conv)
  done

declare word_unat_power[symmetric, simp del]

lemma oblivious_mapM_x:
  "\<forall>x\<in>set xs. oblivious f (g x) \<Longrightarrow> oblivious f (mapM_x g xs)"
  by (induct xs) (auto simp: mapM_x_Nil mapM_x_Cons oblivious_bind)

(* Should probably become part of the hoare_vgc_if_lift2 set *)
lemma hoare_vcg_if_lift3:
  "\<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (P rv s \<longrightarrow> X rv s) \<and> (\<not> P rv s \<longrightarrow> Y rv s)\<rbrace> \<Longrightarrow>
  \<lbrace>R\<rbrace> f \<lbrace>\<lambda>rv s. (if P rv s then X rv else Y rv) s\<rbrace>"
  by auto

lemmas hoare_pre_post = hoare_pre_imp[where Q="\<lambda>_. Q" and P'=Q for Q]

lemmas corres_underlying_gets_pre_rhs =
  corres_symb_exec_r[OF _ _ gets_inv no_fail_pre[OF no_fail_gets TrueI]]

lemma corres_if_r':
  "\<lbrakk> G' \<Longrightarrow> corres_underlying sr nf nf' r P P' a c; \<not>G' \<Longrightarrow> corres_underlying sr nf nf' r P Q' a d \<rbrakk>
   \<Longrightarrow> corres_underlying sr nf nf' r (P) (if G' then P' else Q')
                                     (a) (if G' then c  else d)"
  by simp

lemma valid_corres_combined:
  assumes "valid P f Q"
  assumes "corres_underlying sr False nf' rr P P' f f'"
  assumes "valid (\<lambda>s'. \<exists>s. (s,s')\<in>sr \<and> P s \<and> P' s') f' Q'" (is "valid ?P _ _")
  shows "valid ?P f' (\<lambda>r' s'. \<exists>r s. (s,s') \<in> sr \<and> Q r s \<and> Q' r' s' \<and> rr r r')"
  using assms
  by (fastforce simp: valid_def corres_underlying_def split_def)

(* Move the following 3 to Lib *)
lemma corres_noop3:
  assumes x: "\<And>s s'. \<lbrakk>P s; P' s'; (s, s') \<in> sr\<rbrakk>  \<Longrightarrow> \<lbrace>(=) s\<rbrace> f \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes y: "\<And>s s'. \<lbrakk>P s; P' s'; (s, s') \<in> sr\<rbrakk> \<Longrightarrow> \<lbrace>(=) s'\<rbrace> g \<lbrace>\<lambda>r. (=) s'\<rbrace>"
  assumes z: "nf' \<Longrightarrow> no_fail P' g"
  shows      "corres_underlying sr nf nf' dc P P' f g"
  apply (clarsimp simp: corres_underlying_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule use_exs_valid)
    apply (rule exs_hoare_post_imp)
     prefer 2
     apply (rule x)
       apply assumption+
    apply simp_all
   apply (subgoal_tac "ba = b")
    apply simp
   apply (rule sym)
   apply (rule use_valid[OF _ y], assumption+)
   apply simp
  apply (insert z)
  apply (clarsimp simp: no_fail_def)
  done

lemma corres_symb_exec_l':
  assumes z: "\<And>rv. corres_underlying sr nf nf' r (Q' rv) P' (x rv) y"
  assumes x: "\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> m \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes y: "\<lbrace>Q\<rbrace> m \<lbrace>Q'\<rbrace>"
  shows      "corres_underlying sr nf nf' r (P and Q) P' (m >>= (\<lambda>rv. x rv)) y"
  apply (rule corres_guard_imp)
    apply (subst gets_bind_ign[symmetric], rule corres_split)
       apply (rule corres_noop3)
         apply (erule x)
        apply (rule gets_wp)
       apply (rule no_fail_gets)
      apply (rule z)
     apply (rule y)
    apply (rule gets_wp)
   apply simp+
  done

lemma corres_symb_exec_r':
  assumes z: "\<And>rv. corres_underlying sr nf nf' r P (P'' rv) x (y rv)"
  assumes y: "\<lbrace>P'\<rbrace> m \<lbrace>P''\<rbrace>"
  assumes x: "\<And>s. Q' s \<Longrightarrow> \<lbrace>(=) s\<rbrace> m \<lbrace>\<lambda>r. (=) s\<rbrace>"
  assumes nf: "nf' \<Longrightarrow> no_fail R' m"
  shows      "corres_underlying sr nf nf' r P (P' and Q' and R') x (m >>= (\<lambda>rv. y rv))"
  apply (rule corres_guard_imp)
    apply (subst gets_bind_ign[symmetric], rule corres_split)
       apply (rule_tac P'="a' and a''" for a' a'' in corres_noop3)
         apply (simp add: simpler_gets_def exs_valid_def)
        apply clarsimp
        apply (erule x)
       apply (rule no_fail_pre)
        apply (erule nf)
       apply clarsimp
       apply assumption
      apply (rule z)
     apply (rule gets_wp)
    apply (rule y)
   apply simp+
  done

lemma get_mapM_x_lower:
  fixes P :: "'a option \<Rightarrow> 's \<Rightarrow> bool"
  fixes f :: "('s,'a) nondet_monad"
  fixes g :: "'a \<Rightarrow> 'b \<Rightarrow> ('s,'c) nondet_monad"
  \<comment> \<open>@{term g} preserves the state that @{term f} cares about\<close>
  assumes g: "\<And>x y. \<lbrace> P (Some x) \<rbrace> g x y \<lbrace> \<lambda>_. P (Some x) \<rbrace>"
  \<comment> \<open>@{term P} specifies whether @{term f} either fails or returns a deterministic result\<close>
  assumes f: "\<And>opt_x s. P opt_x s \<Longrightarrow> f s = case_option ({},True) (\<lambda>x. ({(x,s)},False)) opt_x"
  \<comment> \<open>Every state determines P, and therefore the behaviour of @{term f}\<close>
  assumes x: "\<And>s. \<exists> opt_x. P opt_x s"
  \<comment> \<open>If @{term f} may fail, ensure there is at least one @{term f}\<close>
  assumes y: "\<exists>s. P None s \<Longrightarrow> ys \<noteq> []"
  shows "do x \<leftarrow> f; mapM_x (g x) ys od = mapM_x (\<lambda>y. do x \<leftarrow> f; g x y od) ys"
  proof -
    have f_rv: "\<lbrace>\<top>\<rbrace> f \<lbrace>\<lambda>r. P (Some r)\<rbrace>"
      using x f
      apply (clarsimp simp: valid_def)
      apply (drule_tac x=s in meta_spec; clarsimp)
      apply (case_tac opt_x; simp)
      done
    { fix y and h :: "'a \<Rightarrow> ('s,'d) nondet_monad"
      have "do x \<leftarrow> f; _ \<leftarrow> g x y; h x od
              = do x \<leftarrow> f; _ \<leftarrow> g x y; x \<leftarrow> f; h x od"
        apply (rule ext)
        apply (subst monad_eq_split[where g="do x \<leftarrow> f; g x y; return x od"
                                      and P="\<top>" and Q="\<lambda>r. P (Some r)"
                                      and f="h" and f'="\<lambda>_. f >>= h",
                                    simplified bind_assoc, simplified])
        apply (wpsimp wp: g f_rv simp: f return_def bind_def)+
        done
    } note f_redundant = this
    show ?thesis
    proof (cases "\<exists>s. P None s")
      case True show ?thesis
        apply (cases ys; simp add: True y mapM_x_Cons bind_assoc)
        subgoal for y ys
          apply (thin_tac _)
          apply (induct ys arbitrary: y; simp add: mapM_x_Nil mapM_x_Cons bind_assoc)
          apply (subst f_redundant; simp)
          done
        done
    next
      case False
      show ?thesis using False
        apply (induct ys; simp add: mapM_x_Nil mapM_x_Cons bind_assoc)
         apply (rule ext)
         subgoal for s
           by (insert x[of s]; drule spec[of _ s]; clarsimp; case_tac opt_x;
               clarsimp simp: bind_def return_def f)
        apply (subst f_redundant; simp)
        done
    qed
  qed

(* Move to DetSchedDomainTime_AI *)
crunch do_user_op
  for domain_list_inv[wp]: "\<lambda>s. P (domain_list s)"

lemma next_child_child_set:
  "\<lbrakk>next_child slot (cdt_list s) = Some child; valid_list s\<rbrakk>
    \<Longrightarrow> child \<in> (case next_child slot (cdt_list s) of None \<Rightarrow> {} | Some n \<Rightarrow> {n})"
  by (simp add: next_child_def)

lemma cap_delete_one_cur_tcb[wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> cap_delete_one slot \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  apply (simp add: cur_tcb_def)
  apply (rule hoare_pre)
   apply wps
   apply wp
  apply simp
  done

lemma check_active_irq_invs:
  "\<lbrace>invs and (ct_running or ct_idle) and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
    and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>
   check_active_irq
   \<lbrace>\<lambda>_. invs and (ct_running or ct_idle) and valid_list and valid_sched
        and (\<lambda>s. scheduler_action s = resume_cur_thread)
        and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>"
  by (wpsimp simp: check_active_irq_def ct_in_state_def)

lemma check_active_irq_invs_just_running:
  "\<lbrace>invs and ct_running and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>
   check_active_irq
   \<lbrace>\<lambda>_. invs and ct_running and valid_list and valid_sched
        and (\<lambda>s. scheduler_action s = resume_cur_thread)
        and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>"
  by (wpsimp simp: check_active_irq_def ct_in_state_def)

lemma check_active_irq_invs_just_idle:
  "\<lbrace>invs and ct_idle and einvs and (\<lambda>s. scheduler_action s = resume_cur_thread)
      and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>
   check_active_irq
   \<lbrace>\<lambda>_. invs and ct_idle and valid_list and valid_sched
        and (\<lambda>s. scheduler_action s = resume_cur_thread)
        and (\<lambda>s. 0 < domain_time s) and valid_domain_list \<rbrace>"
  by (wpsimp simp: check_active_irq_def ct_in_state_def)

lemma sym_ref_BlockedOnReceive_RecvEP:
  "\<lbrakk> sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
   tcb_state tcb = Structures_A.BlockedOnReceive eptr ropt pl \<rbrakk> \<Longrightarrow>
     \<exists>list. kheap s eptr = Some (Structures_A.Endpoint (Structures_A.RecvEP list))"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def)
  apply (drule_tac x="(eptr, TCBBlockedRecv)" in bspec)
   apply (fastforce split: if_split_asm)
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac koa; case_tac koa;
         clarsimp simp: ep_q_refs_of_def get_refs_def2)
  apply (rename_tac ep; case_tac ep; simp)
  done

lemma sym_ref_BlockedOnSend_SendEP:
  "\<lbrakk> sym_refs (state_refs_of s); kheap s tp = Some (TCB tcb);
   tcb_state tcb = Structures_A.BlockedOnSend eptr pl \<rbrakk> \<Longrightarrow>
     \<exists>list. kheap s eptr = Some (Structures_A.Endpoint (Structures_A.SendEP list))"
  apply (drule sym_refs_obj_atD[rotated, where p=tp])
   apply (clarsimp simp: obj_at_def, simp)
  apply (clarsimp simp: state_refs_of_def)
  apply (drule_tac x="(eptr, TCBBlockedSend)" in bspec)
   apply (fastforce split: if_split_asm)
  apply (clarsimp simp: obj_at_def)
  apply (rename_tac koa; case_tac koa;
         clarsimp simp: ep_q_refs_of_def get_refs_def2)
  apply (rename_tac ep; case_tac ep; simp)
  done

lemma Receive_or_Send_ep_at:
  "\<lbrakk> st = Structures_A.thread_state.BlockedOnReceive epPtr rp p' \<or>
     st = Structures_A.thread_state.BlockedOnSend epPtr p;
     valid_objs s; st_tcb_at ((=) st) t s\<rbrakk>
        \<Longrightarrow> ep_at epPtr s"
  apply (drule (1) st_tcb_at_valid_st2)
  by (fastforce simp: obj_at_def valid_tcb_state_def)

lemma Reply_or_Receive_reply_at:
  "\<lbrakk> st = Structures_A.thread_state.BlockedOnReply rp
     \<or> st = Structures_A.thread_state.BlockedOnReceive epPtr (Some rp) p'; valid_objs s;
        st_tcb_at ((=) st) t s\<rbrakk> \<Longrightarrow> reply_at rp s"
  apply (drule (1) st_tcb_at_valid_st2)
  by (fastforce simp: obj_at_def valid_tcb_state_def)

lemma valid_tcb_state_BlockedOnReply[simp]:
  "valid_tcb_state (Structures_A.thread_state.BlockedOnReply reply_ptr) = reply_at reply_ptr"
  by (rule ext, simp add: valid_tcb_state_def)

lemma receive_blocked_equiv:
  "receive_blocked st = is_blocked_on_receive st"
  by (case_tac st; clarsimp simp: receive_blocked_def is_blocked_on_receive_def)

lemma delta_sym_refs_remove_only:
  assumes x: "sym_refs rfs'"
      and diff: "p2 \<noteq> p1"
      and y: "nr1 = Set.remove (p2, tp) (rfs' p1)"
      and z: "nr2 = Set.remove (p1, symreftype tp) (rfs' p2)"
  shows "sym_refs (\<lambda>p. if p = p1 then nr1
                  else if p = p2 then nr2
                  else rfs' p)"
  apply (rule delta_sym_refs[OF x])
  using diff by (auto simp: y z split: if_splits)

lemma subset_remove:
  "X \<subseteq> Set.remove x Y = (X \<subseteq> Y \<and> x \<notin> X)"
  apply (rule iffI; clarsimp simp: subset_eq)
  by fastforce

lemma fst_image_set_zip:
  "length xs = length ys \<Longrightarrow> fst ` set (zip xs ys) = set xs"
  by (auto simp: set_zip in_set_conv_nth image_def)

lemma thread_set_ko_not_tcb_at[wp]:
  "\<lbrace>\<lambda>s. \<not> ko_at (TCB tcb) t s \<and> (t = tptr \<longrightarrow> obj_at (\<lambda>ko. \<exists>tcb'. ko = TCB tcb' \<and> f tcb' \<noteq> tcb) tptr s)\<rbrace>
  thread_set f tptr
  \<lbrace>\<lambda>_ s. \<not> ko_at (TCB tcb) t s\<rbrace>"
  apply (wpsimp simp: thread_set_def set_object_def obj_at_def pred_neg_def
                  wp: get_object_wp)+
  apply (clarsimp simp: obj_at_def dest!: get_tcb_SomeD)
  done

lemma thread_set_valid_tcb[wp]:
  "thread_set f tptr \<lbrace>valid_tcb ptr tcb\<rbrace>"
  by (wpsimp wp: get_object_wp simp: thread_set_def)

lemma valid_BlockedOnReceive[simp]:
  "valid_tcb_state (Structures_A.thread_state.BlockedOnReceive epptr replyOpt payload)
   = (ep_at epptr and valid_bound_reply replyOpt)"
  by (rule ext, clarsimp simp: valid_tcb_state_def split: option.splits)

(* FIXME RT: move to Lib? *)
lemma case_option_ext:
  "(case_option f f' x) s = case_option (f s) (\<lambda>y. f' y s) x"
  by (case_tac x; simp)

lemma sc_at_sc_obj_at:
  "sc_at p s = (\<exists>n. sc_obj_at n p s)"
  by (auto simp: obj_at_def)

(* FIXME RT: move to KHeap_AI *)
lemma update_sched_context_decompose:
   "update_sched_context scp (\<lambda>sc. f (g sc))
    = (do update_sched_context scp g; update_sched_context scp f od)"
  apply (rule ext)
  by (clarsimp simp: update_sched_context_def get_object_def set_object_def a_type_simps
                     gets_def get_def put_def return_def fail_def assert_def bind_def
                     gets_the_def assert_opt_def
              split: Structures_A.kernel_object.splits option.splits)

(* FIXME RT: move to Lib? *)
lemma maybeM_when:
  "maybeM f x = when (x \<noteq> None) (f (the x))"
  unfolding maybeM_def
  by (clarsimp split: option.splits)

(* FIXME RT: This should replace lookup_cap_and_slot_valid_fault2 *)
lemma lookup_cap_and_slot_valid_fault3[wp]:
  "\<lbrace>invs and K (p = to_bl p')\<rbrace>
   lookup_cap_and_slot thread p
   -,\<lbrace>\<lambda>ft s. valid_fault (ExceptionTypes_A.CapFault p' rp ft)\<rbrace>"
  using lookup_cap_and_slot_valid_fault
  apply (clarsimp simp: validE_E_def validE_def valid_def
                 split: sum.splits)
  apply (drule invs_valid_objs, fastforce)
  done

(* An "excluded middle" lemma for sc_at_ppred *)
lemma sc_at_ppred_exm:
  "sc_at_ppred p P scp s = (obj_at (\<lambda>ko. \<exists>sc n. ko = SchedContext sc n) scp s \<and> \<not> sc_at_ppred p (\<lambda>x. \<not> P x) scp s)"
  by (fastforce simp: sc_at_pred_n_def obj_at_def is_sc_obj pred_neg_def)

lemma get_object_exs_valid:
  "obj_at \<top> ptr s \<Longrightarrow> \<lbrace>(=) s\<rbrace> get_object ptr \<exists>\<lbrace>\<lambda>r. (=) s\<rbrace>"
  apply (clarsimp simp: get_object_def assert_def return_def fail_def gets_def exs_valid_def get_def
                        bind_def obj_at_def gets_the_def)
  done

lemma monadic_rewrite_rewrite_head:
  "\<lbrakk>monadic_rewrite False True P f f'; monadic_rewrite False True P (f' >>= g) (h >>= j)\<rbrakk>
   \<Longrightarrow> monadic_rewrite False True P (f >>= g) (h >>= j)"
  apply (clarsimp simp: monadic_rewrite_def bind_def)
  done

lemma bind_assoc_group4:
  "(do x \<leftarrow> a; y \<leftarrow> b x; z \<leftarrow> c y; w \<leftarrow> d z; f w od)
   = (do w \<leftarrow> (do x \<leftarrow> a; y \<leftarrow> b x; z <- c y; d z od); f w od)"
  apply (simp add: bind_assoc)
  done

(* FIXME RT: move *)
lemmas update_sched_context_decompose_ext
  = update_sched_context_decompose[where f="f x" and g="g y" for f g x y]
lemmas update_sched_context_decompose2
  = update_sched_context_decompose[where g="\<lambda>sc. g (h sc)" for g h]
lemmas update_sched_context_decompose_ext2
  = update_sched_context_decompose2[where f="f x" and g="g y" for f g x y]

(* FIXME RT: move to ListLibLemmas.thy? *)
lemma hd_drop_length_2_last:
  "length list = 2 \<Longrightarrow> hd (tl list) = last list"
  apply (prop_tac "\<exists>a b. list = [a,b]")
   apply (cases list; simp)
   apply (rename_tac a lista)
   apply (case_tac lista; simp)
  apply clarsimp
  done

crunch reply_remove
  for scheduler_act_not[wp]: "scheduler_act_not tPtr"
  (wp: crunch_wps)

lemma reply_tcb_sym_refsD:
  "\<lbrakk>sym_refs (state_refs_of s);
    st_tcb_at ((=) (Structures_A.thread_state.BlockedOnReply rp1)) thread s;
    reply_tcb_reply_at (\<lambda>x. x = Some thread) rp2 s\<rbrakk>
   \<Longrightarrow> rp1 = rp2"
  apply (clarsimp simp: reply_tcb_reply_at_def)
  apply (drule (1) sym_refs_obj_atD[where p=rp2])
  apply clarsimp
  apply (clarsimp simp: get_refs_def2 obj_at_def pred_tcb_at_def)
  apply (rename_tac ko; case_tac ko; clarsimp simp: get_refs_def2)
  done

lemma ipc_queued_thread_def2:
  "ipc_queued_thread t s = (blocked_on_reply_tcb_at t s \<or> blocked_on_send_tcb_at t s \<or> blocked_on_recv_ntfn_tcb_at t s)"
  apply (case_tac "tcb_sts_of s t")
  apply (clarsimp simp: pred_map_def)
   apply (case_tac a; simp)
  apply (clarsimp simp: pred_map_def)+
  done

lemma released_ipc_queuesE1:
  "released_ipc_queues s \<Longrightarrow> ipc_queued_thread t s \<Longrightarrow> active_if_bound_sc_tcb_at t s"
  apply (clarsimp simp: released_ipc_queues_defs ipc_queued_thread_def2 released_sc_tcb_at_def)
  apply (drule_tac x=t in spec)
  by auto

lemma active_sc_at_equiv[obj_at_kh_kheap_simps]:
  "active_sc_at scPtr = is_active_sc scPtr"
  by (fastforce simp: obj_at_def pred_map_def vs_all_heap_simps)

lemma TCB_cte_wp_at_obj_at:
  "tcb_at t s \<Longrightarrow>
   (cte_wp_at P (t, n) s = obj_at (\<lambda>ko. \<exists>tcb. ko = TCB tcb \<and> case_option False P (tcb_cnode_map tcb n)) t s)"
   by (fastforce dest!: singleton_eqD
                  simp: get_object_def gets_the_def gets_def get_def bind_assoc assert_opt_def in_monad
                        obj_at_def cte_wp_at_def get_cap_def is_tcb
                 split: option.splits)

end
