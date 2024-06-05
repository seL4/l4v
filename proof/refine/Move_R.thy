(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Arch generic lemmas that should be moved into theory files before Refine *)

theory Move_R
imports
  "AInvs.ArchDetSchedSchedule_AI"

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

lemma caps_of_state_kheap_ekheap[simp]:
  "caps_of_state (kheap_update f (ekheap_update ef s))
     = caps_of_state (kheap_update f s)"
  apply (simp add: trans_state_update[symmetric] del: trans_state_update)
  done

end
