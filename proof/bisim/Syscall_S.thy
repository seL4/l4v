(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Syscall_S
imports Separation
begin

context begin interpretation Arch . (*FIXME: arch-split*)

lemma syscall_bisim:
  assumes bs:
    "bisim (fr \<oplus> r_flt_rel) P P' m_flt m_flt'"
    "\<And>flt flt'. fr flt flt' \<Longrightarrow>
        bisim r (P_flt flt) (P'_flt flt') (h_flt flt) (h_flt' flt')"
    "\<And>rv rv'. r_flt_rel rv rv' \<Longrightarrow>
        bisim (ser \<oplus> r_err_rel rv rv')
               (P_no_flt rv) (P'_no_flt rv')
               (m_err rv) (m_err' rv')"
    "\<And>rv rv' err err'. \<lbrakk>r_flt_rel rv rv'; ser err err'\<rbrakk>
     \<Longrightarrow> bisim r (P_err rv err)
            (P'_err rv' err') (h_err err) (h_err' err')"
    "\<And>rvf rvf' rve rve'. \<lbrakk>r_flt_rel rvf rvf'; r_err_rel rvf rvf' rve rve'\<rbrakk>
     \<Longrightarrow> bisim (f \<oplus> r)
           (P_no_err rvf rve) (P'_no_err rvf' rve')
           (m_fin rve) (m_fin' rve')"
  assumes wp:  "\<And>rv.  \<lbrace>Q_no_flt rv\<rbrace>   m_err rv   \<lbrace>P_no_err rv\<rbrace>,  \<lbrace>P_err rv\<rbrace>"
               "\<And>rv'. \<lbrace>Q'_no_flt rv'\<rbrace> m_err' rv' \<lbrace>P'_no_err rv'\<rbrace>,\<lbrace>P'_err rv'\<rbrace>"
               "\<lbrace>Q\<rbrace> m_flt \<lbrace>\<lambda>rv. P_no_flt rv and Q_no_flt rv\<rbrace>, \<lbrace>P_flt\<rbrace>"
               "\<lbrace>Q'\<rbrace> m_flt' \<lbrace>\<lambda>rv. P'_no_flt rv and Q'_no_flt rv\<rbrace>, \<lbrace>P'_flt\<rbrace>"

  shows "bisim (f \<oplus> r) (P and Q) (P' and Q')
           (syscall m_flt  h_flt m_err h_err m_fin)
           (syscall m_flt' h_flt' m_err' h_err' m_fin')"
  apply (simp add: syscall_def liftE_bindE)
  apply (rule bisim_split_bind_case_sum)
      apply (rule bs)
     apply simp
     apply (rule bs)
     apply simp
    apply (simp add: liftE_bindE)
    apply (rule bisim_split_bind_case_sum)
        apply (erule bs)
       apply simp
       apply (erule bs)
       apply simp
      apply (erule(1) bs)
     apply (rule wp)+
  done

lemma dc_refl: "dc r r" by simp


lemma bisim_catch_faults_r:
  assumes bs: "\<And>x. bisim_underlying sr r P (P' x) a (m x)"
  and    flt: "\<lbrace>S\<rbrace> b \<lbrace>\<lambda>_ _. False\<rbrace>, \<lbrace>P'\<rbrace>"
  and   pure: "\<And>s. \<lbrace>S' and (=) s\<rbrace> b \<lbrace>\<lambda>_. (=) s\<rbrace>"
  and     db: "not_empty Pd b"
  shows "bisim_underlying sr r P (S and S' and Pd) a (b <catch> m)"
  unfolding catch_def
  apply (rule bisim_symb_exec_r [OF _ flt [unfolded validE_def] pure db] )
  apply (case_tac x)
   apply simp
   apply (rule bs)
   apply simp
   apply (rule bisim_underlyingI, simp_all)[1]
  done

lemma bisim_validE_R:
  assumes ac: "bisim_underlying (=) (dc \<oplus> (=)) P P' a a'"
  and     rl: "\<lbrace>Q\<rbrace> a \<lbrace>S\<rbrace>, -"
  shows   "\<lbrace>P and P' and Q\<rbrace> a' \<lbrace>S\<rbrace>, -"
  using ac rl
  unfolding  bisim_underlying_def valid_def validE_def validE_R_def
  by (fastforce simp: split_def split: sum.splits)

lemma bisim_validE_R2:
  assumes ac: "bisim_underlying (=) (=) P P' a a'"
  and     rl: "\<lbrace>Q\<rbrace> a' \<lbrace>S\<rbrace>, -"
  shows   "\<lbrace>P and P' and Q\<rbrace> a \<lbrace>S\<rbrace>, -"
  using ac rl
  unfolding  bisim_underlying_def valid_def validE_def validE_R_def
  by (fastforce simp: split_def split: sum.splits)


lemma bisim_rab:
  "bisim (dc \<oplus> (=)) \<top> (\<lambda>s. separate_cnode_cap (caps_of_state s) cap \<and> valid_cap cap s)
                       (doE
                            _ \<leftarrow> whenE (length cref < word_bits) (throwError undefined);
                            case cap of
                                 CNodeCap p bits guard \<Rightarrow> if guard \<le> cref then
                                                             returnOk ((p, take bits (drop (length guard) cref)), drop (bits + length guard) cref)
                                                          else
                                                             (throwError undefined)
                                | _ \<Rightarrow> throwError undefined
                        odE)
                      (resolve_address_bits (cap, cref))"
  using resolve_address_bits'.simps[simp]
  unfolding resolve_address_bits_def
  apply (cases "length cref < word_bits")
   apply (auto intro!: bisim_underlyingI
               elim!: separate_cnode_capE
               simp: whenE_def in_monad Bex_def in_bindE word_bits_def in_get_cap_cte_wp_at cte_wp_at_caps_of_state
               simp del: add_is_0 split: if_split_asm)[1]
  apply simp
  apply (rule bisim_underlyingI)
   apply (clarsimp )
   apply (erule separate_cnode_capE)
    apply (fastforce simp: word_bits_def in_monad )
     apply (case_tac "\<not> guard \<le> cref")
    apply (clarsimp simp: in_monad Bex_def)
 apply (drule (2) valid_sep_cap_not_cnode [where cref = cref])
    apply simp
   apply (fastforce simp: in_monad Bex_def in_bindE word_bits_def in_get_cap_cte_wp_at cte_wp_at_caps_of_state whenE_def
               simp del: add_is_0 split: if_split_asm)
  apply clarsimp
  apply (erule separate_cnode_capE)
   apply (fastforce simp: word_bits_def in_monad)
  apply (drule (2) valid_sep_cap_not_cnode [where cref = cref])
   apply simp
  apply (fastforce simp: in_monad Bex_def in_bindE word_bits_def in_get_cap_cte_wp_at cte_wp_at_caps_of_state whenE_def
              simp del: add_is_0 split: if_split_asm)
  done


lemma lsft_sep:
  "\<lbrace>separate_state and valid_objs\<rbrace> lookup_slot_for_thread tcb cptr \<lbrace>\<lambda>rv s. \<forall>cap. caps_of_state s (fst rv) = Some cap \<longrightarrow> separate_cap cap\<rbrace>, -"
  unfolding lookup_slot_for_thread_def
  apply wp
  apply (rule bisim_validE_R)
  apply (rule bisim_rab)
  apply (wpc | wp whenE_throwError_wp)+
  apply (fastforce elim: separate_cnode_capE dest: separate_state_get_tcbD objs_valid_tcb_ctable)
  done

lemma get_cap_wp':
  "\<lbrace>\<lambda>s. \<forall>cap. caps_of_state s p = Some cap \<longrightarrow> Q cap s\<rbrace> get_cap p \<lbrace>Q\<rbrace>"
  apply (wp get_cap_wp)
  apply (simp add: cte_wp_at_caps_of_state)
  done

lemma lc_sep [wp]:
  "\<lbrace>separate_state and valid_objs \<rbrace> lookup_cap tcb cptr \<lbrace>\<lambda>cap _. separate_cap cap\<rbrace>, -"
  unfolding lookup_cap_def
  apply (simp add: split_def)
  apply (rule hoare_pre)
   apply (wp get_cap_wp' lsft_sep)
  apply simp
  done


lemma not_empty_thread_get [wp]:
  "not_empty (tcb_at p) (thread_get f p)"
  unfolding thread_get_def
  apply (rule not_empty_guard_imp)
  apply (simp add: gets_the_def bind_assoc)
  apply wp
  apply (simp add: tcb_at_def)
  done

lemma not_empty_throwError [wp]:
  "not_empty \<top> (throwError e)"
  unfolding not_empty_def throwError_def by (fastforce simp: return_def)

lemma not_empty_cap_fault_on_failure [wp]:
  assumes d: "not_empty P m"
  shows "not_empty P (cap_fault_on_failure a b m)"
  unfolding cap_fault_on_failure_def
  apply (simp add: handleE_def handleE'_def)
  apply (rule not_empty_guard_imp)
  apply (wp d | wpc | simp)+
  done

lemma not_empty_splitE [wp_split]:
  assumes da: "not_empty Pa a"
  and     db: "\<And>x. not_empty (Pb x) (b x)"
  and      v: "\<lbrace>Pb'\<rbrace> a \<lbrace>Pb\<rbrace>, -"
  shows "not_empty (Pa and Pb') (a >>=E b)"
  using v
  apply (clarsimp simp: bindE_def validE_R_def validE_def)
  apply (rule not_empty_split [OF da])
  apply (rule not_empty_lift [OF db])
  apply (erule hoare_post_imp [rotated])
  apply (clarsimp split: sum.splits)
  done

lemma not_empty_whenE_throwError [wp]:
  "not_empty \<top> (whenE P (throwError e))"
  by (simp add: whenE_def throwError_def return_def not_empty_def returnOk_def)

lemma not_empty_returnOk [wp]:
  "not_empty \<top> (returnOk v)"
  by (simp add: return_def not_empty_def returnOk_def)

lemma not_empty_if [wp_split]:
  "\<lbrakk> not_empty Pt m; not_empty Pf m' \<rbrakk> \<Longrightarrow> not_empty (\<lambda>s. (b \<longrightarrow> Pt s) \<and> ( \<not> b \<longrightarrow> Pf s)) (if b then m else m')"
  by clarsimp

lemma not_empty_lsft:
  shows "not_empty (tcb_at t and valid_objs and separate_state) (lookup_slot_for_thread t cptr)"
  unfolding lookup_slot_for_thread_def
  apply (simp add: gets_the_def bind_assoc)
  apply (rule not_empty_guard_imp)
  apply (wp bisim_not_empty [OF bisim_rab] | wpc)+
  apply (fastforce simp: tcb_at_def elim: separate_cnode_capE dest: separate_state_get_tcbD objs_valid_tcb_ctable)
  done

lemma not_empty_get_cap [wp]:
  "not_empty (cte_at p) (get_cap p)"
  unfolding not_empty_def
  by (clarsimp simp: cte_at_def)

lemma not_empty_lc:
  shows "not_empty (tcb_at t and valid_objs and separate_state) (lookup_cap t cptr)"
  unfolding lookup_cap_def
  apply (simp add: split_def)
  apply (rule not_empty_guard_imp)
  apply (wp not_empty_lsft)
  apply simp
  done

lemma not_empty_get [wp]:
  "not_empty \<top> get"
  unfolding not_empty_def get_def by simp

lemma not_empty_put [wp]:
  "not_empty \<top> (put s)"
  unfolding not_empty_def put_def by simp

lemma not_empty_assert [wp]:
  "not_empty (\<lambda>s. C) (assert C)"
  by (clarsimp simp: assert_def not_empty_def return_def)

lemma not_empty_get_object [wp]:
  "not_empty (\<lambda>s. kheap s p \<noteq> None) (get_object p)"
  unfolding get_object_def
  apply (rule not_empty_guard_imp)
   apply wpsimp+
  done

lemma not_empty_set_object [wp]:
  "not_empty (\<lambda>s. typ_at (a_type v) p s) (set_object p v)"
  unfolding set_object_def
  apply (rule not_empty_guard_imp)
   apply (wpsimp wp: get_object_wp)
  apply (clarsimp simp: obj_at_def)
  done

lemma not_empty_assert_opt [wp]:
  "not_empty (\<lambda>_. v \<noteq> None) (assert_opt v)"
  unfolding not_empty_def assert_opt_def
  by (clarsimp simp: return_def)

lemma not_empty_thread_set [wp]:
  "not_empty (tcb_at p) (thread_set f p)"
  unfolding thread_set_def
  apply (simp add: gets_the_def bind_assoc)
  apply (rule not_empty_guard_imp)
   apply wp
  apply (clarsimp simp: tcb_at_def)
  done

lemma not_empty_False:
  "not_empty (\<lambda>_. False) m"
  unfolding not_empty_def by simp

lemma not_empty_gen_asm:
  assumes ne: "P \<Longrightarrow> not_empty R m"
  shows "not_empty (R and (\<lambda>_. P)) m"
  using ne unfolding not_empty_def by auto

lemmas bisim_refl' = bisim_refl [where P = \<top> and P' = \<top> and R = "(=)", OF refl]

lemma send_fault_ipc_bisim:
  "bisim (=) \<top> (tcb_at tcb and valid_objs and separate_state)
   (set_thread_state tcb Inactive) (send_fault_ipc tcb flt' <catch> handle_double_fault tcb flt')"
  unfolding send_fault_ipc_def
  apply (rule bisim_guard_imp)
    apply (rule bisim_catch_faults_r [where S = "separate_state and valid_objs"])
       apply (clarsimp simp: handle_double_fault_def)
       apply (rule bisim_refl')
      apply (simp add: Let_def)
      apply (rule bindE_wp)
       apply (rule bindE_wp)
        apply (wpc; wp)
       apply wp
       apply simp
       apply (rule hoare_strengthen_postE_R [OF lc_sep])
       apply (clarsimp simp: separate_cap_def)
      apply (wp | simp add: Let_def)+
        apply (rule_tac P = "separate_cap handler_cap" in hoare_gen_asmE')
        apply (erule separate_capE, simp_all)[1]
         apply (wp | simp)+
       apply (wp not_empty_lc)
      apply (rule_tac P = "separate_cap xa" in not_empty_gen_asm)
      apply (erule separate_capE, simp_all)[1]
       apply wpsimp+
  done

lemma handle_fault_bisim:
  "bisim (=) \<top> (separate_state and tcb_at tcb and valid_objs) (handle_fault tcb flt) (Ipc_A.handle_fault tcb flt')"
  unfolding handle_fault_def Ipc_A.handle_fault_def
  apply (rule bisim_guard_imp)
    apply (rule bisim_symb_exec_r [where Pe = \<top>])
       apply simp
       apply (rule send_fault_ipc_bisim)
      apply (wpsimp simp: gets_the_def tcb_at_def)+
  done

lemmas bisim_throwError_dc = bisim_throwError [where f = dc, OF dc_refl]

lemma bisim_returnOk:
  "R a b \<Longrightarrow> bisim (f \<oplus> R) \<top> \<top> (returnOk a) (returnOk b)"
  apply (simp add: returnOk_def)
  apply (rule bisim_return)
  apply simp
  done

lemma bisim_liftME_same:
  assumes bs: "bisim (f \<oplus> (=)) P P' m m'"
  shows "bisim (f \<oplus> (=)) P P' (liftME g m) (liftME g m')"
  unfolding liftME_def
  apply (rule bisim_guard_imp)
    apply (rule bisim_splitE [OF bs])
      apply simp
      apply (rule bisim_returnOk)
      apply simp
     apply wp+
   apply simp+
  done

lemma bisim_split_if:
  "\<lbrakk> P \<Longrightarrow> bisim R Pt Pt' a a'; \<not> P \<Longrightarrow> bisim R Pf Pf' b b' \<rbrakk> \<Longrightarrow>
     bisim R (\<lambda>s. (P \<longrightarrow> Pt s) \<and> (\<not> P \<longrightarrow> Pf s)) (\<lambda>s. (P \<longrightarrow> Pt' s) \<and> (\<not> P \<longrightarrow> Pf' s))
                                               (if P then a else b) (if P then a' else b')"
  by simp

lemma bisim_reflE:
  "bisim ((=) \<oplus> (=)) \<top> \<top> a a"
  apply (rule bisim_underlyingI)
   apply (case_tac r, fastforce+)[1]
  apply (case_tac r', fastforce+)[1]
  done

lemma bisim_reflE_dc:
  "bisim (dc \<oplus> (=)) \<top> \<top> a a"
  apply (rule bisim_underlyingI)
   apply (case_tac r, fastforce+)[1]
  apply (case_tac r', fastforce+)[1]
  done

lemma decode_invocation_bisim:
  "bisim ((=) \<oplus> (=)) \<top> (K (separate_cap cap))
     (decode_invocation a b c d cap f) (Decode_A.decode_invocation a b c d cap f)"
  unfolding decode_invocation_def Decode_A.decode_invocation_def
  apply (rule bisim_guard_imp)
    apply (rule bisim_separate_cap_cases [where cap = cap])
      apply (simp split del: if_split)
      apply (rule bisim_throwError, simp)
     apply (simp split del: if_split)
     apply (rule bisim_reflE)
    apply (fastforce intro!: bisim_throwError bisim_returnOk simp: AllowRecv_def AllowSend_def)
   apply simp
  done

abbreviation
  "separate_inv c \<equiv> \<exists>ptr badge. c = InvokeNotification ptr badge"

lemma perform_invocation_bisim:
  "bisim (dc \<oplus> (=)) \<top> (\<top> and K (separate_inv c))
  (perform_invocation a b c) (Syscall_A.perform_invocation a b c)"
  apply (rule bisim_gen_asm_r)
    apply clarsimp
    apply (rule bisim_reflE_dc)
  done

lemmas bisim_split_reflE_eq = bisim_split_reflE [where R = "(=)" and f = "(=)", OF _ _ _ refl refl]
lemmas bisim_split_reflE_dc = bisim_split_reflE [where R = "(=)" and f = "dc", OF _ _ _ dc_refl refl]

lemma decode_separate_inv:
  "\<lbrace>\<top> and K ((\<forall>c \<in> set f. separate_cap (fst c)) \<and> (separate_cap cap))\<rbrace> Decode_A.decode_invocation a b c d cap f  \<lbrace>\<lambda>rv s. separate_inv rv\<rbrace>, -"
  unfolding Decode_A.decode_invocation_def
  apply (rule hoare_gen_asmE)
  apply clarify
  apply (erule separate_capE, simp_all split del: if_split)
    apply (rule hoare_pre, (wp | simp add: comp_def)+)[1]
   apply (rule hoare_pre)
   apply (wp | simp)+
done

lemma lcas_sep [wp]:
  "\<lbrace>separate_state and valid_objs\<rbrace> lookup_cap_and_slot t v \<lbrace>\<lambda>rv s. separate_cap (fst rv)\<rbrace>, -"
  apply (simp add: lookup_cap_and_slot_def split_def bind_assoc)
  apply (rule hoare_pre)
   apply (wp lsft_sep get_cap_wp'|simp)+
  done

lemma lec_separate_caps:
  "\<lbrace>separate_state and valid_objs\<rbrace> lookup_extra_caps t buffer ra \<lbrace>\<lambda>rv s. (\<forall>c\<in>set rv. separate_cap (fst c))\<rbrace>, -"
  unfolding lookup_extra_caps_def
  apply (wp mapME_set | simp)+
  done

lemma handle_invocation_bisim:
  "bisim (dc \<oplus> (=)) \<top> (separate_state and valid_objs and cur_tcb) (handle_invocation c b) (Syscall_A.handle_invocation c b)"
  unfolding handle_invocation_def Syscall_A.handle_invocation_def
  apply (simp add: split_def)
  apply (rule bisim_guard_imp)
    apply (rule bisim_split_reflE_dc)+
          apply (rule syscall_bisim)
                  apply (rule bisim_split_reflE_dc [where Q = "\<lambda>_. \<top>" and Q' = "\<lambda>_. \<top>"])+
                        apply (rule bisim_reflE_dc)
                       apply wp+
                 apply (rule bisim_when [OF _ refl])
                 apply (rule handle_fault_bisim)
                apply simp
                apply (rule bisim_split_reflE_eq)
                  apply (rule decode_invocation_bisim)
                 apply wp+
               apply (simp, rule bisim_refl')
              apply simp
              apply (rule bisim_split_reflE_dc)
                apply (rule bisim_splitE_req)
                   apply (rule perform_invocation_bisim)
                  apply simp
                  apply (rule bisim_refl')
                 apply (wp | simp)+
             apply (rule decode_separate_inv)
            apply (wp lec_separate_caps | simp add: cur_tcb_def)+
  done

lemma bisim_split_catch:
  assumes bm: "bisim (f' \<oplus> r) Pn Pn' m m'"
  and     bc: "\<And>x x'. f' x x' \<Longrightarrow> bisim r (Pf x) (Pf' x') (c x) (c' x')"
  and     v1: "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>Pf\<rbrace>"
  and     v2: "\<lbrace>P'\<rbrace> m' \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>Pf'\<rbrace>"
  shows "bisim r (Pn and P) (Pn' and P') (m <catch> c) (m' <catch> c')"
  unfolding catch_def
  apply (rule bisim_split [where Q = "\<lambda>r s. case_sum (\<lambda>l. Pf l s) (\<lambda>_. True) r" and Q' = "\<lambda>r s. case_sum (\<lambda>l. Pf' l s) (\<lambda>_. True) r", OF bm, folded validE_def])
    apply (case_tac ra)
     apply clarsimp
     apply (erule bc)
    apply clarsimp
    apply (rule bisim_return')
    apply simp
   apply (rule v1)
  apply (rule v2)
  done

lemma rel_sum_comb_eq:
  "((=) \<oplus> (=)) = (=)"
  apply (rule ext, rule ext)
  apply (case_tac x)
  apply auto
  done

lemma bisim_split_catch_req:
  assumes bm: "bisim ((=) \<oplus> (=)) Pn Pn' m m'"
  and     bc: "\<And>x. bisim (=) (Pf x) (Pf' x) (c x) (c' x)"
  and     v1: "\<lbrace>P\<rbrace> m \<lbrace>\<lambda>_ _. True\<rbrace>, \<lbrace>\<lambda>r. Pf r and Pf' r\<rbrace>"
  shows "bisim (=) (Pn and P) Pn' (m <catch> c) (m' <catch> c')"
  unfolding catch_def
  apply (rule bisim_split_req [where Q = "\<lambda>r s. case_sum (\<lambda>l. Pf l s) (\<lambda>_. True) r" and Q' = "\<lambda>r s. case_sum (\<lambda>l. Pf' l s) (\<lambda>_. True) r"])
  apply (rule bm [simplified rel_sum_comb_eq])
  apply (case_tac r)
     apply clarsimp
     apply (rule bc)
    apply clarsimp
    apply (rule bisim_return')
    apply simp
  apply (rule hoare_post_imp [OF _ v1 [unfolded validE_def]])
  apply (clarsimp split: sum.split_asm)
  done

lemma bisim_injection:
  assumes x: "t = injection_handler fn"
  assumes y: "t' = injection_handler fn'"
  assumes z: "\<And>ft ft'. f' ft ft' \<Longrightarrow> f (fn ft) (fn' ft')"
  shows      "bisim (f' \<oplus> r) P P' m m'
     \<Longrightarrow> bisim (f \<oplus> r) P P' (t m) (t' m')"
  apply (simp add: injection_handler_def handleE'_def x y)
  apply (rule bisim_guard_imp)
    apply (erule bisim_split)
      apply (case_tac ra, clarsimp+)[1]
       apply (rule bisim_throwError)
       apply (simp add: z)
      apply clarsimp
      apply (rule bisim_return)
      apply wpsimp+
  done

lemma separate_cap_NullCap [simp]: "separate_cap NullCap" by (simp add: separate_cap_def)

lemma set_cap_NullCap_separate_state [wp]:
  "\<lbrace>separate_state\<rbrace> set_cap NullCap cptr \<lbrace>\<lambda>_. separate_state\<rbrace>"
  unfolding separate_state_def separate_tcb_def separate_cnode_cap_def
  apply (simp add: tcb_at_typ)
  apply (rule hoare_pre)
   apply wps
   apply (wp set_cap_typ_at hoare_vcg_all_lift)
  apply (clarsimp simp: separate_cap_def)
  apply (drule spec, drule (1) mp)
  apply (clarsimp split: cap.splits option.splits)
  done

lemma separate_state_pres:
  assumes rl: "(\<And>P t p. \<lbrace>\<lambda>s. P (typ_at t p s) (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at t p s) (caps_of_state s)\<rbrace>)"
  shows  "\<lbrace>separate_state\<rbrace> f \<lbrace>\<lambda>_. separate_state\<rbrace>"
  unfolding separate_state_def[abs_def]
  apply (simp add: tcb_at_typ)
  apply (wp hoare_vcg_all_lift rl)
  done

lemma separate_state_pres':
  assumes rl: "(\<And>P t p. \<lbrace>\<lambda>s. P (typ_at t p s)\<rbrace> f \<lbrace>\<lambda>_ s. P (typ_at t p s)\<rbrace>)"
  "(\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>)"
  shows  "\<lbrace>separate_state\<rbrace> f \<lbrace>\<lambda>_. separate_state\<rbrace>"
  apply (rule separate_state_pres)
  apply (rule hoare_pre)
  apply (wps rl)
  apply wp
  apply simp
  done

lemma cap_delete_one_sep [wp]:
  "\<lbrace>separate_state\<rbrace> cap_delete_one cptr \<lbrace>\<lambda>_. separate_state\<rbrace>"
  unfolding cap_delete_one_def empty_slot_def post_cap_deletion_def
  by (wpsimp wp: get_cap_wp' hoare_drop_imps |
      rule separate_state_pres, rule hoare_pre, (wps set_cdt_typ_at; wp), assumption)+

lemma bisim_caller_cap:
  assumes bs: "bisim R P P' a (f NullCap)"
  shows   "bisim R P (P' and tcb_at p and separate_state) a (get_cap (p, tcb_cnode_index 3) >>= f)"
  apply (rule bisim_guard_imp)
  apply (rule bisim_symb_exec_r [where Pe = \<top>])
  apply (rule_tac F = "rv = NullCap" in bisim_gen_asm_r)
   apply simp
   apply (rule bs)
  apply (wp get_cap_wp')+
  apply fastforce
  apply wp
  apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state tcb_at_def
    caps_of_state_tcb_cap_cases dom_tcb_cap_cases
    cong: conj_cong)
  apply (drule (1) separate_state_get_tcbD)
  apply simp
  done

lemma delete_caller_cap_bisim:
  "bisim (=) \<top> (tcb_at r and separate_state) (return ()) (delete_caller_cap r)"
  unfolding delete_caller_cap_def
  apply (rule bisim_guard_imp)
  apply (simp add: cap_delete_one_def unless_when)
  apply (rule bisim_caller_cap)
  apply (simp add: when_def)
  apply (rule bisim_refl')
  apply simp_all
  done

lemma bisim_guard_imp_both:
  "\<lbrakk> bisim r P P' m m'; \<And>s. R s \<Longrightarrow> P s \<and> P' s \<rbrakk> \<Longrightarrow> bisim r \<top> R m m'"
  unfolding bisim_underlying_def by auto

lemma handle_recv_bisim:
  "bisim (=) \<top> (separate_state and cur_tcb and valid_objs) (handle_recv is_blocking) (Syscall_A.handle_recv is_blocking)"
  unfolding handle_recv_def Syscall_A.handle_recv_def
  apply (simp add: Let_def)
  apply (rule bisim_guard_imp_both)
   apply (rule bisim_split_refl)
       apply (rule bisim_split_refl)
           apply (rule bisim_split_catch_req)
              apply (simp add: cap_fault_injection)
              apply (rule bisim_injection [OF refl refl, where f' = "(=)"])
               apply simp
              apply (rule bisim_split_reflE)
                  apply (rule_tac cap = rb in bisim_separate_cap_cases)
                    apply (simp, rule bisim_throwError, rule refl)+
                   apply (simp split del: if_split)
                   apply (rule bisim_refl [where P = \<top> and P' = \<top>])
                   apply (case_tac rc, simp_all)[1]
                   apply (wp get_cap_wp' lsft_sep | simp add: lookup_cap_def split_def)+
                   apply (rule handle_fault_bisim)
                   apply (wp get_simple_ko_wp | wpc | simp)+
                   apply (rule_tac Q' = "\<lambda>_. separate_state and valid_objs and tcb_at r" in hoare_strengthen_postE_R)
                    prefer 2
                    apply simp
                   apply (wp | simp add: cur_tcb_def)+
  done

lemma handle_reply_bisim:
  "bisim (=) \<top> (separate_state and cur_tcb) (return ()) Syscall_A.handle_reply"
  unfolding Syscall_A.handle_reply_def
  apply (rule bisim_guard_imp_both)
   apply (rule bisim_symb_exec_r [where Pe = \<top>])
      apply (rule bisim_caller_cap)
      apply simp
      apply (rule bisim_return)
      apply simp
     apply (wp | simp add: cur_tcb_def)+
  done

lemma handle_event_bisim:
  "bisim (dc \<oplus> (=)) \<top> (separate_state and cur_tcb and valid_objs) (handle_event ev) (Syscall_A.handle_event ev)"
  apply (cases ev; simp add: handle_send_def Syscall_A.handle_send_def
                             handle_call_def Syscall_A.handle_call_def
                             handle_reply_def
                        cong: syscall.case_cong)

       apply (rename_tac syscall)
       apply (case_tac syscall, simp_all)[1]

              apply (rule bisim_guard_imp_both, rule handle_invocation_bisim, simp)
             apply (rule bisim_guard_imp_both)
              apply (rule bisim_symb_exec_r_bs)
               apply (rule handle_reply_bisim)
              apply (rule handle_recv_bisim)
             apply simp

            apply (rule bisim_guard_imp_both, rule handle_invocation_bisim, simp)
           apply (rule bisim_guard_imp_both, rule handle_invocation_bisim, simp)
          apply (rule bisim_guard_imp_both, rule handle_recv_bisim, simp)
         apply (rule bisim_guard_imp_both, rule handle_reply_bisim, simp)

        apply (simp add: handle_yield_def Syscall_A.handle_yield_def)
        apply (rule bisim_guard_imp_both, rule bisim_refl', simp)

       apply (rule bisim_guard_imp_both, rule handle_recv_bisim, simp)

      apply (rule bisim_split_refl)
        apply (rule handle_fault_bisim)
       apply wp+
      apply (simp add: cur_tcb_def)

     apply (rule bisim_split_refl)
       apply (rule handle_fault_bisim)
      apply wp+
     apply (simp add: cur_tcb_def)

    apply (rule bisim_refl)
    apply simp

   apply (rename_tac vmfault_type)
   apply (rule bisim_guard_imp_both)
    apply (rule bisim_split_refl)
      apply (rule bisim_split_catch_req)
        apply (rule bisim_reflE)
       apply (rule handle_fault_bisim)
      apply (wpsimp wp: hv_inv_ex)
        apply wpsimp+
   apply (simp add: cur_tcb_def)

  apply (rule bisim_refl, simp)
  done

lemma call_kernel_bisim:
  "bisim (=) \<top> (separate_state and cur_tcb and valid_objs) (call_kernel ev) (Syscall_A.call_kernel ev)"
  unfolding call_kernel_def Syscall_A.call_kernel_def
  apply (rule bisim_guard_imp_both)
   apply simp
   apply (rule bisim_split)
      apply (rule bisim_split_handle)
         apply (rule handle_event_bisim)
        apply simp
        apply (rule bisim_refl')
       apply wp+
     apply (rule bisim_refl')
    apply wpsimp+
  done


lemma as_user_separate_state [wp]:
  "\<lbrace>separate_state\<rbrace> as_user t f \<lbrace>\<lambda>_. separate_state\<rbrace>"
  by (wp separate_state_pres')

lemma activate_thread_separate_state [wp]:
  "\<lbrace>separate_state\<rbrace> activate_thread \<lbrace>\<lambda>_. separate_state\<rbrace>"
  unfolding activate_thread_def
  by (wp separate_state_pres' | wpc | simp add: arch_activate_idle_thread_def |  strengthen imp_consequent)+

crunch schedule_choose_new_thread
  for separate_state[wp]: separate_state
  and typ_at[wp]: "\<lambda>s. P (typ_at t p s)"
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma schedule_separate_state [wp]:
  "\<lbrace>separate_state\<rbrace> schedule :: (unit,unit) s_monad \<lbrace>\<lambda>_. separate_state\<rbrace>"
  unfolding schedule_def switch_to_thread_def arch_switch_to_thread_def
            switch_to_idle_thread_def arch_switch_to_idle_thread_def
  by (wpsimp wp: select_inv separate_state_pres' gts_wp
             simp: arch_activate_idle_thread_def |
      strengthen imp_consequent)+

lemma set_message_info_sep_pres [wp]:
      "\<lbrace>\<lambda>s. P (typ_at t p s) (caps_of_state s)\<rbrace>
      set_message_info a b
      \<lbrace>\<lambda>_ s. P (typ_at t p s) (caps_of_state s)\<rbrace>"
  apply (rule hoare_pre)
  apply (wp | wpc | wps | simp )+
  done

lemma set_mrs_separate_state [wp]:
  "\<lbrace>separate_state\<rbrace> set_mrs a b c \<lbrace>\<lambda>_. separate_state\<rbrace>"
  apply (rule separate_state_pres)
  apply (rule hoare_pre)
  apply (wp | wpc | wps | simp )+
  done

lemma send_signal_separate_state [wp]:
  "\<lbrace>separate_state\<rbrace> send_signal a b \<lbrace>\<lambda>_. separate_state\<rbrace>"
  unfolding send_signal_def cancel_ipc_def
  apply (rule separate_state_pres)
  apply (rule hoare_pre)
  apply (wp gts_wp get_simple_ko_wp hoare_pre_cont[where f="reply_cancel_ipc x" for x]
        | wpc | wps
        | simp add: update_waiting_ntfn_def)+
  apply (clarsimp)
  apply (simp add: receive_blocked_def)
  apply (case_tac st; clarsimp)
  apply (clarsimp simp add: pred_tcb_at_def obj_at_def)
  done

lemma thread_set_time_slice_separate_state[wp]:
  "thread_set_time_slice t time \<lbrace>separate_state\<rbrace>"
  unfolding thread_set_time_slice_def
  apply (rule separate_state_pres)
  apply (wp_pre, wps)
   apply (wpsimp wp: separate_state_pres thread_set_caps_of_state_trivial)+
   apply (fastforce simp: ran_tcb_cap_cases)
  apply clarsimp
  done

crunch timer_tick, do_machine_op
  for separate_state[wp]: separate_state
  (wp: crunch_wps set_object_wp simp: crunch_simps)

lemma handle_interrupt_separate_state [wp]:
  "\<lbrace>separate_state\<rbrace> handle_interrupt irq \<lbrace>\<lambda>_. separate_state\<rbrace>"
  unfolding handle_interrupt_def
  apply (rule hoare_pre)
  apply (wp | wpc | wps | simp add: handle_reserved_irq_def arch_mask_irq_signal_def
         | strengthen imp_consequent)+
  done

lemma decode_invocation_separate_state [wp]:
  "\<lbrace> separate_state \<rbrace>
  Decode_SA.decode_invocation param_a param_b param_c param_d param_e param_f
  \<lbrace> \<lambda>_. separate_state \<rbrace>"
  unfolding decode_invocation_def by wpsimp

crunch set_thread_state, set_simple_ko
  for separate_state[wp]: "separate_state"
   (wp: separate_state_pres' crunch_wps simp: crunch_simps)

crunch "Syscall_SA.handle_event"
  for separate_state[wp]: "separate_state"
   (wp: crunch_wps syscall_valid
    simp: crunch_simps
    ignore: syscall)

lemma call_kernel_separate_state:
  "\<lbrace>separate_state and cur_tcb and valid_objs\<rbrace> Syscall_A.call_kernel ev :: (unit,unit) s_monad \<lbrace>\<lambda>_. separate_state\<rbrace>"
  apply (rule hoare_pre)
  apply (rule bisim_valid)
   apply (rule call_kernel_bisim)
  apply (simp add: call_kernel_def)
  apply (wp | wpc | wps | simp | strengthen imp_consequent)+
  done

end

end
