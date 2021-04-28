(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Retype_IF
imports CNode_IF
begin

context begin interpretation Arch . (*FIXME: arch_split*)

lemma create_cap_reads_respects:
  "reads_respects aag l (K (is_subject aag (fst (fst slot))))
     (create_cap type bits untyped dev slot)"
  apply (rule gen_asm_ev)
  apply (simp add: create_cap_def split_def bind_assoc[symmetric])
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc create_cap_ext_def)
  apply (wp set_cap_reads_respects set_original_reads_respects update_cdt_list_reads_respects update_cdt_reads_respects| simp | fastforce simp: equiv_for_def split: option.splits)+
  apply (intro impI conjI allI)
   apply (fastforce simp: reads_equiv_def2 equiv_for_def
                    elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt
                    dest: aag_can_read_self
                   split: option.splits)+
  done

lemma gets_any_evrv:
  "equiv_valid_rv_inv I A \<top>\<top> \<top> (gets f)"
  apply(clarsimp simp: equiv_valid_2_def in_monad)
  done

lemma select_f_any_evrv:
  "equiv_valid_rv_inv I A \<top>\<top> \<top> (select_f f)"
  apply(clarsimp simp: equiv_valid_2_def select_f_def)
  done

lemma select_f_any_ev2:
  "equiv_valid_2 I A A \<top>\<top> \<top> \<top> (select_f f) (select_f f')"
  apply(clarsimp simp: equiv_valid_2_def select_f_def)
  done

lemma machine_op_lift_ev':
  "equiv_valid_inv I A (K (\<forall> s t x y. (I s t \<longrightarrow> I (s\<lparr>machine_state_rest := x\<rparr>) (t\<lparr>machine_state_rest := y\<rparr>)) \<and> (A s t \<longrightarrow> A (s\<lparr>machine_state_rest := x\<rparr>) (t\<lparr>machine_state_rest := y\<rparr>)))) (machine_op_lift mop)"
  apply(rule gen_asm_ev)
  unfolding machine_op_lift_def comp_def machine_rest_lift_def
  apply(simp add: equiv_valid_def2)
  apply(rule equiv_valid_rv_bind)
    apply(rule gets_any_evrv)
   apply(rule_tac R'="\<top>\<top>" and Q="\<top>\<top>" and Q'="\<top>\<top>" in equiv_valid_2_bind_pre)
        apply(simp add: split_def)
        apply(rule modify_ev2)
        apply(auto)[1]
       apply(rule select_f_any_ev2)
      apply (rule wp_post_taut | simp)+
  done


lemma equiv_machine_state_machine_state_rest_update:
  "equiv_machine_state P s t \<Longrightarrow>
   equiv_machine_state P (s\<lparr> machine_state_rest := x \<rparr>) (t\<lparr> machine_state_rest := y \<rparr>)"
  by(fastforce intro: equiv_forI elim: equiv_forE)

lemma machine_op_lift_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top> (machine_op_lift mop)"
  apply (rule equiv_valid_guard_imp)
  apply (rule machine_op_lift_ev')
  apply clarsimp
  apply (intro conjI impI)
  apply (drule equiv_machine_state_machine_state_rest_update, fastforce)+
  done

lemma cacheRangeOp_ev[wp]:
  "(\<And>a b. equiv_valid_inv I A \<top> (oper a b))
    \<Longrightarrow> equiv_valid_inv I A \<top> (cacheRangeOp oper x y z)"
  apply (simp add: cacheRangeOp_def split_def)
  apply (rule mapM_x_ev)
   apply simp
  apply (rule hoare_TrueI)
  done

lemma cleanCacheRange_PoU_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top> (cleanCacheRange_PoU vstart vend pstart)"
  unfolding cleanCacheRange_PoU_def
  apply (wp machine_op_lift_ev | simp add: cleanByVA_PoU_def)+
  done

lemma modify_underlying_memory_update_0_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top>
          (modify
            (underlying_memory_update
              (\<lambda>m. m(x := word_rsplit 0 ! 3, x + 1 := word_rsplit 0 ! 2,
                     x + 2 := word_rsplit 0 ! 1, x + 3 := word_rsplit 0 ! 0))))"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad)
  apply(fastforce intro: equiv_forI elim: equiv_forE)
  done

lemma storeWord_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) \<top> (storeWord x 0)"
  unfolding storeWord_def
  apply (wp modify_underlying_memory_update_0_ev assert_inv | simp add: no_irq_def)+
  done

lemma clearMemory_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) (\<lambda>_. True) (clearMemory ptr bits)"
  unfolding clearMemory_def
  apply simp
  apply(rule equiv_valid_guard_imp)
   apply(rule bind_ev)
     apply(rule cleanCacheRange_PoU_ev)
    apply(rule mapM_x_ev[OF storeWord_ev])
    apply(rule wp_post_taut | simp)+
  done

lemma freeMemory_ev:
  "equiv_valid_inv (equiv_machine_state P) (equiv_machine_state Q) (\<lambda>_. True) (freeMemory ptr bits)"
  unfolding freeMemory_def
  apply(rule equiv_valid_guard_imp)
   apply(rule mapM_x_ev[OF storeWord_ev])
   apply(rule wp_post_taut | simp)+
  done

lemma machine_op_lift_irq_state[wp]:
  " \<lbrace>\<lambda>ms. P (irq_state ms)\<rbrace> machine_op_lift mop \<lbrace>\<lambda>_ ms. P (irq_state ms)\<rbrace>"
  apply(simp add: machine_op_lift_def machine_rest_lift_def | wp | wpc)+
  done

lemma dmo_mol_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (machine_op_lift mop))"
  apply(rule use_spec_ev)
  apply(rule do_machine_op_spec_reads_respects)
   apply(rule equiv_valid_guard_imp[OF machine_op_lift_ev])
   apply simp
  apply wp
  done

lemma dmo_bind_ev:
  "equiv_valid_inv I A P (do_machine_op (a >>= b)) = equiv_valid_inv I A P (do_machine_op a >>= (\<lambda>rv. do_machine_op (b rv)))"
  by (fastforce simp: do_machine_op_def gets_def get_def select_f_def modify_def put_def return_def bind_def equiv_valid_def2 equiv_valid_2_def)

lemma dmo_bind_ev':
  "equiv_valid_inv I A P (a >>= (\<lambda>rv. do_machine_op (b rv >>= c rv)))
    = equiv_valid_inv I A P (a >>= (\<lambda>rv. do_machine_op (b rv) >>= (\<lambda>rv'. do_machine_op (c rv rv'))))"
  by (fastforce simp: do_machine_op_def gets_def get_def select_f_def modify_def put_def return_def bind_def equiv_valid_def2 equiv_valid_2_def)

lemma dmo_mapM_ev_pre:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> do_machine_op (m x) \<lbrace> \<lambda>_. I \<rbrace>"
  assumes inv_established: "\<And> s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (do_machine_op (mapM m lst))"
  using assms
  apply(atomize)
  apply(rule_tac Q=I in equiv_valid_guard_imp)
  apply(induct lst)
    apply(simp add: mapM_Nil return_ev_pre)
   apply(subst mapM_Cons)
   apply(simp add: dmo_bind_ev dmo_bind_ev')
   apply(rule bind_ev_pre[where P''="I"])
    apply(rule bind_ev[OF return_ev])
    apply fastforce
    apply (rule wp_post_taut)
    apply fastforce+
  done

lemma dmo_mapM_x_ev_pre:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> do_machine_op (m x) \<lbrace> \<lambda>_. I \<rbrace>"
  assumes inv_established: "\<And> s. P s \<Longrightarrow> I s"
  shows "equiv_valid_inv D A P (do_machine_op (mapM_x m lst))"
  apply(subst mapM_x_mapM)
  apply(simp add: dmo_bind_ev)
  apply(rule bind_ev_pre[OF return_ev dmo_mapM_ev_pre])
  apply (blast intro: reads_res invariant inv_established wp_post_taut)+
  done

lemma dmo_mapM_ev:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> do_machine_op (m x) \<lbrace> \<lambda>_. I \<rbrace>"
  shows "equiv_valid_inv D A I (do_machine_op (mapM m lst))"
  using assms by (auto intro: dmo_mapM_ev_pre)

lemma dmo_mapM_x_ev:
  assumes reads_res: "\<And> x. x \<in> set lst \<Longrightarrow> equiv_valid_inv D A I (do_machine_op (m x))"
  assumes invariant: "\<And> x. x \<in> set lst \<Longrightarrow> \<lbrace> I \<rbrace> do_machine_op (m x) \<lbrace> \<lambda>_. I \<rbrace>"
  shows "equiv_valid_inv D A I (do_machine_op (mapM_x m lst))"
  using assms by (auto intro: dmo_mapM_x_ev_pre)

lemma dmo_cacheRangeOp_reads_respects:
  "(\<And>a b. reads_respects aag l \<top> (do_machine_op (oper a b)))
    \<Longrightarrow> reads_respects aag l \<top> (do_machine_op (cacheRangeOp oper x y z))"
  apply (simp add: cacheRangeOp_def)
  apply (rule dmo_mapM_x_ev)
   apply (simp add: split_def)
  apply (rule hoare_TrueI)
  done

lemma dmo_cleanCacheRange_PoU_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (cleanCacheRange_PoU vsrat vend pstart))"
  unfolding cleanCacheRange_PoU_def
  by(wp dmo_cacheRangeOp_reads_respects dmo_mol_reads_respects | simp add: cleanByVA_PoU_def)+

crunch irq_state[wp]: clearMemory "\<lambda>s. P (irq_state s)"
  (wp: crunch_wps simp: crunch_simps storeWord_def cleanByVA_PoU_def
   ignore_del: clearMemory)

lemma dmo_clearMemory_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (clearMemory ptr bits))"
  apply(rule use_spec_ev)
  apply(rule do_machine_op_spec_reads_respects)
   apply(rule equiv_valid_guard_imp[OF clearMemory_ev], rule TrueI)
  apply wp
  done

crunch irq_state[wp]: freeMemory "\<lambda>s. P (irq_state s)"
  (wp: crunch_wps simp: crunch_simps storeWord_def)

lemma dmo_freeMemory_reads_respects:
  "reads_respects aag l \<top> (do_machine_op (freeMemory ptr bits))"
  apply(rule use_spec_ev)
  apply(rule do_machine_op_spec_reads_respects)
   apply(rule equiv_valid_guard_imp[OF freeMemory_ev], rule TrueI)
  apply wp
  done

lemma set_pd_globals_equiv:
  "\<lbrace>globals_equiv st and (\<lambda>s. a \<noteq> arm_global_pd (arch_state s))\<rbrace> set_pd a b \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  unfolding set_pd_def
  by (wpsimp wp: set_object_globals_equiv[THEN hoare_set_object_weaken_pre]
           simp: obj_at_def)

lemma globals_equiv_cdt_update[simp]:
  "globals_equiv s (s'\<lparr> cdt := x \<rparr>) = globals_equiv s s'"
  by(fastforce simp: globals_equiv_def idle_equiv_def)

lemma globals_equiv_is_original_cap_update[simp]:
  "globals_equiv s (s'\<lparr> is_original_cap := x \<rparr>) = globals_equiv s s'"
  by(fastforce simp: globals_equiv_def idle_equiv_def)

lemma create_cap_globals_equiv:
  "\<lbrace> globals_equiv s and valid_global_objs \<rbrace> create_cap type bits untyped dev slot
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply (simp add: create_cap_def split_def)
  apply (wp set_cap_globals_equiv set_original_globals_equiv set_cdt_globals_equiv
            set_cdt_valid_global_objs dxo_wp_weak set_original_wp | simp)+
  done

lemma set_pd_reads_respects:
  "reads_respects aag l (K (is_subject aag a)) (set_pd a b)"
  unfolding set_pd_def
  by (blast intro: equiv_valid_guard_imp set_object_reads_respects)


lemma set_pd_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. is_subject aag ptr \<and> ptr \<noteq> arm_global_pd (arch_state s)) (set_pd ptr pd)"
  apply(fastforce intro: equiv_valid_guard_imp[OF reads_respects_g]
                 intro: doesnt_touch_globalsI
                        set_pd_reads_respects set_pd_globals_equiv)
  done

abbreviation reads_equiv_valid_g_inv where
"reads_equiv_valid_g_inv A aag P f \<equiv> equiv_valid_inv (reads_equiv_g aag) A P f"

lemma gets_apply_ev':
  "\<forall> s t. I s t \<and> A s t \<and> P s \<and> P t \<longrightarrow> (f s) x = (f t) x \<Longrightarrow>
   equiv_valid I A A P (gets_apply f x)"
  apply(simp add: gets_apply_def get_def bind_def return_def)
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  done

lemma get_object_arm_global_pd_revg:
  "reads_equiv_valid_g_inv A aag (\<lambda> s. p = arm_global_pd (arch_state s)) (get_object p)"
  apply(unfold get_object_def fun_app_def)
  apply(subst gets_apply)
  apply(wp gets_apply_ev')
    defer
    apply(wp hoare_drop_imps)
   apply(rule conjI)
    apply assumption
   apply simp
  apply(auto simp: reads_equiv_g_def globals_equiv_def)
  done

lemma get_pd_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag ptr)) (get_pd ptr)"
  unfolding get_pd_def
  apply(wp get_object_rev | wpc | clarsimp)+
  done

lemma get_pd_revg:
  "reads_equiv_valid_g_inv A aag (\<lambda> s. ptr = arm_global_pd (arch_state s)) (get_pd ptr)"
  unfolding get_pd_def
  apply(wp get_object_arm_global_pd_revg | wpc | clarsimp)+
  done

lemma store_pde_reads_respects:
  "reads_respects aag l (K (is_subject aag (ptr && ~~ mask pd_bits)))
                         (store_pde ptr pde)"
  unfolding store_pde_def fun_app_def
  apply(wp set_pd_reads_respects get_pd_rev)
  apply(clarsimp)
  done


lemma store_pde_globals_equiv:
  "\<lbrace> globals_equiv s and (\<lambda> s. ptr && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s)) \<rbrace>
   (store_pde ptr pde)
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  unfolding store_pde_def
  apply(wp set_pd_globals_equiv)
  apply simp
  done

lemma store_pde_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. is_subject aag (ptr && ~~ mask pd_bits) \<and> ptr && ~~ mask pd_bits \<noteq> arm_global_pd (arch_state s)) (store_pde ptr pde)"
  apply(fastforce intro: equiv_valid_guard_imp[OF reads_respects_g]
                 intro: doesnt_touch_globalsI
                        store_pde_reads_respects store_pde_globals_equiv)
  done

lemma get_pde_rev:
  "reads_equiv_valid_inv A aag (K (is_subject aag (ptr && ~~ mask pd_bits)))
                                 (get_pde ptr)"
  unfolding get_pde_def fun_app_def
  by (wpsimp wp: get_pd_rev)

lemma get_pde_revg:
  "reads_equiv_valid_g_inv A aag (\<lambda> s. (ptr && ~~ mask pd_bits) = arm_global_pd (arch_state s))
                                 (get_pde ptr)"
  unfolding get_pde_def fun_app_def
  by (wpsimp wp: get_pd_revg)

lemma copy_global_mappings_reads_respects_g:
  "is_aligned x pd_bits \<Longrightarrow>
  reads_respects_g aag l (\<lambda> s. (is_subject aag x \<and> x \<noteq> arm_global_pd (arch_state s)) \<and> pspace_aligned s \<and> valid_arch_state s) (copy_global_mappings x)"
  unfolding copy_global_mappings_def
  apply simp
  apply(rule bind_ev_pre)
     prefer 3
     apply(rule_tac Q="\<lambda> s. pspace_aligned s \<and> valid_arch_state s \<and> is_subject aag x \<and> x \<noteq> arm_global_pd (arch_state s)" in hoare_weaken_pre)
      apply(rule gets_sp)
     apply(assumption)
    apply(wp mapM_x_ev store_pde_reads_respects_g get_pde_revg)
     apply(drule subsetD[OF copy_global_mappings_index_subset])
     apply(clarsimp simp: pd_shifting' invs_aligned_pdD)
    apply(wp get_pde_inv store_pde_aligned store_pde_valid_arch | simp | fastforce)+
  apply(fastforce dest: reads_equiv_gD simp: globals_equiv_def)
  done

lemma do_machine_op_globals_equiv:
   "(\<And> s sa. \<lbrakk>P sa; globals_equiv s sa\<rbrakk> \<Longrightarrow>
         \<forall>x\<in>fst (f (machine_state sa)).
            globals_equiv s (sa\<lparr>machine_state := snd x\<rparr>)) \<Longrightarrow>
  \<lbrace> globals_equiv s and P \<rbrace>
   do_machine_op f
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  unfolding do_machine_op_def
  apply (wp | simp add: split_def)+
  done

lemma dmo_no_mem_globals_equiv:
  "\<lbrakk>\<And>P. invariant f (\<lambda>ms. P (underlying_memory ms));
    \<And>P. invariant f (\<lambda>ms. P (device_state ms));
    \<And>P. invariant f (\<lambda>ms. P (exclusive_state ms))\<rbrakk> \<Longrightarrow>
  invariant (do_machine_op f) (globals_equiv s)"
  unfolding do_machine_op_def
  apply (wp | simp add: split_def)+
  apply atomize
  apply (erule_tac x="(=) (underlying_memory (machine_state sa))" in allE)
  apply (erule_tac x="(=) (device_state (machine_state sa))" in allE)
  apply (erule_tac x="(=) (exclusive_state (machine_state sa))" in allE)
  apply (fastforce simp: valid_def globals_equiv_def idle_equiv_def)
  done

lemma mol_globals_equiv:
  "\<lbrace>\<lambda>ms. globals_equiv st (s\<lparr>machine_state := ms\<rparr>)\<rbrace> machine_op_lift mop \<lbrace>\<lambda>a b. globals_equiv st (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  unfolding machine_op_lift_def
  apply (simp add: machine_rest_lift_def split_def)
  apply wp
  apply (clarsimp simp: globals_equiv_def idle_equiv_def)
  done

lemma mol_exclusive_state:
  "invariant (machine_op_lift mop) (\<lambda>ms. P (exclusive_state ms))"
  apply (simp add: machine_op_lift_def machine_rest_lift_def)
  apply (wp | simp add: split_def)+
  done

lemma dmo_mol_globals_equiv:
  "invariant (do_machine_op (machine_op_lift f)) (globals_equiv s)"
  apply(rule dmo_no_mem_globals_equiv)
   apply(simp add: machine_op_lift_def machine_rest_lift_def)
   apply(wp mol_exclusive_state | simp add: split_def)+
   done

lemma dmo_cleanCacheRange_PoU_globals_equiv:
  "invariant (do_machine_op (cleanCacheRange_PoU x y z)) (globals_equiv s)"
  unfolding cleanCacheRange_PoU_def
  by(wp dmo_mol_globals_equiv dmo_cacheRangeOp_lift | simp add: cleanByVA_PoU_def)+

lemma dmo_cleanCacheRange_reads_respects_g:
  "reads_respects_g aag l \<top> (do_machine_op (cleanCacheRange_PoU x y z))"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule dmo_cleanCacheRange_PoU_reads_respects)
   apply(rule doesnt_touch_globalsI[where P="\<top>", simplified, OF dmo_cleanCacheRange_PoU_globals_equiv])
  by simp

lemma storeWord_globals_equiv:
  "\<lbrace>\<lambda>ms. globals_equiv st (s\<lparr>machine_state := ms\<rparr>)\<rbrace> storeWord p v \<lbrace>\<lambda>a b. globals_equiv st (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  unfolding storeWord_def
  apply (simp add: is_aligned_mask[symmetric])
  apply wp
  apply (clarsimp simp: globals_equiv_def idle_equiv_def)
  done

lemma ptr_range_memE:
  "\<lbrakk>x \<in> ptr_range ptr bits; \<lbrakk>ptr \<le> x; x \<le> ptr + 2 ^ bits - 1\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by(clarsimp simp: ptr_range_def)

lemma is_aligned_2_upto_enum_step_mem:
  fixes ptr :: "word32"
  shows
  "\<lbrakk>is_aligned ptr bits; 2 \<le> bits; bits < word_bits;
    x \<in> set [ptr , ptr + word_size .e. ptr + 2 ^ bits - 1]\<rbrakk> \<Longrightarrow>
   is_aligned x 2"
  apply(clarsimp simp: upto_enum_step_shift_red[where us=2, simplified] word_size_def word_bits_def)
  apply(erule aligned_add_aligned)
    apply(rule is_alignedI)
    apply(simp add: mult.commute)
   apply(simp add: word_bits_conv)
  done

(* TODO: cleanup this beautiful proof *)
lemma ptr_range_subset:
  fixes ptr :: "word32"
  shows
  "\<lbrakk>is_aligned ptr bits; 2 \<le> bits; bits < word_bits;
    x \<in> set [ptr , ptr + word_size .e. ptr + 2 ^ bits - 1]\<rbrakk> \<Longrightarrow>
   ptr_range x 2 \<subseteq> ptr_range ptr bits"
  apply(frule is_aligned_2_upto_enum_step_mem, assumption+)
  apply(rule subsetI)
  apply(clarsimp simp: upto_enum_step_shift_red[where us=2, simplified] word_size_def word_bits_def)
  apply(subst ptr_range_def)
  apply(clarsimp)
  apply(erule ptr_range_memE)
  apply(rule conjI)
   apply(erule order_trans[rotated])
   apply(erule is_aligned_no_wrap')
   apply(rule word_less_power_trans2[where k=2, simplified])
     apply(erule of_nat_power)
     apply(simp add: word_bits_conv)
    apply assumption
   apply simp
  apply(erule order_trans)
  apply(subgoal_tac "ptr + of_nat xaa * 4 + 2\<^sup>2 - 1 = ptr + (3 + of_nat xaa * 4)")
   apply(subgoal_tac "ptr + 2 ^ bits - 1 = ptr + (2 ^ bits - 1)")
    apply(erule ssubst)+
    apply(rule word_plus_mono_right)
     apply(drule is_aligned_addD1)
      apply(erule (1) is_aligned_weaken)
     prefer 2
     apply(erule is_aligned_no_wrap')
     apply simp
    apply(simp_all)
  apply(drule (1) word_less_power_trans_ofnat[where 'a=machine_word_len], simp)
  apply simp
  apply(subst add.commute)
  apply(erule is_aligned_add_less_t2n)
  apply(simp_all)
  done



lemma dmo_clearMemory_globals_equiv:
  "\<lbrace> globals_equiv s \<rbrace>
   do_machine_op (clearMemory ptr (2 ^ bits))
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply(rule hoare_pre)
  apply(simp add: do_machine_op_def clearMemory_def split_def cleanCacheRange_PoU_def)
  apply(wp)
  apply clarsimp
  apply(erule use_valid)
  apply(wp mapM_x_wp' storeWord_globals_equiv mol_globals_equiv | simp add: cleanByVA_PoU_def)+
  done

lemma dmo_clearMemory_reads_respects_g:
  "reads_respects_g aag l \<top> (do_machine_op (clearMemory ptr (2 ^bits)))"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_g)
    apply(rule dmo_clearMemory_reads_respects)
   apply(rule doesnt_touch_globalsI[where P = \<top>, simplified, OF dmo_clearMemory_globals_equiv])
  apply clarsimp
  done

lemma dmo_freeMemory_globals_equiv:
  "\<lbrace> globals_equiv s\<rbrace>
   do_machine_op (freeMemory ptr bits)
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply(rule hoare_pre)
  apply(simp add: do_machine_op_def freeMemory_def split_def)
  apply(wp)
  apply clarsimp
  apply(erule use_valid)
  apply(wp mapM_x_wp' storeWord_globals_equiv mol_globals_equiv)
  apply(simp_all)
  done

lemma dmo_freeMemory_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. is_aligned ptr bits \<and> 2 \<le> bits \<and> bits < word_bits)
  (do_machine_op (freeMemory ptr bits))"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_g)
    apply(rule dmo_freeMemory_reads_respects)
   apply(rule doesnt_touch_globalsI[where P = \<top>, simplified, OF dmo_freeMemory_globals_equiv])
  apply clarsimp
  done

lemma do_machine_op_mapM_x:
  assumes ef:
  "\<And> a. empty_fail (f a)"
  shows
    "do_machine_op (mapM_x f xs) = mapM_x (\<lambda> x. do_machine_op (f x)) xs"
  apply(induct xs)
   apply(simp add: mapM_x_Nil)
  apply(clarsimp simp: mapM_x_Cons do_machine_op_bind[OF ef empty_fail_mapM_x[OF ef]])
  done

text \<open>

        | simp add: unless_def when_def
        | intro conjI impI)+
     (create_word_objects ptr numObjects bits dev)"
\<close>

lemma init_arch_objects_reads_respects_g:
  "reads_respects_g aag l
         ((\<lambda> s. arm_global_pd (arch_state s) \<notin> set refs \<and>
                 pspace_aligned s \<and> valid_arch_state s) and
          K (\<forall>x\<in>set refs. is_subject aag x) and
          K (\<forall>x\<in>set refs. new_type = ArchObject PageDirectoryObj
                            \<longrightarrow> is_aligned x pd_bits) and
          K ((0::word32) < of_nat num_objects))
        (init_arch_objects new_type ptr num_objects obj_sz refs)"
  apply (unfold init_arch_objects_def fun_app_def)
  apply (rule gen_asm_ev)+
  apply (subst do_machine_op_mapM_x[OF empty_fail_cleanCacheRange_PoU])+
  apply (rule equiv_valid_guard_imp)
  apply (wp dmo_cleanCacheRange_reads_respects_g mapM_x_ev''
         equiv_valid_guard_imp[OF copy_global_mappings_reads_respects_g]
         copy_global_mappings_valid_arch_state copy_global_mappings_pspace_aligned
         hoare_vcg_ball_lift | wpc | simp)+
  apply clarsimp
  done

lemma copy_global_mappings_globals_equiv:
  "\<lbrace> globals_equiv s and (\<lambda> s. x \<noteq> arm_global_pd (arch_state s) \<and> is_aligned x pd_bits)\<rbrace>
   copy_global_mappings x
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  unfolding copy_global_mappings_def including no_pre
  apply simp
  apply wp
   apply(rule_tac Q="\<lambda>_. globals_equiv s and (\<lambda> s. x \<noteq> arm_global_pd (arch_state s) \<and>  is_aligned x pd_bits)" in hoare_strengthen_post)
    apply(wp mapM_x_wp[OF _ subset_refl] store_pde_globals_equiv)
    apply(fastforce dest: subsetD[OF copy_global_mappings_index_subset] simp: pd_shifting')
   apply(simp_all)
  done

lemma init_arch_objects_globals_equiv:
  "\<lbrace> globals_equiv s and
     (\<lambda> s. arm_global_pd (arch_state s) \<notin> set refs \<and>
           pspace_aligned s \<and> valid_arch_state s) and
     K (\<forall>x\<in>set refs. is_aligned x (obj_bits_api new_type obj_sz))\<rbrace>
   (init_arch_objects new_type ptr num_objects obj_sz refs)
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  unfolding init_arch_objects_def fun_app_def
  apply(rule hoare_gen_asm)+
  apply(subst do_machine_op_mapM_x[OF empty_fail_cleanCacheRange_PoU])+
  apply(rule hoare_pre)
  apply(wpc | wp mapM_x_wp[OF dmo_cleanCacheRange_PoU_globals_equiv subset_refl])+
  apply(rule_tac Q="\<lambda>_. globals_equiv s and (\<lambda> s. arm_global_pd (arch_state s) \<notin> set refs)" in hoare_strengthen_post)
      apply(wp mapM_x_wp[OF _ subset_refl] copy_global_mappings_globals_equiv
               dmo_cleanCacheRange_PoU_globals_equiv
            | simp add: obj_bits_api_def default_arch_object_def
                        pd_bits_def pageBits_def | blast)+
  done

lemma create_cap_reads_respects_g:
  "reads_respects_g aag l (K (is_subject aag (fst (fst slot))) and valid_global_objs)
  (create_cap type bits untyped dev slot)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule create_cap_reads_respects)
   apply(rule doesnt_touch_globalsI[OF create_cap_globals_equiv])
  by simp

lemma default_object_not_asid_pool:
  "\<lbrakk>type \<noteq> ArchObject ASIDPoolObj; type \<noteq> Untyped\<rbrakk> \<Longrightarrow>
        \<not> default_object type o_bits dev = ArchObj (ASIDPool asid_pool)"
  apply(clarsimp simp: default_object_def split: apiobject_type.splits
    simp: default_arch_object_def split: aobject_type.splits)
  done

lemma retype_region_ext_def2:
  "retype_region_ext a b =
   modify (\<lambda>exst. ekheap_update (\<lambda>ekh x. if x \<in> set a then default_ext b (cur_domain exst) else ekh x) exst)"
  apply (simp add: retype_region_ext_def foldr_upd_app_if' gets_def bind_def return_def
                   modify_def get_def put_def fun_eq_iff)
  done

lemma retype_region_reads_respects:
  "reads_respects aag l \<top> (retype_region ptr num_objects o_bits type dev)"
  apply(simp only: retype_region_def retype_addrs_def
                   foldr_upd_app_if fun_app_def K_bind_def when_def
                   retype_region_ext_extended.dxo_eq
                   )
  apply (simp only: retype_region_ext_def2)
  apply(simp split del: if_split add: equiv_valid_def2)
  apply(rule_tac W="\<top>\<top>" and Q="\<top>\<top>" in equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF if_evrv])
      apply (rule equiv_valid_rv_bind[OF gets_kheap_revrv])
       apply simp
       apply (rule_tac Q="\<lambda>_ s. rv = kheap s" and Q'="\<lambda>_ s. rv' = kheap s" and R'="(=)" in equiv_valid_2_bind_pre)
            apply (rule modify_ev2)
            apply(fastforce elim: reads_equiv_identical_kheap_updates affects_equiv_identical_kheap_updates simp: identical_kheap_updates_def)
           apply (rule_tac P=\<top> and P'=\<top> in modify_ev2)
           apply (fastforce intro: reads_equiv_identical_ekheap_updates affects_equiv_identical_ekheap_updates simp: identical_updates_def default_ext_def reads_equiv_def)
          apply (wp | simp)+
     apply(rule return_ev2 | simp | rule impI, rule TrueI)+
  apply(intro impI, wp)
  done

lemma subset_thing:
  "\<lbrakk>a \<le> b; a \<le> a\<rbrakk> \<Longrightarrow> {a} \<subseteq> {a..b}"
  apply (auto)
  done

lemma updates_not_idle: "idle_equiv st s \<Longrightarrow> \<forall>a \<in> S. a \<noteq> idle_thread s  \<Longrightarrow>
        idle_equiv st
           (s\<lparr>kheap :=
                 \<lambda>a. if a \<in> S
                     then y else kheap s a\<rparr>)"
  apply (clarsimp simp add: idle_equiv_def tcb_at_def2)
  apply blast
  done

(* FIXME: cleanup this proof *)
lemma retype_region_globals_equiv:
  notes blah[simp del] = atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  shows
  "\<lbrace>globals_equiv s and
    (\<lambda>s. \<exists>idx. cte_wp_at (\<lambda>c. c = UntypedCap dev (ptr && ~~ mask sz) sz idx)
               slot s \<and>
              (idx \<le> unat (ptr && mask sz) \<or>
               pspace_no_overlap_range_cover ptr sz s)) and
    invs and
    K (range_cover ptr sz (obj_bits_api type o_bits) num_objects) and
    K (0 < num_objects)\<rbrace>
  retype_region ptr num_objects o_bits type dev
  \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply(simp only: retype_region_def foldr_upd_app_if fun_app_def K_bind_def)
  apply (wp dxo_wp_weak |simp)+
      apply (simp add: trans_state_update[symmetric] del: trans_state_update)
     apply (wp | simp)+
  apply clarsimp
  apply (simp only: globals_equiv_def)
  apply (clarsimp split del: if_split)
  apply (subgoal_tac "pspace_no_overlap_range_cover ptr sz sa")
   apply (rule conjI)
    apply(clarsimp simp: pspace_no_overlap_def)
    apply(drule_tac x="arm_global_pd (arch_state sa)" in spec)
    apply(clarsimp simp: invs_def valid_state_def valid_global_objs_def valid_vso_at_def obj_at_def ptr_add_def)
    apply(frule_tac p=x in range_cover_subset)
      apply(simp add: blah)
     apply simp
    apply(frule range_cover_subset')
     apply simp
    apply(clarsimp simp: p_assoc_help)
    apply(drule disjoint_subset_neg1[OF _ subset_thing], rule is_aligned_no_wrap')
        apply(clarsimp simp: valid_pspace_def pspace_aligned_def)
        apply(drule_tac x="arm_global_pd (arch_state sa)" and A="dom (kheap sa)"  in bspec)
         apply (simp add: domI)
        apply simp
       apply(rule word_power_less_1)
       apply(case_tac ao, simp_all add: arch_kobj_size_def word_bits_def)
      apply(simp add: pageBits_def)
     apply(simp add: pageBitsForSize_def split: vmpage_size.splits)
    apply(drule (1) subset_trans)
    apply(erule_tac P="a \<in> b" for a b in notE)
    apply(erule_tac A="{ptr + c..d}" for c d in subsetD)
    apply(simp add: blah)
    apply(rule is_aligned_no_wrap')
     apply(rule is_aligned_add[OF _ is_aligned_mult_triv2])
     apply(simp add: range_cover_def)
    apply(rule word_power_less_1)
    apply(simp add: range_cover_def)
   apply (erule updates_not_idle)
   apply(clarsimp simp: pspace_no_overlap_def)
   apply(drule_tac x="idle_thread sa" in spec)
   apply(clarsimp simp: invs_def valid_state_def valid_global_objs_def valid_ao_at_def obj_at_def ptr_add_def valid_idle_def pred_tcb_at_def)
   apply(frule_tac p=a in range_cover_subset)
     apply(simp add: blah)
    apply simp
   apply(frule range_cover_subset')
    apply simp
   apply(clarsimp simp: p_assoc_help)
   apply(drule disjoint_subset_neg1[OF _ subset_thing], rule is_aligned_no_wrap')
       apply(clarsimp simp: valid_pspace_def pspace_aligned_def)
       apply(drule_tac x="idle_thread sa" and A="dom (kheap sa)"  in bspec)
        apply (simp add: domI)
       apply simp
      apply uint_arith
     apply simp+
   apply(drule (1) subset_trans)
   apply(erule_tac P="a \<in> b" for a b in notE)
   apply(erule_tac A="{idle_thread_ptr..d}" for d in subsetD)
   apply(simp add: blah)
   apply (erule_tac t=idle_thread_ptr in subst)
   apply(rule is_aligned_no_wrap')
    apply(rule is_aligned_add[OF _ is_aligned_mult_triv2])
    apply (simp add: range_cover_def)+
  apply(auto intro!: cte_wp_at_pspace_no_overlapI simp: range_cover_def word_bits_def)[1]
  done


lemma retype_region_reads_respects_g:
  "reads_respects_g aag l
        ((\<lambda>s. \<exists>idx. cte_wp_at (\<lambda>c. c = UntypedCap dev (ptr && ~~ mask sz) sz idx)
                    slot s \<and>
                    (idx \<le> unat (ptr && mask sz) \<or>
                     pspace_no_overlap_range_cover ptr sz s)) and
         invs and
         K (range_cover ptr sz (obj_bits_api type o_bits) num_objects) and
         K (0 < num_objects))
   (retype_region ptr num_objects o_bits type dev)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g[OF retype_region_reads_respects]])
   apply(rule doesnt_touch_globalsI)
   apply(rule hoare_weaken_pre[OF retype_region_globals_equiv])
   apply simp
  apply (auto)
  done

lemma post_retype_invs_valid_arch_stateI:
  "post_retype_invs ty rv s \<Longrightarrow> valid_arch_state s"
  apply(clarsimp simp: post_retype_invs_def invs_def valid_state_def split: if_split_asm)
  done

lemma post_retype_invs_pspace_alignedI:
  "post_retype_invs ty rv s \<Longrightarrow> pspace_aligned s"
  apply(clarsimp simp: post_retype_invs_def invs_def valid_state_def split: if_split_asm)
  done

lemma detype_def2: "detype S (s :: det_state) = s
\<lparr>kheap := \<lambda>x. if x \<in> S then None else kheap s x,
 ekheap := \<lambda>x. if x \<in> S then None else ekheap s x\<rparr>"
  apply (simp add: detype_def detype_ext_def)
  done

lemma states_equiv_for_detype:
  "states_equiv_for P Q R S s s' \<Longrightarrow> states_equiv_for P Q R S (detype N s) (detype N s')"
  apply(simp add: detype_def detype_ext_def)
  apply (simp add: states_equiv_for_def equiv_for_def equiv_asids_def
         equiv_asid_def obj_at_def)
  done

lemma cur_thread_detype:
  "cur_thread (detype S s) = cur_thread s"
  by(auto simp: detype_def)

lemma cur_domain_detype:
  "cur_domain (detype S s) = cur_domain s"
  by (auto simp: detype_def detype_ext_def)

lemma sched_act_detype:
  "scheduler_action (detype S s) = scheduler_action s"
  by (auto simp: detype_def detype_ext_def)

lemma wuc_detype:
  "work_units_completed (detype S s) = work_units_completed s"
  by (auto simp: detype_def detype_ext_def)

lemma machine_state_detype:
  "machine_state (detype S s) = machine_state s"
  by (auto simp: detype_def detype_ext_def)

lemma detype_reads_respects:
  "reads_respects aag l \<top> (modify (detype S))"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad reads_equiv_def2 affects_equiv_def2)
  apply (simp add: cur_domain_detype cur_thread_detype sched_act_detype wuc_detype machine_state_detype)
  apply (fastforce intro: states_equiv_for_detype)
  done

lemma detype_globals_equiv:
  "\<lbrace> globals_equiv st and ((\<lambda> s. arm_global_pd (arch_state s) \<notin> S) and (\<lambda> s. idle_thread s \<notin> S)) \<rbrace>
   modify (detype S)
   \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  apply(wp)
  apply(clarsimp simp: globals_equiv_def detype_def idle_equiv_def tcb_at_def2)
  done
lemma detype_reads_respects_g:
  "reads_respects_g aag l ((\<lambda> s. arm_global_pd (arch_state s) \<notin> S) and (\<lambda>s. idle_thread s \<notin> S)) (modify (detype S))"
  apply (rule equiv_valid_guard_imp)
   apply (rule reads_respects_g)
    apply (rule detype_reads_respects)
   apply (rule doesnt_touch_globalsI[OF detype_globals_equiv])
  apply simp
  done

lemma a_type_small_pageD:
  "a_type ko = AArch (AUserData ARMSmallPage) \<Longrightarrow>
  ko = ArchObj (DataPage False ARMSmallPage)"
  apply clarsimp
  done

lemma obj_range_small_page_as_ptr_range:
  "obj_range ptr (ArchObj (DataPage dev ARMSmallPage)) =
   ptr_range ptr 12"
  apply(simp add: obj_range_def)
  apply(simp add: ptr_range_def)
  done


lemma untyped_caps_do_not_overlap_global_refs:
  "\<lbrakk>cte_wp_at ((=) (UntypedCap dev word sz idx)) slot s;
    valid_global_refs s\<rbrakk> \<Longrightarrow>
  ptr_range word sz \<inter> global_refs s = {}"
   apply(simp add: cte_wp_at_caps_of_state)
   apply(drule (1) valid_global_refsD2)
   apply(fastforce simp: cap_range_def ptr_range_def)
  done

lemma singleton_set_size:
  "{ptr..(ptr::'a::len word) + 2 ^ 0 - 1} = {ptr}"
  by (simp add: field_simps)

lemma cap_range_of_valid_capD:
  "valid_cap cap s \<Longrightarrow> (cap_range cap = {}) \<or> (\<exists>ptr sz. (cap_range cap = ptr_range ptr sz))"
   apply (rule disj_subst)
   apply (case_tac cap,auto simp: valid_cap_def valid_untyped_def cap_aligned_def cap_range_def ptr_range_def)[1]
   apply (intro exI | rule singleton_set_size[symmetric])+
   done

(* FIX ME: Many ptr_range proofs are not nice, should use the following lemma instead *)
lemma ptr_range_disjoint_strong:
  "\<lbrakk>ptr'  \<notin> ptr_range (ptr :: ('a :: len word)) sz; is_aligned ptr sz; is_aligned ptr' sz';
       sz < len_of TYPE('a); sz'\<le> sz \<rbrakk>
       \<Longrightarrow> ptr_range ptr sz \<inter> ptr_range ptr' sz' = {}"
  apply (unfold ptr_range_def)
  apply (frule(1) aligned_ranges_subset_or_disjoint[where p'=ptr'])
  apply (elim disjE)
    apply simp
   apply clarsimp
   apply (drule order_trans[where x = ptr and y = "ptr + a - b" for a b])
    apply simp
   apply (drule neg_mask_mono_le[where n = sz'])
   apply (subst (asm) is_aligned_neg_mask_eq)
    apply (erule is_aligned_weaken)
     apply simp
    apply (subst(asm) x_t2n_sub_1_neg_mask)
      apply simp
     apply simp
   apply (subst (asm) is_aligned_neg_mask_eq)
    apply (erule is_aligned_weaken)
     apply simp
   apply simp
  apply (drule base_member_set[where sz = sz'],simp)
   apply fastforce
  done

lemma obj_range_page_as_ptr_range_pageBitsForSize:
  "obj_range ptr (ArchObj (DataPage dev vmpage_size)) =
   ptr_range ptr (pageBitsForSize vmpage_size)"
  apply(simp add: obj_range_def)
  apply(simp add: ptr_range_def)
  done


lemma pspace_distinct_def':
  "pspace_distinct \<equiv> \<lambda>s. \<forall>x y ko ko'.
             kheap s x = Some ko \<and> kheap s y = Some ko' \<and> x \<noteq> y \<longrightarrow>
             obj_range x ko \<inter> obj_range y ko' = {}"
  by(auto simp: pspace_distinct_def obj_range_def field_simps)

lemma delete_objects_reads_respects_g:
 "reads_equiv_valid_g_inv (affects_equiv aag l) aag
    (\<lambda>s. arm_global_pd (arch_state s) \<notin> ptr_range p b \<and>
         idle_thread s \<notin> ptr_range p b \<and>
         is_aligned p b \<and> 2 \<le> b \<and> b < word_bits)
    (delete_objects p b)"
  apply (simp add: delete_objects_def2)
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_freeMemory_reads_respects_g)
    apply (rule detype_reads_respects_g)
   apply wp
  apply (unfold ptr_range_def)
  apply simp
  done

lemma set_cap_reads_respects_g:
  "reads_respects_g aag l (valid_global_objs and K (is_subject aag (fst slot))) (set_cap cap slot)"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_g[OF set_cap_reads_respects])
   apply(rule doesnt_touch_globalsI[OF set_cap_globals_equiv])
  by simp

(*FIXME move*)
lemma when_ev:
  "\<lbrakk>C \<Longrightarrow> equiv_valid I A A P handle\<rbrakk> \<Longrightarrow>
   equiv_valid I A A (\<lambda>s. C \<longrightarrow> P s) (when C handle)"
  apply (wp | auto simp: when_def)+
  done


lemma delete_objects_caps_no_overlap:
  "\<lbrace> invs and ct_active and (\<lambda> s. \<exists> slot idx.
    cte_wp_at ((=) (UntypedCap dev ptr sz idx)) slot s \<and> descendants_range_in {ptr..ptr + 2 ^ sz - 1} slot s) \<rbrace>
    delete_objects ptr sz
  \<lbrace>\<lambda>_ s :: det_ext state. caps_no_overlap ptr sz s\<rbrace>"
  apply(clarsimp simp: valid_def)
  apply(rule descendants_range_caps_no_overlapI)
    apply(erule use_valid | wp | simp add: descendants_range_def2 | blast)+
   apply(frule untyped_cap_aligned,
         (simp add: invs_valid_objs)+)
   apply(rule conjI, assumption)
   apply(drule (2) untyped_slots_not_in_untyped_range, simp+, rule subset_refl)
    apply simp
  apply(erule use_valid | wp delete_objects_descendants_range_in | simp | blast)+
  done

lemma get_cap_reads_respects_g:
  "reads_respects_g aag l (K (is_subject aag (fst slot))) (get_cap slot)"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_g[OF get_cap_rev])
   apply(rule doesnt_touch_globalsI)
   apply wp
   apply clarsimp
  apply simp
  done

lemma irq_state_independent_globals_equiv[simp,intro!]:
  "irq_state_independent_A (globals_equiv st)"
  by (clarsimp simp: irq_state_independent_A_def globals_equiv_def
                     idle_equiv_def)

lemma irq_state_independent_A_only_timer_irq_inv[simp]:
  "irq_state_independent_A (only_timer_irq_inv irq st)"
  apply (simp add: only_timer_irq_inv_def)
  apply (rule irq_state_independent_A_conjI)
   apply (simp add: domain_sep_inv_def)
  apply (simp add: irq_state_independent_A_def only_timer_irq_def
                   irq_is_recurring_def is_irq_at_def)
  done

lemma only_timer_irq_inv_work_units_completed[simp]:
  "only_timer_irq_inv irq st (work_units_completed_update f s)
    = only_timer_irq_inv irq st s"
  apply (simp add: only_timer_irq_inv_def)
  apply (simp add: domain_sep_inv_def)
  apply (simp add: irq_state_independent_A_def only_timer_irq_def
                   irq_is_recurring_def is_irq_at_def)
  done

lemma no_irq_freeMemory:
  "no_irq (freeMemory ptr sz)"
  apply (simp add: freeMemory_def)
  apply (wp no_irq_mapM_x no_irq_storeWord)
  done

crunch irq_masks[wp]: delete_objects "\<lambda>s. P (irq_masks (machine_state s))"
  (ignore: do_machine_op wp: dmo_wp no_irq_freeMemory no_irq
     simp: detype_def)

lemma delete_objects_pspace_no_overlap_again:
  "\<lbrace> pspace_aligned and valid_objs and
     (\<lambda> s. \<exists>slot. cte_wp_at (\<lambda>cp. is_untyped_cap cp \<and> obj_ref_of cp = ptr \<and> bits_of cp = sz) slot s)
     and K (S \<subseteq> {ptr .. ptr + 2 ^ sz - 1})\<rbrace>
    delete_objects ptr sz
   \<lbrace>\<lambda>rv. pspace_no_overlap S\<rbrace>"
  unfolding delete_objects_def do_machine_op_def
  apply(wp | simp add: split_def detype_machine_state_update_comm)+
  apply(clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
  apply(drule caps_of_state_cteD)
  apply(frule cte_wp_at_valid_objs_valid_cap, clarsimp+)
  apply(erule pspace_no_overlap_subset[rotated])
  apply(rule pspace_no_overlap_subset, rule pspace_no_overlap_detype, simp+)
  apply(simp add: valid_cap_simps cap_aligned_def field_simps)
  done

lemma ex_tupleI:
  "P (fst t) (snd t) \<Longrightarrow> \<exists>a b. P a b"
  by blast

lemma reset_untyped_cap_reads_respects_g:
 "reads_equiv_valid_g_inv (affects_equiv aag l) aag
    (\<lambda>s. cte_wp_at is_untyped_cap slot s \<and> invs s \<and> ct_active s
        \<and> only_timer_irq_inv irq st s
        \<and> is_subject aag (fst slot)
        \<and> (descendants_of slot (cdt s) = {}))
    (reset_untyped_cap slot)"
  apply (simp add: reset_untyped_cap_def cong: if_cong)
  apply (rule equiv_valid_guard_imp)
   apply (wp set_cap_reads_respects_g dmo_clearMemory_reads_respects_g
       | simp add: unless_def when_def split del: if_split)+
       apply (rule_tac I="invs and cte_wp_at (\<lambda>cp. is_untyped_cap rv
             \<and> (\<exists>idx. cp = free_index_update (\<lambda>_. idx) rv)
             \<and> free_index_of rv \<le> 2 ^ (bits_of rv)
             \<and> is_subject aag (fst slot)) slot
             and pspace_no_overlap (untyped_range rv)
             and only_timer_irq_inv irq st
             and (\<lambda>s. descendants_of slot (cdt s) = {})" in mapME_x_ev)
        apply (rule equiv_valid_guard_imp)
         apply wp
             apply (rule reads_respects_g_from_inv)
              apply (rule preemption_point_reads_respects[where irq=irq and st=st])
             apply ((wp preemption_point_inv set_cap_reads_respects_g
                       set_untyped_cap_invs_simple
                       only_timer_irq_inv_pres[where Q=\<top>, OF _ set_cap_domain_sep_inv]
                       dmo_clearMemory_reads_respects_g
                     | simp)+)
         apply (strengthen empty_descendants_range_in)
         apply (wp only_timer_irq_inv_pres[where P=\<top> and Q=\<top>]
                   no_irq_clearMemory
              | simp
              | wp (once) dmo_wp)+
        apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
        apply (frule(1) caps_of_state_valid)
        apply (clarsimp simp: valid_cap_simps cap_aligned_def field_simps
                              free_index_of_def invs_valid_global_objs)
        apply (simp add: aligned_add_aligned is_aligned_shiftl)
        apply (clarsimp simp: reset_chunk_bits_def)
       apply (rule hoare_pre)
        apply (wp preemption_point_inv' set_untyped_cap_invs_simple
                  set_cap_cte_wp_at set_cap_no_overlap
                  only_timer_irq_inv_pres[where Q=\<top>, OF _ set_cap_domain_sep_inv]
           | simp)+
        apply (strengthen empty_descendants_range_in)
         apply (wp only_timer_irq_inv_pres[where P=\<top> and Q=\<top>]
                   no_irq_clearMemory
             | simp
             | wp (once) dmo_wp)+
        apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
        apply (frule(1) caps_of_state_valid)
        apply (clarsimp simp: valid_cap_simps cap_aligned_def field_simps
                              free_index_of_def)
       apply (wp | simp)+
       apply (wp delete_objects_reads_respects_g)
      apply (simp add: if_apply_def2)
      apply (strengthen invs_valid_global_objs)
      apply (wp add: delete_objects_invs_ex
                      hoare_vcg_const_imp_lift delete_objects_pspace_no_overlap_again
                      only_timer_irq_inv_pres[where P=\<top> and Q=\<top>]
                 del: Untyped_AI.delete_objects_pspace_no_overlap
          | simp)+
     apply (rule get_cap_reads_respects_g)
    apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps bits_of_def)
  apply (frule(1) caps_of_state_valid)
  apply (clarsimp simp: valid_cap_simps cap_aligned_def field_simps
                        free_index_of_def invs_valid_global_objs)
  apply (frule valid_global_refsD2, clarsimp+)
  apply (clarsimp simp: ptr_range_def[symmetric] global_refs_def
                        descendants_range_def2)
  apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
  apply (strengthen refl[where t=True] refl ex_tupleI[where t=slot]
            empty_descendants_range_in
    | clarsimp)+
  apply (drule ex_cte_cap_protects[OF _ _ _ _ order_refl],
    erule caps_of_state_cteD)
     apply (clarsimp simp: descendants_range_def2 empty_descendants_range_in)
    apply clarsimp+
  apply (fastforce simp: untyped_min_bits_def)
  done

lemma equiv_valid_obtain:
  assumes fn_eq: "\<And>s t. I s t \<Longrightarrow> A s t \<Longrightarrow> P s \<Longrightarrow> P t \<Longrightarrow>  fn s = fn t"
  assumes pr: "\<And>x. equiv_valid I A B (P and (\<lambda>s. fn s = x)) f"
  shows "equiv_valid I A B P f"
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply (frule(1) fn_eq, simp+)
  apply (cut_tac x="fn s" in pr)
  apply (clarsimp simp: equiv_valid_def2 equiv_valid_2_def)
  apply fastforce
  done

lemma reads_equiv_cte_wp_at:
  "reads_equiv aag s s'
    \<Longrightarrow> is_subject aag (fst slot)
    \<Longrightarrow> cte_wp_at P slot s = cte_wp_at P slot s'"
  apply (frule(1) is_subject_kheap_eq)
  apply (simp add: cte_wp_at_cases)
  done

lemma reads_equiv_caps_of_state:
  "reads_equiv aag s s'
    \<Longrightarrow> is_subject aag (fst slot)
    \<Longrightarrow> caps_of_state s slot = caps_of_state s' slot"
  apply (frule(1) reads_equiv_cte_wp_at[where P="(=) (the (caps_of_state s slot))"])
  apply (frule(1) reads_equiv_cte_wp_at[where P="\<top>"])
  apply (auto simp: cte_wp_at_caps_of_state)
  done

lemma untyped_cap_refs_in_kernel_window_helper:
  "\<lbrakk> caps_of_state s p = Some (UntypedCap dev ptr sz idx);
    cap_refs_in_kernel_window s;
    S' \<subseteq> {ptr .. ptr + 2 ^ sz - 1} \<rbrakk>
    \<Longrightarrow> \<forall>r \<in> S'.  arm_kernel_vspace (arch_state s) r = ArmVSpaceKernelWindow"
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply (simp add: untyped_range_def)
  apply blast
  done

lemma invs_valid_global_objs_strg:
  "invs s \<longrightarrow> valid_global_objs s"
  by (clarsimp simp: invs_def valid_state_def)

lemma retype_region_ret_pd_aligned:
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) num_objects)\<rbrace>
   retype_region ptr num_objects us tp dev
   \<lbrace>\<lambda>rv. K (\<forall> ref \<in> set rv. tp = ArchObject PageDirectoryObj \<longrightarrow> is_aligned ref pd_bits)\<rbrace>"
  apply(rule hoare_strengthen_post)
  apply(rule hoare_weaken_pre)
  apply(rule retype_region_aligned_for_init)
   apply simp
  apply (clarsimp simp: obj_bits_api_def default_arch_object_def pd_bits_def pageBits_def)
  done

lemma invoke_untyped_reads_respects_g_wcap:
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  shows
  "reads_respects_g aag l (invs and valid_untyped_inv_wcap ui (Some (UntypedCap dev ptr sz idx))
      and only_timer_irq_inv irq st
      and ct_active and pas_refined aag
      and K (authorised_untyped_inv aag ui)) (invoke_untyped ui)"
  apply(case_tac ui)
  apply(rename_tac cslot_ptr reset ptr_base ptr' apiobject_type nat list dev')
  apply(case_tac "\<not> (dev' = dev \<and> ptr = ptr' && ~~ mask sz)")
   (* contradictory *)
   apply (rule equiv_valid_guard_imp, rule_tac gen_asm_ev'[where P="\<top>" and Q=False],
     simp)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply(simp add: invoke_untyped_def mapM_x_def[symmetric])
  apply(wp mapM_x_ev'' create_cap_reads_respects_g hoare_vcg_ball_lift
           init_arch_objects_reads_respects_g
        | simp)+
           apply(rule_tac Q="\<lambda>_. invs" in hoare_strengthen_post)
            apply(wp init_arch_objects_invs_from_restricted)
           apply(fastforce simp: invs_def)
          apply(wp retype_region_reads_respects_g[where sz=sz and slot="slot_of_untyped_inv ui"])
         apply(rule_tac Q="\<lambda>rvc s.
                                (\<forall>x\<in>set rvc. is_subject aag x) \<and>
                                (\<forall>x\<in>set rvc. is_aligned x (obj_bits_api apiobject_type nat)) \<and>
                                ((0::word32) < of_nat (length list)) \<and>
                                post_retype_invs apiobject_type rvc s \<and>
                                global_refs s \<inter> set rvc = {} \<and>
                                (\<forall>x\<in>set list. is_subject aag (fst x))"
                for sz in hoare_strengthen_post)
          apply(wp retype_region_ret_is_subject[where sz=sz, simplified]
                   retype_region_global_refs_disjoint[where sz=sz]
                   retype_region_ret_pd_aligned[where sz=sz]
                   retype_region_aligned_for_init[where sz=sz]
                   retype_region_post_retype_invs_spec[where sz=sz])
         apply(fastforce simp: global_refs_def
                        intro: post_retype_invs_pspace_alignedI
                               post_retype_invs_valid_arch_stateI
                        simp: obj_bits_api_def default_arch_object_def
                              pd_bits_def pageBits_def
                        elim: in_set_zipE)
        apply(rule set_cap_reads_respects_g)
       apply simp
       apply(wp hoare_vcg_ex_lift set_cap_cte_wp_at_cases
                 hoare_vcg_disj_lift set_cap_no_overlap
                 set_free_index_invs_UntypedCap
                 set_untyped_cap_caps_overlap_reserved
                 set_cap_caps_no_overlap
                 region_in_kernel_window_preserved)
      apply(wp when_ev delete_objects_reads_respects_g hoare_vcg_disj_lift
               delete_objects_pspace_no_overlap
               delete_objects_descendants_range_in
               delete_objects_caps_no_overlap
               region_in_kernel_window_preserved
               get_cap_reads_respects_g get_cap_wp
           |simp split del: if_split)+
    apply (rule reset_untyped_cap_reads_respects_g[where irq=irq and st=st])
  apply (rule_tac P="authorised_untyped_inv aag ui
        \<and> (\<forall>p \<in> ptr_range ptr sz. is_subject aag p)" in hoare_gen_asmE)
  apply (rule validE_validE_R, rule_tac E="\<top>\<top>" and Q="\<lambda>_. invs and valid_untyped_inv_wcap ui
      (Some (UntypedCap dev ptr sz (if reset then 0 else idx))) and ct_active
      and (\<lambda>s. reset \<longrightarrow> pspace_no_overlap {ptr .. ptr + 2 ^ sz - 1} s)"
    in hoare_post_impErr)
     apply (rule hoare_pre, wp hoare_whenE_wp)
      apply (rule validE_validE_R, rule hoare_post_impErr, rule reset_untyped_cap_invs_etc)
       apply (clarsimp simp only: if_True simp_thms, intro conjI, assumption+)
      apply simp
     apply assumption
    apply (clarsimp simp only: )
    apply (frule(2) invoke_untyped_proofs.intro)
    apply (clarsimp simp: cte_wp_at_caps_of_state bits_of_def
                          free_index_of_def untyped_range_def
                          if_split[where P="\<lambda>x. x \<le> unat v" for v]
               split del: if_split)
    apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
    apply (strengthen refl)
    apply (strengthen invs_valid_global_objs_strg)
    apply (clarsimp simp: authorised_untyped_inv_def conj_comms
                          invoke_untyped_proofs.simps)
    apply (simp add: arg_cong[OF mask_out_sub_mask, where f="\<lambda>y. x - y" for x]
                       field_simps invoke_untyped_proofs.idx_le_new_offs
                       invoke_untyped_proofs.idx_compare'
                       untyped_range_def)
    apply (strengthen caps_region_kernel_window_imp[mk_strg I E])
    apply (simp add: invoke_untyped_proofs.simps untyped_range_def
                     invs_cap_refs_in_kernel_window
                     atLeastatMost_subset_iff[where b=x and d=x for x]
               cong: conj_cong split del: if_split)
    apply (intro conjI)
         (* mostly clagged from Untyped_AI *)
           apply (simp add: atLeastatMost_subset_iff word_and_le2)

          apply (case_tac reset)
           apply (clarsimp elim!: pspace_no_overlap_subset del: subsetI
                            simp: blah word_and_le2)
          apply (drule invoke_untyped_proofs.ps_no_overlap)
          apply (simp add: field_simps)

         apply (simp add: Int_commute, erule disjoint_subset2[rotated])
         apply (simp add: atLeastatMost_subset_iff word_and_le2)

        apply (clarsimp dest!: invoke_untyped_proofs.idx_le_new_offs)

       apply (simp add: ptr_range_def)
       apply (erule ball_subset, rule range_subsetI[OF _ order_refl])
       apply (simp add: word_and_le2)

      apply (erule order_trans[OF invoke_untyped_proofs.subset_stuff])
      apply (simp add: atLeastatMost_subset_iff word_and_le2)

     apply (drule invoke_untyped_proofs.usable_range_disjoint)
     apply (clarsimp simp: field_simps mask_out_sub_mask shiftl_t2n)

    apply blast

   apply simp

  apply (clarsimp simp: cte_wp_at_caps_of_state authorised_untyped_inv_def)
  apply (strengthen refl)
  apply (frule(1) cap_auth_caps_of_state)
  apply (simp add: aag_cap_auth_def untyped_range_def
                   aag_has_Control_iff_owns ptr_range_def[symmetric])
  apply (erule disjE, simp_all)[1]
  done

lemma invoke_untyped_reads_respects_g:
  "reads_respects_g aag l (invs and valid_untyped_inv ui
      and only_timer_irq_inv irq st
      and ct_active and pas_refined aag
      and K (authorised_untyped_inv aag ui)) (invoke_untyped ui)"
  apply (rule_tac fn="\<lambda>s. caps_of_state s (slot_of_untyped_inv ui)" in equiv_valid_obtain)
   apply (cases ui, clarsimp simp: valid_untyped_inv_wcap reads_equiv_g_def)
   apply (simp add: authorised_untyped_inv_def
                    reads_equiv_caps_of_state)
  apply (case_tac "x \<noteq> None \<and> is_untyped_cap (the x)")
   apply (clarsimp simp: is_cap_simps)
   apply (rule equiv_valid_guard_imp, rule invoke_untyped_reads_respects_g_wcap)
   apply (cases ui, clarsimp simp: cte_wp_at_caps_of_state valid_untyped_inv_wcap)
   apply auto[1]
  apply (rule equiv_valid_guard_imp, rule gen_asm_ev'[where Q=False])
   apply simp
  apply (cases ui, clarsimp simp: valid_untyped_inv_wcap cte_wp_at_caps_of_state)
  done

lemma delete_objects_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and
    (\<lambda>s. is_aligned p b \<and> 2 \<le> b \<and> b < word_bits \<and>
         arm_global_pd (arch_state s) \<notin> ptr_range p b \<and>
         idle_thread s \<notin> ptr_range p b)\<rbrace>
   delete_objects p b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wp detype_globals_equiv dmo_freeMemory_globals_equiv)
  apply (clarsimp simp: ptr_range_def)+
  done

lemma reset_untyped_cap_globals_equiv:
  "\<lbrace>globals_equiv st and invs and cte_wp_at is_untyped_cap slot
      and ct_active and (\<lambda>s. descendants_of slot (cdt s) = {})\<rbrace>
    reset_untyped_cap slot
  \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (simp add: reset_untyped_cap_def cong: if_cong)
  apply (rule hoare_pre)
   apply (wp set_cap_globals_equiv dmo_clearMemory_globals_equiv
             preemption_point_inv | simp add: unless_def)+
     apply (rule valid_validE)
     apply (rule_tac P="cap_aligned cap \<and> is_untyped_cap cap" in hoare_gen_asm)
     apply (rule_tac Q="\<lambda>_ s. valid_global_objs s \<and> globals_equiv st s"
       in hoare_strengthen_post)
      apply (rule validE_valid, rule mapME_x_wp')
      apply (rule hoare_pre)
       apply (wp set_cap_globals_equiv dmo_clearMemory_globals_equiv
                 preemption_point_inv | simp add: if_apply_def2)+
      apply (clarsimp simp: is_cap_simps ptr_range_def[symmetric]
                            cap_aligned_def bits_of_def
                            free_index_of_def)
    apply (clarsimp simp: reset_chunk_bits_def)
    apply (strengthen invs_valid_global_objs)
    apply (wp delete_objects_invs_ex
       hoare_vcg_const_imp_lift get_cap_wp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state descendants_range_def2 is_cap_simps bits_of_def
             split del: if_split)
  apply (frule caps_of_state_valid_cap, clarsimp+)
  apply (clarsimp simp: valid_cap_simps cap_aligned_def untyped_min_bits_def)
  apply (frule valid_global_refsD2, clarsimp+)
  apply (clarsimp simp: ptr_range_def[symmetric] global_refs_def)
  apply (strengthen empty_descendants_range_in)
  apply (cases slot)
  apply fastforce
  done

lemma invoke_untyped_globals_equiv:
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  shows
  "\<lbrace> globals_equiv st and invs and valid_untyped_inv ui and ct_active\<rbrace>
   invoke_untyped ui
   \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre, rule invoke_untyped_Q)
       apply (wp create_cap_globals_equiv)
       apply auto[1]
      apply (wp init_arch_objects_globals_equiv)
      apply (clarsimp simp: retype_addrs_aligned_range_cover cte_wp_at_caps_of_state
                  simp del: valid_untyped_inv_wcap.simps)
      apply (frule valid_global_refsD2)
       apply (clarsimp simp: post_retype_invs_def split: if_split_asm)
      apply (drule disjoint_subset2[rotated])
       apply (rule order_trans, erule retype_addrs_subset_ptr_bits)
       apply (simp add: untyped_range_def blah word_and_le2 field_simps)
      apply (auto simp: global_refs_def post_retype_invs_def split: if_split_asm)[1]
     apply (rule hoare_pre, wp retype_region_globals_equiv[where slot="slot_of_untyped_inv ui"])
     apply (clarsimp simp: cte_wp_at_caps_of_state)
     apply (strengthen refl)
     apply simp
    apply (wp set_cap_globals_equiv)
    apply auto[1]
   apply (wp reset_untyped_cap_globals_equiv)
  apply (cases ui, clarsimp simp: cte_wp_at_caps_of_state)
  done

end

end
