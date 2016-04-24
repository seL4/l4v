(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory Retype_IF
imports CNode_IF
begin

context begin interpretation ARM . (*FIXME: arch_split*)

lemma create_cap_reads_respects:
  "reads_respects aag l (K (is_subject aag (fst (fst slot)))) (create_cap type bits untyped slot)"
  apply(rule gen_asm_ev)
  apply(simp add: create_cap_def split_def bind_assoc[symmetric])
  apply (fold update_cdt_def)
  apply (simp add: bind_assoc create_cap_ext_def)
  apply (wp set_cap_reads_respects set_original_reads_respects update_cdt_list_reads_respects update_cdt_reads_respects| simp | fastforce simp: equiv_for_def split: option.splits)+
  apply (intro impI conjI allI)
   apply(fastforce simp: reads_equiv_def2 equiv_for_def elim: states_equiv_forE_is_original_cap states_equiv_forE_cdt dest: aag_can_read_self split: option.splits)+
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
  "equiv_machine_state P X s t \<Longrightarrow>
   equiv_machine_state P X (s\<lparr> machine_state_rest := x \<rparr>) (t\<lparr> machine_state_rest := y \<rparr>)"
  by(fastforce intro: equiv_forI elim: equiv_forE)

lemma machine_op_lift_ev:
  "equiv_valid_inv (equiv_machine_state P X) (equiv_machine_state Q Y) \<top> (machine_op_lift mop)"
  apply(rule equiv_valid_guard_imp)
  apply(rule machine_op_lift_ev')
  apply(fastforce intro: equiv_machine_state_machine_state_rest_update)
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
  "equiv_valid_inv (equiv_machine_state P X) (equiv_machine_state Q Y) \<top> (cleanCacheRange_PoU vstart vend pstart)"
  unfolding cleanCacheRange_PoU_def
  apply (wp machine_op_lift_ev | simp add: cleanByVA_PoU_def)+
  done

lemma modify_underlying_memory_update_0_ev:
  "equiv_valid_inv (equiv_machine_state P X) (equiv_machine_state Q Y) \<top>
          (modify
            (underlying_memory_update
              (\<lambda>m. m(x := word_rsplit 0 ! 3, x + 1 := word_rsplit 0 ! 2,
                     x + 2 := word_rsplit 0 ! 1, x + 3 := word_rsplit 0 ! 0))))"
  apply(clarsimp simp: equiv_valid_def2 equiv_valid_2_def in_monad)
  apply(fastforce intro: equiv_forI elim: equiv_forE)
  done

lemma storeWord_ev:
  "equiv_valid_inv (equiv_machine_state P X) (equiv_machine_state Q Y) \<top> (storeWord x 0)"
  unfolding storeWord_def
  apply (wp modify_underlying_memory_update_0_ev assert_inv | simp add: no_irq_def)+
  done

lemma clearMemory_ev:
  "equiv_valid_inv (equiv_machine_state P X) (equiv_machine_state Q Y) (\<lambda>_. True) (clearMemory ptr bits)"
  unfolding clearMemory_def
  apply simp
  apply(rule equiv_valid_guard_imp)
   apply(rule bind_ev)
     apply(rule cleanCacheRange_PoU_ev)
    apply(rule mapM_x_ev[OF storeWord_ev])
    apply(rule wp_post_taut | simp)+
  done

lemma freeMemory_ev:
  "equiv_valid_inv (equiv_machine_state P X) (equiv_machine_state Q Y) (\<lambda>_. True) (freeMemory ptr bits)"
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
  (wp: crunch_wps simp: crunch_simps storeWord_def cleanByVA_PoU_def ignore: cacheRangeOp)

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

lemma set_pd_globals_equiv: "\<lbrace>globals_equiv st and (\<lambda>s. a \<noteq> arm_global_pd (arch_state s))\<rbrace> set_pd a b \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (rule hoare_pre)
   apply (simp add: set_pd_def get_object_def)
   apply (wp set_object_globals_equiv)
  apply clarsimp
  done

crunch globals_equiv: set_pd "globals_equiv s"
  (simp: crunch_simps wp: crunch_wps set_object_globals_equiv)

lemma globals_equiv_cdt_update:
  "globals_equiv s s' \<Longrightarrow> globals_equiv s (s'\<lparr> cdt := x \<rparr>)"
  by(fastforce simp: globals_equiv_def idle_equiv_def)

lemma globals_equiv_is_original_cap_update:
  "globals_equiv s s' \<Longrightarrow> globals_equiv s (s'\<lparr> is_original_cap := x \<rparr>)"
  by(fastforce simp: globals_equiv_def idle_equiv_def)


lemma create_cap_globals_equiv:
  "\<lbrace> globals_equiv s and valid_global_objs \<rbrace> create_cap type bits untyped slot
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply(simp add: create_cap_def split_def)
  apply (wp set_cap_globals_equiv set_original_globals_equiv set_cdt_globals_equiv set_cdt_valid_global_objs dxo_wp_weak| simp)+
  done


(* could remove the precondition here and replace with \<top> if we wanted the trouble *)
lemma set_pd_reads_respects:
  "reads_respects aag l (K (is_subject aag a)) (set_pd a b)"
  unfolding set_pd_def
  apply(wp set_object_reads_respects get_object_rev get_object_wp | clarsimp split: kernel_object.splits arch_kernel_obj.splits simp: asid_pool_at_kheap obj_at_def)+
  done

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
  apply(wp get_pd_rev)
  apply(clarsimp)
  done

lemma get_pde_revg:
  "reads_equiv_valid_g_inv A aag (\<lambda> s. (ptr && ~~ mask pd_bits) = arm_global_pd (arch_state s))
                                 (get_pde ptr)"
  unfolding get_pde_def fun_app_def
  apply(wp get_pd_revg)
  apply(clarsimp)
  done

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
    apply(wp get_pde_inv store_pde_arm_global_pd store_pde_aligned store_pde_valid_arch | simp | fastforce)+
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
    \<And>P. invariant f (\<lambda>ms. P (exclusive_state ms))\<rbrakk> \<Longrightarrow>
  invariant (do_machine_op f) (globals_equiv s)"
  unfolding do_machine_op_def
  apply(wp | simp add: split_def)+
  apply atomize
  apply(erule_tac x="op = (underlying_memory (machine_state sa))" in allE)
  apply(erule_tac x="op = (exclusive_state (machine_state sa))" in allE)
  apply(fastforce simp: valid_def globals_equiv_def idle_equiv_def)
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
  "\<lbrace>\<lambda>ms. globals_equiv st (s\<lparr>machine_state := ms\<rparr>) \<and> (ptr_range p 2 \<inter> range_of_arm_globals_frame s = {})\<rbrace> storeWord p v \<lbrace>\<lambda>a b. globals_equiv st (s\<lparr>machine_state := b\<rparr>)\<rbrace>"
  unfolding storeWord_def
  apply (simp add: is_aligned_mask[symmetric])
  apply wp
  apply (clarsimp simp: globals_equiv_def idle_equiv_def)
  apply (drule (1) orthD2)
  apply(fastforce intro: ptr_range_memI elim: notE intro: ptr_range_add_memI)
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
  apply(clarsimp simp: upto_enum_step_shift_red[where us=2, simplified] word_size_def )
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
  apply(clarsimp simp: upto_enum_step_shift_red[where us=2, simplified] word_size_def)
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
   apply (fold word_bits_def, assumption)
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
  apply(drule (2) word_less_power_trans_ofnat[where 'a=32, folded word_bits_def])
  apply simp
  apply(subst add.commute)
  apply(erule is_aligned_add_less_t2n)
  apply(simp_all)
  done



lemma dmo_clearMemory_globals_equiv:
  "\<lbrace> globals_equiv s and (\<lambda> s. is_aligned ptr bits \<and> 2 \<le> bits \<and> bits < word_bits \<and> ptr_range ptr bits \<inter> range_of_arm_globals_frame s = {})\<rbrace>
   do_machine_op (clearMemory ptr (2 ^ bits))
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply(rule hoare_pre)
  apply(simp add: do_machine_op_def clearMemory_def split_def cleanCacheRange_PoU_def)
  apply(wp)
  apply clarsimp
  apply(erule use_valid)
  apply(wp mapM_x_wp' storeWord_globals_equiv mol_globals_equiv | simp add: cleanByVA_PoU_def)+
  apply(simp_all)
  apply(frule is_aligned_2_upto_enum_step_mem, assumption+)
  apply(drule ptr_range_subset, assumption+)
  apply blast
  done

lemma dmo_clearMemory_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. is_aligned ptr bits \<and> 2 \<le> bits \<and> bits < word_bits \<and> ptr_range ptr bits \<inter> range_of_arm_globals_frame s = {}) (do_machine_op (clearMemory ptr (2 ^bits)))"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_g)
    apply(rule dmo_clearMemory_reads_respects)
   apply(rule doesnt_touch_globalsI[OF dmo_clearMemory_globals_equiv])
  apply clarsimp
  done

lemma dmo_freeMemory_globals_equiv:
  "\<lbrace> globals_equiv s and (\<lambda> s. is_aligned ptr bits \<and> 2 \<le> bits \<and> bits < word_bits \<and> ptr_range ptr bits \<inter> range_of_arm_globals_frame s = {})\<rbrace>
   do_machine_op (freeMemory ptr bits)
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  apply(rule hoare_pre)
  apply(simp add: do_machine_op_def freeMemory_def split_def)  
  apply(wp)
  apply clarsimp
  apply(erule use_valid)
  apply(wp mapM_x_wp' storeWord_globals_equiv mol_globals_equiv)
  apply(simp_all)
  apply(frule is_aligned_2_upto_enum_step_mem, assumption+)
  apply(drule ptr_range_subset, assumption+)
  apply blast
  done

lemma dmo_freeMemory_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. is_aligned ptr bits \<and> 2 \<le> bits \<and> bits < word_bits \<and> ptr_range ptr bits \<inter> range_of_arm_globals_frame s = {}) (do_machine_op (freeMemory ptr bits))"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_g)
    apply(rule dmo_freeMemory_reads_respects)
   apply(rule doesnt_touch_globalsI[OF dmo_freeMemory_globals_equiv])
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

lemma create_word_objects_reads_respects:
  "reads_respects aag l \<top> (create_word_objects ptr bits sz)"
  unfolding create_word_objects_def fun_app_def reserve_region_def
  apply(subst do_machine_op_mapM_x[OF empty_fail_clearMemory])
  apply(wp dmo_clearMemory_reads_respects mapM_x_ev | simp)+
  done

lemma create_word_objects_globals_equiv:
  notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  shows
  "\<lbrace> globals_equiv s and (\<lambda> s. range_cover ptr sz bits numObjects \<and> 
     (0::word32) < of_nat numObjects \<and> 2 \<le> bits \<and> {ptr..ptr + of_nat numObjects * 2 ^ bits - 1} \<inter> range_of_arm_globals_frame s = {})\<rbrace>
   create_word_objects ptr numObjects bits
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  unfolding create_word_objects_def reserve_region_def fun_app_def do_machine_op_def
  apply(rule hoare_pre)
  apply(simp add: do_machine_op_def clearMemory_def split_def cleanCacheRange_PoU_def)
  apply(wp)
  apply clarsimp
  apply(erule use_valid)
  apply(wp mapM_x_wp' storeWord_globals_equiv mol_globals_equiv | simp add: cleanByVA_PoU_def)+
  apply(simp_all)
  apply(drule ptr_range_subset[rotated])
     apply (simp add: range_cover_def[where 'a=32, folded word_bits_def])+
   apply (fastforce intro: is_aligned_add is_aligned_shiftl_self)
  apply(erule disjoint_subset)
  apply(erule disjoint_subset[rotated]) 
  apply(clarsimp del: subsetI simp: shiftl_t2n ptr_range_def)
  apply(drule_tac p="unat n" in range_cover_subset)
    apply(rule unat_less_helper)
    apply(rule minus_one_helper5)
     apply simp
    apply assumption
   apply(fastforce dest: unat_less_helper)
  apply(clarsimp simp: mult.commute)
  done

lemma create_word_objects_reads_respects_g:
  "reads_respects_g aag l (\<lambda> s. range_cover ptr sz bits numObjects \<and> 
     (0::word32) < of_nat numObjects \<and> 2 \<le> bits \<and> {ptr..ptr + of_nat numObjects * 2 ^ bits - 1} \<inter> range_of_arm_globals_frame s = {}) (create_word_objects ptr numObjects bits)"
  apply(rule equiv_valid_guard_imp)
   apply(rule reads_respects_g)
    apply(rule create_word_objects_reads_respects)
   apply(rule doesnt_touch_globalsI[OF create_word_objects_globals_equiv])
  apply auto
  done

crunch arm_global_pd: copy_global_mappings "\<lambda> s. P (arm_global_pd (arch_state s))"
  (wp: crunch_wps simp: crunch_simps)

definition word_object_range_cover_globals where
  "word_object_range_cover_globals new_type ptr sz num_objects s \<equiv>
   if new_type
      \<in> ArchObject ` {SmallPageObj, LargePageObj, SectionObj, SuperSectionObj}
   then range_cover ptr sz (word_object_size new_type) num_objects \<and>
        ({ptr..ptr + of_nat num_objects * 2 ^ word_object_size new_type - 1} \<inter> 
         range_of_arm_globals_frame s = {})
   else True"

lemma init_arch_objects_reads_respects_g:
  "reads_respects_g aag l 
         ((\<lambda> s. arm_global_pd (arch_state s) \<notin> set refs \<and> 
                 pspace_aligned s \<and> valid_arch_state s) and
          word_object_range_cover_globals new_type ptr sz num_objects and
          K (\<forall>x\<in>set refs. is_subject aag x) and
          K (\<forall>x\<in>set refs. new_type = ArchObject PageDirectoryObj
                            \<longrightarrow> is_aligned x pd_bits) and
          K ((0::word32) < of_nat num_objects))
        (init_arch_objects new_type ptr num_objects obj_sz refs)"
  apply(unfold init_arch_objects_def fun_app_def)
  apply(rule gen_asm_ev)+
  apply(subst do_machine_op_mapM_x[OF empty_fail_cleanCacheRange_PoU])+
  apply(rule equiv_valid_guard_imp)
  apply(wp create_word_objects_reads_respects_g dmo_cleanCacheRange_reads_respects_g mapM_x_ev'' equiv_valid_guard_imp[OF copy_global_mappings_reads_respects_g] copy_global_mappings_valid_arch_state copy_global_mappings_pspace_aligned copy_global_mappings_arm_global_pd hoare_vcg_ball_lift | wpc | simp)+
  apply(fastforce simp: word_object_range_cover_globals_def word_object_size_def)
  done

lemma copy_global_mappings_globals_equiv:
  "\<lbrace> globals_equiv s and (\<lambda> s. x \<noteq> arm_global_pd (arch_state s) \<and> is_aligned x pd_bits)\<rbrace> 
   copy_global_mappings x
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  unfolding copy_global_mappings_def
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
     word_object_range_cover_globals new_type ptr sz num_objects and
     K (\<forall>x\<in>set refs. new_type = ArchObject PageDirectoryObj
                            \<longrightarrow> is_aligned x pd_bits) and
     K ((0::word32) < of_nat num_objects)\<rbrace>
   (init_arch_objects new_type ptr num_objects obj_sz refs)
   \<lbrace> \<lambda>_. globals_equiv s \<rbrace>"
  unfolding init_arch_objects_def fun_app_def
  apply(rule hoare_gen_asm)+
  apply(subst do_machine_op_mapM_x[OF empty_fail_cleanCacheRange_PoU])+
  apply(rule hoare_pre)
  apply(wpc | wp create_word_objects_globals_equiv mapM_x_wp[OF dmo_cleanCacheRange_PoU_globals_equiv subset_refl])+
  apply(rule_tac Q="\<lambda>_. globals_equiv s and (\<lambda> s. arm_global_pd (arch_state s) \<notin> set refs)" in hoare_strengthen_post)
      apply(wp mapM_x_wp[OF _ subset_refl] copy_global_mappings_globals_equiv copy_global_mappings_arm_global_pd copy_global_mappings_arm_globals_frame dmo_cleanCacheRange_PoU_globals_equiv | simp | blast)+
  apply (fastforce simp: word_object_range_cover_globals_def word_object_size_def)
  done

lemma create_cap_reads_respects_g:
  "reads_respects_g aag l (K (is_subject aag (fst (fst slot))) and valid_global_objs) (create_cap type bits untyped slot)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g])
    apply(rule create_cap_reads_respects)
   apply(rule doesnt_touch_globalsI[OF create_cap_globals_equiv])
  by simp

lemma default_object_not_asid_pool:
  "\<lbrakk>type \<noteq> ArchObject ASIDPoolObj; type \<noteq> Untyped\<rbrakk> \<Longrightarrow>
        \<not> default_object type o_bits = ArchObj (ASIDPool asid_pool)"
  apply(clarsimp simp: default_object_def split: apiobject_type.splits simp: default_arch_object_def split: aobject_type.splits)
  done

lemma retype_region_ext_def2:
  "retype_region_ext a b =
   modify (\<lambda>exst. ekheap_update (\<lambda>ekh x. if x \<in> set a then default_ext b (cur_domain exst) else ekh x) exst)"
  apply (simp add: retype_region_ext_def foldr_upd_app_if' gets_def bind_def return_def
                   modify_def get_def put_def fun_eq_iff)
  done

lemma retype_region_reads_respects:
  "reads_respects aag l \<top> (retype_region ptr num_objects o_bits type)"
  apply(simp only: retype_region_def retype_addrs_def 
                   foldr_upd_app_if fun_app_def K_bind_def when_def
                   retype_region_ext_extended.dxo_eq
                   )
  apply (simp only: retype_region_ext_def2)
  apply(simp split del: split_if add: equiv_valid_def2)
  apply(rule_tac W="\<top>\<top>" and Q="\<top>\<top>" in equiv_valid_rv_bind)
    apply(rule equiv_valid_rv_guard_imp[OF if_evrv])
      apply (rule equiv_valid_rv_bind[OF gets_kheap_revrv])
       apply simp
       apply (rule_tac Q="\<lambda>_ s. rv = kheap s" and Q'="\<lambda>_ s. rv' = kheap s" and R'="op =" in equiv_valid_2_bind_pre)
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
    (\<lambda>s. \<exists>idx. cte_wp_at (\<lambda>c. c = UntypedCap (ptr && ~~ mask sz) sz idx)
               slot s \<and>
              (idx \<le> unat (ptr && mask sz) \<or>
               pspace_no_overlap ptr sz s)) and
    invs and
    K (range_cover ptr sz (obj_bits_api type o_bits) num_objects) and
    K (0 < num_objects)\<rbrace>
  retype_region ptr num_objects o_bits type
  \<lbrace>\<lambda>_. globals_equiv s\<rbrace>"
  apply(simp only: retype_region_def foldr_upd_app_if fun_app_def K_bind_def)
  apply (wp dxo_wp_weak |simp)+
      apply (simp add: trans_state_update[symmetric] del: trans_state_update)
     apply (wp | simp)+
  apply clarsimp
  apply (simp only: globals_equiv_def)
  apply (clarsimp split del: split_if)
  apply (subgoal_tac "pspace_no_overlap ptr sz sa")
   apply (rule conjI)
    apply(clarsimp simp: pspace_no_overlap_def)
    apply(drule_tac x="arm_global_pd (arch_state sa)" in spec)
    apply(clarsimp simp: invs_def valid_state_def valid_global_objs_def valid_ao_at_def obj_at_def ptr_add_def)
    apply(frule_tac p=p in range_cover_subset)
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
        ((\<lambda>s. \<exists>idx. cte_wp_at (\<lambda>c. c = UntypedCap (ptr && ~~ mask sz) sz idx)
                    slot s \<and>
                    (idx \<le> unat (ptr && mask sz) \<or>
                     pspace_no_overlap ptr sz s)) and
         invs and
         K (range_cover ptr sz (obj_bits_api type o_bits) num_objects) and
         K (0 < num_objects))
   (retype_region ptr num_objects o_bits type)"
  apply(rule equiv_valid_guard_imp[OF reads_respects_g[OF retype_region_reads_respects]])
   apply(rule doesnt_touch_globalsI)
   apply(rule hoare_weaken_pre[OF retype_region_globals_equiv])
   apply simp
  apply (auto)
  done

lemma post_retype_invs_valid_arch_stateI:
  "post_retype_invs ty rv s \<Longrightarrow> valid_arch_state s"
  apply(clarsimp simp: post_retype_invs_def invs_def valid_state_def split: split_if_asm)
  done

lemma post_retype_invs_pspace_alignedI:
  "post_retype_invs ty rv s \<Longrightarrow> pspace_aligned s"
  apply(clarsimp simp: post_retype_invs_def invs_def valid_state_def split: split_if_asm)
  done

lemma detype_def2: "detype S (s :: det_state) = s
\<lparr>kheap := \<lambda>x. if x \<in> S then None else kheap s x,
 ekheap := \<lambda>x. if x \<in> S then None else ekheap s x\<rparr>"
  apply (simp add: detype_def detype_ext_def)
  done

lemma states_equiv_for_detype:
  "states_equiv_for P Q R S X s s' \<Longrightarrow> states_equiv_for P Q R S X (detype N s) (detype N s')"
  
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
  "a_type ko = AArch (AIntData ARMSmallPage) \<Longrightarrow> 
  ko = ArchObj (DataPage ARMSmallPage)"
  apply (clarsimp simp: a_type_def
               split: Structures_A.kernel_object.splits 
                      arch_kernel_obj.splits split_if_asm)
  done

lemma obj_range_small_page_as_ptr_range:
  "obj_range ptr (ArchObj (DataPage ARMSmallPage)) =
   ptr_range ptr 12"
  apply(simp add: obj_range_def)
  apply(simp add: ptr_range_def)
  done


lemma untyped_caps_do_not_overlap_global_refs:
  "\<lbrakk>cte_wp_at (op = (UntypedCap word sz idx)) slot s;
    valid_global_refs s\<rbrakk> \<Longrightarrow>
  ptr_range word sz \<inter> global_refs s = {}"
   apply(simp add: cte_wp_at_caps_of_state)
   apply(drule (1) valid_global_refsD2)
   apply(fastforce simp: cap_range_def ptr_range_def)
  done

lemma untyped_caps_do_not_overlap_arm_globals_frame:
  "\<lbrakk>cte_wp_at (op = (UntypedCap word sz idx)) slot s; valid_objs s;
    valid_arch_state s; valid_global_refs s\<rbrakk> \<Longrightarrow>
  ptr_range word sz \<inter> range_of_arm_globals_frame s = {}"
  apply(frule (1) cte_wp_at_valid_objs_valid_cap)
  apply(clarsimp simp: valid_cap_def valid_untyped_def)
  apply(clarsimp simp: valid_arch_state_def)
  apply(clarsimp simp: obj_at_def)
  apply(drule_tac x="arm_globals_frame (arch_state s)" in spec)
  apply(drule_tac x="ArchObj (DataPage ARMSmallPage)" in spec)
  apply(simp add: cte_wp_at_caps_of_state)
  apply(drule (1) valid_global_refsD2)
  apply(fold ptr_range_def)
  apply(clarsimp simp: cap_range_def, fold ptr_range_def)
  apply(simp add: obj_range_small_page_as_ptr_range)
  apply(rule ccontr)
  apply(simp add: Int_ac)
  apply(clarsimp simp: global_refs_def)
  apply(fastforce simp: ptr_range_def)
  done
  
lemma obj_range_page_as_ptr_range_pageBitsForSize:
  "obj_range ptr (ArchObj (DataPage vmpage_size)) =
   ptr_range ptr (pageBitsForSize vmpage_size)"
  apply(simp add: obj_range_def)
  apply(simp add: ptr_range_def)
  done


lemma pspace_distinct_def':
  "pspace_distinct \<equiv> \<lambda>s. \<forall>x y ko ko'.
             kheap s x = Some ko \<and> kheap s y = Some ko' \<and> x \<noteq> y \<longrightarrow>
             obj_range x ko \<inter> obj_range y ko' = {}"
  by(auto simp: pspace_distinct_def obj_range_def field_simps)

lemma page_caps_do_not_overlap_arm_globals_frame:
  "\<lbrakk>cte_wp_at (op = (ArchObjectCap (PageCap word fun vmpage_size option))) slot s; valid_objs s;
    valid_arch_state s; valid_global_refs s; pspace_distinct s\<rbrakk> \<Longrightarrow>
  ptr_range word (pageBitsForSize vmpage_size) \<inter> range_of_arm_globals_frame s = {}"
  apply(frule (1) cte_wp_at_valid_objs_valid_cap)
  apply(clarsimp simp: valid_cap_def pspace_distinct_def')
  apply(clarsimp simp: valid_global_refs_def valid_refs_def)
  apply(drule_tac x="fst slot" in spec, drule_tac x="snd slot" in spec)
  apply(clarsimp simp: cte_wp_at_def cap_range_def)
  apply(rule ccontr)
  apply(drule_tac x=word in spec)
  apply(drule_tac x="arm_globals_frame (arch_state s)" in spec)
  apply(clarsimp simp: valid_arch_state_def obj_at_def global_refs_def)
  apply(simp add: obj_range_small_page_as_ptr_range)
  apply(simp add: obj_range_page_as_ptr_range_pageBitsForSize)
  done

lemma delete_objects_reads_respects_g:
 "reads_equiv_valid_g_inv (affects_equiv aag l) aag
    (\<lambda>s. arm_global_pd (arch_state s) \<notin> ptr_range p b \<and>
         idle_thread s \<notin> ptr_range p b \<and>
         is_aligned p b \<and> 2 \<le> b \<and> b < word_bits \<and>
         ptr_range p b \<inter> range_of_arm_globals_frame s = {})
    (delete_objects p b)"
  apply (simp add: delete_objects_def2)
  apply (rule equiv_valid_guard_imp)
   apply (wp dmo_freeMemory_reads_respects_g)
    apply (rule detype_reads_respects_g)
   apply wp
  apply (unfold ptr_range_def)
  apply simp
  done

lemma word_object_range_cover_globals_inv:
  assumes agpd:
    "\<And> P. \<lbrace> \<lambda> s. P (arm_globals_frame (arch_state s)) \<rbrace> 
           f 
           \<lbrace> \<lambda> rv s. P (arm_globals_frame (arch_state s)) \<rbrace>"
  shows
    "\<lbrace> word_object_range_cover_globals new_type ptr sz num_objects \<rbrace> f
     \<lbrace>\<lambda>_. word_object_range_cover_globals new_type ptr sz num_objects\<rbrace>"
  apply(clarsimp simp: valid_def word_object_range_cover_globals_def split_def)
  apply safe
     apply(drule use_valid |
           rule_tac P="\<lambda> y. {ptr..ptr + of_nat num_objects * 2 ^ sz - 1} \<inter> ptr_range y 12 = {}"
           for sz in agpd | fastforce)+
  done
    
      
lemma set_cap_reads_respects_g:
  "reads_respects_g aag l (valid_global_objs and K (is_subject aag (fst slot))) (set_cap cap slot)"
  apply(rule equiv_valid_guard_imp) 
   apply(rule reads_respects_g[OF set_cap_reads_respects])
   apply(rule doesnt_touch_globalsI[OF set_cap_globals_equiv])
  by simp

(* FIXME: put this into Retype_AC instead *)   
lemma set_free_index_invs':
  "\<lbrace> (\<lambda>s. invs s \<and>
         cte_wp_at (op = cap) slot s \<and>
         (free_index_of cap \<le> idx' \<or> 
          (descendants_range_in {word1..word1 + 2 ^ sz - 1} slot s \<and>
           pspace_no_overlap word1 sz s)) \<and>
         idx' \<le> 2 ^ sz \<and> 
         is_untyped_cap cap) and K(word1 = obj_ref_of cap \<and> sz = bits_of cap)\<rbrace>
       set_cap
           (UntypedCap word1 sz idx')
            slot
       \<lbrace>\<lambda>_. invs \<rbrace>"
  apply(rule hoare_gen_asm)
  apply(case_tac cap, simp_all add: bits_of_def)
  apply(case_tac "free_index_of cap \<le> idx'")
   apply simp
    apply(cut_tac cap=cap and cref=slot and idx="idx'" in set_free_index_invs)
    apply(simp add: free_index_update_def conj_comms)
   apply simp
   apply(wp set_untyped_cap_invs_simple | simp)+
   apply(fastforce simp: cte_wp_at_def)
   done

(*FIXME move*)
lemma when_ev:
  "\<lbrakk>C \<Longrightarrow> equiv_valid I A A P handle\<rbrakk> \<Longrightarrow>
   equiv_valid I A A (\<lambda>s. C \<longrightarrow> P s) (when C handle)"
  apply (wp | auto simp: when_def)+
  done


lemma delete_objects_caps_no_overlap:
  "\<lbrace> invs and ct_active and (\<lambda> s. \<exists> slot idx. cte_wp_at (op = (UntypedCap ptr sz idx)) slot s \<and> descendants_range_in {ptr..ptr + 2 ^ sz - 1} slot s) \<rbrace> delete_objects ptr sz \<lbrace>\<lambda>_. caps_no_overlap ptr sz\<rbrace>"
  apply(clarsimp simp: valid_def)
  apply(rule descendants_range_caps_no_overlapI)
    apply(erule use_valid | wp | simp add: descendants_range_def2 | blast)+
   apply(frule untyped_cap_aligned, 
         (simp add: is_aligned_neg_mask_eq invs_valid_objs)+)
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


lemma word_object_range_cover_globalsI:
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
  shows
  "\<lbrakk>range_cover ptr sz (obj_bits_api new_type us) num_objects;
        cte_wp_at (op = (UntypedCap (ptr && ~~ mask sz) sz idx)) slot s; invs s;
        num_objects \<noteq> 0\<rbrakk> \<Longrightarrow> 
       word_object_range_cover_globals new_type ptr sz num_objects s"
  apply(clarsimp simp: word_object_range_cover_globals_def obj_bits_api_def word_object_size_def default_arch_object_def)
  apply(frule range_cover_subset', simp+)
  apply(frule untyped_caps_do_not_overlap_arm_globals_frame, (simp add: invs_valid_objs invs_arch_state invs_valid_global_refs)+)
  apply(clarsimp split: apiobject_type.splits aobject_type.splits simp: default_arch_object_def)
     apply(erule disjoint_subset)
     apply(erule disjoint_subset[rotated])
     apply(simp add: ptr_range_def blah word_and_le2)
    apply(erule disjoint_subset)
    apply(erule disjoint_subset[rotated])
    apply(simp add: ptr_range_def blah word_and_le2)
   apply(erule disjoint_subset)
   apply(erule disjoint_subset[rotated])
   apply(simp add: ptr_range_def blah word_and_le2)
  apply(erule disjoint_subset)
  apply(erule disjoint_subset[rotated])
  apply(simp add: ptr_range_def blah word_and_le2)
  done
  

lemma invoke_untyped_reads_respects_g:
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  shows
  "reads_respects_g aag l (invs and valid_untyped_inv ui and ct_active and authorised_untyped_inv_state aag ui and K (authorised_untyped_inv aag ui)) (invoke_untyped ui)"
  apply(case_tac ui)
  apply(rename_tac cslot_ptr word1 word2 apiobject_type nat list)
  apply(simp add: mapM_x_def[symmetric])
  apply(wp mapM_x_ev'' create_cap_reads_respects_g hoare_vcg_ball_lift
           create_cap_valid_global_objs init_arch_objects_reads_respects_g
        | simp)+
           apply(rule_tac Q="\<lambda>_. invs" in hoare_strengthen_post)
            apply(wp init_arch_objects_invs_from_restricted)
           apply(fastforce simp: invs_def)
          apply(wp retype_region_reads_respects_g[where slot="slot_of_untyped_inv ui"])
         apply(rule_tac Q="\<lambda>rvc s. 
                              word_object_range_cover_globals apiobject_type word2 sz (length list) s \<and> 
                                (\<forall>x\<in>set rvc. is_subject aag x) \<and>
                                (\<forall>x\<in>set rvc. is_aligned x (obj_bits_api apiobject_type nat)) \<and> 
                                ((0::word32) < of_nat (length list)) \<and>
                                post_retype_invs apiobject_type rvc s \<and>
                                global_refs s \<inter> set rvc = {} \<and> 
                                (\<forall>x\<in>set list. is_subject aag (fst x))"
                for sz in hoare_strengthen_post)
          apply(wp word_object_range_cover_globals_inv 
                   retype_region_ret_is_subject[simplified] 
                   retype_region_global_refs_disjoint 
                   retype_region_ret_pd_aligned 
                   retype_region_aligned_for_init 
                   retype_region_post_retype_invs)
         apply(fastforce simp: global_refs_def 
                        intro: post_retype_invs_pspace_alignedI 
                               post_retype_invs_valid_arch_stateI 
                        simp: obj_bits_api_def default_arch_object_def 
                              pd_bits_def pageBits_def 
                        elim: in_set_zipE)
        apply(rule set_cap_reads_respects_g)
       apply simp
       (* sanitise postcondition *)
       apply(rule_tac Q="\<lambda>rvb s.
           (\<exists>idx. cte_wp_at
                   (\<lambda>c. c =
                        UntypedCap
                         (word2 &&
                          ~~ mask
                              (bits_of rv))
                         (bits_of rv)
                         idx)
                   cslot_ptr s \<and>
                  (idx
                   \<le> unat
                      (word2 &&
                       mask
                        (bits_of rv)) \<or>
                   pspace_no_overlap word2 (bits_of rv) s)) \<and>
           invs s \<and>
            range_cover word2 (bits_of rv)
            (obj_bits_api apiobject_type nat) (length list) \<and> 
           list \<noteq> [] \<and>
           word_object_range_cover_globals apiobject_type word2
            (bits_of rv)
            (length list) s \<and>
(\<forall>x\<in>{word2..(word2 &&
                        ~~ mask
                            (bits_of rv)) +
                       (2 ^
                        (bits_of rv) -
                        1)}.
               is_subject aag x) \<and> (0::word32) < of_nat (length list) \<and>
pspace_no_overlap word2
            (bits_of rv) s \<and>
caps_no_overlap word2
            (bits_of rv) s \<and> 
 caps_overlap_reserved
            {word2..word2 +
                    of_nat (length list) *
                    2 ^ obj_bits_api apiobject_type nat -
                    1}
            s \<and> 
region_in_kernel_window
            {word2..(word2 &&
                     ~~ mask
                         (bits_of rv)) +
                    2 ^
                    (bits_of rv) -
                    1}
            s \<and> (apiobject_type = CapTableObject \<longrightarrow> 0 < nat) \<and>
{word2..(word2 &&
                    ~~ mask
                        (bits_of rv)) +
                   2 ^
                   bits_of rv -
                   1} \<inter>
           global_refs s =
           {} \<and>  (\<forall>x\<in>set list. is_subject aag (fst x))
" in hoare_strengthen_post)
        apply(wp hoare_vcg_ex_lift set_cap_cte_wp_at_cases
                 hoare_vcg_disj_lift set_cap_no_overlap set_free_index_invs'
                 word_object_range_cover_globals_inv 
                 set_untyped_cap_caps_overlap_reserved
                 set_cap_caps_no_overlap
                 region_in_kernel_window_preserved)
       apply clarsimp
       apply(rule conjI)
        apply(rule_tac x=idx in exI)
        apply fastforce
       apply fastforce
      apply(wp when_ev delete_objects_reads_respects_g hoare_vcg_disj_lift
               delete_objects_pspace_no_overlap 
               delete_objects_descendants_range_in
               word_object_range_cover_globals_inv
               delete_objects_caps_no_overlap
               region_in_kernel_window_preserved
               get_cap_reads_respects_g get_cap_wp
           |strengthen invs_valid_global_objs_strg
           |simp split del: split_if)+
  apply(clarsimp simp: conj_comms cong: conj_cong split del: split_if simp: authorised_untyped_inv_def authorised_untyped_inv_state_def)
  apply(drule (1) cte_wp_at_eqD2, clarsimp split del: split_if simp: cte_wp_at_sym)
  apply(frule cte_wp_at_valid_objs_valid_cap, simp add: invs_valid_objs)
  apply(clarsimp simp: valid_cap_def cap_aligned_def is_aligned_neg_mask_eq bits_of_UntypedCap split del: split_if cong: if_cong)
  apply(intro conjI)
   apply(clarsimp)
   apply(rule conjI)
   apply (fastforce dest: untyped_caps_do_not_overlap_global_refs simp: global_refs_def)
   apply (rule conjI)
    apply(fastforce dest: untyped_caps_do_not_overlap_global_refs simp: global_refs_def)
   apply(erule untyped_caps_do_not_overlap_arm_globals_frame, auto simp: invs_def valid_state_def)[1]
  apply clarsimp
  apply(intro impI conjI)
  apply(simp_all add: invs_psp_aligned invs_valid_objs cte_wp_cte_at bits_of_UntypedCap)
                                        apply(clarsimp simp: descendants_range_def2 blah)
                                        apply(rule ssubst[OF free_index_of_UntypedCap])
                                        apply fastforce
                                       apply(fastforce dest!: untyped_slots_not_in_untyped_range[OF _ _ _ _ _ subset_refl] simp: blah)
                                      apply(fastforce intro!: disjI2)
                                     apply(clarsimp simp: descendants_range_def2 blah)
                                     apply(rule ssubst[OF free_index_of_UntypedCap])
                                     apply fastforce
                                    apply(fastforce dest!: untyped_slots_not_in_untyped_range[OF _ _ _ _ _ subset_refl] simp: blah)
                                   apply(fastforce intro!: disjI2)
                                  apply(frule range_cover.range_cover_compare_bound)
                                  apply(frule range_cover.unat_of_nat_n)
                                  apply(simp add: shiftl_t2n)
                                  apply(subst unat_mult_power_lem)
                                  apply(erule range_cover.string)
                                 apply(simp add: mult.commute)
                                apply(fastforce intro!: word_object_range_cover_globalsI)
                               apply(fastforce simp: ptr_range_def bits_of_UntypedCap p_assoc_help)
                              apply fastforce
                             apply(fastforce simp: cte_wp_at_def blah)
                            apply(fastforce dest!: untyped_slots_not_in_untyped_range[OF _ _ _ _ _ subset_refl] simp: blah)
                           apply fastforce
                          apply(clarsimp simp: descendants_range_def2 blah)
                          apply(rule ssubst[OF free_index_of_UntypedCap])
                          apply fastforce
                         apply(fastforce dest: range_cover_subset')
                        apply(subgoal_tac "usable_untyped_range
           (UntypedCap (word2 && ~~ mask sz) sz
             (unat
               ((word2 && mask sz) + of_nat (length list) * 2 ^ obj_bits_api apiobject_type nat))) \<inter>
          {word2..word2 +
                  of_nat (length list) * 2 ^ obj_bits_api apiobject_type nat - 1} = {}")
                         apply(subgoal_tac "word2 && mask sz = 0", clarsimp simp: shiftl_t2n mult.commute)
                         apply(erule subst, rule mask_neg_mask_is_zero)
                        apply(rule usable_range_disjoint, simp+)
                         apply(fastforce elim: ex_cte_cap_wp_to_weakenE)
                        apply assumption
                       apply fastforce
                      apply(erule ssubst[OF free_index_of_UntypedCap])
                     apply(drule cap_refs_in_kernel_windowD2)
                      apply(simp add: invs_cap_refs_in_kernel_window)
                     apply(fastforce simp: cap_range_def blah)
                    apply(fastforce dest!: untyped_caps_do_not_overlap_global_refs simp: invs_valid_global_refs ptr_range_def)
                   apply(simp add: invs_valid_global_objs)
                  apply(rule disjI2)
                  apply(fastforce intro!: cte_wp_at_pspace_no_overlapI simp: cte_wp_at_sym)
                 apply(rule disjI1)
                 apply(simp add: free_index_of_UntypedCap)
                 apply(simp add: mask_out_sub_mask add.commute mult.commute shiftl_t2n)
                 apply(erule order_trans)
                 apply(simp add: range_cover_unat)
                apply(simp add: mask_out_sub_mask add.commute mult.commute)
                apply (rule le_trans[OF unat_plus_gt])
                apply(subst range_cover.unat_of_nat_n_shift, simp+)
                apply(simp add: range_cover.range_cover_compare_bound[simplified add.commute])
               apply(simp add: bits_of_UntypedCap)+
            apply(fastforce intro!: word_object_range_cover_globalsI)
           apply(drule_tac x="UntypedCap (word2 && ~~ mask sz) sz idx" in spec)
           apply(clarsimp simp: ptr_range_def p_assoc_help bits_of_UntypedCap)
           apply(erule_tac A="{word2 && ~~ mask sz..b}" for b in bspec)
           apply(erule subsetD[rotated])
           apply(simp add: blah word_and_le2)
          apply(fastforce intro!: cte_wp_at_pspace_no_overlapI simp: cte_wp_at_sym)
         apply(fastforce simp: cte_wp_at_def blah)
        apply(fastforce intro!: cte_wp_at_caps_no_overlapI simp: cte_wp_at_sym)
       apply(drule range_cover_subset', simp)
       apply(erule subset_trans)
       apply(simp add: blah word_and_le2)
      apply(simp add: shiftl_t2n mask_out_sub_mask add.commute mult.commute)
      apply(simp add: mask_out_sub_mask[symmetric])
      apply(rule usable_range_disjoint, simp+)
       apply(fastforce elim: ex_cte_cap_wp_to_weakenE)
      apply assumption
     apply(rule descendants_range_in_subseteq[OF cte_wp_at_caps_descendants_range_inI])
         apply (simp add: cte_wp_at_sym)+
     apply(fastforce dest: range_cover_subset')
    apply(simp add: free_index_of_UntypedCap)
   apply(drule cap_refs_in_kernel_windowD2)
    apply(simp add: invs_cap_refs_in_kernel_window)
   apply(clarsimp simp: cap_range_def)
   apply(erule region_in_kernel_window_subseteq)
   apply(simp add: word_and_le2 blah)
  apply(drule untyped_caps_do_not_overlap_global_refs)
   apply(simp add: invs_valid_global_refs)
  apply(erule disjoint_subset[rotated])
  apply(simp add: ptr_range_def blah word_and_le2)
  done
  

declare modify_wp [wp del]

lemma delete_objects_globals_equiv[wp]:
  "\<lbrace>globals_equiv st and
    (\<lambda>s. is_aligned p b \<and> 2 \<le> b \<and> b < word_bits \<and>
         ptr_range p b \<inter> range_of_arm_globals_frame s = {} \<and>
         arm_global_pd (arch_state s) \<notin> ptr_range p b \<and>
         idle_thread s \<notin> ptr_range p b)\<rbrace>
   delete_objects p b
   \<lbrace>\<lambda>_. globals_equiv st\<rbrace>"
  apply (simp add: delete_objects_def)
  apply (wp detype_globals_equiv dmo_freeMemory_globals_equiv)
  apply (clarsimp simp: ptr_range_def)+
  done

fun slots_of_untyped_inv where "slots_of_untyped_inv (Retype _ _ _ _ _ slots ) = slots"

lemma invoke_untyped_globals_equiv:
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
  shows
  "\<lbrace> globals_equiv st and invs and valid_untyped_inv ui and ct_active and
     K ((0::word32) < of_nat (length (slots_of_untyped_inv ui))) \<rbrace>
   invoke_untyped ui
   \<lbrace> \<lambda>_. globals_equiv st \<rbrace>"
  apply(rule hoare_gen_asm)
  apply(case_tac ui)
  apply(rename_tac cslot_ptr word1 word2 apiobject_type nat list)
  apply(simp add: mapM_x_def[symmetric])
  apply(wp)
      apply(rule_tac Q="\<lambda>_. globals_equiv st and valid_global_objs" in hoare_strengthen_post)
       apply(wp mapM_x_wp[OF _ subset_refl] create_cap_globals_equiv | simp)+
    apply(rule_tac Q="\<lambda>_. globals_equiv st and invs" in hoare_strengthen_post)
     apply(wp init_arch_objects_globals_equiv init_arch_objects_invs_from_restricted)
    apply(fastforce simp: invs_def)
   apply(rule_tac Q="\<lambda> rva s. globals_equiv st s \<and> 
word_object_range_cover_globals apiobject_type word2
                sz
                (length list) s \<and> 
                   ((0::word32) < of_nat (length list)) \<and>
                              (\<forall>x\<in>set rva. is_aligned x (obj_bits_api apiobject_type nat)) \<and> 
                              (post_retype_invs apiobject_type rva s) \<and> 
                              (global_refs s \<inter> set rva = {})" for sz in hoare_strengthen_post)
    apply(wp retype_region_ret_is_subject[simplified] retype_region_global_refs_disjoint retype_region_ret_pd_aligned retype_region_aligned_for_init retype_region_post_retype_invs retype_region_globals_equiv[where slot="slot_of_untyped_inv ui"] word_object_range_cover_globals_inv)[1]
   apply(auto simp: global_refs_def simp: obj_bits_api_def default_arch_object_def pd_bits_def pageBits_def post_retype_invs_def)[1]
   apply (fold ptr_range_def, simp)
   apply(rule_tac
     Q="\<lambda>ya s. globals_equiv st s \<and>
 (\<exists>idx. cte_wp_at
                   (\<lambda>c. c =
                        UntypedCap
                         (word2 &&
                          ~~ mask
                              (bits_of cap))
                         (bits_of cap)
                         idx)
                   cslot_ptr s \<and>
                  (idx
                   \<le> unat
                      (word2 &&
                       mask
                        (bits_of cap)) \<or>
                   pspace_no_overlap word2
                    (bits_of cap)
                    s)) \<and>
           invs s \<and> range_cover word2
            (bits_of cap)
            (obj_bits_api apiobject_type nat) (length list) \<and>
           list \<noteq> [] \<and>
           word_object_range_cover_globals apiobject_type word2
            (bits_of cap)
            (length list) s \<and>
           (0::word32) < of_nat (length list) \<and>
            caps_no_overlap word2 (bits_of cap) s \<and>  
           pspace_no_overlap word2 (bits_of cap) s \<and> 
           caps_overlap_reserved
            {word2..word2 +
                    of_nat (length list) *
                    2 ^ obj_bits_api apiobject_type nat -
                    1}
            s \<and>
           region_in_kernel_window
            {word2..(word2 &&
                     ~~ mask
                         (bits_of cap)) +
                    2 ^
                    (bits_of cap) -
                    1}
            s \<and>
           (apiobject_type = CapTableObject \<longrightarrow> 0 < nat) \<and>
{word2..(word2 &&
                    ~~ mask
                        (bits_of cap)) +
                   2 ^
                   (bits_of cap) -
                   1} \<inter>
           global_refs s =
           {}
           " in hoare_strengthen_post)
     apply (wp set_cap_globals_equiv hoare_vcg_ex_lift set_cap_cte_wp_at_cases
               hoare_vcg_disj_lift set_cap_no_overlap set_free_index_invs'
               word_object_range_cover_globals_inv set_cap_caps_no_overlap
               set_untyped_cap_caps_overlap_reserved 
               region_in_kernel_window_preserved)
    apply fastforce
   apply(wp hoare_vcg_ex_lift hoare_vcg_disj_lift 
            delete_objects_pspace_no_overlap delete_objects_descendants_range_in
            word_object_range_cover_globals_inv delete_objects_caps_no_overlap
            region_in_kernel_window_preserved get_cap_wp
        | simp split del: split_if
        | strengthen invs_valid_global_objs_strg)+
  apply(clarsimp simp: conj_comms cong: conj_cong split del: split_if simp: authorised_untyped_inv_def authorised_untyped_inv_state_def)
  apply(drule (1) cte_wp_at_eqD2, clarsimp split del: split_if simp: cte_wp_at_sym)
  apply(frule cte_wp_at_valid_objs_valid_cap, simp add: invs_valid_objs)  
  apply(split split_if)
  apply(intro impI conjI)
  apply(simp_all add: invs_psp_aligned invs_valid_objs cte_wp_cte_at bits_of_UntypedCap)
                                     apply(clarsimp simp: valid_cap_def cap_aligned_def)
                                     apply(rule conjI)
                                      apply (erule untyped_caps_do_not_overlap_arm_globals_frame, (simp add: invs_valid_objs invs_arch_state invs_valid_global_refs)+)
                                     apply(fastforce dest!: untyped_caps_do_not_overlap_global_refs simp: invs_valid_global_refs ptr_range_def global_refs_def)
                                    apply(clarsimp simp: descendants_range_def2 blah)
                                    apply(rule ssubst[OF free_index_of_UntypedCap])
                                    apply(fastforce simp: ptr_range_def)
                                   apply(fastforce dest!: untyped_slots_not_in_untyped_range[OF _ _ _ _ _ subset_refl] simp: blah ptr_range_def)
                                  apply(fastforce intro!: disjI2)
                                 apply(clarsimp simp: descendants_range_def2 blah)
                                 apply(rule ssubst[OF free_index_of_UntypedCap])
                                 apply(fastforce simp: ptr_range_def)
                                apply(fastforce dest!: untyped_slots_not_in_untyped_range[OF _ _ _ _ _ subset_refl] simp: blah ptr_range_def)
                               apply(fastforce intro!: disjI2 simp:ptr_range_def)
                              apply(frule range_cover.range_cover_compare_bound)
                              apply(frule range_cover.unat_of_nat_n)
                              apply(simp add: shiftl_t2n)
                              apply(subst unat_mult_power_lem)
                              apply(erule range_cover.string)
                             apply(simp add: mult.commute)
                            apply(fastforce intro!: word_object_range_cover_globalsI)
                           apply(fastforce simp: ptr_range_def bits_of_UntypedCap p_assoc_help)
                          apply(fastforce simp: bits_of_UntypedCap)
                         apply(fastforce intro!: word_object_range_cover_globalsI)
                        apply(fastforce simp: cte_wp_at_def blah)
                       apply(fastforce dest!: untyped_slots_not_in_untyped_range[OF _ _ _ _ _ subset_refl] simp: blah ptr_range_def)
                      apply (fastforce simp: ptr_range_def)
                     apply fastforce
                    apply(clarsimp simp: descendants_range_def2 blah)
                    apply(rule ssubst[OF free_index_of_UntypedCap])
                    apply(fastforce simp: ptr_range_def)
                   apply(fastforce dest: range_cover_subset')
                  apply(subgoal_tac "usable_untyped_range
           (UntypedCap (word2 && ~~ mask sz) sz
             (unat
               ((word2 && mask sz) + of_nat (length list) * 2 ^ obj_bits_api apiobject_type nat))) \<inter>
          {word2..word2 +
                  of_nat (length list) * 2 ^ obj_bits_api apiobject_type nat -
                  1} =
          {}")
                   apply(subgoal_tac "word2 && mask sz = 0", clarsimp simp: shiftl_t2n mult.commute)
                   apply(erule subst, rule mask_neg_mask_is_zero)
                  apply(rule usable_range_disjoint, simp+)
                   apply(fastforce elim: ex_cte_cap_wp_to_weakenE)
                  apply assumption
                 apply(fastforce simp: ptr_range_def)
                apply(erule ssubst[OF free_index_of_UntypedCap])
               apply(drule cap_refs_in_kernel_windowD2)
                apply(simp add: invs_cap_refs_in_kernel_window)
               apply(fastforce simp: cap_range_def blah)
              apply(fastforce dest!: untyped_caps_do_not_overlap_global_refs simp: invs_valid_global_refs ptr_range_def)
             apply(simp add: invs_valid_global_objs)
            apply(rule disjI2)
            apply(fastforce intro!: cte_wp_at_pspace_no_overlapI simp: cte_wp_at_sym valid_cap_def cap_aligned_def)
           apply(rule conjI, assumption)
           apply(rule conjI)
            apply(rule disjI1)
            apply(simp add: free_index_of_UntypedCap)
            apply(simp add: mask_out_sub_mask add.commute mult.commute shiftl_t2n)
            apply(erule order_trans)
            apply(simp add: range_cover_unat)
           apply(simp add: mask_out_sub_mask add.commute mult.commute bits_of_UntypedCap)
           apply (rule le_trans[OF unat_plus_gt])
           apply(subst range_cover.unat_of_nat_n_shift, simp+)
           apply(simp add: range_cover.range_cover_compare_bound[simplified add.commute])
          apply(fastforce intro!: word_object_range_cover_globalsI)
         apply(rule conjI)
          apply(fastforce simp: cte_wp_at_def blah)
         apply(fastforce intro!: cte_wp_at_caps_no_overlapI simp: cte_wp_at_sym valid_cap_def cap_aligned_def)
        apply(fastforce intro!: cte_wp_at_pspace_no_overlapI simp: cte_wp_at_sym valid_cap_def cap_aligned_def)
       apply(drule range_cover_subset', simp)
       apply(erule subset_trans)
       apply(simp add: blah word_and_le2)
      apply(simp add: shiftl_t2n mask_out_sub_mask add.commute mult.commute)
      apply(simp add: mask_out_sub_mask[symmetric])
      apply(rule usable_range_disjoint, simp+)
       apply(fastforce elim: ex_cte_cap_wp_to_weakenE)
      apply assumption
     apply(rule descendants_range_in_subseteq[OF cte_wp_at_caps_descendants_range_inI])
         apply (simp add: cte_wp_at_sym valid_cap_def cap_aligned_def)+
     apply(fastforce dest: range_cover_subset')
    apply(simp add: free_index_of_UntypedCap)
   apply(drule cap_refs_in_kernel_windowD2)
    apply(simp add: invs_cap_refs_in_kernel_window)
   apply(clarsimp simp: cap_range_def)
   apply(erule region_in_kernel_window_subseteq)
   apply(simp add: word_and_le2 blah)
  apply(drule untyped_caps_do_not_overlap_global_refs)
   apply(simp add: invs_valid_global_refs)
  apply(erule disjoint_subset[rotated])
  apply(simp add: ptr_range_def blah word_and_le2)
  done

end

end
