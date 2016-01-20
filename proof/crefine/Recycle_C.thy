(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Recycle_C
imports Delete_C Retype_C
begin

context kernel_m
begin

lemma isArchPageCap_ArchObjectCap:
  "isArchPageCap (ArchObjectCap acap)
       = isPageCap acap"
  by (simp add: isArchPageCap_def isPageCap_def)

definition
  "replicateHider \<equiv> replicate"

lemma collapse_foldl_replicate:
  "replicate (length xs) v = xs \<Longrightarrow>
   foldl (op @) [] (map (\<lambda>_. xs) ys)
        = replicateHider (length xs * length ys) v"
  apply (induct ys rule: rev_induct)
   apply (simp add: replicateHider_def)
  apply (simp add: replicateHider_def)
  apply (subst add.commute, simp add: replicate_add)
  done

lemma coerce_memset_to_heap_update_user_data:
  "heap_update_list x (replicateHider 4096 0)
      = heap_update (Ptr x :: user_data_C ptr)
             (user_data_C (FCP (\<lambda>_. 0)))"
  apply (intro ext, simp add: heap_update_def)
  apply (rule_tac f="\<lambda>xs. heap_update_list x xs a b" for a b in arg_cong)
  apply (simp add: to_bytes_def size_of_def typ_info_simps user_data_C_tag_def)
  apply (simp add: ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def)
  apply (simp add: typ_info_simps 
                   user_context_C_tag_def thread_state_C_tag_def fault_C_tag_def
                   lookup_fault_C_tag_def update_ti_t_ptr_0s
                   ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td 
                   ti_typ_combine_empty_ti ti_typ_combine_td       
                   align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def 
                   align_td_array' size_td_array)
  apply (simp add: typ_info_array')
  apply (subst access_ti_list_array)
     apply simp
    apply simp
   apply (simp add: fcp_beta typ_info_word typ_info_ptr word_rsplit_0)
   apply fastforce
  apply (simp add: collapse_foldl_replicate)
  done

lemma clift_foldl_hrs_mem_update:
  "\<lbrakk> \<forall>x \<in> set xs. hrs_htd s \<Turnstile>\<^sub>t f x;
     \<And>x s. hrs_htd s \<Turnstile>\<^sub>t f x \<Longrightarrow> clift (hrs_mem_update (heap_update (f x) v) s)
                                  = g (clift s :: ('a :: c_type) ptr \<rightharpoonup> 'a) x \<rbrakk>
   \<Longrightarrow>
   clift (hrs_mem_update (\<lambda>s. foldl (\<lambda>s x. heap_update (f x) v s) s xs) s)
       = foldl g (clift s :: 'a ptr \<rightharpoonup> 'a) xs"
  using [[hypsubst_thin]]
  apply (cases s, clarsimp)
  apply (induct xs arbitrary: a b)
   apply (simp add: hrs_mem_update_def)
  apply (clarsimp simp add: hrs_mem_update_def split_def hrs_htd_def)
  done

lemma map_to_user_data_aligned:
  "\<lbrakk> map_to_user_data (ksPSpace s) x = Some y; pspace_aligned' s \<rbrakk>
        \<Longrightarrow> is_aligned x pageBits"
  apply (clarsimp simp: map_comp_eq projectKOs split: option.split_asm)
  apply (drule(1) pspace_alignedD')
  apply (simp add: objBits_simps)
  done

lemma help_force_intvl_range_conv:
  "\<lbrakk> is_aligned (p::word32) n; v = 2 ^ n; n < word_bits \<rbrakk>
    \<Longrightarrow> {p ..+ v} = {p .. p + 2 ^ n - 1}"
  by (simp add: intvl_range_conv word_bits_def)

lemma cmap_relation_If_upd:
  "\<lbrakk> cmap_relation f g ptrfun rel; rel v v'; ptrfun ` S = S'; inj ptrfun \<rbrakk>
   \<Longrightarrow> cmap_relation (\<lambda>x. if x \<in> S then Some v else f x)
                     (\<lambda>y. if y \<in> S' then Some v' else g y)
        ptrfun rel"
  apply (simp add: cmap_relation_def dom_If_Some)
  apply (rule context_conjI)
   apply blast
  apply clarsimp
  apply (case_tac "x \<in> S")
   apply simp
  apply clarsimp
  apply (subst if_not_P)
   apply (clarsimp simp: inj_eq)
  apply (drule bspec, erule domI)
  apply simp
  done

lemma length_replicateHider [simp]:
  "length (replicateHider n x) = n"
  by (simp add: replicateHider_def)

lemma coerce_heap_update_to_heap_updates':
  "n = chunk * m \<Longrightarrow>
  heap_update_list x (replicateHider n 0)
  = (\<lambda>s. foldl (\<lambda>s x. heap_update_list x (replicateHider chunk 0) s) s
    (map (\<lambda>n. x + (of_nat n * of_nat chunk)) [0 ..< m]))"
  using [[hypsubst_thin]]
  apply clarsimp
  apply (induct m arbitrary: x)
   apply (rule ext, simp)
   apply (simp add: replicateHider_def)
  apply (rule ext)
  apply (simp only: map_upt_unfold map_Suc_upt[symmetric])
  apply (simp add: replicate_add[folded replicateHider_def]
                   heap_update_list_concat_unfold
                   o_def field_simps
                   length_replicate[folded replicateHider_def])
  done

lemma h_t_valid_dom_s:
  "\<lbrakk> h_t_valid htd c_guard p; x = ptr_val (p :: ('a :: mem_type) ptr);
              n = size_of TYPE ('a) \<rbrakk>
    \<Longrightarrow> {x ..+ n} \<times> {SIndexVal, SIndexTyp 0} \<subseteq> dom_s htd"
  apply (clarsimp simp: h_t_valid_def valid_footprint_def Let_def
                        intvl_def)
  apply (drule_tac x=k in spec, simp add: size_of_def)
  apply (clarsimp simp: dom_s_def)
  apply (drule_tac x=0 in map_leD, simp_all)
  done

lemma user_page_at_rf_sr_dom_s:
  "\<lbrakk> typ_at' UserDataT x s; (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> {x ..+ 2 ^ pageBits} \<times> {SIndexVal, SIndexTyp 0}
    \<subseteq> dom_s (hrs_htd (t_hrs_' (globals s')))"
  apply (drule rf_sr_heap_relation)
  apply (drule user_data_at_ko)
  apply (erule_tac x=x in cmap_relationE1)
   apply (simp only: heap_to_page_data_def Let_def ko_at_projectKO_opt)
   apply simp
  apply (drule h_t_valid_clift)
  apply (simp add: h_t_valid_dom_s pageBits_def)
  done

lemma intvl_2_power_times_decomp:
  "\<forall>y < 2 ^ (n - m). {x + y * 2 ^ m ..+ 2 ^ m} \<times> S \<subseteq> T
    \<Longrightarrow> m \<le> n \<Longrightarrow> n < word_bits
    \<Longrightarrow> {(x :: word32) ..+ 2 ^ n} \<times> S \<subseteq> T"
  apply (clarsimp simp: intvl_def)
  apply (drule_tac x="of_nat k >> m" in spec)
  apply (drule mp)
   apply (rule shiftr_less_t2n)
   apply (rule word_of_nat_less)
   apply (simp add: word_of_nat_less)
  apply (erule subsetD)
  apply (clarsimp simp: shiftl_t2n[unfolded mult.commute mult.left_commute, symmetric]
                        shiftr_shiftl1)
  apply (rule_tac x="unat (of_nat k && mask m :: word32)" in exI)
  apply (simp add: field_simps word_plus_and_or_coroll2)
  apply (simp add: word_bits_def unat_less_power and_mask_less')
  done

lemma flex_user_page_at_rf_sr_dom_s:
  "\<lbrakk> (\<forall>p<2 ^ (pageBitsForSize sz - pageBits).
         typ_at' UserDataT (x + p * 2 ^ pageBits) s); (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> {x ..+ 2 ^ pageBitsForSize sz} \<times> {SIndexVal, SIndexTyp 0}
    \<subseteq> dom_s (hrs_htd (t_hrs_' (globals s')))"
  apply (rule_tac m=pageBits in intvl_2_power_times_decomp,
         simp_all add: pbfs_atleast_pageBits pbfs_less_wb')
  apply (erule allEI, clarsimp)
  apply (drule(1) user_page_at_rf_sr_dom_s)
  apply (erule subsetD)
  apply simp
  done

lemma clearMemory_PageCap_ccorres:
  "ccorres dc xfdc (invs' and valid_cap' (ArchObjectCap (PageCap ptr undefined sz None))
           and (\<lambda>s. 2 ^ pageBitsForSize sz \<le> gsMaxObjectSize s)
           and K ({ptr .. ptr + 2 ^ (pageBitsForSize sz) - 1} \<inter> kernel_data_refs = {})
           )
      (UNIV \<inter> {s. bits_' s = of_nat (pageBitsForSize sz)}
            \<inter> {s. ptr___ptr_to_unsigned_long_' s = Ptr ptr})
      []
     (doMachineOp (clearMemory ptr (2 ^ pageBitsForSize sz))) (Call clearMemory_'proc)"
  (is "ccorres dc xfdc ?P ?P' [] ?m ?c")
  apply (cinit' lift: bits_' ptr___ptr_to_unsigned_long_')
   apply (rule_tac P="capAligned (ArchObjectCap (PageCap ptr undefined sz None))"
                in ccorres_gen_asm)
   apply (rule ccorres_Guard_Seq)
   apply (simp add: clearMemory_def)
   apply (simp add: doMachineOp_bind ef_storeWord)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (rule_tac P="?P" in ccorres_from_vcg[where P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: valid_cap'_def capAligned_def
                            is_aligned_no_wrap'[OF _ word32_power_less_1])
      apply (subgoal_tac "2 \<le> pageBitsForSize sz")
       prefer 2
       apply (simp add: pageBitsForSize_def split: vmpage_size.split)
      apply (rule conjI)
       apply (erule is_aligned_weaken)
       apply (clarsimp simp: pageBitsForSize_def split: vmpage_size.splits)
      apply (rule conjI)
       apply (rule is_aligned_power2)
       apply (clarsimp simp: pageBitsForSize_def split: vmpage_size.splits)
      apply (clarsimp simp: ghost_assertion_size_logic[unfolded o_def])
      apply (simp add: flex_user_page_at_rf_sr_dom_s)
      apply (clarsimp simp: field_simps word_size_def mapM_x_storeWord_step)
      apply (simp add: doMachineOp_def split_def exec_gets)
      apply (simp add: select_f_def simpler_modify_def bind_def)
      apply (fold replicateHider_def)[1]
      apply (subst coerce_heap_update_to_heap_updates'
                         [where chunk=4096 and m="2 ^ (pageBitsForSize sz - pageBits)"])
       apply (simp add: pageBitsForSize_def pageBits_def
                 split: vmpage_size.split)
      apply (subst coerce_memset_to_heap_update_user_data)
      apply (subgoal_tac "\<forall>p<2 ^ (pageBitsForSize sz - pageBits).
                               x \<Turnstile>\<^sub>c (Ptr (ptr + of_nat p * 0x1000) :: user_data_C ptr)")
       prefer 2
       apply (erule allfEI[where f=of_nat])
       apply clarsimp
       apply (subst(asm) of_nat_power, assumption)
        apply simp
        apply (insert pageBitsForSize_32 [of sz])[1]
        apply (erule order_le_less_trans [rotated])        
        apply simp
       apply (simp, drule ko_at_projectKO_opt[OF user_data_at_ko])
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def cpspace_relation_def)
       apply (erule cmap_relationE1, simp(no_asm) add: heap_to_page_data_def Let_def)
        apply fastforce
       subgoal by (simp add: pageBits_def typ_heap_simps)
      apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
      apply (clarsimp simp: cpspace_relation_def typ_heap_simps
                            clift_foldl_hrs_mem_update foldl_id
                            carch_state_relation_def        
                            cmachine_state_relation_def
                            foldl_fun_upd_const[unfolded fun_upd_def])
      apply (subst help_force_intvl_range_conv, assumption)
        subgoal by (simp add: pageBitsForSize_def split: vmpage_size.split)
       apply assumption
      apply (subst heap_to_page_data_update_region)
       apply (drule map_to_user_data_aligned, clarsimp)
       apply (rule aligned_range_offset_mem_helper[where m=pageBits], simp_all)[1]
       apply (rule pbfs_atleast_pageBits)
      apply (erule cmap_relation_If_upd)
        apply (clarsimp simp: cuser_data_relation_def fcp_beta
                              order_less_le_trans[OF unat_lt2p])
        apply (fold word_rsplit_0, simp add: word_rcat_rsplit)[1]
       apply (rule image_cong[OF _ refl])
       apply (rule set_eqI, rule iffI)
        apply (clarsimp simp del: atLeastAtMost_iff)
        apply (drule map_to_user_data_aligned, clarsimp)
        apply (simp only: mask_in_range[symmetric])
        apply (rule_tac x="unat ((xa && mask (pageBitsForSize sz)) >> pageBits)" in image_eqI)
         apply (simp add: subtract_mask(2)[symmetric])
         apply (cut_tac w="xa - ptr" and n=pageBits in and_not_mask[symmetric])
         apply (simp add: shiftl_t2n field_simps pageBits_def)
         apply (subst aligned_neg_mask, simp_all)[1]
         apply (erule aligned_sub_aligned, simp_all add: word_bits_def)[1]
         apply (erule is_aligned_weaken)
         apply (rule pbfs_atleast_pageBits[unfolded pageBits_def])
        apply simp
        apply (rule unat_less_power)
         apply (fold word_bits_def, simp)
        apply (rule shiftr_less_t2n)
        apply (simp add: pbfs_atleast_pageBits)
        apply (rule and_mask_less_size)
        apply (simp add: word_bits_def word_size)
       apply (rule IntI)
        apply (clarsimp simp del: atLeastAtMost_iff)
        apply (subst aligned_range_offset_mem_helper, assumption, simp_all)[1]
        apply (rule order_le_less_trans[rotated], erule shiftl_less_t2n [OF of_nat_power],
               simp_all add: word_bits_def)[1]
         apply (insert pageBitsForSize_32 [of sz])[1]
         apply (erule order_le_less_trans [rotated])        
         subgoal by simp        
        subgoal by (simp add: pageBits_def shiftl_t2n field_simps)
       apply clarsimp
       apply (drule_tac x="of_nat n" in spec)
       apply (simp add: of_nat_power[where 'a=32, folded word_bits_def])
       apply (rule exI)
       subgoal by (simp add: pageBits_def ko_at_projectKO_opt[OF user_data_at_ko])
      subgoal by simp
     apply csymbr
     apply (ctac add: cleanCacheRange_PoU_ccorres[unfolded dc_def])
    apply wp
   apply (simp add: guard_is_UNIV_def unat_of_nat
                    word_bits_def capAligned_def word_of_nat_less)
  apply (clarsimp simp: word_bits_def valid_cap'_def
                        capAligned_def word_of_nat_less)
  apply (frule is_aligned_addrFromPPtr_n, simp add: pageBitsForSize_def split: vmpage_size.splits)
  by (clarsimp simp: is_aligned_no_overflow'[where n=12, simplified]
                        is_aligned_no_overflow'[where n=16, simplified]
                        is_aligned_no_overflow'[where n=20, simplified]
                        is_aligned_no_overflow'[where n=24, simplified] pageBits_def
                        field_simps is_aligned_mask[symmetric] mask_AND_less_0
                        pageBitsForSize_def split: vmpage_size.splits)

lemma coerce_memset_to_heap_update_asidpool:
  "heap_update_list x (replicateHider 4096 0)
      = heap_update (Ptr x :: asid_pool_C ptr)
             (asid_pool_C (FCP (\<lambda>x. Ptr 0)))"
  apply (intro ext, simp add: heap_update_def)
  apply (rule_tac f="\<lambda>xs. heap_update_list x xs a b" for a b in arg_cong)
  apply (simp add: to_bytes_def size_of_def typ_info_simps asid_pool_C_tag_def)
  apply (simp add: ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def)
  apply (simp add: typ_info_simps 
                   user_context_C_tag_def thread_state_C_tag_def fault_C_tag_def
                   lookup_fault_C_tag_def update_ti_t_ptr_0s
                   ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td 
                   ti_typ_combine_empty_ti ti_typ_combine_td       
                   align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def 
                   align_td_array' size_td_array)
  apply (simp add: typ_info_array')
  apply (subst access_ti_list_array)
     apply simp
    apply simp
   apply (simp add: fcp_beta typ_info_word typ_info_ptr word_rsplit_0)
   apply fastforce
  apply (simp add: collapse_foldl_replicate)
  done

declare replicate_numeral [simp]

lemma coerce_memset_to_heap_update_pte:
  "heap_update_list x (replicateHider 4 0)
      = heap_update (Ptr x :: pte_C ptr)
             (pte_C.pte_C (FCP (\<lambda>x. 0)))"
  apply (intro ext, simp add: heap_update_def)
  apply (rule_tac f="\<lambda>xs. heap_update_list x xs a b" for a b in arg_cong)
  apply (simp add: to_bytes_def size_of_def typ_info_simps pte_C_tag_def)
  apply (simp add: ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def)
  apply (simp add: typ_info_simps align_td_array' size_td_array)
  apply (simp add: typ_info_array' typ_info_word word_rsplit_0)
  apply (simp add: replicateHider_def)
  done

lemma coerce_memset_to_heap_update_pde:
  "heap_update_list x (replicateHider 4 0)
      = heap_update (Ptr x :: pde_C ptr)
             (pde_C.pde_C (FCP (\<lambda>x. 0)))"
  apply (intro ext, simp add: heap_update_def)
  apply (rule_tac f="\<lambda>xs. heap_update_list x xs a b" for a b in arg_cong)
  apply (simp add: to_bytes_def size_of_def typ_info_simps pde_C_tag_def)
  apply (simp add: ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def)
  apply (simp add: typ_info_simps align_td_array' size_td_array)
  apply (simp add: typ_info_array' typ_info_word word_rsplit_0)
  apply (simp add: replicateHider_def)
  done

lemma objBits_eq_by_type:
  fixes x :: "'a :: pspace_storable" and y :: 'a
  shows "objBits x = objBits y"
  apply (simp add: objBits_def)
  apply (rule objBits_type)
  apply (simp add: koTypeOf_injectKO)
  done

lemma mapM_x_store_memset_ccorres_assist:
  fixes val :: "'a :: pspace_storable"
  assumes nofail: "\<not> snd (mapM_x (\<lambda>slot. setObject slot val) slots \<sigma>)"
  assumes slots1: "\<forall>n < length slots. slots ! n = hd slots + (of_nat n << objBits val)"
  assumes slots2: "n = length slots * (2 ^ objBits val)"
  assumes ptr: "ptr = hd slots"
  assumes ko: "\<And>ko :: 'a. updateObject ko = updateObject_default ko"
              "\<And>ko :: 'a. (1 :: word32) < 2 ^ objBits ko"
  assumes restr: "set slots \<subseteq> S"
  assumes worker: "\<And>ptr s s' (ko :: 'a). \<lbrakk> (s, s') \<in> rf_sr; ko_at' ko ptr s; ptr \<in> S \<rbrakk>
                                \<Longrightarrow> (s \<lparr> ksPSpace := ksPSpace s (ptr \<mapsto> injectKO val)\<rparr>,
                                     globals_update (t_hrs_'_update (hrs_mem_update
                                                    (heap_update_list ptr
                                                    (replicateHider (2 ^ objBits val) (ucast c))))) s') \<in> rf_sr"
  assumes rf_sr: "(\<sigma>, s) \<in> rf_sr"
  shows
  "\<exists>(rv, \<sigma>') \<in> fst (mapM_x (\<lambda>slot. setObject slot val) slots \<sigma>).
      (\<sigma>', globals_update (t_hrs_'_update (hrs_mem_update
                          (heap_update_list ptr (replicateHider n c)))) s) \<in> rf_sr"
  unfolding slots2 ptr using rf_sr slots1 nofail restr
proof (induct slots arbitrary: s \<sigma>)
  case Nil
  show ?case
    using Nil.prems
    apply (simp add: mapM_x_def sequence_x_def return_def replicateHider_def)
    apply (simp add: rf_sr_def hrs_mem_update_def cstate_relation_def Let_def
                     carch_state_relation_def cmachine_state_relation_def
                     h_t_valid_clift_Some_iff)
    done
next
  case (Cons x xs tPre sPre)

  note nofail_bind = Cons.prems(3)[unfolded mapM_x_Cons K_bind_def]

  have obj_at: "obj_at' (\<lambda>x :: 'a. True) x sPre"
    using not_snd_bindI1[OF nofail_bind]
    apply (subst(asm) setObject_obj_at_pre, simp_all add: ko snd_bind)
    apply (clarsimp simp: stateAssert_def exec_get return_def)
    apply (simp add: koTypeOf_injectKO typ_at_to_obj_at')
    done

  note in_setObject = setObject_eq[OF _ _ objBits_eq_by_type obj_at,
                                   where ko=val, simplified ko, simplified]

  note nofail_mapM = not_snd_bindI2[OF nofail_bind, OF in_setObject]

  have hd_xs: "xs \<noteq> [] \<Longrightarrow> hd xs = x + (2 ^ objBits val)"
    using Cons.prems(2)[rule_format, where n=1]
    by (simp add: hd_conv_nth)

  show ?case
    using obj_at_ko_at'[OF obj_at] Cons.prems(4)
    apply (clarsimp simp add: mapM_x_Cons bind_def split_def)
    apply (rule rev_bexI, rule in_setObject)
    apply (cut_tac Cons.hyps[OF _ _ nofail_mapM])
       defer
       apply (rule worker, rule Cons.prems, assumption+)
      apply clarsimp
      apply (case_tac "xs = []", simp_all)[1]
      apply (insert Cons.prems, simp)[1]
      apply (frule_tac x="Suc n" in spec)
      apply (simp add: hd_xs shiftl_t2n field_simps)
     apply assumption
    apply clarsimp
    apply (rule rev_bexI, assumption)
    apply (simp add: o_def)
    apply (case_tac "xs = []")
     apply (simp add: hrs_mem_update_def split_def replicateHider_def)
    apply (subst(asm) heap_update_list_concat_fold_hrs_mem)
     apply (simp add: hd_xs replicateHider_def)
    apply (simp add: replicateHider_def replicate_add)
    done
qed

lemma invalidateTLBByASID_ccorres:
  "ccorres dc xfdc (valid_pde_mappings' and (\<lambda>_. asid \<le> mask asid_bits))
                   (UNIV \<inter> {s. asid_' s = asid}) []
       (invalidateTLBByASID asid) (Call invalidateTLBByASID_'proc)"
  apply (cinit lift: asid_')
   apply (ctac(no_vcg) add: loadHWASID_ccorres)
    apply csymbr
    apply (simp add: case_option_If2 del: Collect_const)
    apply (rule ccorres_if_cond_throws2[where Q=\<top> and Q'=\<top>])
       apply (clarsimp simp: pde_stored_asid_def to_bool_def split: split_if)
      apply (rule ccorres_return_void_C[unfolded dc_def])
     apply (simp add: dc_def[symmetric])
     apply csymbr
     apply (ctac add: invalidateTLB_ASID_ccorres)
    apply vcg
   apply (wp hoare_drop_imps)
  apply (clarsimp simp: pde_stored_asid_def to_bool_def)
  done

(* FIXME: also in VSpace_C *)
lemma ignoreFailure_liftM:
  "ignoreFailure = liftM (\<lambda>v. ())"
  apply (rule ext)+
  apply (simp add: ignoreFailure_def liftM_def
                   catch_def)
  apply (rule bind_apply_cong[OF refl])
  apply (simp split: sum.split)
  done

end

crunch pde_mappings'[wp]: invalidateTLBByASID "valid_pde_mappings'"
crunch ksArchState[wp]: invalidateTLBByASID "\<lambda>s. P (ksArchState s)"

crunch gsMaxObjectSize[wp]: invalidateTLBByASID "\<lambda>s. P (gsMaxObjectSize s)"
crunch gsMaxObjectSize[wp]: deleteASIDPool "\<lambda>s. P (gsMaxObjectSize s)"
  (ignore: setObject getObject wp: crunch_wps getObject_inv loadObject_default_inv
     simp: crunch_simps)

context kernel_m begin

lemma page_table_at_rf_sr_dom_s:
  "\<lbrakk> page_table_at' x s; (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> {x ..+ 2 ^ ptBits} \<times> {SIndexVal, SIndexTyp 0}
    \<subseteq> dom_s (hrs_htd (t_hrs_' (globals s')))"
  apply (rule_tac m=2 in intvl_2_power_times_decomp,
         simp_all add: shiftl_t2n field_simps ptBits_def pageBits_def
                       word_bits_def)
  apply (clarsimp simp: page_table_at'_def intvl_def)
  apply (drule spec, drule(1) mp)
  apply (simp add: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1[OF rf_sr_cpte_relation])
   apply (erule ko_at_projectKO_opt)
  apply (drule h_t_valid_clift)
  apply (drule h_t_valid_dom_s[OF _ refl refl])
  apply (erule subsetD)
  apply (auto simp add: intvl_def shiftl_t2n)[1]
  done

lemma page_directory_at_rf_sr_dom_s:
  "\<lbrakk> page_directory_at' x s; (s, s') \<in> rf_sr \<rbrakk>
    \<Longrightarrow> {x ..+ 2 ^ pdBits} \<times> {SIndexVal, SIndexTyp 0}
    \<subseteq> dom_s (hrs_htd (t_hrs_' (globals s')))"
  apply (rule_tac m=2 in intvl_2_power_times_decomp,
         simp_all add: shiftl_t2n field_simps pdBits_def pageBits_def
                       word_bits_def)
  apply (clarsimp simp: page_directory_at'_def intvl_def)
  apply (drule spec, drule(1) mp)
  apply (simp add: typ_at_to_obj_at_arches)
  apply (drule obj_at_ko_at', clarsimp)
  apply (erule cmap_relationE1[OF rf_sr_cpde_relation])
   apply (erule ko_at_projectKO_opt)
  apply (drule h_t_valid_clift)
  apply (drule h_t_valid_dom_s[OF _ refl refl])
  apply (erule subsetD)
  apply (auto simp add: intvl_def shiftl_t2n)[1]
  done

lemma clearMemory_setObject_PTE_ccorres:
  "ccorres dc xfdc (page_table_at' ptr
                and (\<lambda>s. 2 ^ ptBits \<le> gsMaxObjectSize s)
                and (\<lambda>_. is_aligned ptr ptBits \<and> ptr \<noteq> 0 \<and> pstart = addrFromPPtr ptr))
            (UNIV \<inter> {s. ptr___ptr_to_unsigned_long_' s = Ptr ptr} \<inter> {s. bits_' s = of_nat ptBits}) []
       (do x \<leftarrow> mapM_x (\<lambda>a. setObject a Hardware_H.pte.InvalidPTE)
                       [ptr , ptr + 2 ^ objBits Hardware_H.pte.InvalidPTE .e. ptr + 2 ^ ptBits - 1];
           doMachineOp (cleanCacheRange_PoU ptr (ptr + 2 ^ ptBits - 1) pstart)
        od)
       (Call clearMemory_'proc)"
  apply (rule ccorres_gen_asm)+
  apply (cinit' lift: ptr___ptr_to_unsigned_long_' bits_')
   apply (rule ccorres_Guard_Seq)
   apply (rule ccorres_split_nothrow_novcg_dc)
      apply (rule_tac P="page_table_at' ptr and (\<lambda>s. 2 ^ ptBits \<le> gsMaxObjectSize s)"
               in ccorres_from_vcg_nofail[where P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply clarsimp
      apply (subst ghost_assertion_size_logic[unfolded o_def])
        apply (simp add: ptBits_def pageBits_def)
       apply simp
      apply (clarsimp simp: replicateHider_def[symmetric])
      apply (frule is_aligned_no_overflow')
      apply (intro conjI)
          apply (clarsimp simp add: ptBits_def pageBits_def
                          cong: StateSpace.state.fold_congs globals.fold_congs)
         apply (erule is_aligned_weaken, simp add: ptBits_def pageBits_def)
        apply (clarsimp simp: is_aligned_def ptBits_def pageBits_def)
       apply (simp add: unat_of_nat32 order_less_le_trans[OF pt_bits_stuff(2)]
                        word_bits_def page_table_at_rf_sr_dom_s)
      apply (clarsimp simp add: ptBits_def pageBits_def
                      cong: StateSpace.state.fold_congs globals.fold_congs)
      apply (simp add: upto_enum_step_def objBits_simps ptBits_def pageBits_def
                       field_simps linorder_not_less[symmetric] archObjSize_def
                       upto_enum_word split_def)
      apply (erule mapM_x_store_memset_ccorres_assist
                      [unfolded split_def, OF _ _ _ _ _ _ subset_refl],
             simp_all add: shiftl_t2n hd_map objBits_simps archObjSize_def)[1]
      apply (rule cmap_relationE1, erule rf_sr_cpte_relation, erule ko_at_projectKO_opt)
      apply (subst coerce_memset_to_heap_update_pte)
      apply (clarsimp simp: rf_sr_def Let_def cstate_relation_def typ_heap_simps)
      apply (rule conjI)
       apply (simp add: cpspace_relation_def typ_heap_simps update_pte_map_tos
                        update_pte_map_to_ptes carray_map_relation_upd_triv)
       apply (rule cmap_relation_updI, simp_all)[1]
       apply (simp add: cpte_relation_def Let_def pte_lift_def
                        fcp_beta pte_get_tag_def pte_tag_defs)
       apply (simp add: carch_state_relation_def cmachine_state_relation_def
                        typ_heap_simps update_pte_map_tos)
      apply csymbr
     apply (rule ccorres_Guard)
     apply (ctac add: cleanCacheRange_PoU_ccorres)
    apply (wp mapM_x_wp' setObject_ksPSpace_only updateObject_default_inv | simp)+
   apply (clarsimp simp: guard_is_UNIV_def ptBits_def pageBits_def)
  apply (clarsimp simp: ptBits_def pageBits_def)
  apply (frule is_aligned_addrFromPPtr_n, simp)
  apply (clarsimp simp: is_aligned_no_overflow'[where n=10, simplified] pageBits_def
                        field_simps is_aligned_mask[symmetric] mask_AND_less_0)
  done

lemma ccorres_make_xfdc:
  "ccorresG rf_sr \<Gamma> r xf P P' h a c \<Longrightarrow> ccorresG rf_sr \<Gamma> dc xfdc P P' h a c"
  apply (erule ccorres_rel_imp)
  apply simp
  done
  
lemma ccorres_if_True_False_simps:
  "ccorres r xf P P' hs a (IF True THEN c ELSE c' FI) = ccorres r xf P P' hs a c"
  "ccorres r xf P P' hs a (IF False THEN c ELSE c' FI) = ccorres r xf P P' hs a c'"
  "ccorres r xf P P' hs a (IF True THEN c ELSE c' FI ;; d) = ccorres r xf P P' hs a (c ;; d)"
  "ccorres r xf P P' hs a (IF False THEN c ELSE c' FI ;; d) = ccorres r xf P P' hs a (c' ;; d)"
  by (simp_all add: ccorres_cond_iffs ccorres_seq_simps)

lemmas cap_tag_values =
  cap_untyped_cap_def
  cap_endpoint_cap_def
  cap_notification_cap_def
  cap_reply_cap_def
  cap_cnode_cap_def
  cap_thread_cap_def
  cap_irq_handler_cap_def
  cap_null_cap_def
  cap_irq_control_cap_def
  cap_zombie_cap_def
  cap_small_frame_cap_def
  cap_frame_cap_def
  cap_page_table_cap_def
  cap_page_directory_cap_def
  cap_asid_pool_cap_def

lemma resetMemMapping_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. c_valid_cap (cap_' s)\<rbrace>
           Call resetMemMapping_'proc
           {s'. option_map ((\<lambda>acap. case acap of ArchObjectCap acap' \<Rightarrow> ArchObjectCap (resetMemMapping acap') | _ \<Rightarrow> acap) \<circ> cap_to_H) (cap_lift (cap_' s)) =
                option_map cap_to_H (cap_lift (ret__struct_cap_C_' s')) \<and> c_valid_cap (ret__struct_cap_C_' s')}"
  apply vcg
  apply (subgoal_tac "\<forall>t cap. (scast (t :: sword32) = cap_get_tag cap) = (cap_get_tag cap = scast t)")
  apply clarsimp
  apply (intro impI allI conjI)
   apply (auto simp: isCap_simps resetMemMapping_def cap_to_H_simps cap_lifts ccap_relation_def c_valid_cap_def cl_valid_cap_def
      asidInvalid_def)[7]
  apply (clarsimp split: capability.splits cap_CL.splits option.splits)
  apply (rename_tac arch_capability)
  by (case_tac arch_capability,
        auto simp: resetMemMapping_def cap_to_H_def
        cap_small_frame_cap_lift_def cap_frame_cap_lift_def
        cap_page_table_cap_lift_def cap_page_directory_cap_lift_def
        cap_lift_def cap_tag_values Let_def
        split: cap_CL.splits split_if_asm)

lemma ccorres_return_C_seq:
  "\<lbrakk>\<And>s f. xf (global_exn_var_'_update f (xfu (\<lambda>_. v s) s)) = v s; \<And>s f. globals (xfu f s) = globals s; wfhandlers hs\<rbrakk>
  \<Longrightarrow> ccorres_underlying rf_sr \<Gamma> r rvxf arrel xf (\<lambda>_. True) {s. arrel rv (v s)} hs (return rv) (return_C xfu v ;; d)"
  apply (rule ccorres_guard_imp)
  apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
  apply vcg
  apply simp_all
  done

lemma arch_recycleCap_ccorres_helper:
  notes Collect_const [simp del]
  notes ccorres_if_True_False_simps [simp]
  shows "ccorres (\<lambda>a. ccap_relation (ArchObjectCap a)) ret__struct_cap_C_' 
           (invs' and valid_cap' (ArchObjectCap cp) and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s)
               and K (ccap_relation (ArchObjectCap cp) cap))
           UNIV [SKIP]
           (do y \<leftarrow> ArchRetypeDecls_H.finaliseCap cp is_final;
               return (resetMemMapping cp)
            od)
           (call (\<lambda>s. s\<lparr>cap_' := cap, final_' := from_bool is_final\<rparr>) Arch_finaliseCap_'proc (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>s t. Basic (\<lambda>s. s));;
            (\<acute>ret__struct_cap_C :== CALL resetMemMapping(cap);;
             (return_C ret__struct_cap_C_'_update ret__struct_cap_C_' ;; cruft)))"
  apply (rule ccorres_guard_imp2)
   apply (ctac (no_vcg) add: ccorres_make_xfdc [OF Arch_finaliseCap_ccorres])
    apply csymbr -- "C reset mem mapping"
    apply (rule ccorres_return_C_seq, simp_all)[1]
   apply wp
  by (clarsimp elim!: ccap_relationE simp: option_map_Some_eq2 ccap_relation_def)

lemma arch_recycleCap_ccorres_helper':
  notes Collect_const [simp del]
  notes ccorres_if_True_False_simps [simp]
  shows "ccorres (\<lambda>a. ccap_relation (ArchObjectCap a)) ret__struct_cap_C_'
                 (invs' and valid_cap' (ArchObjectCap cp) and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s)
                    and K (ccap_relation (ArchObjectCap cp) cap))
                 UNIV 
            [SKIP]
           (do y \<leftarrow> ArchRetypeDecls_H.finaliseCap cp is_final;
               return (if is_final then resetMemMapping cp else cp)
            od)
           (call (\<lambda>s. s\<lparr>cap_' := cap, final_' := from_bool is_final\<rparr>) Arch_finaliseCap_'proc (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>s t. Basic (\<lambda>s. s));;
           (Cond \<lbrace>from_bool is_final \<noteq> 0\<rbrace>
             (\<acute>ret__struct_cap_C :== CALL resetMemMapping(cap);;
              return_C ret__struct_cap_C_'_update ret__struct_cap_C_')
            SKIP;;
           (return_C ret__struct_cap_C_'_update (\<lambda>s. cap);; cruft)))"
  apply (rule ccorres_guard_imp2)
  apply (ctac (no_vcg) add: ccorres_make_xfdc [OF Arch_finaliseCap_ccorres])
  apply (simp add: if_distrib [where f = return])
  apply (rule ccorres_if_cond_throws [where Q=\<top> and Q'=\<top>])
   apply (simp add: from_bool_0)
   apply csymbr
   apply (rule ccorres_return_C, simp_all)[1]
  apply (rule ccorres_return_C_seq, simp_all)[1]
   apply vcg
  apply wp
  by (clarsimp simp: from_bool_0 ccap_relation_def option_map_Some_eq2)

lemma arch_recycleCap_ccorres:
  notes Collect_const [simp del]
  notes ccorres_if_True_False_simps [simp]
  notes if_cong[cong]
  shows "ccorres (ccap_relation o ArchObjectCap) ret__struct_cap_C_'
         (invs' and valid_cap' (ArchObjectCap cp)
                and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s)
                and (\<lambda>s. capRange (ArchObjectCap cp) \<inter> kernel_data_refs = {}))
         (UNIV \<inter> {s. (is_final_' s) = from_bool is_final} \<inter> {s. ccap_relation (ArchObjectCap cp) (cap_' s)}
         ) []
     (ArchRetypeDecls_H.recycleCap is_final cp) (Call Arch_recycleCap_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: is_final_' cap_'  )
   apply csymbr
   apply (simp add: ArchRetype_H.recycleCap_def cap_get_tag_isCap
                    cap_get_tag_isCap_ArchObject
                    isArchPageCap_ArchObjectCap
               del: Collect_const cong: call_ignore_cong)
   apply (rule ccorres_if_lhs)
    apply (simp add: ccorres_cond_iffs Collect_True
                del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply (rule ccorres_symb_exec_r)
      apply (rule ccorres_Guard_Seq)

      apply (rule ccorres_basic_srnoop2, simp)
      apply csymbr
      apply (simp add: doMachineOp_bind shiftL_nat)
      apply (ctac (no_vcg) add: clearMemory_PageCap_ccorres)
       apply (rule arch_recycleCap_ccorres_helper)
      apply wp
     apply vcg
    apply (rule conseqPre, vcg, clarsimp)
   apply (rule ccorres_if_lhs)
    apply (simp add: ccorres_cond_iffs Collect_True Collect_False
                     Let_def
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply (csymbr, csymbr, csymbr)
    apply (subst bind_assoc[symmetric])
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (simp add: storePTE_def)
       apply (ctac add: clearMemory_setObject_PTE_ccorres)
      apply csymbr
      apply (rule_tac P="ret__unsigned = from_bool (capPTMappedAddress cp \<noteq> None)"
                   in ccorres_gen_asm2)
      apply wpc
       apply (simp add: false_def)
       apply (rule arch_recycleCap_ccorres_helper')
      apply (simp add: split_def true_def bind_assoc)
      apply (rule ccorres_rhs_assoc)+
      apply csymbr
      apply csymbr
      apply (ctac(no_vcg) add: pageTableMapped_ccorres)
       apply (simp add: case_option_If del: Collect_const)
       apply (ctac (no_vcg, no_simp) add: ccorres_when [where R = \<top>]) -- "leave guard = goal and a call to invalidateTLB"
           apply (simp add: option_to_0_def option_to_ptr_def
                     split: option.splits)
           apply (ctac (no_vcg) add: invalidateTLBByASID_ccorres)
         apply (rule arch_recycleCap_ccorres_helper')
        apply wp
       apply simp
      apply simp
      apply (wp hoare_drop_imps)[1] 
     apply (rule_tac Q="\<lambda>rv. invs' and valid_cap' (ArchObjectCap cp)
                     and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s)"
                 in hoare_post_imp)
      apply (clarsimp simp: valid_cap'_def isCap_simps mask_def)
     apply (wp mapM_x_wp' | simp)+
    apply (clarsimp simp: guard_is_UNIV_def cap_get_tag_isCap_ArchObject)
    apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
    apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def
                          cap_page_table_cap_lift_def to_bool_def
                          true_def false_def
                   elim!: ccap_relationE split: split_if_asm)
    apply (clarsimp simp: word_neq_0_conv resetMemMapping_def
                          ccap_relation_def option_map_Some_eq2)
   apply (rule ccorres_if_lhs)
    apply (simp add: ccorres_cond_iffs Collect_True Collect_False
                     Let_def ARMSectionBits_def
                del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply (csymbr, csymbr)
    apply (rule ccorres_Guard_Seq)+
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (rule_tac P="capPDBasePtr_CL (cap_page_directory_cap_lift cap) = capPDBasePtr cp"
                         in ccorres_gen_asm2)
       apply (rule_tac P="valid_cap' (ArchObjectCap cp) and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s)
                      and K (capPDBasePtr cp \<noteq> 0)"
                   in ccorres_from_vcg_nofail[where P'=UNIV])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: replicateHider_def[symmetric] valid_cap'_def
                             capAligned_def)
       apply (clarsimp simp: isCap_simps storePDE_def o_def)
       apply (subst ghost_assertion_size_logic[unfolded o_def, rotated])
         apply simp
        apply simp
       apply (subst is_aligned_no_wrap', assumption)
        apply simp
       apply clarsimp
       apply (intro conjI)
          apply (erule is_aligned_weaken, simp)
         apply (clarsimp simp: is_aligned_def)
        apply (clarsimp simp: valid_cap'_def)
        apply (drule(1) page_directory_at_rf_sr_dom_s)
        apply (clarsimp simp: pdBits_def pageBits_def)
        apply (erule subsetD, simp)
        apply (erule subsetD[rotated], rule intvl_start_le)
        apply simp
       apply (clarsimp simp: split_def upto_enum_word kernelBase_def
                       cong: StateSpace.state.fold_congs globals.fold_congs)
       apply (erule_tac S="{x. valid_pde_mapping_offset' (x && mask pdBits)}"
                  in mapM_x_store_memset_ccorres_assist[unfolded split_def],
              simp_all add: hd_map objBits_simps archObjSize_def)[1]
        apply (clarsimp simp: pdBits_def pageBits_def)
        apply (subst field_simps, simp add: mask_add_aligned)
        apply (simp add: valid_pde_mapping_offset'_def)
        apply (subst iffD2[OF mask_eq_iff_w2p])
          apply (simp add: word_size)
         apply (rule shiftl_less_t2n)
          apply (rule of_nat_power)
           apply simp+
        apply (rule notI, drule arg_cong[where f="\<lambda>a. a >> 2"],
               subst(asm) shiftl_shiftr_id)
          apply (simp add: word_bits_def)
         apply (rule of_nat_power)
          apply (simp add: word_bits_def)
         apply (simp add: word_bits_def)
        apply (erule notE[rotated], rule less_imp_neq, rule word_of_nat_less)
        apply (simp add: pd_asid_slot_def)
       apply (rule cmap_relationE1, erule rf_sr_cpde_relation, erule ko_at_projectKO_opt)
       apply (subst coerce_memset_to_heap_update_pde)
       apply (clarsimp simp: rf_sr_def Let_def cstate_relation_def typ_heap_simps)
       apply (rule conjI)
        apply (simp add: cpspace_relation_def typ_heap_simps update_pde_map_tos
                         update_pde_map_to_pdes carray_map_relation_upd_triv)
        apply (rule cmap_relation_updI, simp_all)[1]
        subgoal by (simp add: cpde_relation_def Let_def pde_lift_def
                         fcp_beta pde_get_tag_def pde_tag_defs)
       subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                        typ_heap_simps pde_stored_asid_update_valid_offset
                        update_pde_map_tos)
      apply csymbr
      apply (rule ccorres_Guard_Seq)+
      apply (ctac(no_vcg) add: cleanCacheRange_PoU_ccorres)
       apply csymbr
       apply (rule_tac P="capPDBasePtr_CL (cap_page_directory_cap_lift cap) = capPDBasePtr cp
                              \<and> ret__unsigned = from_bool (capPDMappedASID cp \<noteq> None)"
                     in ccorres_gen_asm2)
       apply wpc
        apply (simp add: false_def)
        apply (rule arch_recycleCap_ccorres_helper')
       apply (simp add: split_def true_def bind_assoc)
       apply (rule ccorres_rhs_assoc)+
       apply csymbr
       apply csymbr
       apply (simp add: true_def ccorres_cond_iffs ignoreFailure_liftM)
       apply (rule ccorres_rhs_assoc2)
       apply (rule ccorres_split_nothrow_novcg_dc)
          apply simp
          apply (rule ccorres_split_nothrowE)
               apply (ctac add: findPDForASID_ccorres)
              apply ceqv
             apply (simp add: liftE_liftM when_def dc_def[symmetric] del: Collect_const)
             apply (rule ccorres_cond2[where R=\<top>])
               apply fastforce
              apply (ctac add: invalidateTLBByASID_ccorres)
             apply (rule ccorres_return_Skip)
            apply (simp add: ccorres_cond_iffs throwError_def)
            apply (rule ccorres_return_Skip')
           apply (wp hoare_drop_imps)
          apply simp
          apply (vcg exspec=findPDForASID_modifies)
         apply (rule arch_recycleCap_ccorres_helper')
        apply (wp | simp)+
       apply (clarsimp simp: guard_is_UNIV_def)
      apply (wp hoare_vcg_all_lift static_imp_wp | wp_once mapM_x_wp' | simp)+
    apply (clarsimp simp: guard_is_UNIV_def
                          cap_get_tag_isCap_ArchObject[symmetric])
    apply (clarsimp simp: field_simps pdBits_def pageBits_def word_sle_def)
    apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                          cap_page_directory_cap_lift_def
                          to_bool_def true_def false_def
                   elim!: ccap_relationE split: split_if_asm)
    apply (simp add: word_neq_0_conv)
   apply (rule ccorres_if_lhs)
    apply (simp add: ccorres_cond_iffs Collect_True Collect_False
                     Let_def
                del: Collect_const)
    apply (rule ccorres_split_throws, rule ccorres_return_C, simp+)
    apply vcg
   apply (rule ccorres_if_lhs)
    apply (simp add: ccorres_cond_iffs Collect_True Collect_False
                     Let_def
                del: Collect_const)
    apply (rule ccorres_rhs_assoc)+
    apply (csymbr, csymbr, csymbr)
    apply (rule ccorres_Guard_Seq)+
    apply (rule ccorres_symb_exec_l
                 [OF _ gets_inv gets_wp empty_fail_gets])
    apply (rule ccorres_split_nothrow_novcg_dc)
       apply (simp add: when_def del: Collect_const)
       apply (rule_tac R="\<lambda>s. rv = armKSASIDTable (ksArchState s)
                               \<and> capASIDPool cp \<noteq> 0"
                   in ccorres_cond2)
         apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric])
         apply (clarsimp simp: cap_to_H_def cap_lift_asid_pool_cap
                               cap_asid_pool_cap_lift_def
                        elim!: ccap_relationE)
         apply (subst ucast_asid_high_bits_is_shift)
          apply (simp add: mask_def asid_bits_def)
          apply (rule word_and_le1)
         apply (subst rf_sr_armKSASIDTable, assumption)
          apply (simp add: asid_high_bits_word_bits)
          apply (rule shiftr_less_t2n)
          apply (rule order_le_less_trans [OF _ and_mask_less_size])
           apply (simp add: asid_low_bits_def asid_high_bits_def mask_def)
           apply (rule order_refl)
          apply (simp add: asid_low_bits_def asid_high_bits_def word_size)
         apply (simp add: option_to_ptr_def option_to_0_def
                   split: option.split)
        apply (rule ccorres_rhs_assoc)+
        apply (ctac(no_vcg) add: deleteASIDPool_ccorres)
         apply (rule ccorres_split_nothrow_novcg_dc)
            apply (rule_tac P="valid_cap' (ArchObjectCap cp) and (\<lambda>s. 2 ^ acapBits cp \<le> gsMaxObjectSize s)
                          and no_0_obj'"
                       in ccorres_from_vcg[where P'=UNIV])
            apply (rule allI, rule conseqPre, vcg)
            apply (clarsimp simp: cap_get_tag_isCap_ArchObject[symmetric]
                                  asidLowBits_handy_convs word_sle_def
                                  word_sless_def)
            apply (clarsimp simp: ccap_relation_def cap_asid_pool_cap_lift
                                  cap_to_H_def valid_cap'_def capAligned_def
                                  typ_at_to_obj_at_arches)
            apply (subst ghost_assertion_size_logic[unfolded o_def, rotated],
              assumption)
             apply (erule order_trans[rotated])
             apply (simp add: asid_low_bits_def)
            apply (drule obj_at_ko_at', clarsimp)
            apply (rule cmap_relationE1[OF rf_sr_cpspace_asidpool_relation],
                    assumption)
             apply (erule ko_at_projectKO_opt)
            apply (frule h_t_valid_clift)
            apply (subst h_t_valid_dom_s, assumption, simp)
             apply (simp add: asid_low_bits_def)
            apply simp
            apply (rule conjI, clarsimp)
            apply (rule conjI, erule is_aligned_no_wrap')
             apply (clarsimp simp: asid_low_bits_def)
            apply (rule conjI)
             apply (erule is_aligned_weaken)
             apply (clarsimp simp: asid_low_bits_def)
            apply (rule conjI)
             apply (clarsimp simp: is_aligned_def asid_low_bits_def)
            apply (clarsimp simp: typ_at_to_obj_at_arches)
            apply (rule rev_bexI, rule setObject_eq[where P=\<top>],
                   (simp add: objBits_simps archObjSize_def pageBits_def)+)
             apply (simp add: obj_at'_weakenE[OF _ TrueI])
            apply (simp only: replicateHider_def[symmetric])
            apply (clarsimp simp: asid_low_bits_def)
            apply (subst coerce_memset_to_heap_update_asidpool)
            apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                  cpspace_relation_def typ_heap_simps
                                  update_asidpool_map_tos
                                  update_asidpool_map_to_asidpools)
            apply (rule conjI)
             apply (erule cmap_relation_updI, simp_all)[1]
             apply (simp add: makeObject_asidpool casid_pool_relation_def)
             apply (clarsimp simp: array_relation_def
                                   option_to_ptr_def option_to_0_def)
             apply (subst fcp_beta)
              apply (simp add: asid_low_bits_def, unat_arith)
             apply simp
            subgoal by (simp add: carch_state_relation_def cmachine_state_relation_def
                             typ_heap_simps)
           apply (rule ccorres_from_vcg[where P=\<top> and P'=UNIV])
           apply (rule allI, rule conseqPre, vcg)
           apply (clarsimp simp: word_sle_def word_sless_def
                                 asidLowBits_handy_convs
                                 exec_gets simpler_modify_def
                       simp del: rf_sr_upd_safe)
           apply (simp add: cap_get_tag_isCap_ArchObject[symmetric])
           apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def
                                 cap_asid_pool_cap_lift_def
                          elim!: ccap_relationE
                       simp del: rf_sr_upd_safe)
           apply (clarsimp simp: rf_sr_def cstate_relation_def
                                 Let_def carch_state_relation_def carch_globals_def
                                 cmachine_state_relation_def
                                 h_t_valid_clift_Some_iff
                                 asid_shiftr_low_bits_less[unfolded mask_def asid_bits_def]
                                 word_and_le1)
           apply (subst ucast_asid_high_bits_is_shift)
            apply (simp add: mask_def asid_bits_def
                             word_and_le1)
           apply (erule array_relation_update[unfolded fun_upd_def])
             subgoal by simp
            subgoal by (simp add: option_to_ptr_def option_to_0_def)
           subgoal by (simp add: asid_high_bits_def)
          apply wp
         apply (simp add: guard_is_UNIV_def)
        apply (wp typ_at_lifts [OF deleteASIDPool_typ_at'])
        apply (rule hoare_strengthen_post, rule deleteASIDPool_invs)
        apply clarsimp
       apply (rule ccorres_return_Skip)
      apply (rule ccorres_split_throws)
       apply (rule ccorres_return_C, simp+)
      apply vcg
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply (rule ccorres_inst[where P=\<top> and P'=UNIV])
   apply (cases cp, simp_all add: isCap_simps)[1]
  apply (clarsimp simp: word_sle_def word_sless_def
                        asidLowBits_handy_convs
                        cap_get_tag_isCap_ArchObject)
  apply (cases cp, simp_all add: isCap_simps valid_cap'_def
                                 capRange_def)
     apply (frule cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: cap_lift_asid_pool_cap cap_to_H_def
                           cap_asid_pool_cap_lift_def
                           order_le_less_trans[OF word_and_le1]
                           valid_cap'_def capAligned_def
                           asid_shiftr_low_bits_less[unfolded mask_def asid_bits_def]
                           word_and_le1
                    elim!: ccap_relationE cong: conj_cong)
    apply (rename_tac vmpage_size opt)
    apply (simp add: capAligned_def)
    apply (case_tac "vmpage_size = ARMSmallPage")
     apply (frule(1) cap_get_tag_isCap_unfolded_H_cap)
     apply (clarsimp simp: cap_lift_small_frame_cap cap_to_H_def
                           cap_small_frame_cap_lift_def
                           order_le_less_trans[OF word_and_le1]
                           valid_cap'_def capAligned_def
                           get_capSizeBits_CL_def get_capPtr_CL_def
                           ghost_assertion_size_logic[unfolded o_def]
                    elim!: ccap_relationE cong: conj_cong)
     apply (simp add: cap_tag_defs)
    apply (frule(1) cap_get_tag_isCap_unfolded_H_cap)
    apply (clarsimp simp: cap_lift_frame_cap cap_to_H_def
                          cap_frame_cap_lift_def
                          order_le_less_trans[OF word_and_le1]
                          valid_cap'_def capAligned_def
                          get_capSizeBits_CL_def get_capPtr_CL_def
                          generic_frame_cap_get_capFSize_CL_def
                          gen_framesize_to_H_is_framesize_to_H_if_not_ARMSmallPage
                          c_valid_cap_def cl_valid_cap_def
                   elim!: ccap_relationE cong: conj_cong)
    apply (simp add: pageBitsForSize_def cap_tag_defs
                     ghost_assertion_size_logic[unfolded o_def]
              split: vmpage_size.split_asm)[1]
   apply (frule cap_get_tag_isCap_unfolded_H_cap)
   apply (clarsimp simp: cap_lift_page_table_cap cap_to_H_def
                         cap_page_table_cap_lift_def
                         order_le_less_trans[OF word_and_le1]
                         valid_cap'_def capAligned_def
                         get_capSizeBits_CL_def get_capPtr_CL_def
                         ptBits_def pageBits_def
                  elim!: ccap_relationE cong: conj_cong)
   apply (simp add: page_table_at'_def, drule spec[where x=0], clarsimp)
  apply (frule cap_get_tag_isCap_unfolded_H_cap)
  apply (frule invs_arch_state')
  apply (clarsimp simp: capAligned_def pdBits_def pageBits_def)
  apply (frule is_aligned_addrFromPPtr_n, simp)
  apply (clarsimp simp: is_aligned_no_overflow'[where n=14, simplified] pageBits_def
                        field_simps is_aligned_mask[symmetric] mask_AND_less_0)
  apply (clarsimp simp: cap_lift_page_directory_cap cap_to_H_def
                        cap_page_directory_cap_lift_def
                        order_le_less_trans[OF word_and_le1]
                        valid_cap'_def to_bool_def
                        get_capSizeBits_CL_def get_capPtr_CL_def
                        mask_def[where n=asid_bits]
                        valid_arch_state'_def page_directory_at'_def
                 elim!: ccap_relationE cong: conj_cong split: split_if_asm)
   by (auto simp: page_directory_at'_def dest!: spec[where x=0])[2]

lemma ccap_relation_get_capZombiePtr_CL:
  "\<lbrakk> ccap_relation cap cap'; isZombie cap; capAligned cap \<rbrakk>
      \<Longrightarrow> get_capZombiePtr_CL (cap_zombie_cap_lift cap') = capZombiePtr cap"
  apply (simp only: cap_get_tag_isCap[symmetric])
  apply (drule(1) cap_get_tag_to_H)
  apply (clarsimp simp: get_capZombiePtr_CL_def get_capZombieBits_CL_def Let_def split: split_if)
  apply (subst less_mask_eq)
   apply (clarsimp simp add: capAligned_def objBits_simps word_bits_conv)
   apply unat_arith
  apply simp
  done

lemma double_neg_mask:
  "(~~ mask n) && (~~ mask m) = (~~ mask (max n m))"
  apply (rule word_eqI)
  apply (simp add: word_size word_ops_nth_size)
  apply fastforce
  done

lemma modify_gets_helper:
  "do y \<leftarrow> modify (ksPSpace_update (\<lambda>_. ps)); ps' \<leftarrow> gets ksPSpace; f ps' od
      = do y \<leftarrow> modify (ksPSpace_update (\<lambda>_. ps)); f ps od"
  by (simp add: bind_def simpler_modify_def simpler_gets_def)

lemma snd_lookupAround2_update:
  "ps y \<noteq> None \<Longrightarrow>
    snd (lookupAround2 x (ps (y \<mapsto> v'))) = snd (lookupAround2 x ps)"
  apply (clarsimp simp: lookupAround2_def lookupAround_def Let_def
                        dom_fun_upd2
              simp del: dom_fun_upd cong: if_cong option.case_cong)
  apply (clarsimp split: option.split split_if  cong: if_cong)
  apply auto
  done

lemma double_setEndpoint:
  "do y \<leftarrow> setEndpoint epptr v1; setEndpoint epptr v2 od
       = setEndpoint epptr v2"
  apply (simp add: setEndpoint_def setObject_def bind_assoc split_def
                   modify_gets_helper)
  apply (simp add: updateObject_default_def bind_assoc objBits_simps)
  apply (rule ext)
  apply (rule bind_apply_cong, rule refl)+
  apply (clarsimp simp add: in_monad projectKOs magnitudeCheck_assert
                            snd_lookupAround2_update)
  apply (simp add: lookupAround2_known1 assert_opt_def projectKO_def projectKO_opt_ep
                    alignCheck_assert)
  apply (simp add: bind_def simpler_modify_def)
  done

lemma filterM_setEndpoint_adjustment:
  "\<lbrakk> \<And>v. do setEndpoint epptr IdleEP; body v od
          = do v' \<leftarrow> body v; setEndpoint epptr IdleEP; return v' od \<rbrakk>
    \<Longrightarrow>
   (do q' \<leftarrow> filterM body q; setEndpoint epptr (f q') od)
    = (do setEndpoint epptr IdleEP; q' \<leftarrow> filterM body q; setEndpoint epptr (f q') od)"
  apply (rule sym)
  apply (induct q arbitrary: f)
   apply (simp add: double_setEndpoint)
  apply (simp add: bind_assoc)
  apply (subst bind_assoc[symmetric], simp, simp add: bind_assoc)
  done

lemma ccorres_inst_voodoo:
  "\<forall>x. ccorres r xf (P x) (P' x) hs (h x) (c x)
     \<Longrightarrow> \<forall>x. ccorres r xf (P x) (P' x) hs (h x) (c x)"
  by simp

lemma cpspace_relation_ep_update_ep2:
  "\<lbrakk> ko_at' (ep :: endpoint) epptr s;
      cmap_relation (map_to_eps (ksPSpace s))
           (cslift t) ep_Ptr (cendpoint_relation (cslift t));
      cendpoint_relation (cslift t') ep' endpoint;
      (cslift t' :: tcb_C ptr \<rightharpoonup> tcb_C) = cslift t \<rbrakk>
     \<Longrightarrow> cmap_relation (map_to_eps (ksPSpace s(epptr \<mapsto> KOEndpoint ep')))
          (cslift t(ep_Ptr epptr \<mapsto> endpoint))
          ep_Ptr (cendpoint_relation (cslift t'))"
  apply (rule cmap_relationE1, assumption, erule ko_at_projectKO_opt)
  apply (rule_tac P="\<lambda>a. cmap_relation a b c d" for b c d in rsubst,
                   erule cmap_relation_upd_relI, assumption+)
    apply simp+
  apply (rule ext, simp add: map_comp_def projectKO_opt_ep split: split_if)
  done

end

lemma setObject_tcb_ep_obj_at'[wp]:
  "\<lbrace>obj_at' (P :: endpoint \<Rightarrow> bool) ptr\<rbrace> setObject ptr' (tcb :: tcb) \<lbrace>\<lambda>rv. obj_at' P ptr\<rbrace>"
  apply (rule obj_at_setObject2, simp_all)
  apply (clarsimp simp: updateObject_default_def in_monad)
  done

crunch ep_obj_at'[wp]: setThreadState "obj_at' (P :: endpoint \<Rightarrow> bool) ptr"
  (ignore: getObject setObject simp: unless_def)

context kernel_m begin

lemma ccorres_abstract_h_val:
  "(\<And>rv. P rv \<Longrightarrow> ccorres r xf G (G' rv) hs a c) \<Longrightarrow>
   ccorres r xf G ({s. P (h_val (hrs_mem (t_hrs_' (globals s))) p) 
            \<longrightarrow> s \<in> G' (h_val (hrs_mem (t_hrs_' (globals s))) 
            p)} 
   \<inter> {s. P (h_val (hrs_mem (t_hrs_' (globals s))) p)}) hs a c"
   apply (rule ccorres_tmp_lift1 [where P = P])
   apply (clarsimp simp: Collect_conj_eq [symmetric])
   apply (fastforce intro: ccorres_guard_imp)
   done

lemma ccorres_subst_basic_helper:
  "\<lbrakk> \<And>s s'. \<lbrakk> P s; s' \<in> P'; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> f s' = f' s';
     \<And>s s'. \<lbrakk> P s; s' \<in> P'; (s, s') \<in> rf_sr \<rbrakk> \<Longrightarrow> (s, f' s') \<in> rf_sr;
     \<And>s'. xf' (f' s') = v; \<And>rv' t t'. ceqv \<Gamma> xf' rv' t t' c (c' rv');
        ccorres rrel xf Q Q' hs a (c' v) \<rbrakk>
       \<Longrightarrow> ccorres rrel xf (P and Q) {s. s \<in> P' \<and> f' s \<in> Q'} hs a (Basic f ;; c)"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_add_return)
   apply (rule ccorres_split_nothrow[where xf'=xf' and r'="\<lambda>rv rv'. rv' = v"])
       apply (rule ccorres_from_vcg[where P=P and P'=P'])
       apply (rule allI, rule conseqPre, vcg)
       apply (clarsimp simp: return_def)
      apply assumption
     apply simp
    apply wp
   apply vcg
  apply clarsimp
  done

lemma ctcb_relation_blocking_ipc_badge:
  "\<lbrakk> ctcb_relation tcb ctcb; isBlockedOnSend (tcbState tcb) \<rbrakk> \<Longrightarrow>
      tsType_CL (thread_state_lift (tcbState_C ctcb)) = scast ThreadState_BlockedOnSend"
  "\<lbrakk> ctcb_relation tcb ctcb;
        tsType_CL (thread_state_lift (tcbState_C ctcb)) = scast ThreadState_BlockedOnSend \<rbrakk>
      \<Longrightarrow> blockingIPCBadge (tcbState tcb)
             = blockingIPCBadge_CL (thread_state_lift (tcbState_C ctcb))"
   apply (clarsimp simp add: ctcb_relation_def)
   apply (simp add: isBlockedOnSend_def split: Structures_H.thread_state.split_asm)
   apply (clarsimp simp: cthread_state_relation_def)
  apply (clarsimp simp add: ctcb_relation_def cthread_state_relation_def)
  apply (cases "tcbState tcb", simp_all add: "StrictC'_thread_state_defs")
  done

lemma cendpoint_relation_q_cong:
  "\<lbrakk> \<And>t rf. (t, rf) \<in> ep_q_refs_of' ep \<Longrightarrow> hp (tcb_ptr_to_ctcb_ptr t) = hp' (tcb_ptr_to_ctcb_ptr t) \<rbrakk>
      \<Longrightarrow> cendpoint_relation hp ep ep' = cendpoint_relation hp' ep ep'"
  apply (cases ep, simp_all add: cendpoint_relation_def Let_def)
   apply (rule conj_cong [OF refl])
   apply (rule tcb_queue_relation'_cong[OF refl refl refl])
   apply clarsimp
  apply (rule conj_cong [OF refl])
  apply (rule tcb_queue_relation'_cong[OF refl refl refl])
  apply clarsimp
  done

lemma cnotification_relation_q_cong:
  "\<lbrakk>\<And>t rf. (t, rf) \<in> ntfn_q_refs_of' (ntfnObj ntfn) \<Longrightarrow>  hp (tcb_ptr_to_ctcb_ptr t) = hp' (tcb_ptr_to_ctcb_ptr t)\<rbrakk>
      \<Longrightarrow>  cnotification_relation hp ntfn ntfn' = cnotification_relation hp' ntfn ntfn'"
  apply (cases "ntfnObj ntfn", simp_all add: cnotification_relation_def Let_def)
  apply (auto intro: iffD1[OF tcb_queue_relation'_cong[OF refl refl refl]])
  done

lemma tcbSchedEnqueue_ep_at:
  "\<lbrace>obj_at' (P :: endpoint \<Rightarrow> bool) ep\<rbrace>
      tcbSchedEnqueue t
   \<lbrace>\<lambda>rv. obj_at' P ep\<rbrace>"
  apply (simp add: tcbSchedEnqueue_def unless_def null_def)
  apply (wp threadGet_wp, clarsimp, wp)
  apply (clarsimp split: split_if, wp)
  done

lemma ctcb_relation_unat_tcbPriority_C:
  "ctcb_relation tcb tcb' \<Longrightarrow> unat (tcbPriority_C tcb') = unat (tcbPriority tcb)"
  apply (clarsimp simp: ctcb_relation_def)
  apply (rule trans, rule arg_cong[where f=unat], erule sym)
  apply (simp(no_asm))
  done

lemma ccorres_duplicate_guard:
  "ccorres r xf (P and P) Q hs f f' \<Longrightarrow> ccorres r xf P Q hs f f'"
  by (erule ccorres_guard_imp, auto)


lemma ep_q_refs'_no_NTFNBound[simp]:
  "(x, NTFNBound) \<notin> ep_q_refs_of' ep"
  by (auto simp: ep_q_refs_of'_def split: endpoint.splits)


lemma ntfn_q_refs'_no_NTFNBound[simp]:
  "(x, NTFNBound) \<notin> ntfn_q_refs_of' ntfn"
  by (auto simp: ntfn_q_refs_of'_def split: ntfn.splits)

lemma cancelBadgedSends_ccorres:
  "ccorres dc xfdc (invs' and ep_at' ptr)
              (UNIV \<inter> {s. epptr_' s = Ptr ptr} \<inter> {s. badge_' s = bdg}) []
       (cancelBadgedSends ptr bdg) (Call cancelBadgedSends_'proc)"
  apply (cinit lift: epptr_' badge_' simp: whileAnno_def)
   apply (simp add: list_case_return2
              cong: list.case_cong Structures_H.endpoint.case_cong call_ignore_cong
               del: Collect_const)
   apply (rule ccorres_pre_getEndpoint)
   apply (rule_tac R="ko_at' rv ptr" and xf'="ret__unsigned_'"
               and val="case rv of RecvEP q \<Rightarrow> scast EPState_Recv | IdleEP \<Rightarrow> scast EPState_Idle
                                | SendEP q \<Rightarrow> scast EPState_Send"
               in ccorres_symb_exec_r_known_rv_UNIV[where R'=UNIV])
      apply vcg
      apply clarsimp
      apply (erule cmap_relationE1 [OF cmap_relation_ep], erule ko_at_projectKO_opt)
      apply (clarsimp simp: typ_heap_simps cendpoint_relation_def Let_def
                     split: Structures_H.endpoint.split_asm)
     apply ceqv
    apply wpc
      apply (simp add: dc_def[symmetric] ccorres_cond_iffs)
      apply (rule ccorres_return_Skip)
     apply (simp add: dc_def[symmetric] ccorres_cond_iffs)
     apply (rule ccorres_return_Skip)
    apply (rename_tac list)
    apply (simp add: Collect_True Collect_False endpoint_state_defs
                     ccorres_cond_iffs dc_def[symmetric]
                del: Collect_const cong: call_ignore_cong)
    apply (rule ccorres_rhs_assoc)+
    apply (csymbr, csymbr)
    apply (drule_tac s = rv in sym, simp only:)
    apply (rule_tac P="ko_at' rv ptr and invs'" in ccorres_cross_over_guard)
    apply (rule ccorres_symb_exec_r)
      apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2)
      apply (rule ccorres_split_nothrow[where r'=dc and xf'=xfdc, OF _ ceqv_refl])
         apply (rule_tac P="ko_at' rv ptr"
                    in ccorres_from_vcg[where P'=UNIV])
         apply (rule allI, rule conseqPre, vcg)
         apply clarsimp
         apply (rule cmap_relationE1[OF cmap_relation_ep], assumption)
          apply (erule ko_at_projectKO_opt)
         apply (clarsimp simp: typ_heap_simps setEndpoint_def)
         apply (rule rev_bexI)
          apply (rule setObject_eq; simp add: objBits_simps)[1]
         apply (clarsimp simp: rf_sr_def cstate_relation_def
                               Let_def carch_state_relation_def
                               cmachine_state_relation_def
                               )
         apply (clarsimp simp: cpspace_relation_def
                               update_ep_map_tos)
         apply (erule(1) cpspace_relation_ep_update_ep2)
          apply (simp add: cendpoint_relation_def endpoint_state_defs)
         subgoal by simp
        apply (rule ccorres_symb_exec_r)
          apply (rule_tac xs=list in filterM_voodoo)
          apply (rule_tac P="\<lambda>xs s. (\<forall>x \<in> set xs \<union> set list.
                   st_tcb_at' (\<lambda>st. isBlockedOnSend st \<and> blockingObject st = ptr) x s)
                              \<and> distinct (xs @ list) \<and> ko_at' IdleEP ptr s
                              \<and> (\<forall>p. \<forall>x \<in> set (xs @ list). \<forall>rf. (x, rf) \<notin> {r \<in> state_refs_of' s p. snd r \<noteq> NTFNBound})
                              \<and> valid_queues s \<and> pspace_aligned' s \<and> pspace_distinct' s
                              \<and> sch_act_wf (ksSchedulerAction s) s \<and> valid_objs' s"
                     and P'="\<lambda>xs. {s. ep_queue_relation' (cslift s) (xs @ list)
                                         (head_C (queue_' s)) (end_C (queue_' s))}
                                \<inter> {s. thread_' s = (case list of [] \<Rightarrow> tcb_Ptr 0
                                                       | x # xs \<Rightarrow> tcb_ptr_to_ctcb_ptr x)}"
                      in ccorres_inst_voodoo)
          apply (induct_tac list)
           apply (rule allI)
           apply (rule iffD1 [OF ccorres_expand_while_iff_Seq])
           apply (rule ccorres_tmp_lift2 [OF _ _ refl])
            apply ceqv
           apply (simp add: ccorres_cond_iffs)
           apply (rule ccorres_rhs_assoc2)
           apply (rule ccorres_duplicate_guard, rule ccorres_split_nothrow_novcg_dc)
              apply (rule ccorres_from_vcg, rule allI, rule conseqPre, vcg)
              apply clarsimp
              apply (drule obj_at_ko_at', clarsimp)
              apply (rule cmap_relationE1[OF cmap_relation_ep], assumption)
               apply (erule ko_at_projectKO_opt)
              apply (clarsimp simp: typ_heap_simps tcb_queue_relation'_def)
              apply (case_tac x)
               apply (clarsimp simp: setEndpoint_def)
               apply (rule rev_bexI, rule setObject_eq,
                      (simp add: objBits_simps)+)
               apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                 carch_state_relation_def
                 cmachine_state_relation_def
                 cpspace_relation_def
                 update_ep_map_tos)
               apply (erule(1) cpspace_relation_ep_update_ep2)
                subgoal by (simp add: cendpoint_relation_def Let_def)
               subgoal by simp
              apply (clarsimp simp: tcb_at_not_NULL[OF pred_tcb_at']
                                    setEndpoint_def)
              apply (rule rev_bexI, rule setObject_eq,
                      (simp add: objBits_simps)+)
              apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                                     carch_state_relation_def
                                     cmachine_state_relation_def
                                     cpspace_relation_def
                                     update_ep_map_tos)
              apply (erule(1) cpspace_relation_ep_update_ep2)
               apply (simp add: cendpoint_relation_def Let_def)
               apply (subgoal_tac "tcb_at' (last (a # list)) \<sigma> \<and> tcb_at' a \<sigma>")
                apply (clarsimp simp: is_aligned_neg_mask [OF is_aligned_tcb_ptr_to_ctcb_ptr[where P=\<top>]])
                subgoal by (simp add: tcb_queue_relation'_def EPState_Send_def mask_def)
               subgoal by (auto split: split_if)
              subgoal by simp
             apply (ctac add: rescheduleRequired_ccorres[unfolded dc_def])
            apply (rule hoare_pre, wp weak_sch_act_wf_lift_linear set_ep_valid_objs')
            apply (clarsimp simp: weak_sch_act_wf_def sch_act_wf_def)
            apply (fastforce simp: valid_ep'_def pred_tcb_at' split: list.splits)
           apply (simp add: guard_is_UNIV_def)
          apply (rule allI)
          apply (rename_tac a lista x)
          apply (rule iffD1 [OF ccorres_expand_while_iff_Seq])
          apply (rule ccorres_init_tmp_lift2, ceqv)
          apply (rule ccorres_guard_imp2)
           apply (simp add: bind_assoc dc_def[symmetric]
                       del: Collect_const)
           apply (rule ccorres_cond_true)
           apply (rule ccorres_rhs_assoc)+
           apply (rule ccorres_pre_threadGet[where f=tcbState, folded getThreadState_def])
           apply (rule ccorres_move_c_guard_tcb)
           apply csymbr
           apply (rule ccorres_abstract_cleanup)
           apply (rule ccorres_move_c_guard_tcb)
           apply (rule_tac P=\<top>
                      and P'="{s. ep_queue_relation' (cslift s) (x @ a # lista)
                                        (head_C (queue_' s)) (end_C (queue_' s))}"
                      and f'="\<lambda>s. s \<lparr> next___ptr_to_struct_tcb_C_' := (case lista of [] \<Rightarrow> tcb_Ptr 0 
                                              | v # vs \<Rightarrow> tcb_ptr_to_ctcb_ptr v) \<rparr>"
                      and xf'="next___ptr_to_struct_tcb_C_'"
                           in ccorres_subst_basic_helper)
               apply (thin_tac "\<forall>x. P x" for P)
               apply (rule myvars.fold_congs, (rule refl)+)
               apply (clarsimp simp: tcb_queue_relation'_def use_tcb_queue_relation2
                                     tcb_queue_relation2_concat)
               apply (clarsimp simp: typ_heap_simps split: list.split)
              subgoal by (simp add: rf_sr_def)
             apply simp
            apply ceqv
           apply (rule_tac P="b=blockingIPCBadge rva" in ccorres_gen_asm2)
           apply (rule ccorres_if_bind, rule ccorres_if_lhs)
            apply (simp add: bind_assoc dc_def[symmetric])
            apply (rule ccorres_rhs_assoc)+
            apply (ctac add: setThreadState_ccorres)
              apply (ctac add: tcbSchedEnqueue_ccorres)
                apply (rule_tac P="\<lambda>s. \<forall>t \<in> set (x @ a # lista). tcb_at' t s"
                             in ccorres_cross_over_guard)
                apply (rule ccorres_add_return, rule ccorres_split_nothrow[OF _ ceqv_refl])
                   apply (rule_tac rrel=dc and xf=xfdc
                               and P="\<lambda>s. (\<forall>t \<in> set (x @ a # lista). tcb_at' t s)
                                          \<and> (\<forall>p. \<forall>t \<in> set (x @ a # lista). \<forall>rf. (t, rf) \<notin> {r \<in> state_refs_of' s p. snd r \<noteq> NTFNBound})
                                          \<and> valid_queues s \<and> distinct (x @ a # lista)
                                          \<and> pspace_aligned' s \<and> pspace_distinct' s"
                              and P'="{s. ep_queue_relation' (cslift s) (x @ a # lista)
                                           (head_C (queue_' s)) (end_C (queue_' s))}"
                               in ccorres_from_vcg)
                   apply (thin_tac "\<forall>x. P x" for P)
                   apply (rule allI, rule conseqPre, vcg)
                   apply (clarsimp simp: ball_Un)
                   apply (rule exI, rule conjI)
                    apply (rule exI, erule conjI)
                    apply (intro conjI[rotated]) 
                    apply (assumption)
                    apply fold_subgoals[3]
                    subgoal by (fastforce intro: pred_tcb_at')+
                   apply (clarsimp simp: return_def rf_sr_def cstate_relation_def Let_def)
                   apply (rule conjI)
                    apply (clarsimp simp: cpspace_relation_def)
                    apply (rule conjI, erule ctcb_relation_null_queue_ptrs)
                     apply (rule null_ep_queue)
                     subgoal by (simp add: o_def)
                    apply (rule conjI)
                     apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
                     apply clarsimp
                     apply (rule cendpoint_relation_q_cong)
                     apply (rule sym, erule restrict_map_eqI)
                     apply (clarsimp simp: image_iff)
                     apply (drule(2) map_to_ko_atI2)
                     apply (drule ko_at_state_refs_ofD')
                     apply clarsimp
                     apply (drule_tac x=p in spec)
                     subgoal by fastforce
                    apply (erule iffD1 [OF cmap_relation_cong, OF refl refl, rotated -1])
                    apply clarsimp
                    apply (drule(2) map_to_ko_atI2, drule ko_at_state_refs_ofD')

                    apply (rule cnotification_relation_q_cong)
                    apply (rule sym, erule restrict_map_eqI)
                    apply (clarsimp simp: image_iff)
                    apply (drule_tac x=p in spec)
                    subgoal by fastforce
                   apply (rule conjI)
                    apply (erule cready_queues_relation_not_queue_ptrs,
                           auto dest: null_ep_schedD[unfolded o_def] simp: o_def)[1]
                   apply (simp add: carch_state_relation_def 
                                    cmachine_state_relation_def
                                    h_t_valid_clift_Some_iff)
                  apply (rule ccorres_symb_exec_r2)
                    apply (erule spec)
                   apply vcg
                  apply (vcg spec=modifies)
                 apply wp
                apply simp
                apply vcg
               apply (wp hoare_vcg_const_Ball_lift tcbSchedEnqueue_ep_at
                         sch_act_wf_lift)
              apply simp
              apply (vcg exspec=tcbSchedEnqueue_cslift_spec)
             apply (wp hoare_vcg_const_Ball_lift sts_st_tcb_at'_cases
                       sts_sch_act sts_valid_queues setThreadState_oa_queued)
            apply (vcg exspec=setThreadState_cslift_spec)
           apply (simp add: ccorres_cond_iffs dc_def[symmetric])
           apply (rule ccorres_symb_exec_r2)
             apply (drule_tac x="x @ [a]" in spec, simp add: dc_def[symmetric])
            apply vcg
           apply (vcg spec=modifies)
          apply (thin_tac "\<forall>x. P x" for P)
          apply (clarsimp simp: pred_tcb_at' ball_Un)
          apply (rule conjI)
           apply (clarsimp split: split_if)
           subgoal by (fastforce simp: valid_tcb_state'_def valid_objs'_maxDomain
                                  valid_objs'_maxPriority dest: pred_tcb_at')
          apply (clarsimp simp: tcb_at_not_NULL [OF pred_tcb_at'])
          apply (clarsimp simp: typ_heap_simps st_tcb_at'_def)
          apply (drule(1) obj_at_cslift_tcb)
          apply (clarsimp simp: ctcb_relation_blocking_ipc_badge)
          apply (rule conjI, simp add: "StrictC'_thread_state_defs" mask_def)
          apply (rule conjI)
           apply clarsimp
           apply (frule rf_sr_cscheduler_relation)
           apply (clarsimp simp: cscheduler_action_relation_def st_tcb_at'_def
                          split: scheduler_action.split_asm)
           apply (rename_tac word)
           apply (frule_tac x=word in tcbSchedEnqueue_cslift_precond_discharge)
              apply simp
             subgoal by clarsimp
            subgoal by clarsimp
           subgoal by clarsimp
          apply clarsimp
          apply (rule conjI)
           apply (frule(3) tcbSchedEnqueue_cslift_precond_discharge)
           subgoal by clarsimp
          apply clarsimp
          apply (rule context_conjI)
           apply (clarsimp simp: tcb_queue_relation'_def)
           apply (erule iffD2[OF ep_queue_relation_shift[rule_format], rotated -1])
           subgoal by simp
          apply (rule_tac x="x @ a # lista" in exI)
          apply (clarsimp simp: ball_Un)
          apply (rule conjI, fastforce)
          subgoal by (clarsimp simp: remove1_append)
         apply vcg
        apply (rule conseqPre, vcg)
        apply clarsimp
       apply (wp hoare_vcg_const_Ball_lift)
       apply (wp obj_at_setObject3[where 'a=endpoint, folded setEndpoint_def])
         apply (simp add: objBits_simps)+
       apply (wp set_ep_valid_objs')
      apply vcg
     apply vcg
    apply (rule conseqPre, vcg)
    apply clarsimp
   apply (clarsimp simp: guard_is_UNIV_def)
   apply (erule cmap_relationE1[OF cmap_relation_ep], erule ko_at_projectKO_opt)
   apply (clarsimp simp: typ_heap_simps)
   apply (clarsimp simp: cendpoint_relation_def Let_def)
   subgoal by (clarsimp simp: tcb_queue_relation'_def neq_Nil_conv
                  split: split_if_asm)
  apply clarsimp
  apply (frule ko_at_valid_objs', clarsimp)
   apply (simp add: projectKOs)
  apply (clarsimp simp: valid_obj'_def valid_ep'_def)
  apply (frule sym_refs_ko_atD', clarsimp)
  apply (clarsimp simp: st_tcb_at_refs_of_rev')
  apply (rule conjI)
   subgoal by (auto simp: isBlockedOnSend_def elim!: pred_tcb'_weakenE)
  apply (rule conjI)
   apply (clarsimp split: split_if)
   apply (drule sym_refsD, clarsimp)
   apply (drule(1) bspec)+
   by (auto simp: obj_at'_def projectKOs state_refs_of'_def pred_tcb_at'_def tcb_bound_refs'_def 
              dest!: symreftype_inverse')


lemma tcb_ptr_to_ctcb_ptr_force_fold:
  "x + 0x100 = ptr_val (tcb_ptr_to_ctcb_ptr x)"
  by (simp add: tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)


lemma coerce_memset_to_heap_update:
  "heap_update_list x (replicateHider (size_of (TYPE (tcb_C))) 0)
      = heap_update (tcb_Ptr x)
             (tcb_C (arch_tcb_C (user_context_C (FCP (\<lambda>x. 0))))
                    (thread_state_C (FCP (\<lambda>x. 0)))
                    (NULL)
                    (fault_C (FCP (\<lambda>x. 0)))
                    (lookup_fault_C (FCP (\<lambda>x. 0)))
                      0 0 0 0 0 NULL NULL NULL NULL)"
  apply (intro ext, simp add: heap_update_def)
  apply (rule_tac f="\<lambda>xs. heap_update_list x xs a b" for a b in arg_cong)
  apply (simp add: to_bytes_def size_of_def typ_info_simps tcb_C_tag_def)
  apply (simp add: ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def)
  apply (simp add: typ_info_simps 
                   user_context_C_tag_def thread_state_C_tag_def fault_C_tag_def
                   lookup_fault_C_tag_def update_ti_t_ptr_0s arch_tcb_C_tag_def
                   ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td 
                   ti_typ_combine_empty_ti ti_typ_combine_td       
                   align_of_def padup_def
                   final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def 
                   align_td_array' size_td_array)
  apply (simp add: typ_info_array')
  apply (simp add: typ_info_word word_rsplit_0 upt_conv_Cons)
  apply (simp add: typ_info_word typ_info_ptr word_rsplit_0
                   replicateHider_def)
  done

lemma isArchObjectCap_capBits:
  "isArchObjectCap cap \<Longrightarrow> capBits cap = acapBits (capCap cap)"
  by (clarsimp simp: isCap_simps)

declare Kernel_C.tcb_C_size [simp del]
lemma recycleCap_ccorres':
  "ccorres ccap_relation ret__struct_cap_C_'
     (invs' and valid_cap' cp and (\<lambda>s. 2 ^ capBits cp \<le> gsMaxObjectSize s)
         and (\<lambda>s. capRange cp \<inter> kernel_data_refs = {}))
     (UNIV \<inter> {s. (is_final_' s) = from_bool is_final} \<inter> {s. ccap_relation cp (cap_' s)}) []
     (recycleCap is_final cp) (Call recycleCap_'proc)"
  apply (rule ccorres_gen_asm)
  apply (cinit lift: cap_')
   apply csymbr
   apply (simp only: cap_get_tag_isCap)
   apply (rule ccorres_Cond_rhs_Seq)
    apply (simp add: from_bool_neq_0)
    apply (subst if_not_P, fastforce simp: isCap_simps)+
    apply (simp add: isArchCap_T_isArchObjectCap Let_def liftM_def)
    apply (rule ccorres_rhs_assoc)+
    apply (ctac(no_vcg) add: arch_recycleCap_ccorres)
     apply (rule ccorres_rhs_assoc2, rule ccorres_split_throws)
      apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
      apply (rule allI, rule conseqPre, vcg)
      apply (clarsimp simp: return_def)
     apply vcg
    apply wp
   apply (simp del: Collect_const)
   apply csymbr
   apply (simp only: cap_get_tag_isCap)
   apply (rule ccorres_cond2[where R=\<top>], simp del: Collect_const)
    apply (simp?, rule ccorres_fail)
   apply (rule ccorres_Cond_rhs)
    apply (subst if_not_P, fastforce simp: isCap_simps)+
    apply ((rule ccorres_return_C | simp)+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (subst if_not_P, fastforce simp: isCap_simps)+
    apply ((rule ccorres_return_C | simp)+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (subst if_not_P, fastforce simp: isCap_simps)+
    apply ((rule ccorres_return_C | simp)+)[1]
   apply (rule ccorres_Cond_rhs)
    apply (rule_tac P="capAligned cp \<and> capZombieType cp \<noteq> ZombieCNode 0"
               in ccorres_gen_asm)
    apply (simp only: cap_get_tag_isCap[symmetric],
           frule(1) cap_get_tag_to_H)
    apply (simp add: Let_def word_sle_def Collect_True
                     Collect_False cap_get_tag_to_H
                del: Collect_const)
    apply (csymbr | rule ccorres_rhs_assoc ccorres_Guard)+
    apply (simp del: Collect_const)
    apply (rule ccorres_Cond_rhs)
     apply (simp add: isZombieTCB_C_def ZombieTCB_C_def)
     apply (rule ccorres_rhs_assoc | csymbr)+
     apply (simp del: Collect_const)
     apply (rule  ccorres_Guard_Seq[where S=UNIV])+
     apply csymbr
     apply (rule ccorres_move_c_guard_tcb)
     apply (rule ccorres_symb_exec_r)
       apply (simp del: Collect_const)
       apply (rule ccorres_pre_threadGet)
       apply (rule ccorres_assert)+
       apply (rule ccorres_pre_curDomain)
       apply (rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2, rule ccorres_rhs_assoc2,
              rule ccorres_split_nothrow_novcg_dc)
          apply (rule_tac P="op = tcb" and P'="\<lambda>s. invs' s \<and> rv = ksCurDomain s
                            \<and> size_of TYPE(tcb_C) \<le> gsMaxObjectSize s"
                     in threadSet_ccorres_lemma3, vcg)
          apply (simp only: replicateHider_def[symmetric])
          apply clarsimp
          apply (clarsimp simp: get_capZombiePtr_CL_def get_capZombieBits_CL_def
                                isZombieTCB_C_def ZombieTCB_C_def word_bits_conv
                                is_aligned_no_wrap' capAligned_def)
          apply (subst ghost_assertion_size_logic[unfolded o_def, rotated])
            apply assumption
           apply (simp add: tcb_C_size)
          apply (subst h_t_valid_dom_s, erule h_t_valid_clift)
            apply (simp add: tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)
           apply (simp add: tcb_C_size)
          apply (frule tcb_at_not_NULL[OF obj_at'_weakenE, OF _ TrueI],
                 simp add: tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)
          apply (rule conjI)
           apply (simp add: size_of_def)
           apply (drule is_aligned_no_wrap'[OF is_aligned_tcb_ptr_to_ctcb_ptr, where off="0x8B"])
            subgoal by simp
           apply (simp add: field_simps tcb_ptr_to_ctcb_ptr_def ctcb_offset_def)

          apply (rule conjI)
           apply (erule aligned_add_aligned)
             apply (clarsimp simp: is_aligned_def)
            subgoal by simp
          apply (rule conjI)
           subgoal by (clarsimp simp: is_aligned_def size_of_def)
          apply (clarsimp simp: typ_heap_simps' CPSR_def)
          apply (simp add: word_of_nat[symmetric] word_unat.Abs_inverse
                           unats_def max_size[simplified addr_card, simplified]
                           coerce_memset_to_heap_update word_sle_def)
          apply (clarsimp simp: typ_heap_simps' packed_heap_update_collapse_hrs)
          apply (clarsimp cong: StateSpace.state.fold_congs globals.fold_congs)
          apply (rule rf_sr_tcb_update_not_in_queue2,
                 (simp add: typ_heap_simps' tcb_ptr_to_ctcb_ptr_def ctcb_offset_def
                      cong: if_weak_cong)+) (*
             apply (clarsimp split: Structures_H.thread_state.split_asm)
            apply simp *)
           subgoal by (rule ball_tcb_cte_casesI, simp_all)
          apply (clarsimp simp: ctcb_relation_def makeObject_tcb minBound_word
                                fault_lift_null_fault fault_null_fault_def
                                fault_get_tag_def fcp_beta cfault_rel_def
                                lookup_fault_lift_def lookup_fault_tag_defs
                                lookup_fault_get_tag_def Let_def
                                thread_state_lift_def cthread_state_relation_def
                                "StrictC'_thread_state_defs" ccontext_relation_def
                                newContext_def2 option_to_ptr_def option_to_0_def
                                rf_sr_ksCurDomain)
          apply (clarsimp simp add: timeSlice_def is_cap_fault_def)
          subgoal for \<dots> r by (cases r, simp_all add: "StrictC'_register_defs")
         apply csymbr
         apply (rule ccorres_return_C, simp+)[1]
        apply wp
       apply (clarsimp simp add: guard_is_UNIV_def ccap_relation_def
                                 cap_thread_cap_lift cap_to_H_def
                                 to_bool_def true_def
                                 mask_def[where n="Suc 0"])
       apply (rule iffD1 [OF tcb_ptr_to_ctcb_ptr_eq], simp)
       apply (clarsimp simp: tcb_ptr_to_ctcb_ptr_def ctcb_offset_def
                             capAligned_def is_aligned_neg_mask)
       apply (clarsimp simp: get_capZombiePtr_CL_def get_capZombieBits_CL_def Let_def
                             isZombieTCB_C_def ZombieTCB_C_def)
       apply (rule sym, rule is_aligned_neg_mask)
        apply (erule aligned_add_aligned[where m=8], simp_all)[1]
        subgoal by (simp add: is_aligned_def)
       subgoal by simp
      apply vcg
     apply (rule conseqPre, vcg)
     subgoal by clarsimp
    apply (simp add: isZombieTCB_C_def ZombieTCB_C_def
                     Let_def
                del: Collect_const)
    apply (rule ccorres_from_vcg_throws[where P=\<top> and P'=UNIV])
    apply (rule allI, rule conseqPre, vcg)
    apply (clarsimp simp: return_def ccap_zombie_radix_less4
                          isCap_simps)
    apply (subst ccap_relation_def)
    apply (clarsimp simp: cap_to_H_def cap_cnode_cap_lift[THEN iffD1]
                          get_capZombiePtr_CL_def Let_def
                          get_capZombieBits_CL_def
                          isZombieTCB_C_def ZombieTCB_C_def
                          less_mask_eq[where n=5]
                          ccap_zombie_radix_less2
                          c_valid_cap_def cl_valid_cap_def)
    apply (rule sym, rule is_aligned_neg_mask)
     apply (clarsimp simp: capAligned_def, assumption)
    apply (clarsimp simp: capAligned_def objBits_simps)
   apply (simp del: Collect_const)
   apply (rule ccorres_if_lhs,
          simp_all add: Let_def ccorres_cond_iffs Collect_True
                        when_def
                   del: Collect_const)[1]
    apply (rule ccorres_rhs_assoc | csymbr)+
    apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
        apply (rule_tac R=\<top> in ccorres_cond2)
          apply (clarsimp simp: cap_get_tag_isCap[symmetric] isDomainCap[symmetric]
                      simp del: Collect_const isDomainCap dest!: cap_get_tag_to_H)
         apply (rule ccorres_rhs_assoc | csymbr)+
         apply (ctac add: cancelBadgedSends_ccorres)
        apply (rule ccorres_return_Skip)
       apply (rule ceqv_refl)
      apply (rule ccorres_return_C, simp+)[1]
     apply wp
    apply (simp add: guard_is_UNIV_def)
   apply (simp add: ccorres_cond_iffs isArchCap_T_isArchObjectCap from_bool_0)
   apply (rule ccorres_return_C, simp+)[1]
  apply (clarsimp simp: Collect_const_mem)
  apply (simp add: eq_commute[where 'a=tcb])
  apply (frule valid_capAligned)
  apply (simp add: ccap_zombie_radix_less4 isArchObjectCap_Cap_capCap cap_get_tag_isCap
                   isArchCap_T_isArchObjectCap from_bool_neq_0 from_bool_0)
  apply (intro conjI impI, simp_all add: cap_get_tag_isCap[symmetric])
     by (clarsimp simp: isZombieTCB_C_def ZombieTCB_C_def
                           valid_cap'_def ctcb_ptr_to_tcb_ptr_def
                           ctcb_offset_def get_capZombiePtr_CL_def
                           get_capZombieBits_CL_def valid_cap'_def
                           Let_def isDomainCap[symmetric] isArchObjectCap_Cap_capCap
                           isArchObjectCap_capBits tcb_C_size
                 simp del: isDomainCap
                    dest!: cap_get_tag_to_H
                    split: split_if_asm)+

lemma recycleCap_ccorres:
  "ccorres ccap_relation ret__struct_cap_C_'
     (invs' and (\<lambda>s. \<exists>p. cte_wp_at' (\<lambda>cte. cteCap cte = cp) p s))
     (UNIV \<inter> {s. (is_final_' s) = from_bool is_final} \<inter> {s. ccap_relation cp (cap_' s)}) []
     (recycleCap is_final cp) (Call recycleCap_'proc)"
  apply (rule ccorres_guard_imp2, rule recycleCap_ccorres')
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (auto dest: valid_global_refsD_with_objSize)
  done

lemma cteRecycle_ccorres:
  "ccorres (cintr \<currency> dc) (liftxf errstate id (K ()) ret__unsigned_long_')
     (invs' and sch_act_simple) (UNIV \<inter> {s. slot_' s = cte_Ptr slot}) []
     (cteRecycle slot) (Call cteRecycle_'proc)"
  apply (cinit lift: slot_')
   apply (ctac(no_vcg) add: cteRevoke_ccorres)
     apply (simp add: Collect_False del: Collect_const)
     apply (ctac(no_vcg) add: ccorres_use_cutMon [OF finaliseSlot_ccorres])
       apply (simp add: Collect_False liftE_def bind_assoc unless_def when_def
                        dc_def[symmetric]
                   del: Collect_const)
       apply (rule ccorres_pre_getCTE)
       apply (rule ccorres_move_c_guard_cte)
       apply (rule_tac xf'=ret__unsigned_'
                     and F="\<lambda>v. (v = scast cap_null_cap) = (cteCap x = NullCap)"
                     and R="cte_wp_at' (op = x) slot"
                  in ccorres_symb_exec_r_abstract_UNIV[where R'=UNIV])
          apply vcg
          apply (clarsimp simp: cte_wp_at_ctes_of)
          apply (erule(1) cmap_relationE1 [OF cmap_relation_cte])
          apply (clarsimp simp: cap_get_tag_isCap typ_heap_simps
                         dest!: ccte_relation_ccap_relation)
         apply ceqv
        apply (simp del: Collect_const)
        apply (rule_tac P="cte_wp_at' (op = x) slot" in ccorres_cross_over_guard)
        apply (rule_tac r'=dc and xf'=xfdc in ccorres_split_nothrow_novcg)
            apply (rule ccorres_cond[where R=\<top>])
              apply (simp del: Collect_const)
             apply (rule ccorres_rhs_assoc)+
             apply (csymbr, csymbr)
             apply (ctac add: isFinalCapability_ccorres [where slot = slot])
               apply (rule ccorres_move_c_guard_cte)
               apply (ctac(no_vcg) add: recycleCap_ccorres)
                apply (rule ccorres_move_c_guard_cte)
                apply (rule ccorres_updateCap)
               apply (wp isFinalCapability_inv)
             apply (vcg exspec=isFinalCapability_modifies)
            apply (rule ccorres_return_Skip)
           apply (rule ceqv_refl)
          apply (rule ccorres_return_CE[unfolded returnOk_def o_def], simp+)[1]
         apply wp
        apply (simp add: guard_is_UNIV_def)
       apply (simp add: guard_is_UNIV_def del: Collect_const)
       apply (clarsimp simp: cte_wp_at_ctes_of)
       apply (erule(1) cmap_relationE1[OF cmap_relation_cte])
       apply (clarsimp simp: typ_heap_simps dest!: ccte_relation_ccap_relation)
      apply simp
      apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
      apply vcg
     apply (simp add: cte_wp_at_ctes_of exI[where x=slot] imp_conjL[symmetric])
     apply (wp finaliseSlot_invs hoare_drop_imps)
    apply simp
    apply (rule ccorres_split_throws, rule ccorres_return_C_errorE, simp+)
    apply vcg
   apply simp
   apply (wp cteRevoke_invs' cteRevoke_sch_act_simple)
  apply (clarsimp simp: from_bool_def true_def exception_defs cintr_def)
  done

end
end
