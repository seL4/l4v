(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchFinalise_AI
imports "../Finalise_AI"
begin

context Arch begin

named_theorems Finalise_AI_asms

lemma obj_at_not_live_valid_arch_cap_strg [Finalise_AI_asms]:
  "(s \<turnstile> ArchObjectCap cap \<and> aobj_ref cap = Some r)
        \<longrightarrow> obj_at (\<lambda>ko. \<not> live ko) r s"
  by (clarsimp simp: valid_cap_def obj_at_def
                     a_type_arch_live
              split: arch_cap.split_asm if_split_asm)

global_naming X64

lemma valid_global_refs_asid_table_udapte [iff]:
  "valid_global_refs (s\<lparr>arch_state := x64_asid_table_update f (arch_state s)\<rparr>) =
  valid_global_refs s"
  by (simp add: valid_global_refs_def global_refs_def)

lemma reachable_pg_cap_cdt_update[simp]:
  "reachable_pg_cap x (cdt_update f s) = reachable_pg_cap x s"
  by (simp add: reachable_pg_cap_def)

lemma reachable_pg_cap_is_original_cap_update [simp]:
  "reachable_pg_cap x (is_original_cap_update f s) = reachable_pg_cap x s"
  by (simp add: reachable_pg_cap_def)

lemma reachable_pg_cap_update[simp]:
  "reachable_pg_cap cap' (trans_state f s) = reachable_pg_cap cap' s"
  by (simp add:reachable_pg_cap_def vs_lookup_pages_def
    vs_lookup_pages1_def obj_at_def)

(* FIXME x64: this needs stuff about equality between vs_lookup and vs_lookup_pages
              for PageMapL4, PDPTs *)
lemma vs_lookup_pages_eq:
  "\<lbrakk>valid_arch_objs s; valid_asid_table (x64_asid_table (arch_state s)) s;
    valid_cap cap s; table_cap_ref cap = Some vref; oref \<in> obj_refs cap\<rbrakk>
   \<Longrightarrow> (vref \<unrhd> oref) s = (vref \<rhd> oref) s"
  apply (clarsimp simp: table_cap_ref_def
                        vs_lookup_pages_eq_at[symmetric, THEN fun_cong]
                        vs_lookup_pages_eq_ap[symmetric, THEN fun_cong]
                 split: cap.splits arch_cap.splits option.splits)
  apply (rule iffI[rotated, OF vs_lookup_pages_vs_lookupI], assumption)
  apply (simp add: valid_cap_def)
  apply (erule vs_lookup_vs_lookup_pagesI', clarsimp+)
  sorry

lemma nat_to_cref_unat_of_bl':
  "\<lbrakk> length xs < word_bits; n = length xs \<rbrakk> \<Longrightarrow>
   nat_to_cref n (unat (of_bl xs :: machine_word)) = xs"
  apply (simp add: nat_to_cref_def word_bits_def)
  apply (rule nth_equalityI)
   apply simp
  apply clarsimp
  apply (subst to_bl_nth)
   apply (simp add: word_size)
  apply (simp add: word_size)
  apply (simp add: test_bit_of_bl rev_nth)
  apply fastforce
  done

lemmas nat_to_cref_unat_of_bl = nat_to_cref_unat_of_bl' [OF _ refl]

(* FIXME x64: this needs reevaluation - do we need the "asid_map" premise?
              note delete_asid_pool for arm and x64 differ a lot *)
lemma invs_x64_asid_table_unmap:
  "invs s \<and> is_aligned base asid_low_bits \<and> base \<le> mask asid_bits
       \<and> (\<forall>x\<in>set [0.e.2 ^ asid_low_bits - 1]. x64_asid_map (arch_state s) (base + x) = None)
       \<and> tab = x64_asid_table (arch_state s)
     \<longrightarrow> invs (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := tab(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
  apply (strengthen valid_asid_map_unmap valid_arch_objs_unmap_strg
                    valid_vs_lookup_unmap_strg valid_arch_state_unmap_strg)
  apply (simp add: valid_irq_node_def valid_kernel_mappings_def
                   valid_global_objs_arch_update)
  apply (simp add: valid_table_caps_def valid_machine_state_def)
  done

crunch asid_map[wp]: do_machine_op "valid_asid_map"

lemma invalidate_asid_asid_map_None_inv:
  "\<lbrace>\<lambda>s. x64_asid_map (arch_state s) y = None\<rbrace>
  invalidate_asid x
  \<lbrace>\<lambda>_ s. x64_asid_map (arch_state s) y = None\<rbrace>"
  apply (simp add: invalidate_asid_def)
  apply (wp )
  apply simp
  done

lemma invalidate_asid_entry_asid_map_None_inv:
  "\<lbrace>\<lambda>s. x64_asid_map (arch_state s) y = None\<rbrace>
  invalidate_asid_entry x z
  \<lbrace>\<lambda>_ s. x64_asid_map (arch_state s) y = None\<rbrace>"
  apply (simp add: invalidate_asid_entry_def)
  by (wp invalidate_asid_asid_map_None_inv)

crunch vs_lookup [wp]: invalidate_asid_entry "\<lambda>s. P (vs_lookup s)"

crunch aligned [wp]: invalidate_asid_entry pspace_aligned

crunch "distinct" [wp]: invalidate_asid_entry pspace_distinct

crunch caps_of_state[wp]: invalidate_asid_entry "\<lambda>s. P (caps_of_state s)"

crunch arch_objs [wp]: invalidate_asid_entry valid_arch_objs
  (simp: valid_arch_objs_arch_update)

lemma invalidate_asid_invalidates:
  "\<lbrace>valid_asid_map and valid_arch_state and K (asid \<le> mask asid_bits) and
    (\<lambda>s. x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some ap)\<rbrace>
   invalidate_asid asid
   \<lbrace>\<lambda>rv s. \<forall>asida. asida \<le> mask asid_bits \<longrightarrow>
              ucast asida = (ucast asid :: 9 word) \<longrightarrow>
              x64_asid_table (arch_state s) (asid_high_bits_of asida) =
                Some ap \<longrightarrow>
              x64_asid_map (arch_state s) asida = None\<rbrace>"
  apply (simp add: invalidate_asid_def)
  apply (wp )
  apply clarsimp
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
  apply (drule_tac x="asid_high_bits_of asid" and y="asid_high_bits_of asida" in inj_onD)
     apply simp
    apply blast
   apply blast
  apply clarsimp
  apply (drule asid_low_high_bits', simp)
    apply (fastforce simp: mask_def)
   apply (fastforce simp: mask_def)
  apply (erule (1) notE)
  done

crunch typ_at [wp]: invalidate_asid_entry "\<lambda>s. P (typ_at T p s)"


lemmas invalidate_asid_entry_typ_ats [wp] =
  abs_typ_at_lifts [OF invalidate_asid_entry_typ_at]


crunch cur [wp]: invalidate_asid_entry cur_tcb


crunch valid_objs [wp]: invalidate_asid_entry valid_objs


lemma invalidate_asid_asid_map [wp]:
  "\<lbrace>valid_asid_map\<rbrace> invalidate_asid asid \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: invalidate_asid_def )
  apply (wp )
  apply (clarsimp simp: valid_asid_map_def simp del: fun_upd_apply)
  apply (clarsimp simp: vspace_at_asid_def vs_lookup_arch_update)
  apply auto
  done

crunch asid_map[wp]: invalidate_asid_entry "valid_asid_map"

crunch obj_at [wp]: invalidate_asid_entry "\<lambda>s. P (obj_at Q p s)"

lemma invalidate_asid_invs [wp]:
  "\<lbrace>invs\<rbrace> invalidate_asid asid \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invalidate_asid_def)
  apply (rule hoare_pre, wp )
  apply (clarsimp simp: invs_def valid_state_def valid_irq_node_def
                        valid_arch_caps_def valid_table_caps_def
                        valid_kernel_mappings_def valid_global_objs_def
                        valid_global_refs_def global_refs_def
                        valid_vs_lookup_def
                        vs_lookup_arch_update vs_lookup_pages_arch_update
                        valid_arch_objs_def valid_arch_state_def
                  simp del: fun_upd_apply)
  apply (clarsimp simp: valid_asid_map_def valid_machine_state_def)
  apply (rule conjI)
   apply (erule order_trans[rotated], clarsimp)
  apply (simp add: vspace_at_asid_arch_up')
  done

crunch valid_vs_lookup[wp]: invalidate_asid "valid_vs_lookup"
  (simp: valid_vs_lookup_def)

crunch valid_vs_lookup[wp]: invalidate_asid_entry "valid_vs_lookup"

crunch arm_asid_table_inv[wp]: invalidate_asid_entry
    "\<lambda>s. P (x64_asid_table (arch_state s))"

lemma hwASIDInvalidate_underlying_memory:
  "\<lbrace>\<lambda>m'. underlying_memory m' p = um\<rbrace>
   hwASIDInvalidate a b
   \<lbrace>\<lambda>_ m'. underlying_memory m' p = um\<rbrace>"
  by (clarsimp simp: hwASIDInvalidate_def machine_op_lift_def
                     machine_rest_lift_def split_def | wp)+

(* FIXME x64: move to Machine_AI *)
lemma no_irq_hwASIDInvalidate: "no_irq (hwASIDInvalidate a b)"
  by (clarsimp simp: hwASIDInvalidate_def invalidateASID_def)

lemmas hwASIDInvalidate_irq_masks = no_irq[OF no_irq_hwASIDInvalidate]

crunch device_state_inv[wp]: hwASIDInvalidate "\<lambda>ms. P (device_state ms)"
  (ignore: ignore_failure)

lemma dmo_hwASIDInvalidate_invs[wp]:
  "\<lbrace>invs\<rbrace> do_machine_op (hwASIDInvalidate a b) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule use_valid)
     apply (rule hwASIDInvalidate_underlying_memory)
    apply (fastforce+)
  apply (erule (1) use_valid[OF _ hwASIDInvalidate_irq_masks])
  done

lemma invalidate_asid_entry_invs[wp]: "\<lbrace>invs\<rbrace> invalidate_asid_entry asid vspace \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invalidate_asid_entry_def)
  by wp

lemma mapM_invalidate:
  "\<lbrace>[VSRef (ucast (asid_high_bits_of base)) None] \<rhd> ptr and
    ko_at (ArchObj (arch_kernel_obj.ASIDPool pool)) ptr and
    valid_asid_map and K (is_aligned base asid_low_bits)\<rbrace>
       mapM (\<lambda>offset. when (\<exists>y. pool (ucast offset) = Some y) $
                           invalidate_asid_entry (base + offset) (the (pool (ucast offset))))
        [0.e.2 ^ asid_low_bits - 1]
       \<lbrace>\<lambda>rv s. \<forall>x\<le>2 ^ asid_low_bits - 1. x64_asid_map (arch_state s) (base + x) = None\<rbrace>"
proof -
  have ball: "\<And>P w::machine_word. (\<forall>x\<le>w. P x) = (\<forall>x \<in> set [0.e.w]. P x)" by simp
  show ?thesis
    apply (subst ball)
    apply (rule mapM_set)
      apply (wp, simp)
     apply (wp | simp add: invalidate_asid_entry_def invalidate_asid_def
                     cong: if_cong)+
     apply clarsimp
     apply (rule ccontr)
     apply clarsimp
     apply (clarsimp simp: valid_asid_map_def)
     apply (drule bspec, erule graph_ofI)
     apply (erule vs_lookup_atE)
     apply (clarsimp simp: vspace_at_asid_def)
     apply (drule vs_lookup_2ConsD)
     apply clarsimp
     apply (erule vs_lookup_atE)
     apply (drule vs_lookup1D)
     apply clarsimp
     apply (subgoal_tac "p' = ptr")
      apply (clarsimp simp: obj_at_def vs_refs_def graph_of_def)
      apply (subgoal_tac "base + x && mask asid_low_bits = x")
       apply (simp add: ucast_ucast_mask)
       apply (subgoal_tac "a && mask word_bits = a")
        apply (simp add: word_bits_def)
       apply (rule word_eqI)
       apply (simp add: word_size word_bits_def)
      apply (subst add_mask_eq, assumption+)
       apply (simp add: asid_low_bits_def word_bits_def)
      apply (rule refl)
     apply (subst (asm) asid_high_bits_of_add, assumption+)
     apply simp
    apply (wp invalidate_asid_entry_asid_map_None_inv)
    apply simp
    done
qed

lemma delete_asid_pool_invs[wp]:
  "\<lbrace>invs and K (base \<le> mask asid_bits)\<rbrace>
     delete_asid_pool base pptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: delete_asid_pool_def)
  apply wp
  apply (strengthen invs_x64_asid_table_unmap)
  apply simp
  apply (rule hoare_vcg_conj_lift,
           (rule mapM_invalidate[where ptr=pptr, simplified])?,
           ((wp mapM_wp' | simp add: if_apply_def2)+)[1])+
    apply wp+
  apply (clarsimp simp: is_aligned_mask[symmetric])
  apply (rule conjI)
   apply (rule vs_lookupI)
    apply (erule vs_asid_refsI)
   apply simp
  apply clarsimp
  done

lemma set_asid_pool_typ_at [wp]:
  "\<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> set_asid_pool ptr pool \<lbrace>\<lambda>_ s. P (typ_at T p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def)
  apply wp
  done


lemmas set_asid_pool_typ_ats [wp] = abs_typ_at_lifts [OF set_asid_pool_typ_at]

lemma set_asid_pool_arch_objs_unmap':
  "\<lbrace>valid_arch_objs and (\<lambda>s. (\<exists>\<rhd>p) s \<longrightarrow> valid_arch_obj (ASIDPool ap) s) and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  apply (wpsimp wp: set_object_arch_objs get_object_wp)
  apply (fastforce simp: a_type_def vs_refs_def)
  done


lemma set_asid_pool_arch_objs_unmap:
  "\<lbrace>valid_arch_objs and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S)  \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (wp set_asid_pool_arch_objs_unmap')
  apply (clarsimp simp: obj_at_def graph_of_restrict_map)
  apply (drule valid_arch_objsD, simp add: obj_at_def, assumption)
  apply simp
  by (auto simp: obj_at_def dest!: ran_restrictD)

lemma set_asid_pool_iflive [wp]:
  "\<lbrace>\<lambda>s. if_live_then_nonz_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_live_then_nonz_cap s\<rbrace>"
  apply (simp add: set_asid_pool_def update_object_def)
  apply (wp get_object_wp set_object_iflive)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def a_type_simps)
  done


lemma set_asid_pool_zombies [wp]:
  "\<lbrace>\<lambda>s. zombies_final s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. zombies_final s\<rbrace>"
  apply (simp add: set_asid_pool_def update_object_def)
  apply (wp get_object_wp set_object_zombies)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def a_type_simps)
  done

lemma set_asid_pool_zombies_state_refs [wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (state_refs_of s)\<rbrace>"
  apply (clarsimp simp: set_asid_pool_def set_object_def update_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
  apply (erule rsubst [where P=P])
  apply (rule ext)
  apply (clarsimp simp: obj_at_def state_refs_of_def a_type_simps split: option.splits)
  done

lemma set_asid_pool_cdt [wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. P (cdt s)\<rbrace>"
  unfolding set_asid_pool_def including unfold_objects
  by (wpsimp wp: get_object_wp)

lemma set_asid_pool_caps_of_state [wp]:
  "\<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_ s. P (caps_of_state s)\<rbrace>"
  unfolding set_asid_pool_def set_object_def including unfold_objects
  apply (wpsimp wp: get_object_wp)
  apply (subst cte_wp_caps_of_lift)
   prefer 2
   apply assumption
  subgoal for _ _ y by (cases y, auto simp: cte_wp_at_cases)
  done

lemma set_asid_pool_valid_mdb [wp]:
  "\<lbrace>\<lambda>s. valid_mdb s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_mdb s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_mdb_lift simp: set_asid_pool_def)


lemma set_asid_pool_valid_idle [wp]:
  "\<lbrace>\<lambda>s. valid_idle s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_idle s\<rbrace>"
  including unfold_objects
  by (wpsimp wp: valid_idle_lift simp: set_asid_pool_def)


lemma set_asid_pool_ifunsafe [wp]:
  "\<lbrace>\<lambda>s. if_unsafe_then_cap s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. if_unsafe_then_cap s\<rbrace>"
  including unfold_objects
  by (wpsimp simp: set_asid_pool_def)

lemma set_asid_pool_pred_tcb_at[wp]:
  "\<lbrace>pred_tcb_at proj P t\<rbrace> set_asid_pool ptr val \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wpsimp wp: get_object_wp simp: pred_tcb_at_def obj_at_def)
  done

lemma set_asid_pool_reply_caps [wp]:
  "\<lbrace>\<lambda>s. valid_reply_caps s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_reply_caps s\<rbrace>"
  by (wp valid_reply_caps_st_cte_lift)

lemma set_asid_pool_reply_masters [wp]:
  "\<lbrace>valid_reply_masters\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_reply_masters\<rbrace>"
  by (wp valid_reply_masters_cte_lift)

crunch global_ref [wp]: set_asid_pool "\<lambda>s. P (global_refs s)"
  (wp: crunch_wps)

crunch arch [wp]: set_asid_pool "\<lambda>s. P (arch_state s)"
  (wp: crunch_wps)

crunch idle [wp]: set_asid_pool "\<lambda>s. P (idle_thread s)"
  (wp: crunch_wps)

crunch irq [wp]: set_asid_pool "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

crunch valid_irq_states[wp]: set_asid_pool "valid_irq_states"
  (wp: crunch_wps)

lemma set_asid_pool_valid_global [wp]:
  "\<lbrace>\<lambda>s. valid_global_refs s\<rbrace>
  set_asid_pool p ap
  \<lbrace>\<lambda>_ s. valid_global_refs s\<rbrace>"
  by (wp valid_global_refs_cte_lift)

crunch interrupt_states[wp]: set_asid_pool "\<lambda>s. P (interrupt_states s)"
  (wp: crunch_wps)

lemma set_asid_pool_vs_lookup_unmap':
  "\<lbrace>valid_vs_lookup and
    obj_at (\<lambda>ko. \<exists>ap'. ko = ArchObj (ASIDPool ap') \<and> graph_of ap \<subseteq> graph_of ap') p\<rbrace>
  set_asid_pool p ap \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (simp add: valid_vs_lookup_def pred_conj_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def set_object_def update_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def simp del: fun_upd_apply del: disjCI
                  split: kernel_object.splits arch_kernel_obj.splits)
  subgoal for \<dots> pa ref
    apply (spec pa)
    apply (spec ref)
    apply (erule impE)
     apply (erule vs_lookup_pages_stateI)
      by (clarsimp simp: obj_at_def vs_refs_pages_def split: if_split_asm)
         fastforce+
  done


lemma set_asid_pool_vs_lookup_unmap:
  "\<lbrace>valid_vs_lookup and ko_at (ArchObj (ASIDPool ap)) p\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  apply (wp set_asid_pool_vs_lookup_unmap')
  by (clarsimp simp: obj_at_def
                 elim!: subsetD [OF graph_of_restrict_map])

crunch v_ker_map[wp]: set_asid_pool "valid_kernel_mappings"
  (ignore: set_object wp: set_object_v_ker_map crunch_wps)


lemma set_asid_pool_restrict_asid_map:
  "\<lbrace>valid_asid_map and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid \<notin> S \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
  set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. valid_asid_map\<rbrace>"
  apply (simp add: set_asid_pool_def valid_asid_map_def set_object_def update_object_def)
  apply (wp get_object_wp)
  apply (clarsimp split: kernel_object.splits arch_kernel_obj.splits
                  simp del: fun_upd_apply)
  apply (drule(1) bspec)
  apply (clarsimp simp: vspace_at_asid_def obj_at_def graph_of_def)
  apply (drule subsetD, erule domI)
  apply simp
  apply (drule spec, drule(1) mp)
  apply simp
  apply (erule vs_lookupE)
  apply (rule vs_lookupI, simp)
  apply (clarsimp simp: vs_asid_refs_def graph_of_def)
  apply (drule rtranclD)
  apply (erule disjE, clarsimp)
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (rule r_into_rtrancl)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (subst vs_lookup1_def)
  apply (clarsimp simp: obj_at_def)
  apply (erule rtranclE)
   apply (clarsimp simp: vs_refs_def graph_of_def)
   apply (rule image_eqI[where x="(_, _)"])
    apply (simp add: split_def)
   apply (clarsimp simp: restrict_map_def)
   apply (drule ucast_up_inj, simp)
   apply (simp add: mask_asid_low_bits_ucast_ucast)
  apply clarsimp
  apply (drule vs_lookup1_trans_is_append)
  apply clarsimp
  apply (drule vs_lookup1D)
  by clarsimp

lemma set_asid_pool_cur [wp]:
  "\<lbrace>\<lambda>s. P (cur_thread s)\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. P (cur_thread s)\<rbrace>"
  unfolding set_asid_pool_def by (wpsimp wp: get_object_wp)


lemma set_asid_pool_cur_tcb [wp]:
  "\<lbrace>\<lambda>s. cur_tcb s\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_ s. cur_tcb s\<rbrace>"
  unfolding cur_tcb_def
  by (rule hoare_lift_Pf [where f=cur_thread]; wp)


crunch arch [wp]: set_asid_pool "\<lambda>s. P (arch_state s)"
  (wp: get_object_wp)


lemma set_asid_pool_valid_arch [wp]:
  "\<lbrace>valid_arch_state\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (rule valid_arch_state_lift) (wp set_asid_pool_typ_at)+


lemma set_asid_pool_valid_objs [wp]:
  "\<lbrace>valid_objs\<rbrace> set_asid_pool p a \<lbrace>\<lambda>_. valid_objs\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_objs get_object_wp)
  including unfold_objects
  by (clarsimp simp: a_type_def valid_obj_def wellformed_arch_obj_def)

lemma set_asid_pool_global_objs [wp]:
  "\<lbrace>valid_global_objs and valid_arch_state\<rbrace>
   set_asid_pool p ap
   \<lbrace>\<lambda>_. valid_global_objs\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def update_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: valid_global_objs_def valid_ao_at_def simp del: fun_upd_apply)
  apply (rule conjI)
   apply (clarsimp simp: obj_at_def)
   apply (rule conjI)
    subgoal by (clarsimp simp: valid_arch_state_def obj_at_def a_type_def)
   apply clarsimp
   apply (erule (1) valid_arch_obj_same_type[simplified])
   subgoal by (simp add: a_type_def)
  apply (rule conjI)
   subgoal by (clarsimp simp: obj_at_def valid_arch_state_def a_type_def)
  apply (clarsimp simp: obj_at_def)
  by ((rule conjI)?, clarsimp, drule (1) bspec, clarsimp simp: aa_type_simps a_type_simps)+

lemma set_asid_pool_aligned [wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_aligned\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_aligned|wpc)+
  done

lemma set_asid_pool_distinct [wp]:
  "\<lbrace>pspace_distinct\<rbrace> set_asid_pool p ptr \<lbrace>\<lambda>_. pspace_distinct\<rbrace>"
  apply (simp add: set_asid_pool_def get_object_def)
  apply (wp set_object_distinct|wpc)+
  done

lemma set_asid_pool_only_idle [wp]:
  "\<lbrace>only_idle\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. only_idle\<rbrace>"
  by (wp only_idle_lift set_asid_pool_typ_at)


lemma set_asid_pool_equal_mappings [wp]:
  "\<lbrace>equal_kernel_mappings\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. equal_kernel_mappings\<rbrace>"
  by (simp add: set_asid_pool_def update_object_def | wp set_object_equal_mappings get_object_wp)+

lemma set_asid_pool_valid_global_vspace_mappings[wp]:
  "\<lbrace>valid_global_vspace_mappings\<rbrace>
      set_asid_pool p ap \<lbrace>\<lambda>rv. valid_global_vspace_mappings\<rbrace>"
  apply (simp add: set_asid_pool_def update_object_def)
  apply (wp set_object_global_vspace_mappings get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  done

lemma set_asid_pool_kernel_window[wp]:
  "\<lbrace>pspace_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_pspace_in_kernel_window get_object_wp)
  done

lemma set_asid_pool_pspace_respects_device_region[wp]:
  "\<lbrace>pspace_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. pspace_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_pspace_respect_device_region get_object_wp)
  done

lemma set_asid_pool_caps_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_in_kernel_window get_object_wp)
  done

lemma set_asid_pool_caps_respects_device_region[wp]:
  "\<lbrace>cap_refs_respects_device_region\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>rv. cap_refs_respects_device_region\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_cap_refs_respects_device_region get_object_wp)
  done

lemma set_asid_pool_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (simp add: set_asid_pool_def)
  apply (wp set_object_valid_ioc_no_caps get_object_inv)
  done

lemma set_asid_pool_vms[wp]:
  "\<lbrace>valid_machine_state\<rbrace> set_asid_pool p S \<lbrace>\<lambda>_. valid_machine_state\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def update_object_def)
  apply (wp get_object_wp)
  apply clarify
  apply (erule valid_machine_state_heap_updI)
  apply (fastforce simp: a_type_def obj_at_def
                  split: kernel_object.splits arch_kernel_obj.splits)+
  done

lemma set_asid_pool_table_caps [wp]:
  "\<lbrace>valid_table_caps\<rbrace> set_asid_pool p ap \<lbrace>\<lambda>_. valid_table_caps\<rbrace>"
  apply (simp add: valid_table_caps_def)
  apply (rule hoare_lift_Pf2 [where f=caps_of_state];wp?)
  apply (simp add: set_asid_pool_def set_object_def update_object_def)
  apply (wp get_object_wp)
  by (clarsimp split: kernel_object.splits arch_kernel_obj.splits)
     (fastforce simp: obj_at_def empty_table_def a_type_simps)

lemma set_asid_pool_invs_restrict:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid \<notin> S \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap |` S) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def
                   valid_arch_caps_def del: set_asid_pool_def set_arch_obj_simps(5))
  apply_trace (rule hoare_pre,
         wp add: valid_irq_node_typ set_asid_pool_typ_at
            set_asid_pool_arch_objs_unmap  valid_irq_handlers_lift
            set_asid_pool_vs_lookup_unmap set_asid_pool_restrict_asid_map
       | simp del: set_arch_obj_simps(5))+
  done

lemma set_asid_pool_invs_unmap:
  "\<lbrace>invs and ko_at (ArchObj (ASIDPool ap)) p and
    (\<lambda>s. \<forall>asid. asid \<le> mask asid_bits \<longrightarrow> ucast asid = x \<longrightarrow>
                x64_asid_table (arch_state s) (asid_high_bits_of asid) = Some p \<longrightarrow>
                x64_asid_map (arch_state s) asid = None)\<rbrace>
       set_asid_pool p (ap(x := None)) \<lbrace>\<lambda>_. invs\<rbrace>"
  using set_asid_pool_invs_restrict[where S="- {x}"]
  by (simp add: restrict_map_def fun_upd_def if_flip)

lemma delete_asid_invs[wp]:
  "\<lbrace>invs and K (asid \<le> mask asid_bits)\<rbrace>
     delete_asid asid pd
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: delete_asid_def cong: option.case_cong del: set_arch_obj_simps(5))
  apply_trace (wp set_asid_pool_invs_unmap hoare_vcg_all_lift | wpc)+
     apply (simp add: invalidate_asid_entry_def)
     apply (wp invalidate_asid_invalidates gets_wp hoare_vcg_const_imp_lift hoare_vcg_all_lift hoare_vcg_imp_lift invalidate_asid_asid_map_None_inv)
   apply (rule gets_wp) (*FIXME x64: wtf *)
  apply (clarsimp simp del: fun_upd_apply simp: invs_valid_asid_map)
  done

crunch vs_lookup[wp]: set_vm_root "\<lambda>s. P (vs_lookup s)"
  (wp: crunch_wps simp: crunch_simps vs_lookup_arch_update)

lemma delete_asid_pool_unmapped[wp]:
  "\<lbrace>\<top>\<rbrace>
     delete_asid_pool asid poolptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (ucast (asid_high_bits_of asid)) None] \<rhd> poolptr) s\<rbrace>"
  apply (simp add: delete_asid_pool_def)
  apply wp
    apply (rule hoare_strengthen_post [where Q="\<lambda>_. \<top>"])
     apply wp+
    defer
    apply wp+
   apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                  dest!: graph_ofD)
   apply (erule rtranclE)
    apply (simp add: up_ucast_inj_eq)
   apply (drule vs_lookup1D)
   apply clarsimp
   apply (clarsimp simp: vs_refs_def
                  split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits
                  dest!: graph_ofD)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD
                 split: if_split_asm)
  apply (erule rtranclE)
   apply (simp add: up_ucast_inj_eq)
  apply (drule vs_lookup1D)
  apply clarsimp
  apply (clarsimp simp: vs_refs_def
                 split: Structures_A.kernel_object.split_asm arch_kernel_obj.splits
                 dest!: graph_ofD)
 done

lemma set_asid_pool_unmap:
  "\<lbrace>[VSRef highbits None] \<rhd> poolptr\<rbrace>
     set_asid_pool poolptr (pool(lowbits := None))
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (ucast lowbits) (Some AASIDPool),
                   VSRef highbits None] \<rhd> x) s\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def update_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations)
  apply (clarsimp simp: vs_lookup1_def obj_at_def up_ucast_inj_eq)
  apply (fastforce simp: vs_refs_def up_ucast_inj_eq
                 dest!: graph_ofD)
  done

lemma delete_asid_unmapped[wp]:
  "\<lbrace>\<top>\<rbrace>
      delete_asid asid pd
   \<lbrace>\<lambda>rv s.  \<not> ([VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                VSRef (ucast (asid_high_bits_of asid)) None]  \<rhd> pd) s\<rbrace>"
  apply (simp add: delete_asid_def
                   mask_asid_low_bits_ucast_ucast
              del: set_arch_obj_simps(5)
             cong: option.case_cong)
  apply (wp set_asid_pool_unmap hoare_vcg_all_lift hoare_vcg_imp_lift invalidate_asid_entry_vs_lookup
           | wpc
           | simp add: if_apply_def2 del: set_arch_obj_simps(5) split del: if_splits)+
  apply (intro allI conjI impI)
    apply (fastforce simp: vs_lookup_def vs_asid_refs_def up_ucast_inj_eq
                   dest!: graph_ofD vs_lookup1_rtrancl_iterations
                          vs_lookup1D)
   apply (erule vs_lookup_atI)
  apply (clarsimp simp: vs_lookup_def vs_asid_refs_def up_ucast_inj_eq
                 dest!: graph_ofD vs_lookup1_rtrancl_iterations
                        vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def up_ucast_inj_eq
                 dest!: graph_ofD)
  done

lemma set_pt_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pt a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def update_object_def get_object_def
                     set_object_def in_monad a_type_simps)

lemma set_pd_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pd a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def update_object_def get_object_def
                     set_object_def in_monad a_type_simps)

lemma set_pdpt_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pdpt a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def update_object_def get_object_def
                     set_object_def in_monad a_type_simps)

lemma set_pml4_tcb_at_arch[simplified, wp]:
  "\<lbrace>\<lambda>s. P (ko_at (TCB tcb) t s)\<rbrace> set_pml4 a b \<lbrace>\<lambda>_ s. P (ko_at (TCB tcb) t s)\<rbrace>"
  by (clarsimp simp: valid_def obj_at_def update_object_def get_object_def
                     set_object_def in_monad a_type_simps)

crunch tcb_at_arch: unmap_page "\<lambda>s. P (ko_at (TCB tcb) t s)"
    (simp: crunch_simps wp: crunch_wps ignore: set_object)

lemmas unmap_page_tcb_at = unmap_page_tcb_at_arch

lemma unmap_page_tcb_cap_valid:
  "\<lbrace>\<lambda>s. tcb_cap_valid cap r s\<rbrace>
    unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. tcb_cap_valid cap r s\<rbrace>"
  apply (rule tcb_cap_valid_typ_st)
    apply wp
   apply (simp add: pred_tcb_at_def2)
  apply (wp unmap_page_tcb_at hoare_vcg_ex_lift hoare_vcg_all_lift)+
  done

global_naming Arch

lemma (* replaceable_cdt_update *)[simp,Finalise_AI_asms]:
  "replaceable (cdt_update f s) = replaceable s"
  by (fastforce simp: replaceable_def tcb_cap_valid_def)

lemma (* replaceable_revokable_update *)[simp,Finalise_AI_asms]:
  "replaceable (is_original_cap_update f s) = replaceable s"
  by (fastforce simp: replaceable_def is_final_cap'_def2 tcb_cap_valid_def)

lemma (* replaceable_more_update *) [simp,Finalise_AI_asms]:
  "replaceable (trans_state f s) sl cap cap' = replaceable s sl cap cap'"
  by (simp add: replaceable_def)

lemma (* obj_ref_ofI *) [Finalise_AI_asms]: "obj_refs cap = {x} \<Longrightarrow> obj_ref_of cap = x"
  by (case_tac cap, simp_all) (rename_tac arch_cap, case_tac arch_cap, simp_all)

lemma (* empty_slot_invs *) [Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. invs s \<and> cte_wp_at (replaceable s sl cap.NullCap) sl s \<and>
        emptyable sl s \<and>
        (\<forall>irq. irqopt = Some irq \<longrightarrow>
            cap.IRQHandlerCap irq \<notin>
            ran ((caps_of_state s) (sl \<mapsto> cap.NullCap)))\<rbrace>
     empty_slot sl irqopt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: empty_slot_def set_cdt_def bind_assoc cong: if_cong)
  apply (wp opt_deleted_irq_handler_invs)
        apply (simp add: invs_def valid_state_def valid_mdb_def2)
        apply (wp replace_cap_valid_pspace set_cap_caps_of_state2
                  replace_cap_ifunsafe get_cap_wp
                  set_cap_idle valid_irq_node_typ set_cap_typ_at
                  set_cap_irq_handlers set_cap_valid_arch_caps
                  set_cap_cap_refs_respects_device_region_NullCap
      | simp add: trans_state_update[symmetric]
             del: trans_state_update fun_upd_apply
       split del: if_split )+
  apply (clarsimp simp: is_final_cap'_def2 simp del: fun_upd_apply)
  apply (clarsimp simp: conj_comms invs_def valid_state_def valid_mdb_def2)
  apply (subgoal_tac "mdb_empty_abs s")
   prefer 2
   apply (rule mdb_empty_abs.intro)
   apply (rule vmdb_abs.intro)
   apply (simp add: valid_mdb_def swp_def cte_wp_at_caps_of_state conj_comms)
  apply (clarsimp simp: untyped_mdb_def mdb_empty_abs.descendants mdb_empty_abs.no_mloop_n
                        valid_pspace_def cap_range_def)
  apply (clarsimp simp: untyped_inc_def mdb_empty_abs.descendants mdb_empty_abs.no_mloop_n)
  apply (simp add: ut_revocable_def cur_tcb_def valid_irq_node_def
                   no_cap_to_obj_with_diff_ref_Null)
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_cte_at)
  apply (rule conjI)
   apply (clarsimp simp: irq_revocable_def)
  apply (rule conjI)
   apply (clarsimp simp: reply_master_revocable_def)
  apply (thin_tac "\<forall>irq. irqopt = Some irq \<longrightarrow> P irq" for P)
  apply (rule conjI)
   apply (clarsimp simp: valid_machine_state_def)
  apply (rule conjI)
   apply (clarsimp simp:descendants_inc_def mdb_empty_abs.descendants)
  apply (rule conjI)
   apply (clarsimp simp: reply_mdb_def)
   apply (rule conjI)
    apply (unfold reply_caps_mdb_def)[1]
    apply (rule allEI, assumption)
    apply (fold reply_caps_mdb_def)[1]
    apply (case_tac "sl = ptr", simp)
    apply (simp add: fun_upd_def split del: if_split del: split_paired_Ex)
    apply (erule allEI, rule impI, erule(1) impE)
    apply (erule exEI)
    apply (simp, rule ccontr)
    apply (erule(5) emptyable_no_reply_cap)
    apply simp
   apply (unfold reply_masters_mdb_def)[1]
   apply (elim allEI)
   apply (clarsimp simp: mdb_empty_abs.descendants)
  apply (rule conjI)
   apply (simp add: valid_ioc_def)
  apply (rule conjI)
   apply (clarsimp simp: tcb_cap_valid_def
                  dest!: emptyable_valid_NullCapD)
  apply (rule conjI)
   apply (clarsimp simp: mdb_cte_at_def cte_wp_at_caps_of_state)
   apply (cases sl)
   apply (rule conjI, clarsimp)
    apply (subgoal_tac "cdt s \<Turnstile> (ab,bb) \<rightarrow> (ab,bb)")
     apply (simp add: no_mloop_def)
    apply (rule r_into_trancl)
    apply (simp add: cdt_parent_of_def)
   apply fastforce
  apply (clarsimp simp: cte_wp_at_caps_of_state replaceable_def
                        vs_cap_ref_simps table_cap_ref_simps
                   del: allI)
  apply (case_tac "is_final_cap' cap s")
   apply auto[1]
  apply (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state)
  done

lemma dom_tcb_cap_cases_lt_ARCH [Finalise_AI_asms]:
  "dom tcb_cap_cases = {xs. length xs = 3 \<and> unat (of_bl xs :: machine_word) < 5}"
  apply (rule set_eqI, rule iffI)
   apply clarsimp
   apply (simp add: tcb_cap_cases_def tcb_cnode_index_def to_bl_1 split: if_split_asm)
  apply clarsimp
  apply (frule tcb_cap_cases_lt)
  apply (clarsimp simp: nat_to_cref_unat_of_bl'[simplified word_bits_def])
  done

lemma (* unbind_notification_final *) [wp,Finalise_AI_asms]:
  "\<lbrace>is_final_cap' cap\<rbrace> unbind_notification t \<lbrace> \<lambda>rv. is_final_cap' cap\<rbrace>"
  unfolding unbind_notification_def
  apply (wp final_cap_lift thread_set_caps_of_state_trivial hoare_drop_imps
       | wpc | simp add: tcb_cap_cases_def)+
  done

lemma deleting_irq_handler_final [Finalise_AI_asms]:
  "\<lbrace>is_final_cap' cap and cte_wp_at (op = cap) slot
          and K (\<not> can_fast_finalise cap)\<rbrace>
      deleting_irq_handler irq
   \<lbrace>\<lambda>rv. is_final_cap' cap\<rbrace>"
  apply  (rule hoare_gen_asm)
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_final_cap[where slot=slot])
  apply simp
  done

lemma (* finalise_cap_cases1 *)[Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. final \<longrightarrow> is_final_cap' cap s
         \<and> cte_wp_at (op = cap) slot s\<rbrace>
     finalise_cap cap final
   \<lbrace>\<lambda>rv s. fst rv = cap.NullCap
         \<and> snd rv = (if final then cap_irq_opt cap else None)
         \<and> (snd rv \<noteq> None \<longrightarrow> is_final_cap' cap s)
     \<or>
       is_zombie (fst rv) \<and> is_final_cap' cap s
        \<and> snd rv = None
        \<and> appropriate_cte_cap (fst rv) = appropriate_cte_cap cap
        \<and> cte_refs (fst rv) = cte_refs cap
        \<and> obj_refs (fst rv) = obj_refs cap
        \<and> obj_size (fst rv) = obj_size cap
        \<and> cap_irqs (fst rv) = cap_irqs cap
        \<and> fst_cte_ptrs (fst rv) = fst_cte_ptrs cap
        \<and> vs_cap_ref cap = None\<rbrace>"
  apply (cases cap, simp_all split del: if_split cong: if_cong)
            apply ((wp suspend_final_cap[where sl=slot]
                      deleting_irq_handler_final[where slot=slot]
                      | simp add: o_def is_cap_simps fst_cte_ptrs_def
                                  dom_tcb_cap_cases_lt_ARCH tcb_cnode_index_def
                                  can_fast_finalise_def
                                  appropriate_cte_cap_def
                                  vs_cap_ref_def unat_of_bl_length
                      | intro impI TrueI ext conjI
                      | (match conclusion in "{x} \<times> _ = {x} \<times> _" for x
                                     \<Rightarrow> \<open>fastforce simp: unat_of_bl_length\<close>))+)
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp only: simp_thms)+
  done

crunch typ_at_arch[wp,Finalise_AI_asms]: arch_finalise_cap "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps unless_def assertE_def
        ignore: maskInterrupt )

lemma (* finalise_cap_new_valid_cap *)[wp,Finalise_AI_asms]:
  "\<lbrace>valid_cap cap\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. valid_cap (fst rv)\<rbrace>"
  apply (cases cap, simp_all)
            apply (wp suspend_valid_cap
                     | simp add: o_def valid_cap_def cap_aligned_def
                                 valid_cap_Null_ext
                           split del: if_split
                     | clarsimp | rule conjI)+
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
  apply (wp|simp add: o_def valid_cap_def cap_aligned_def
                 split del: if_split|clarsimp|wpc)+
  done

lemma (* arch_finalise_cap_invs *)[wp,Finalise_AI_asms]:
  "\<lbrace>invs and valid_cap (ArchObjectCap cap)\<rbrace>
     arch_finalise_cap cap final
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (wp unmap_page_invs | wpc)+
  apply (clarsimp simp: valid_cap_def cap_aligned_def)
  apply (auto simp: mask_def vmsz_aligned_def wellformed_mapdata_def)
  done


lemma unmap_page_vs_lookup_pages_large:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_arch_state and data_at X64LargePage pg and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_page X64LargePage asid vaddr pg
           \<lbrace>\<lambda>rv s. ([VSRef ((vaddr >> 21) && mask 9) (Some APageDirectory), VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4), VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None],
                    pg) \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_page_vs_lookup_pages_pre[where sz=X64LargePage, simplified]])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma unmap_page_vs_lookup_pages_huge:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_arch_state and data_at X64HugePage pg and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
     unmap_page X64HugePage asid vaddr pg
           \<lbrace>\<lambda>rv s. ([VSRef ((vaddr >> 30) && mask 9) (Some APDPointerTable),
                     VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4), VSRef (asid && mask asid_low_bits) (Some AASIDPool),
                     VSRef (ucast (asid_high_bits_of asid)) None],
                    pg) \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_page_vs_lookup_pages_pre[where sz=X64HugePage, simplified]])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma lookup_refs_pml4_shrink_strg:
  "ko_at (ArchObj (PageMapL4 pm)) ptr s \<longrightarrow>
    lookup_refs (Some (ArchObj (PageMapL4 (pm(slot := InvalidPML4E))))) vs_lookup_pages1_on_heap_obj
      \<subseteq> lookup_refs (kheap s ptr) vs_lookup_pages1_on_heap_obj"
  by (fastforce simp: obj_at_def lookup_refs_def vs_lookup_pages1_on_heap_obj_def
                        vs_refs_pages_def graph_of_def pml4e_ref_pages_def image_def
                 split: if_splits)

lemma vs_refs_pages_pml4:
  "\<lbrakk>pml4e_ref_pages (pml4a a) = Some pdpt; a \<notin> kernel_mapping_slots\<rbrakk> \<Longrightarrow> (VSRef (ucast a) (Some APageMapL4),pdpt) \<in> vs_refs_pages (ArchObj (PageMapL4 pml4a))"
  by (clarsimp simp: vs_refs_pages_def image_def graph_of_def)

lemma lookup_pml4_slot_mask:
  "is_aligned a table_size \<Longrightarrow> lookup_pml4_slot a b && mask pml4_bits = (get_pml4_index b << word_size_bits)"
  apply (simp add: lookup_pml4_slot_def is_aligned_mask bit_simps)
  apply (simp add: mask_inner_mask[symmetric])
  apply (simp add: get_pml4_index_def bit_simps mask_def)
  apply (word_bitwise)
  done

lemma unmap_pdpt_vs_lookup_pages_pre:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_arch_state and typ_at (AArch APDPointerTable) pdpt
     and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
   unmap_pdpt asid vaddr pdpt
   \<lbrace>\<lambda>r s. (the (vs_cap_ref (ArchObjectCap (PDPointerTableCap pdpt (Some (asid,vaddr))))),pdpt) \<notin> vs_lookup_pages s\<rbrace>"
  proof -
  note ref_simps[simp] = vs_cap_ref_simps vs_ref_pages_simps
  note ucast_simps[simp] = up_ucast_inj_eq ucast_up_ucast mask_asid_low_bits_ucast_ucast ucast_ucast_id
  show ?thesis
  apply (clarsimp simp: unmap_pdpt_def vs_cap_ref_simps store_pml4e_def)
  apply wp
        apply (rule update_aobj_not_reachable[where b = "[b,c]" for b c,simplified])
  apply (strengthen lookup_refs_pml4_shrink_strg valid_arch_state_asid_table_strg not_in_vs_refs_pages_strg
         | clarsimp )+
        apply (strengthen | wp hoare_vcg_imp_lift hoare_vcg_all_lift  | clarsimp simp: conj_ac)+
      apply_trace (wpc | wp)+
apply (wp get_pml4e_wp)
   apply (simp add: find_vspace_for_asid_def | wp | wpc)+
     apply (wpc | wp get_pdpte_wp get_pml4e_wp assertE_wp | clarsimp simp: lookup_pml4_slot_def find_vspace_for_asid_def)
  apply clarsimp
  apply (case_tac "([VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
                             VSRef (ucast (ucast asid :: 9 word)) (Some AASIDPool), VSRef (ucast (asid_high_bits_of asid)) None],
                            pdpt)
                           \<notin> vs_lookup_pages s")
   apply (clarsimp simp: graph_of_def split: if_splits)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (extract_vs_lookup | rewrite_lookup_when_aligned)
   apply (clarsimp simp: get_pml4_index_def bit_simps vs_lookup_pages_vs_lookupI lookup_pml4_slot_def obj_at_def
                 split: if_splits)
   apply (drule_tac a2=a in vs_lookup_pages_step[OF vs_lookup_pages_vs_lookupI vs_lookup_pages1I[OF _ vs_refs_pages_pml4 ]])
      apply (simp add: obj_at_def)
     apply (simp add: pml4e_ref_pages_def)
    apply assumption
   apply simp
  apply (clarsimp split:if_splits simp: vs_lookup_pages_def graph_of_def dest!: in_vs_asid_refsD)
  apply (erule wellformed_lookup.lookupE[OF vs_lookup_pages1_is_wellformed_lookup], simp)
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD simp: lookup_leaf_def)
  apply (erule wellformed_lookup.lookup_forwardE[OF vs_lookup_pages1_is_wellformed_lookup], (simp+)[2])
  apply (clarsimp dest!: vs_lookup_pages1D graph_ofD
                         wellformed_lookup.lookup_rtrancl_stepD[OF vs_lookup_pages1_is_wellformed_lookup]
                   simp: obj_at_def)
  apply (fold ko_at_def2 get_pml4_index_bit_def get_pdpt_index_bit_def)
  apply (extract_vs_lookup)+
  apply (rewrite_lookup_when_aligned)
  apply (clarsimp simp: obj_at_def pml4e_ref_pages_def dest!: graph_ofD split: if_splits pml4e.split_asm)
  apply (fold ko_at_def2 vs_asid_refs_def)
  apply (drule eq_ucast_ucast_eq[rotated], simp)
  apply clarsimp
  apply (frule vs_lookup_pages_vs_lookupI)
  apply (clarsimp simp: obj_at_def pdpte_ref_pages_def image_def vs_lookup_pages_def lookup_pml4_slot_mask triple_shift_fun
                 dest!: graph_ofD split: if_splits pdpte.split_asm)
  done
qed

lemma unmap_pdpt_vs_lookup_pages:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_arch_state and typ_at (AArch APDPointerTable) pd and K(vaddr < pptr_base \<and> canonical_address vaddr)\<rbrace>
    unmap_pdpt asid vaddr pd
  \<lbrace>\<lambda>r s. ([VSRef ((vaddr >> 39) && mask 9) (Some APageMapL4),
                       VSRef (asid && mask asid_low_bits) (Some AASIDPool), VSRef (ucast (asid_high_bits_of asid)) None],
        pd)
       \<notin> vs_lookup_pages s\<rbrace>"
  apply (rule hoare_pre)
  apply (rule hoare_post_imp[OF _ unmap_pdpt_vs_lookup_pages_pre])
   apply (simp add: vs_cap_ref_def)
  apply simp
  done

lemma arch_finalise_cap_replaceable[wp]:
  notes strg = tcb_cap_valid_imp_NullCap
               obj_at_not_live_valid_arch_cap_strg[where cap=cap]
  notes simps = replaceable_def and_not_not_or_imp
                vs_lookup_pages_eq_at[THEN fun_cong, symmetric]
                vs_lookup_pages_eq_ap[THEN fun_cong, symmetric]
                is_cap_simps vs_cap_ref_def
                no_cap_to_obj_with_diff_ref_Null o_def
  notes wps = hoare_drop_imp[where R="%_. is_final_cap' cap" for cap]
               valid_cap_typ unmap_page_vs_lookup_pages_small
               unmap_page_vs_lookup_pages_large unmap_page_vs_lookup_pages_huge
  shows
    "\<lbrace>\<lambda>s. s \<turnstile> cap.ArchObjectCap cap \<and>
          x = is_final_cap' (cap.ArchObjectCap cap) s \<and>
          pspace_aligned s \<and> valid_arch_objs s \<and> valid_objs s \<and>
          valid_arch_state s\<rbrace>
     arch_finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl rv (cap.ArchObjectCap cap)\<rbrace>"
  apply (simp add: arch_finalise_cap_def)
  apply (rule hoare_pre)
   apply (simp add: simps split: option.splits vmpage_size.splits)
   apply (wp wps
          | strengthen strg
          | simp add: simps reachable_pg_cap_def
          | wpc)+
     (* unmap_page case is a bit unpleasant *)
     apply (strengthen cases_conj_strg[where P="\<not> is_final_cap' cap s" for cap s, simplified])
     apply (rule hoare_post_imp, clarsimp split: vmpage_size.split, assumption)
     apply simp
     apply ((wp hoare_vcg_disj_lift hoare_vcg_all_lift hoare_vcg_const_imp_lift
               unmap_page_tcb_cap_valid)[1],
             (wp wps unmap_pt_vs_lookup_pages
              unmap_pd_vs_lookup_pages unmap_pdpt_vs_lookup_pages
           | strengthen strg imp_and_strg tcb_cap_valid_imp_NullCap
           | simp add: simps is_master_reply_cap_def reachable_pg_cap_def
           | wpc)+)+ (* long *)
  apply (auto simp: obj_at_def data_at_def wellformed_mapdata_def valid_cap_def
             split: cap.splits arch_cap.splits option.splits vmpage_size.splits)
  done

global_naming Arch
lemma (* deleting_irq_handler_slot_not_irq_node *)[Finalise_AI_asms]:
  "\<lbrace>if_unsafe_then_cap and valid_global_refs
           and cte_wp_at (\<lambda>cp. cap_irqs cp \<noteq> {}) sl\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv s. (interrupt_irq_node s irq, []) \<noteq> sl\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply wp
  apply clarsimp
  apply (drule(1) if_unsafe_then_capD)
   apply clarsimp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (drule cte_refs_obj_refs_elem)
  apply (erule disjE)
   apply simp
   apply (drule(1) valid_global_refsD[OF _ caps_of_state_cteD])
    prefer 2
    apply (erule notE, simp add: cap_range_def, erule disjI2)
   apply (simp add: global_refs_def)
  apply (clarsimp simp: appropriate_cte_cap_def split: cap.split_asm)
  done

lemma no_cap_to_obj_with_diff_ref_finalI_ARCH[Finalise_AI_asms]:
  "\<lbrakk> cte_wp_at (op = cap) p s; is_final_cap' cap s;
            obj_refs cap' = obj_refs cap \<rbrakk>
      \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (case_tac "obj_refs cap = {}")
   apply (case_tac "cap_irqs cap = {}")
    apply (simp add: is_final_cap'_def)
   apply (case_tac cap, simp_all)
   apply (clarsimp simp add: no_cap_to_obj_with_diff_ref_def
                             cte_wp_at_caps_of_state
                             vs_cap_ref_def
                      dest!: obj_ref_none_no_asid[rule_format])
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        is_final_cap'_def2
              simp del: split_paired_All)
  apply (frule_tac x=p in spec)
  apply (drule_tac x="(a, b)" in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state
                        obj_irq_refs_Int)
  done

lemma (* suspend_no_cap_to_obj_ref *)[wp,Finalise_AI_asms]:
  "\<lbrace>no_cap_to_obj_with_diff_ref cap S\<rbrace>
     suspend t
   \<lbrace>\<lambda>rv. no_cap_to_obj_with_diff_ref cap S\<rbrace>"
  apply (simp add: no_cap_to_obj_with_diff_ref_def
                   cte_wp_at_caps_of_state)
  apply (wp suspend_caps_of_state)
  apply (clarsimp simp: table_cap_ref_simps
                 dest!: obj_ref_none_no_asid[rule_format])
  done

lemma (* finalise_cap_replaceable *) [Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s \<and> valid_mdb s
        \<and> cte_wp_at (op = cap) sl s \<and> valid_objs s \<and> sym_refs (state_refs_of s)
        \<and> (cap_irqs cap \<noteq> {} \<longrightarrow> if_unsafe_then_cap s \<and> valid_global_refs s)
        \<and> (is_arch_cap cap \<longrightarrow> pspace_aligned s \<and>
                               valid_arch_objs s \<and>
                               valid_arch_state s)\<rbrace>
     finalise_cap cap x
   \<lbrace>\<lambda>rv s. replaceable s sl (fst rv) cap\<rbrace>"
  apply (cases cap, simp_all add: replaceable_def reachable_pg_cap_def
                       split del: if_split)
            prefer 10
            (* TS: this seems to be necessary for deleting_irq_handler,
                   kind of nasty, not sure how to sidestep *)
            apply ((wp suspend_unlive[unfolded o_def]
                      suspend_final_cap[where sl=sl]
                      unbind_maybe_notification_not_bound
                      get_ntfn_ko
                      unbind_notification_valid_objs
                   | clarsimp simp: o_def dom_tcb_cap_cases_lt_ARCH
                                     ran_tcb_cap_cases is_cap_simps
                                     cap_range_def
                                     can_fast_finalise_def
                                     obj_irq_refs_subset
                                     vs_cap_ref_def unat_of_bl_length
                                     valid_ipc_buffer_cap_def
                              dest!: tcb_cap_valid_NullCapD
                              split: Structures_A.thread_state.split_asm
                   | simp cong: conj_cong
                   | simp cong: rev_conj_cong add: no_cap_to_obj_with_diff_ref_Null
                   | (strengthen tcb_cap_valid_imp_NullCap tcb_cap_valid_imp', wp)
                   | rule conjI
                   | erule cte_wp_at_weakenE tcb_cap_valid_imp'[rule_format, rotated -1]
                   | erule(1) no_cap_to_obj_with_diff_ref_finalI_ARCH
                   | (wp_once hoare_drop_imps,
                       wp_once cancel_all_ipc_unlive[unfolded o_def]
                           cancel_all_signals_unlive[unfolded o_def])
                   | ((wp_once hoare_drop_imps)?,
                      (wp_once hoare_drop_imps)?,
                      wp_once deleting_irq_handler_empty)
                   | wpc
                   | simp add: valid_cap_simps)+)
   apply (rule hoare_chain)
     apply (rule arch_finalise_cap_replaceable[where sl=sl])
    apply assumption
   apply (clarsimp simp: replaceable_def reachable_pg_cap_def
                         o_def cap_range_def
                         ran_tcb_cap_cases is_cap_simps
                         obj_irq_refs_subset vs_cap_ref_def)+
   apply (fastforce split: option.splits vmpage_size.splits)
  apply (simp add: is_arch_cap_def)
  done

lemma (* deleting_irq_handler_cte_preserved *)[Finalise_AI_asms]:
  assumes x: "\<And>cap. P cap \<Longrightarrow> \<not> can_fast_finalise cap"
  shows "\<lbrace>cte_wp_at P p\<rbrace> deleting_irq_handler irq \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_cte_wp_at_preserved | simp add: x)+
  done

lemma set_asid_pool_cte_wp_at:
  "\<lbrace>\<lambda>s. P (cte_wp_at P' p s)\<rbrace>
     set_asid_pool ptr val
   \<lbrace>\<lambda>rv s. P (cte_wp_at P' p s)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def get_object_def update_object_def)
  apply wp
  including unfold_objects_asm
  by (clarsimp elim!: rsubst[where P=P]
             simp: cte_wp_at_after_update a_type_simps)


crunch cte_wp_at[wp,Finalise_AI_asms]: arch_finalise_cap "\<lambda>s. P (cte_wp_at P' p s)"
  (simp: crunch_simps assertE_def
     wp: update_aobj_cte_wp_at crunch_wps set_object_cte_at
   ignore: update_object set_pt set_pd set_pdpt)

end

interpretation Finalise_AI_1?: Finalise_AI_1
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming X64

lemma fast_finalise_replaceable[wp]:
  "\<lbrace>\<lambda>s. s \<turnstile> cap \<and> x = is_final_cap' cap s
     \<and> cte_wp_at (op = cap) sl s \<and> valid_asid_table (x64_asid_table (arch_state s)) s
     \<and> valid_mdb s \<and> valid_objs s \<and> sym_refs (state_refs_of s)\<rbrace>
     fast_finalise cap x
   \<lbrace>\<lambda>rv s. cte_wp_at (replaceable s sl cap.NullCap) sl s\<rbrace>"
  apply (cases "cap_irqs cap = {}")
   apply (simp add: fast_finalise_def2)
   apply wp
    apply (rule hoare_strengthen_post)
     apply (rule hoare_vcg_conj_lift)
      apply (rule finalise_cap_replaceable[where sl=sl])
     apply (rule finalise_cap_equal_cap[where sl=sl])
    apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply wp
   apply (clarsimp simp: is_cap_simps can_fast_finalise_def)
  apply (clarsimp simp: cap_irqs_def cap_irq_opt_def split: cap.split_asm)
  done

global_naming Arch
lemma (* cap_delete_one_invs *) [Finalise_AI_asms,wp]:
  "\<lbrace>invs and emptyable ptr\<rbrace> cap_delete_one ptr \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cap_delete_one_def unless_def is_final_cap_def)
  apply (rule hoare_pre)
  apply (wp empty_slot_invs get_cap_wp)
  apply clarsimp
  apply (drule cte_wp_at_valid_objs_valid_cap, fastforce+)
  done

end

interpretation Finalise_AI_2?: Finalise_AI_2
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming X64

lemma flush_table_irq_node: "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> flush_table a b c d \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  apply (simp add: flush_table_def)
  apply (wp mapM_x_wp' | wpc | simp | rule hoare_pre)+
  done

lemma flush_table_pred_tcb_at: "\<lbrace>\<lambda>s. pred_tcb_at proj P t s\<rbrace> flush_table a b c d \<lbrace>\<lambda>_ s. pred_tcb_at proj P t s\<rbrace>"
  apply (simp add: flush_table_def)
  apply (wp mapM_x_wp' | wpc | simp | rule hoare_pre)+
  done

crunch irq_node[wp]: arch_finalise_cap "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps select_wp simp: crunch_simps)

crunch pred_tcb_at[wp]: arch_finalise_cap "pred_tcb_at proj P t"
  (simp: crunch_simps wp: crunch_wps update_aobj_pred_tcb_at
   ignore: update_object set_object set_pt set_pd set_pdpt set_pml4)

lemma tcb_cap_valid_pagetable:
  "tcb_cap_valid (ArchObjectCap (PageTableCap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PageTableCap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def
                   is_cap_simps valid_ipc_buffer_cap_def
            split: Structures_A.thread_state.split)
  done

lemma tcb_cap_valid_pagedirectory:
  "tcb_cap_valid (ArchObjectCap (PageDirectoryCap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PageDirectoryCap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def
                   is_cap_simps valid_ipc_buffer_cap_def
            split: Structures_A.thread_state.split)
  done

lemma tcb_cap_valid_pdpt:
  "tcb_cap_valid (ArchObjectCap (PDPointerTableCap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PDPointerTableCap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def
                   is_cap_simps valid_ipc_buffer_cap_def
            split: Structures_A.thread_state.split)
  done

lemma tcb_cap_valid_pml4:
  "tcb_cap_valid (ArchObjectCap (PML4Cap word (Some v))) slot
    = tcb_cap_valid (ArchObjectCap (PML4Cap word None)) slot"
  apply (rule ext)
  apply (simp add: tcb_cap_valid_def tcb_cap_cases_def
                   is_cap_simps valid_ipc_buffer_cap_def
            split: Structures_A.thread_state.split)
  done

lemma store_pde_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    store_pde pd_slot InvalidPDE
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (clarsimp simp: store_pde_def set_pd_def set_object_def update_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def empty_table_def pde_ref_def)
  done

lemma store_pte_unmap_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    store_pte xa InvalidPTE
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (wp get_object_wp | simp add: store_pte_def set_pt_def set_object_def update_object_def)+
  apply (clarsimp simp: obj_at_def empty_table_def)
  done

lemma flush_table_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    flush_table ac aa word b
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (clarsimp simp: flush_table_def set_vm_root_def)
  apply (wp do_machine_op_obj_at  hoare_whenE_wp mapM_x_wp'
    | wpc
    | simp
    | wps
    | rule hoare_pre)+
  done

crunch empty[wp]: invalidateLocalPageStructureCacheASID, lookup_pt_slot, set_vm_root, invalidate_asid_entry
  "\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s"
  (wp: crunch_wps simp: crunch_simps)

lemma unmap_page_table_empty:
  "\<lbrace>\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    unmap_page_table aa b word
   \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (wp store_pde_unmap_empty flush_table_empty  | simp | wpc | wp_once hoare_drop_imps)+
  done

definition
  replaceable_or_arch_update
where
  "replaceable_or_arch_update \<equiv> \<lambda>s slot cap cap'.
   if is_pg_cap cap then is_arch_update cap cap' \<and>
        (\<forall>vref. vs_cap_ref cap' = Some vref \<longrightarrow>
          vs_cap_ref cap = Some vref \<and>
          obj_refs cap = obj_refs cap' \<or>
          (\<forall>oref\<in>obj_refs cap'. \<not> (vref \<unrhd> oref) s))
   else replaceable s slot cap cap'"

lemma is_final_cap_pt_asid_eq:
  "is_final_cap' (ArchObjectCap (PageTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageTableCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def)
  done

lemma is_final_cap_pd_asid_eq:
  "is_final_cap' (ArchObjectCap (PageDirectoryCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PageDirectoryCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def)
  done

lemma is_final_cap_pdpt_asid_eq:
  "is_final_cap' (ArchObjectCap (PDPointerTableCap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PDPointerTableCap p x)) s"
  apply (clarsimp simp: is_final_cap'_def)
  done

lemma is_final_cap_pml4_asid_eq:
  "is_final_cap' (ArchObjectCap (PML4Cap p y)) s \<Longrightarrow>
   is_final_cap' (ArchObjectCap (PML4Cap p x)) s"
  apply (clarsimp simp: is_final_cap'_def)
  done

lemma cte_wp_at_obj_refs_singleton_page_table:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PageTableCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at (op = (ArchObjectCap (PageTableCap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma cte_wp_at_obj_refs_singleton_page_directory:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PageDirectoryCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at
            (op = (ArchObjectCap (PageDirectoryCap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma cte_wp_at_obj_refs_singleton_pdpt:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PDPointerTableCap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at
            (op = (ArchObjectCap (PDPointerTableCap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma cte_wp_at_obj_refs_singleton_pml4:
  "\<lbrakk>cte_wp_at
      (\<lambda>cap'. obj_refs cap' = {p}
            \<and> (\<exists>p asid. cap' = ArchObjectCap (PML4Cap p asid)))
      (a, b) s\<rbrakk> \<Longrightarrow>
   \<exists>asid. cte_wp_at
            (op = (ArchObjectCap (PML4Cap p asid))) (a,b) s"
  apply (clarsimp simp: cte_wp_at_def)
  done

lemma final_cap_pt_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PageTableCap p asid)) s;
    cte_wp_at (op = (ArchObjectCap (PageTableCap p asid'))) slot s;
    cte_wp_at (op = (ArchObjectCap (PageTableCap p asid''))) slot' s\<rbrakk> \<Longrightarrow>
   slot' = slot"
  apply (clarsimp simp:is_final_cap'_def2)
  apply (case_tac "(a,b) = slot'")
   apply (case_tac "(a,b) = slot")
    apply simp
   apply (erule_tac x="fst slot" in allE)
   apply (erule_tac x="snd slot" in allE)
   apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  apply (erule_tac x="fst slot'" in allE)
  apply (erule_tac x="snd slot'" in allE)
  apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  done

lemma final_cap_pd_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PageDirectoryCap p asid)) s;
    cte_wp_at (op = (ArchObjectCap (PageDirectoryCap p asid'))) slot s;
    cte_wp_at (op = (ArchObjectCap (PageDirectoryCap p asid''))) slot' s\<rbrakk>
  \<Longrightarrow> slot' = slot"
  apply (clarsimp simp:is_final_cap'_def2)
  apply (case_tac "(a,b) = slot'")
   apply (case_tac "(a,b) = slot")
    apply simp
   apply (erule_tac x="fst slot" in allE)
   apply (erule_tac x="snd slot" in allE)
   apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  apply (erule_tac x="fst slot'" in allE)
  apply (erule_tac x="snd slot'" in allE)
  apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  done

lemma final_cap_pdpt_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PDPointerTableCap p asid)) s;
    cte_wp_at (op = (ArchObjectCap (PDPointerTableCap p asid'))) slot s;
    cte_wp_at (op = (ArchObjectCap (PDPointerTableCap p asid''))) slot' s\<rbrakk>
  \<Longrightarrow> slot' = slot"
  apply (clarsimp simp:is_final_cap'_def2)
  apply (case_tac "(a,b) = slot'")
   apply (case_tac "(a,b) = slot")
    apply simp
   apply (erule_tac x="fst slot" in allE)
   apply (erule_tac x="snd slot" in allE)
   apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  apply (erule_tac x="fst slot'" in allE)
  apply (erule_tac x="snd slot'" in allE)
  apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  done

lemma final_cap_pml4_slot_eq:
  "\<lbrakk>is_final_cap' (ArchObjectCap (PML4Cap p asid)) s;
    cte_wp_at (op = (ArchObjectCap (PML4Cap p asid'))) slot s;
    cte_wp_at (op = (ArchObjectCap (PML4Cap p asid''))) slot' s\<rbrakk>
  \<Longrightarrow> slot' = slot"
  apply (clarsimp simp:is_final_cap'_def2)
  apply (case_tac "(a,b) = slot'")
   apply (case_tac "(a,b) = slot")
    apply simp
   apply (erule_tac x="fst slot" in allE)
   apply (erule_tac x="snd slot" in allE)
   apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  apply (erule_tac x="fst slot'" in allE)
  apply (erule_tac x="snd slot'" in allE)
  apply (clarsimp simp: obj_irq_refs_def cap_irqs_def cte_wp_at_def)
  done

lemma is_arch_update_reset_page:
  "is_arch_update
     (ArchObjectCap (PageCap d p r typ sz m))
     (ArchObjectCap (PageCap d p r' typ sz m'))"
  apply (simp add: is_arch_update_def is_arch_cap_def cap_master_cap_def)
  done

lemma replaceable_reset_pt:
  "\<lbrakk>cap = PageTableCap p m \<and>
   cte_wp_at (op = (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s\<rbrakk> \<Longrightarrow>
   replaceable s slot (ArchObjectCap (PageTableCap p None))
                      (ArchObjectCap cap)"
  apply (elim conjE)
  apply (cases m, simp_all add: replaceable_def obj_irq_refs_def cap_range_def
                                is_cap_simps tcb_cap_valid_pagetable)
  apply (rule conjI)
   apply (frule is_final_cap_pt_asid_eq) defer
   apply clarsimp
   apply (drule cte_wp_at_obj_refs_singleton_page_table)
   apply (erule exE)
   apply (drule_tac x="asid" in is_final_cap_pt_asid_eq)
   apply (drule final_cap_pt_slot_eq)
     apply simp_all
  apply (rule_tac
    cap="(cap.ArchObjectCap cap)"
    in  no_cap_to_obj_with_diff_ref_finalI)
  apply simp_all
  done

lemma replaceable_reset_pd:
  "\<lbrakk>cap = PageDirectoryCap p m \<and>
   cte_wp_at (op = (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s\<rbrakk> \<Longrightarrow>
   replaceable s slot (ArchObjectCap (PageDirectoryCap p None))
                      (ArchObjectCap cap)"
  apply (elim conjE)
  apply (cases m, simp_all add: replaceable_def obj_irq_refs_def cap_range_def is_cap_simps
                           tcb_cap_valid_pagedirectory)
  apply (rule conjI)
   apply (frule is_final_cap_pd_asid_eq) defer
   apply clarsimp
   apply (drule cte_wp_at_obj_refs_singleton_page_directory)
   apply (erule exE)
   apply (drule_tac x="asid" in is_final_cap_pd_asid_eq)
   apply (drule final_cap_pd_slot_eq)
     apply simp_all
  apply (rule_tac
    cap="ArchObjectCap cap"
    in  no_cap_to_obj_with_diff_ref_finalI)
  apply simp_all
  done

lemma replaceable_reset_pdpt:
  "\<lbrakk>cap = PDPointerTableCap p m \<and>
   cte_wp_at (op = (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s\<rbrakk> \<Longrightarrow>
   replaceable s slot (ArchObjectCap (PDPointerTableCap p None))
                      (ArchObjectCap cap)"
  apply (elim conjE)
  apply (cases m, simp_all add: replaceable_def obj_irq_refs_def cap_range_def is_cap_simps
                           tcb_cap_valid_pdpt)
  apply (rule conjI)
   apply (frule is_final_cap_pdpt_asid_eq) defer
   apply clarsimp
   apply (drule cte_wp_at_obj_refs_singleton_pdpt)
   apply (erule exE)
   apply (drule_tac x="asid" in is_final_cap_pdpt_asid_eq)
   apply (drule final_cap_pdpt_slot_eq)
     apply simp_all
  apply (rule_tac
    cap="ArchObjectCap cap"
    in  no_cap_to_obj_with_diff_ref_finalI)
  apply simp_all
  done

lemma replaceable_reset_pml4:
  "\<lbrakk>cap = PML4Cap p m \<and>
   cte_wp_at (op = (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s\<rbrakk> \<Longrightarrow>
   replaceable s slot (ArchObjectCap (PML4Cap p None))
                      (ArchObjectCap cap)"
  apply (elim conjE)
  apply (cases m, simp_all add: replaceable_def obj_irq_refs_def cap_range_def is_cap_simps
                           tcb_cap_valid_pml4)
  apply (rule conjI)
   apply (frule is_final_cap_pml4_asid_eq) defer
   apply clarsimp
   apply (drule cte_wp_at_obj_refs_singleton_pml4)
   apply (erule exE)
   apply (drule_tac x="asid" in is_final_cap_pml4_asid_eq)
   apply (drule final_cap_pml4_slot_eq)
     apply simp_all
  apply (rule_tac
    cap="ArchObjectCap cap"
    in  no_cap_to_obj_with_diff_ref_finalI)
  apply simp_all
  done

crunch caps_of_state [wp]: arch_finalise_cap "\<lambda>s. P (caps_of_state s)"
   (wp: crunch_wps simp: crunch_simps)

crunch obj_at[wp]: invalidateLocalPageStructureCacheASID, invalidate_asid_entry "\<lambda>s. P' (obj_at P p s)"
  (wp: hoare_whenE_wp simp: crunch_simps)

crunch x64_global_pdpts[wp]: invalidateLocalPageStructureCacheASID, invalidate_asid_entry "\<lambda>s. P' (x64_global_pdpts (arch_state s))"
  (wp: hoare_whenE_wp simp: crunch_simps)

lemma delete_asid_empty_table_pml4:
  "\<lbrace>\<lambda>s. page_map_l4_at word s
      \<and> obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>
    delete_asid a word
   \<lbrace>\<lambda>_ s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (simp add: delete_asid_def)
  apply (wp set_object_at_obj get_object_wp | wpc | simp add: update_object_def | wps)+
  apply (clarsimp simp: obj_at_def empty_table_def)
  done

lemma page_map_l4_at_def2:
  "page_map_l4_at p s = (\<exists>pd. ko_at (ArchObj (PageMapL4 pd)) p s)"
  apply (simp add: a_type_def obj_at_def)
  apply (rule iffI)
   apply (erule exE)
   apply (case_tac ko, simp_all split: if_splits)
   apply (rename_tac arch_kernel_obj)
   apply (case_tac arch_kernel_obj, simp_all split: if_splits)
  apply (erule exE)
  apply (rule_tac x="ArchObj (PageMapL4 pd)" in exI)
  apply simp
  done

definition
  pml4e_wp_at :: "(pml4e \<Rightarrow> bool) \<Rightarrow> machine_word \<Rightarrow> 9 word \<Rightarrow> 'z state \<Rightarrow> bool"
  where
  "pml4e_wp_at P ptr slot s \<equiv>
     (case (kheap s ptr) of
         Some (ArchObj (PageMapL4 pd)) \<Rightarrow> P (pd slot)
       | _ \<Rightarrow> False)"

lemma store_pml4e_pml4e_wp_at:
  "\<lbrace>\<top>\<rbrace>
   store_pml4e p x
   \<lbrace>\<lambda>_. pml4e_wp_at
         (\<lambda>pde. pde = x) (p && ~~ mask pml4_bits) (ucast (p && mask pml4_bits >> word_size_bits))\<rbrace>"
  apply (wp
    | simp add: store_pml4e_def set_pml4_def set_object_def get_object_def update_object_def
                obj_at_def pml4e_wp_at_def a_type_simps aa_type_simps)+
  done

lemma store_pml4e_pml4e_wp_at2:
  "\<lbrace>pml4e_wp_at (\<lambda>pde. pde = pml4e.InvalidPML4E) ptr slot\<rbrace>
   store_pml4e p' InvalidPML4E
   \<lbrace>\<lambda>_. pml4e_wp_at (\<lambda>pde. pde = InvalidPML4E) ptr slot\<rbrace>"
  apply (wp
    | simp add: store_pml4e_def set_pml4_def set_object_def get_object_def update_object_def
                obj_at_def pml4e_wp_at_def
    | clarsimp)+
  done

lemma obj_at_empty_tableI:
  "invs s \<and>
  (\<forall>x. x \<notin> kernel_mapping_slots \<longrightarrow>
      pml4e_wp_at (\<lambda>pde. pde = InvalidPML4E) p x s)
  \<Longrightarrow> obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s"
  apply safe
  apply (simp add: obj_at_def empty_table_def pml4e_wp_at_def)
  (* Boring cases *)
  apply (case_tac "\<exists>ko. kheap s p = Some ko")
   apply (erule exE)
   apply (rule_tac x=ko in exI)
   apply (rule conjI)
    apply assumption
   apply (case_tac ko)
       apply ((erule_tac x="ucast (pptr_base >> pml4_shift_bits) - 1" in allE,
         simp add: pptr_base_def kernel_mapping_slots_def pptrBase_def bit_simps)+)[4]
   apply (rename_tac arch_kernel_obj)
   apply (case_tac arch_kernel_obj) defer 5
      apply ((erule_tac x="ucast (pptr_base >> pml4_shift_bits) - 1" in allE,
         simp add: pptr_base_def pptrBase_def bit_simps kernel_mapping_slots_def)+)[6]
   (* Interesting case *)
  apply (rename_tac "fun")
  apply clarsimp
  apply (erule_tac x=x in allE)
  apply (case_tac "x \<notin> kernel_mapping_slots")
   apply (simp add:)
  apply simp
  apply (simp add: invs_def valid_state_def valid_kernel_mappings_def
                    valid_kernel_mappings_if_pm_def)
  apply (erule conjE)+
  apply (erule_tac x="ArchObj (PageMapL4 fun)" in ballE)
   apply simp
  apply (simp add: ran_def)
  done

(* lemma pd_shifting_kernel_mapping_slots:
  "\<lbrakk>is_aligned word pd_bits;
    (sl :: word32) \<le> (kernel_base >> (20::nat)) - (1::word32)\<rbrakk>
   \<Longrightarrow> ucast ((sl << (2::nat)) + word && mask pd_bits >> (2::nat))
      \<notin> kernel_mapping_slots"
  apply (subst pd_shifting_again5)
    apply assumption+
   prefer 2
   apply (simp add:not_le kernel_mapping_slots_def)
   apply (subst (asm) le_m1_iff_lt[THEN iffD1])
    apply (simp add: kernel_base_def)
   apply (rule shiftr_20_less[where x = "sl << 20",THEN iffD2])
   apply (subst shiftl_shiftr_id)
     apply (simp add:word_bits_def)
    defer
    apply assumption
   apply (subst shiftl_shiftr_id)
     apply (simp add:word_bits_def)
    defer
    apply (simp add: ucast_bl word_rep_drop of_drop_to_bl word_size)
    apply (subst eq_commute)
    apply (subst and_mask_eq_iff_le_mask)
    apply (rule order_trans)
     apply ((simp add: kernel_base_def mask_def)+)[2]
   apply (rule_tac x="sl" and y="kernel_base >> 20" in less_trans)
    apply ((simp add: kernel_base_def word_bits_def)+)[2]
  apply (subst (asm) le_m1_iff_lt[THEN iffD1])
   apply (simp add: kernel_base_def)
  apply (rule_tac x="sl" and y="kernel_base >> 20" in less_trans)
   apply ((simp add: kernel_base_def word_bits_def)+)[2]
  done *)

lemma pd_shifting_global_refs:
  "\<lbrakk>is_aligned pd pd_bits;
    ae \<le> (kernel_base >> 20) - 1; pd \<notin> global_refs s\<rbrakk>
   \<Longrightarrow> ((ae::word32) << 2) + pd && ~~ mask pd_bits \<notin> global_refs s"
  apply (cut_tac pd="pd" and ae="ucast ae" in pd_shifting_again3)
   apply simp
  apply (simp add: ucast_bl word_rep_drop of_drop_to_bl word_size)
  apply (insert and_mask_eq_iff_le_mask[where n=12 and w=ae, THEN iffD2])
  apply (frule_tac z="mask 12" in order_trans)
   apply (simp add: mask_def kernel_base_def)
  apply simp
  done

lemma mapM_x_store_pde_InvalidPDE_empty:
  "\<lbrace>(invs and  (\<lambda>s. word \<notin> global_refs s)) and K(is_aligned word pd_bits)\<rbrace>
    mapM_x (swp store_pde InvalidPDE)
           (map (\<lambda>a. (a << 2) + word) [0.e.(kernel_base >> 20) - 1])
   \<lbrace>\<lambda>_ s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_post_imp)
   apply (erule obj_at_empty_tableI)
  apply (wp hoare_vcg_conj_lift)
    apply (rule mapM_x_swp_store_pde_invs_unmap)
   apply (simp add: mapM_x_map)
   apply (rule hoare_strengthen_post)
    apply (rule mapM_x_accumulate_checks[OF store_pde_pml4e_wp_at])
    defer
    apply (rule allI)
    apply (erule_tac x="ucast x" in ballE)
     apply (rule impI)
     apply (frule_tac pd="word" and ae="x" in pd_shifting_again3)
     apply (frule_tac pd="word" and ae="x" in pd_shifting_again5)
      apply ((simp add: kernel_mapping_slots_def kernel_base_def)+)[3]
    apply (subst word_not_le)
    apply (subst (asm) word_not_le)
    apply (cut_tac x="ucast x" and y="kernel_base >> 20" in le_m1_iff_lt)
    apply clarsimp
    apply (simp add: le_m1_iff_lt word_less_nat_alt unat_ucast)
    apply (simp add: pde_ref_def)
   apply (rule conjI, rule allI, rule impI)
    apply (rule pd_shifting_kernel_mapping_slots)
     apply simp+
   apply (rule allI, rule impI)
   apply (rule pd_shifting_global_refs)
     apply simp+
  apply (wp store_pde_pml4e_wp_at2)
  done

lemma word_aligned_pt_slots:
  "\<lbrakk>is_aligned word pt_bits;
    x \<in> set [word , word + 4 .e. word + 2 ^ pt_bits - 1]\<rbrakk>
  \<Longrightarrow> x && ~~ mask pt_bits = word"
  apply (simp add: pt_bits_def pageBits_def)
  apply (drule subsetD[OF upto_enum_step_subset])
  apply (frule_tac ptr'=x in mask_in_range)
  apply simp
  done

lemma pt_shifting:
  "\<lbrakk>is_aligned (pt::machine_word) pt_bits\<rbrakk>
   \<Longrightarrow> pt + (ucast (ae :: 9 word) << word_size_bits) && mask pt_bits
      = (ucast (ae :: 9 word) << word_size_bits)"
  apply (rule conjunct1, erule is_aligned_add_helper)
  apply (rule ucast_less_shiftl_helper)
   apply (simp add: word_bits_def)
  apply (simp add: pt_bits_def pageBits_def)
  done

lemma word32_ucast_enumerates_word8:
  "\<lbrakk>is_aligned (word :: word32) pt_bits\<rbrakk>
  \<Longrightarrow> (x :: word8) \<in> (\<lambda>sl. ucast (sl && mask pt_bits >> 2))
     ` set [word , word + 4 .e. word + 2 ^ pt_bits - 1]"
  apply (rule_tac x="word + (ucast x << 2)" in image_eqI)
   apply (frule_tac ae="x" in pt_shifting)
   apply simp
   apply (rule sym)
   apply (rule pd_casting_shifting)
   apply (simp add: word_size len32)
  apply (clarsimp simp: upto_enum_step_def)
  apply (rule conjI)
   apply (subgoal_tac
     " word + 2 ^ pt_bits - 1 \<ge> word", simp)
   apply (rule is_aligned_no_overflow)
    apply (simp, simp add: pt_bits_def pageBits_def word_bits_def)
  apply clarsimp
  apply (rule_tac x="ucast x" in image_eqI)
   apply (simp add: word_shift_by_2)
  apply (clarsimp simp: pt_bits_def pageBits_def)
  apply (rule order_trans)
   apply (rule minus_one_helper3)
   apply (rule ucast_less)
   apply simp+
  done

lemma caps_of_state_aligned_page_table:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PageTableCap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pt_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pt_bits_def pageBits_def)
  done

lemma caps_of_state_aligned_page_directory:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PageDirectoryCap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pd_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pd_bits_def pageBits_def)
  done

lemma caps_of_state_aligned_pdpt:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PDPointerTableCap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pdpt_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pdpt_bits_def pageBits_def)
  done

lemma caps_of_state_aligned_pml4:
  "\<lbrakk>caps_of_state s slot =
  Some (ArchObjectCap (PML4Cap word option));
  invs s\<rbrakk>
  \<Longrightarrow> is_aligned word pml4_bits"
  apply (frule caps_of_state_valid)
  apply (frule invs_valid_objs, assumption)
  apply (frule valid_cap_aligned)
  apply (simp add: cap_aligned_def pml4_bits_def pageBits_def)
  done
end

lemma invs_valid_arch_capsI:
  "invs s \<Longrightarrow> valid_arch_caps s"
  by (simp add: invs_def valid_state_def)

context Arch begin global_naming X64 (*FIXME: arch_split*)
lemma replaceable_reset_pt_strg:
  "cap = PageTableCap p m \<Longrightarrow> cap = cap' \<and>
   cte_wp_at (op = (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s \<longrightarrow>
   replaceable_or_arch_update s slot (ArchObjectCap (arch_reset_mem_mapping cap)) (ArchObjectCap cap')"
  unfolding replaceable_or_arch_update_def
  by (fastforce simp add: is_cap_simps intro!: replaceable_reset_pt)

lemma replaceable_reset_pd_strg:
  "cap = PageDirectoryCap p m \<Longrightarrow> cap = cap' \<and>
   cte_wp_at (op = (ArchObjectCap cap)) slot s \<and>
   (\<forall>vs. vs_cap_ref (ArchObjectCap cap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> p) s) \<and>
   is_final_cap' (ArchObjectCap cap) s \<and>
   obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) p s \<longrightarrow>
   replaceable_or_arch_update s slot (ArchObjectCap (arch_reset_mem_mapping cap))
                                     (ArchObjectCap cap')"
  unfolding replaceable_or_arch_update_def
  by (fastforce simp add: is_cap_simps intro!: replaceable_reset_pd)

lemma arch_finalise_case_no_lookup:
  "\<lbrace>pspace_aligned and valid_arch_objs and valid_objs and
    valid_cap (cap.ArchObjectCap acap) and (\<lambda>s. valid_asid_table (x64_asid_table (arch_state s)) s)
    and K (aobj_ref acap = Some w \<and> is_final)\<rbrace>
  arch_finalise_cap acap is_final
  \<lbrace>\<lambda>rv s. (\<forall>vs. vs_cap_ref (cap.ArchObjectCap acap) = Some vs \<longrightarrow> \<not> (vs \<unrhd> w) s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_pre)
   apply (simp add: arch_finalise_cap_def)
   apply (wpc | wp delete_asid_pool_unmapped hoare_vcg_imp_lift
                   unmap_page_table_unmapped3
              | simp add: vs_cap_ref_simps
                          vs_lookup_pages_eq_at[THEN fun_cong, symmetric]
                          vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])+
     apply (wp hoare_vcg_all_lift unmap_page_unmapped static_imp_wp)
    apply (wpc|wp unmap_page_table_unmapped3 delete_asid_unmapped
      |simp add:vs_cap_ref_def
      vs_lookup_pages_eq_at[THEN fun_cong,symmetric]
      vs_lookup_pages_eq_ap[THEN fun_cong,symmetric])+
   apply (auto simp: valid_cap_simps valid_arch_state_def
              split: vmpage_size.split)
   done

lemma arch_finalise_pt_pd_empty:
  "\<lbrace>(\<lambda>s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) ptr s) and valid_cap (cap.ArchObjectCap acap) and
    K ((is_pt_cap (cap.ArchObjectCap acap) \<or> is_pd_cap (cap.ArchObjectCap acap)) \<and> aobj_ref acap = Some ptr)\<rbrace>
  arch_finalise_cap acap final
  \<lbrace>\<lambda>rv s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) ptr s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: is_cap_simps arch_finalise_cap_def)
   apply (rule hoare_pre)
   apply (wp unmap_page_table_empty | wpc)+
   apply clarsimp
  apply (clarsimp simp: is_cap_simps arch_finalise_cap_def)
  apply (rule hoare_pre)
  apply (wp unmap_page_table_empty delete_asid_empty_table_pd | wpc)+
  apply (clarsimp simp: valid_cap_def)
  done

lemma do_machine_op_reachable_pg_cap[wp]:
  "\<lbrace>\<lambda>s. P (reachable_pg_cap cap s)\<rbrace>
   do_machine_op mo
   \<lbrace>\<lambda>rv s. P (reachable_pg_cap cap s)\<rbrace>"
  apply (simp add:reachable_pg_cap_def,wp)
  done

lemma replaceable_or_arch_update_pg:
  " (case (vs_cap_ref (ArchObjectCap (PageCap word fun vm_pgsz y))) of None \<Rightarrow> True | Some ref \<Rightarrow> \<not> (ref \<unrhd> word) s)
  \<longrightarrow> replaceable_or_arch_update s slot (ArchObjectCap (PageCap word fun vm_pgsz None))
                (ArchObjectCap (PageCap word fun vm_pgsz y))"
  unfolding replaceable_or_arch_update_def
  apply (auto simp: is_cap_simps is_arch_update_def cap_master_cap_simps)
  done

lemma store_pde_arch_objs_invalid:
  "\<lbrace>valid_arch_objs\<rbrace> store_pde p InvalidPDE \<lbrace>\<lambda>_. valid_arch_objs\<rbrace>"
  apply (wp store_pde_arch_objs_unmap)
  apply (simp add: pde_ref_def)
  done

lemma mapM_x_store_pde_InvalidPDE_empty2:
  "\<lbrace>invs and (\<lambda>s. word \<notin> global_refs s) and K (is_aligned word pd_bits) and K (slots = (map (\<lambda>a. (a << 2) + word) [0.e.(kernel_base >> 20) - 1])) \<rbrace>
  mapM_x (\<lambda>x. store_pde x InvalidPDE) slots
  \<lbrace>\<lambda>_ s. obj_at (empty_table (set (x64_global_pdpts (arch_state s)))) word s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply simp
  apply (wp mapM_x_store_pde_InvalidPDE_empty [unfolded swp_def])
  apply simp
  done

crunch valid_cap: invalidate_tlb_by_asid "valid_cap cap"
crunch inv: page_table_mapped "P"
crunch valid_objs[wp]: invalidate_tlb_by_asid "valid_objs"
crunch valid_asid_table[wp]: do_machine_op
  "\<lambda>s. valid_asid_table (x64_asid_table (arch_state s)) s"

lemma mapM_x_swp_store_invalid_pte_invs:
  "\<lbrace>invs and (\<lambda>s. \<exists>slot. cte_wp_at
             (\<lambda>c. (\<lambda>x. x && ~~ mask pt_bits) ` set slots \<subseteq> obj_refs c \<and>
                  is_pt_cap c) slot s)\<rbrace>
  mapM_x (\<lambda>x. store_pte x InvalidPTE) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add:
    mapM_x_swp_store_pte_invs[unfolded swp_def,
      where pte=InvalidPTE, simplified])

lemma mapM_x_swp_store_invalid_pde_invs:
  "\<lbrace>invs and
   (\<lambda>s. \<forall>sl\<in>set slots.
         ucast (sl && mask pd_bits >> 2) \<notin> kernel_mapping_slots) and
   (\<lambda>s. \<forall>sl\<in>set slots. sl && ~~ mask pd_bits \<notin> global_refs s)\<rbrace>
     mapM_x (\<lambda>x. store_pde x InvalidPDE) slots
   \<lbrace>\<lambda>rv. invs \<rbrace>"
  apply (simp add:mapM_x_mapM)
  apply (wp mapM_swp_store_pde_invs_unmap[unfolded swp_def,
              where pde=InvalidPDE, simplified])
  done

global_naming Arch

lemma (* finalise_cap_invs *)[Finalise_AI_asms]:
  shows "\<lbrace>invs and cte_wp_at (op = cap) slot\<rbrace> finalise_cap cap x \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases cap, simp_all split del: if_split)
         apply (wp cancel_all_ipc_invs cancel_all_signals_invs unbind_notification_invs
                   unbind_maybe_notification_invs
                  | simp add: o_def split del: if_split cong: if_cong
                  | wpc )+
      apply clarsimp (* thread *)
      apply (frule cte_wp_at_valid_objs_valid_cap, clarsimp)
      apply (clarsimp simp: valid_cap_def)
      apply (frule(1) valid_global_refsD[OF invs_valid_global_refs])
       apply (simp add: global_refs_def, rule disjI1, rule refl)
      apply (simp add: cap_range_def)
     apply (wp deleting_irq_handler_invs  | simp | intro conjI impI)+
  apply (auto dest: cte_wp_at_valid_objs_valid_cap)
  done

lemma (* finalise_cap_irq_node *)[Finalise_AI_asms]:
"\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> finalise_cap a b \<lbrace>\<lambda>_ s. P (interrupt_irq_node s)\<rbrace>"
  apply (case_tac a,simp_all)
  apply (wp | clarsimp)+
  done

lemmas (*arch_finalise_cte_irq_node *) [wp,Finalise_AI_asms]
    = hoare_use_eq_irq_node [OF arch_finalise_cap_irq_node arch_finalise_cap_cte_wp_at]

lemma (* deleting_irq_handler_st_tcb_at *) [Finalise_AI_asms]:
  "\<lbrace>st_tcb_at P t and K (\<forall>st. simple st \<longrightarrow> P st)\<rbrace>
     deleting_irq_handler irq
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (simp add: deleting_irq_handler_def)
  apply (wp cap_delete_one_st_tcb_at)
  apply simp
  done

lemma irq_node_global_refs_ARCH [Finalise_AI_asms]:
  "interrupt_irq_node s irq \<in> global_refs s"
  by (simp add: global_refs_def)

lemma (* get_irq_slot_fast_finalisable *)[wp,Finalise_AI_asms]:
  "\<lbrace>invs\<rbrace> get_irq_slot irq \<lbrace>cte_wp_at can_fast_finalise\<rbrace>"
  apply (simp add: get_irq_slot_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def valid_irq_node_def)
  apply (drule spec[where x=irq], drule cap_table_at_cte_at[where offset="[]"])
   apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (case_tac "cap = cap.NullCap")
   apply (simp add: can_fast_finalise_def)
  apply (frule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
   apply simp
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  apply (drule cte_wp_at_norm, clarsimp)
  apply (drule(1) valid_global_refsD [OF _ _ irq_node_global_refs_ARCH[where irq=irq]])
  apply (case_tac c, simp_all)
     apply (clarsimp simp: cap_range_def)
    apply (clarsimp simp: cap_range_def)
   apply (clarsimp simp: appropriate_cte_cap_def can_fast_finalise_def split: cap.split_asm)
  apply (clarsimp simp: cap_range_def)
  done

lemma (* replaceable_or_arch_update_same *) [Finalise_AI_asms]:
  "replaceable_or_arch_update s slot cap cap"
  by (clarsimp simp: replaceable_or_arch_update_def
                replaceable_def is_arch_update_def is_cap_simps)

lemma (* replace_cap_invs_arch_update *)[Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. cte_wp_at (replaceable_or_arch_update s p cap) p s
        \<and> invs s
        \<and> cap \<noteq> cap.NullCap
        \<and> ex_cte_cap_wp_to (appropriate_cte_cap cap) p s
        \<and> s \<turnstile> cap\<rbrace>
     set_cap cap p
   \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (simp add:replaceable_or_arch_update_def)
  apply (cases "is_pg_cap cap")
   apply (wp hoare_pre_disj[OF arch_update_cap_invs_unmap_page arch_update_cap_invs_map])
   apply (simp add:replaceable_or_arch_update_def replaceable_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps obj_irq_refs_def
                         cap_master_cap_simps is_arch_update_def)
  apply (wp replace_cap_invs)
  apply simp
  done

lemma dmo_tcb_cap_valid_ARCH [Finalise_AI_asms]:
  "\<lbrace>\<lambda>s. P (tcb_cap_valid cap ptr s)\<rbrace> do_machine_op mop \<lbrace>\<lambda>_ s. P (tcb_cap_valid cap ptr s)\<rbrace>"
  apply (simp add: tcb_cap_valid_def no_cap_to_obj_with_diff_ref_def)
  apply (rule hoare_pre)
  apply wps
  apply wp
  apply simp
  done

lemma (* dmo_replaceable_or_arch_update *) [Finalise_AI_asms,wp]:
  "\<lbrace>\<lambda>s. replaceable_or_arch_update s slot cap cap'\<rbrace>
    do_machine_op mo
  \<lbrace>\<lambda>r s. replaceable_or_arch_update s slot cap cap'\<rbrace>"
  unfolding replaceable_or_arch_update_def replaceable_def no_cap_to_obj_with_diff_ref_def
            replaceable_final_arch_cap_def replaceable_non_final_arch_cap_def
  apply (rule hoare_pre)
  apply (wps dmo_tcb_cap_valid_ARCH do_machine_op_reachable_pg_cap)
  apply (rule hoare_vcg_prop)
  apply auto
  done

end

context begin interpretation Arch .
requalify_consts replaceable_or_arch_update
end

interpretation Finalise_AI_3?: Finalise_AI_3
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming X64

lemma arch_cap_recycle_replaceable:
  notes if_split [split del]
  and   arch_reset_mem_mapping.simps [simp del]
  shows "\<lbrace>cte_wp_at (op = (ArchObjectCap cap)) slot
    and invs
    and (\<lambda>s. is_final = is_final_cap' (ArchObjectCap cap) s)
    and (\<lambda>s. \<forall>ptr m. cap = PageDirectoryCap ptr m \<longrightarrow> ptr \<notin> global_refs s)\<rbrace>
     arch_recycle_cap is_final cap
   \<lbrace>\<lambda>rv s. replaceable_or_arch_update s slot
            (ArchObjectCap rv) (ArchObjectCap cap)\<rbrace>"
  apply (simp add: arch_recycle_cap_def)
  apply (rule hoare_pre)
   apply (wpc, simp_all only: case_prod_beta cong: option.case_cong imp_cong)
       apply ((wp | simp add: replaceable_or_arch_update_same
                              arch_reset_mem_mapping.simps)+)[3]
      -- "PageCase"
      apply ((simp only:
       | wp arch_finalise_case_no_lookup
            arch_finalise_pt_pd_empty page_table_mapped_inv
            invalidate_tlb_by_asid_pspace_aligned
            invalidate_tlb_by_asid_valid_cap do_machine_op_valid_cap
            final_cap_lift case_options_weak_wp
            mapM_x_wp' [OF store_pte_caps_of_state]
            mapM_x_wp' [OF store_pte_cte_wp_at]
            mapM_x_wp' [OF store_pte_aligned]
            mapM_x_wp' [OF store_pte_typ_ats(14)]
            mapM_x_store_pte_valid_arch_objs
            mapM_x_swp_store_empty_table_set[unfolded swp_def]
            hoare_vcg_all_lift hoare_vcg_const_imp_lift
       | strengthen replaceable_reset_pt_strg [OF refl] invs_valid_objs
                    replaceable_or_arch_update_pg invs_valid_asid_table
       | simp add: replaceable_or_arch_update_same swp_def if_distrib
                   if_apply_def2
       | wp_once hoare_drop_imps )+)[1]
      apply (simp add:arch_finalise_cap_def)
      apply ((wpc | wp valid_case_option_post_wp unmap_page_unmapped
                      hoare_vcg_all_lift hoare_vcg_imp_lift K_valid)+)[2]
      -- "PagetableCap case"
    apply ((simp only: replaceable_or_arch_update_pg
       | wp arch_finalise_case_no_lookup arch_finalise_pt_pd_empty
            page_table_mapped_inv invalidate_tlb_by_asid_pspace_aligned
            invalidate_tlb_by_asid_valid_cap do_machine_op_valid_cap
            final_cap_lift case_options_weak_wp
            mapM_x_swp_store_invalid_pte_invs
            mapM_x_wp' [OF store_pte_caps_of_state]
            mapM_x_wp' [OF store_pte_cte_wp_at]
            mapM_x_wp' [OF store_pte_aligned]
            mapM_x_wp' [OF store_pte_typ_ats(14)]
            mapM_x_store_pte_valid_arch_objs
            mapM_x_swp_store_empty_table_set[unfolded swp_def]
            hoare_vcg_all_lift hoare_vcg_const_imp_lift
       | strengthen replaceable_reset_pt_strg [OF refl] invs_valid_objs
                    invs_valid_asid_table
       | simp add: replaceable_or_arch_update_same swp_def if_distrib
                   if_apply_def2
       | wp_once hoare_drop_imps)+)[1]
   -- "PageDirectory"
   apply ((wp arch_finalise_case_no_lookup arch_finalise_pt_pd_empty
      invalidate_tlb_by_asid_pspace_aligned invalidate_tlb_by_asid_valid_cap
      do_machine_op_valid_cap find_pd_for_asid_inv mapM_x_swp_store_invalid_pde_invs
      final_cap_lift case_options_weak_wp
      mapM_x_wp' [OF store_pde_caps_of_state]
      mapM_x_wp' [OF store_pde_cte_wp_at]
      mapM_x_wp' [OF store_pde_aligned]
      mapM_x_wp' [OF store_pde_arch_objs_invalid]
      mapM_x_wp' [OF store_pde_typ_ats(14)]
      mapM_x_store_pde_InvalidPDE_empty2
      hoare_vcg_all_lift hoare_vcg_const_imp_lift
      | strengthen replaceable_reset_pd_strg [OF refl] invs_valid_asid_table
        invs_valid_objs
      | simp add: replaceable_or_arch_update_same swp_def if_distrib
        if_apply_def2
      | wp_once hoare_drop_imps )+)[1]
  apply (clarsimp simp: cte_wp_at_caps_of_state invs_psp_aligned
                        invs_arch_objs)
  apply (frule (1) caps_of_state_valid [OF _ invs_valid_objs])
  apply (cases cap, simp_all add: is_cap_simps replaceable_or_arch_update_same)
  -- "pt"
    apply (clarsimp simp: vs_cap_ref_def valid_cap_simps invs_psp_aligned
                          invs_arch_objs invs_valid_objs invs_valid_asid_table
                   split: option.splits vmpage_size.splits)
   apply (rename_tac word option)
   apply (case_tac slot)
   apply (clarsimp simp: valid_cap_simps)
   apply (case_tac "\<not> is_final_cap' (cap.ArchObjectCap (arch_cap.PageTableCap word option)) s")
    apply clarsimp
   apply (clarsimp simp:conj_comms)
   apply (intro conjI)
      apply (fastforce intro!: word_aligned_pt_slots
                       elim!: caps_of_state_aligned_page_table)
     apply (fastforce intro: word32_ucast_enumerates_word8
                     elim!: caps_of_state_aligned_page_table)
    apply (rule_tac x = "a" in exI, rule_tac x = "b" in exI)
    apply (clarsimp simp: cap_aligned_def)
    apply (erule word_aligned_pt_slots[rotated])
    apply (simp add: pt_bits_def pageBits_def)
   apply (rule_tac x = "a" in exI, rule_tac x = "b" in exI)
   apply (fastforce intro!: word_aligned_pt_slots
                    elim!: caps_of_state_aligned_page_table)
  apply (rename_tac word option)
  apply (case_tac "\<not> is_final_cap' (cap.ArchObjectCap (arch_cap.PageDirectoryCap word option)) s")
   apply clarsimp
  apply (frule caps_of_state_valid)
   apply fastforce
  apply (clarsimp simp:cap_aligned_def valid_cap_simps conj_comms)
  -- "pd"
  apply (frule caps_of_state_aligned_page_directory)
   apply simp
  apply (clarsimp simp:valid_cap_simps cap_aligned_def pd_bits_def pageBits_def)
  apply (auto simp: pd_shifting_kernel_mapping_slots
                      [unfolded pd_bits_def pageBits_def,simplified]
                    pd_shifting_global_refs
                      [unfolded pd_bits_def pageBits_def,simplified])
  done

crunch irq_node[wp]: recycle_cap "\<lambda>s. P (interrupt_irq_node s)"
  (ignore: filterM clearMemory recycle_cap_ext
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

global_naming Arch

lemma (* cap_recycle_replaceable *) [Finalise_AI_asms]:
  shows "\<lbrace>invs and cte_wp_at (op = cap) slot and zombies_final
    and valid_objs and K (cap \<noteq> NullCap)
    and (\<lambda>s. is_final = is_final_cap' cap s)\<rbrace>
     recycle_cap is_final cap
   \<lbrace>\<lambda>rv s. replaceable_or_arch_update s slot rv cap \<and> rv \<noteq> NullCap\<rbrace>"
  apply (simp add: recycle_cap_def)
  apply (rule hoare_pre)
   apply (wpc, simp_all add: replaceable_or_arch_update_same)
            apply (wp | simp add: replaceable_or_arch_update_same)+
            -- "Zombie"
    apply (simp add: recycle_cap_def replaceable_def replaceable_or_arch_update_def)
    apply (wpc, simp_all)[1]
    apply (wp gts_wp static_imp_wp gbn_wp
               hoare_vcg_disj_lift thread_set_final_cap
               ball_tcb_cap_casesI hoare_vcg_const_Ball_lift
               thread_set_cte_wp_at_trivial
               thread_set_caps_of_state_trivial
               thread_set_no_cap_obj_ref_trivial
               arch_cap_recycle_replaceable
               hoare_vcg_all_lift
                 | simp add: tcb_registers_caps_merge_def tcb_not_empty_table reachable_pg_cap_def
                 | simp cong: rev_conj_cong
                 | strengthen tcb_cap_valid_imp'
                 | simp add: cte_wp_at_caps_of_state o_def
                 | wp_once hoare_use_eq [OF thread_set_arch thread_set_obj_at_impossible])+
    -- "last imp goal"
  apply (simp add: replaceable_or_arch_update_same)
  apply (cases cap, simp_all add: is_cap_simps)
   apply (clarsimp simp: is_cap_simps obj_irq_refs_subset vs_cap_ref_def cap_range_def
                   cong: rev_conj_cong)
   apply (frule(1) zombies_finalD [OF caps_of_state_cteD], clarsimp simp: is_cap_simps)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (frule caps_of_state_valid_cap, clarsimp+)
   apply (rename_tac option nat)
   apply (case_tac option, simp_all)[1]
   -- "None case"
    apply clarsimp
    apply (intro conjI)
       apply (clarsimp simp: valid_cap_def)
       apply (drule(1) order_less_le_trans)
       apply (drule tcb_cap_cases_lt)
       apply (simp add: nat_to_cref_unat_of_bl')

      apply (clarsimp simp: cte_wp_at_caps_of_state
                            tcb_cap_cases_def is_cap_simps
                     split: Structures_A.thread_state.split_asm)
     apply (simp add: valid_ipc_buffer_cap_def)
    apply (erule (1) no_cap_to_obj_with_diff_ref_finalI [OF caps_of_state_cteD])
    apply simp
    -- "Some case"
   apply (intro conjI)
     apply (clarsimp simp: cte_wp_at_caps_of_state
                           tcb_cap_cases_def is_cap_simps
                    split: Structures_A.thread_state.split_asm)
    apply (simp add: valid_ipc_buffer_cap_def)
   apply (erule (1) no_cap_to_obj_with_diff_ref_finalI [OF caps_of_state_cteD])
   apply simp
  -- "arch cap"
  apply clarsimp
  apply (drule cap_not_in_valid_global_refs)
   apply simp
  apply (simp add: global_refs_def)
  done

crunch caps_of_state_ARCH[wp]: recycle_cap "\<lambda>s. P (caps_of_state s)"
  (ignore: filterM set_object thread_set clearMemory recycle_cap_ext
     simp: filterM_mapM crunch_simps tcb_registers_caps_merge_def
       wp: crunch_wps thread_set_caps_of_state_trivial2)

lemmas [Finalise_AI_asms] = recycle_cap_caps_of_state_ARCH
end

interpretation Finalise_AI_4?: Finalise_AI_4
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

context Arch begin global_naming X64

crunch typ_at[wp]: recycle_cap "\<lambda>s. P (typ_at T p s)"
  (ignore: filterM clearMemory recycle_cap_ext
     simp: filterM_mapM crunch_simps
       wp: crunch_wps)

lemma set_asid_pool_obj_at_ptr:
  "\<lbrace>\<lambda>s. P (ArchObj (arch_kernel_obj.ASIDPool mp))\<rbrace>
     set_asid_pool ptr mp
   \<lbrace>\<lambda>rv s. obj_at P ptr s\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  done

lemma valid_arch_state_table_strg:
  "valid_arch_state s \<and> asid_pool_at p s \<and>
   Some p \<notin> x64_asid_table (arch_state s) ` (dom (x64_asid_table (arch_state s)) - {x}) \<longrightarrow>
   valid_arch_state (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table (arch_state s)(x \<mapsto> p)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def ran_def)
  apply (rule conjI, fastforce)
  apply (erule inj_on_fun_upd_strongerI)
  apply simp
  done

lemma valid_table_caps_table [simp]:
  "valid_table_caps (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table'\<rparr>\<rparr>) = valid_table_caps s"
  by (simp add: valid_table_caps_def)

lemma valid_global_objs_table [simp]:
  "valid_global_objs (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table'\<rparr>\<rparr>) = valid_global_objs s"
  by (simp add: valid_global_objs_def)

lemma valid_kernel_mappings [iff]:
  "valid_kernel_mappings (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table'\<rparr>\<rparr>) = valid_kernel_mappings s"
  by (simp add: valid_kernel_mappings_def)

lemma vs_asid_refs_updateD:
  "(ref', p') \<in> vs_asid_refs (table (x \<mapsto> p))
  \<Longrightarrow> (ref',p') \<in> vs_asid_refs table \<or> (ref' = [VSRef (ucast x) None] \<and> p' = p)"
  apply (clarsimp simp: vs_asid_refs_def graph_of_def split: if_split_asm)
  apply (rule_tac x="(a,p')" in image_eqI)
   apply auto
  done

lemma vs_lookup1_arch [simp]:
  "vs_lookup1 (arch_state_update f s) = vs_lookup1 s"
  by (simp add: vs_lookup1_def)

lemma vs_lookup_empty_table:
  "(rs \<rhd> q)
  (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (ASIDPool empty)),
     arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table (arch_state s)(x \<mapsto> p)\<rparr>\<rparr>) \<Longrightarrow>
   (rs \<rhd> q) s \<or> (rs = [VSRef (ucast x) None] \<and> q = p)"
  apply (erule vs_lookupE)
  apply clarsimp
  apply (drule vs_asid_refs_updateD)
  apply (erule disjE)
   apply (drule rtranclD)
   apply (erule disjE)
    apply clarsimp
    apply (fastforce simp: vs_lookup_def)
   apply clarsimp
   apply (drule trancl_sub_lift [rotated])
    prefer 2
    apply (rule vs_lookup_trancl_step)
     prefer 2
     apply assumption
    apply (fastforce simp: vs_lookup_def)
   apply (clarsimp simp: obj_at_def vs_lookup1_def vs_refs_def
                  split: if_split_asm)
  apply clarsimp
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup1D)
  apply (clarsimp simp: obj_at_def vs_refs_def)
  done

lemma vs_lookup_pages_empty_table:
  "(rs \<unrhd> q)
  (s\<lparr>kheap := kheap s(p \<mapsto> ArchObj (ASIDPool empty)),
     arch_state := arch_state s\<lparr>x64_asid_table := x64_asid_table (arch_state s)(x \<mapsto> p)\<rparr>\<rparr>) \<Longrightarrow>
   (rs \<unrhd> q) s \<or> (rs = [VSRef (ucast x) None] \<and> q = p)"
  apply (subst (asm) vs_lookup_pages_def)
  apply (clarsimp simp: Image_def)
  apply (drule vs_asid_refs_updateD)
  apply (erule disjE)
   apply (drule rtranclD)
   apply (erule disjE)
    apply clarsimp
    apply (fastforce simp: vs_lookup_pages_def)
   apply clarsimp
   apply (drule trancl_sub_lift [rotated])
    prefer 2
    apply (rule vs_lookup_pages_trancl_step)
     prefer 2
     apply assumption
    apply (fastforce simp: vs_lookup_pages_def)
   apply (clarsimp simp: obj_at_def vs_lookup_pages1_def vs_refs_pages_def
                  split: if_split_asm)
  apply clarsimp
  apply (drule rtranclD)
  apply (erule disjE)
   apply clarsimp
  apply clarsimp
  apply (drule tranclD)
  apply clarsimp
  apply (drule vs_lookup_pages1D)
  apply (clarsimp simp: obj_at_def vs_refs_pages_def)
  done

lemma set_asid_pool_empty_table_objs:
  "\<lbrace>valid_arch_objs and asid_pool_at p\<rbrace>
  set_asid_pool p empty
   \<lbrace>\<lambda>rv s. valid_arch_objs
             (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table :=
                x64_asid_table (arch_state s)(asid_high_bits_of word2 \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def valid_arch_objs_def
                  simp del: fun_upd_apply
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (rule valid_arch_obj_same_type)
    prefer 2
    apply simp
   prefer 2
   apply (simp add: a_type_def)
  apply (clarsimp simp add: a_type_def split: if_split_asm)
  apply (erule_tac x=pa in allE)
  apply (erule impE)
   apply (drule vs_lookup_empty_table)
   apply fastforce
  apply simp
  done

lemma set_asid_pool_empty_table_lookup:
  "\<lbrace>valid_vs_lookup and asid_pool_at p and
    (\<lambda>s. \<exists>p'. caps_of_state s p' = Some (ArchObjectCap (ASIDPoolCap p base)))\<rbrace>
  set_asid_pool p empty
   \<lbrace>\<lambda>rv s. valid_vs_lookup
             (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table :=
                x64_asid_table (arch_state s)(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def valid_vs_lookup_def
                  simp del: fun_upd_apply)
  apply (drule vs_lookup_pages_empty_table)
  apply (erule disjE)
   apply (fastforce simp: caps_of_state_after_update[folded fun_upd_apply]
                         obj_at_def)
  apply clarsimp
  apply (rule_tac x=a in exI)
  apply (rule_tac x=b in exI)
  apply (simp add: caps_of_state_after_update [folded fun_upd_apply] obj_at_def)
  apply (simp add: vs_cap_ref_def)
  done

lemma set_asid_pool_empty_valid_asid_map:
  "\<lbrace>\<lambda>s. valid_asid_map s \<and> asid_pool_at p s
       \<and> (\<forall>asid'. \<not> ([VSRef asid' None] \<rhd> p) s)
       \<and> (\<forall>p'. \<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p') s)\<rbrace>
       set_asid_pool p empty
   \<lbrace>\<lambda>rv s. valid_asid_map (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table :=
                 x64_asid_table (arch_state s)(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: valid_asid_map_def vspace_at_asid_def
                 dest!: graph_ofD
                 split: Structures_A.kernel_object.split_asm
                        arch_kernel_obj.split_asm)
  apply (drule bspec, erule graph_ofI)
  apply (clarsimp dest!: vs_lookup_2ConsD vs_lookup1D)
  apply (case_tac "p = pa")
   apply simp
  apply (clarsimp elim!: vs_lookup_atE)
  apply (rule vs_lookupI[rotated])
   apply (rule r_into_rtrancl)
   apply (rule_tac p=pa in vs_lookup1I)
     apply (simp add: obj_at_def)
    apply assumption
   apply simp
  apply (rule vs_asid_refsI)
  apply clarsimp
  apply (drule vs_asid_refsI)
  apply (drule vs_lookupI, rule rtrancl_refl)
  apply simp
  done

lemma set_asid_pool_invs_table:
  "\<lbrace>\<lambda>s. invs s \<and> asid_pool_at p s
       \<and> (\<exists>p'. caps_of_state s p' = Some (ArchObjectCap (ASIDPoolCap p base)))
       \<and> (\<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p) s)
       \<and> (\<forall>p'. \<not> ([VSRef (ucast (asid_high_bits_of base)) None] \<rhd> p') s)\<rbrace>
       set_asid_pool p empty
  \<lbrace>\<lambda>x s. invs (s\<lparr>arch_state := arch_state s\<lparr>x64_asid_table :=
                 x64_asid_table (arch_state s)(asid_high_bits_of base \<mapsto> p)\<rparr>\<rparr>)\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_caps_def)
  apply (rule hoare_pre)
   apply (wp valid_irq_node_typ set_asid_pool_typ_at
             set_asid_pool_empty_table_objs
             valid_irq_handlers_lift set_asid_pool_empty_table_lookup
             set_asid_pool_empty_valid_asid_map
          | strengthen valid_arch_state_table_strg)+
  apply (clarsimp simp: conj_comms)
  apply (rule context_conjI)
   apply clarsimp
   apply (frule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
   apply clarsimp
   apply (drule obj_ref_elemD)
   apply (frule(2) unique_table_refsD,
          unfold obj_refs.simps aobj_ref.simps option.simps,
          assumption)
   apply (clarsimp simp:vs_cap_ref_def table_cap_ref_def
     split:cap.split_asm arch_cap.split_asm)
  apply clarsimp
  apply (drule vs_asid_refsI)
  apply (drule vs_lookupI, rule rtrancl_refl)
  apply simp
  done

lemma delete_asid_pool_unmapped2:
  "\<lbrace>\<lambda>s. (base' = base \<and> ptr' = ptr)
         \<or> \<not> ([VSRef (ucast (asid_high_bits_of base')) None] \<rhd> ptr') s\<rbrace>
     delete_asid_pool base ptr
   \<lbrace>\<lambda>rv s. \<not> ([VSRef (ucast (asid_high_bits_of base')) None] \<rhd> ptr') s\<rbrace>"
  (is "valid ?P ?f (\<lambda>rv. ?Q)")
  apply (cases "base = base' \<and> ptr = ptr'")
   apply simp
   apply (wp delete_asid_pool_unmapped)
  apply (simp add: delete_asid_pool_def)
  apply wp
     apply (rule_tac Q="\<lambda>rv s. ?Q s \<and> asid_table = x64_asid_table (arch_state s)"
                in hoare_post_imp)
      apply (clarsimp simp: fun_upd_def[symmetric])
      apply (drule vs_lookup_clear_asid_table[rule_format])
      apply simp
     apply (wp mapM_wp')
     apply clarsimp
    apply wp
  apply clarsimp
  done

lemma page_table_mapped_wp_weak:
  "\<lbrace>\<lambda>s. Q None s \<and> (\<forall>x. Q (Some x) s)\<rbrace>
     page_table_mapped asid vptr pt
   \<lbrace>Q\<rbrace>"
  (is "\<lbrace>?P\<rbrace> page_table_mapped asid vptr pt \<lbrace>Q\<rbrace>")
  apply (simp add: page_table_mapped_def)
  apply (rule hoare_pre)
   apply (wp get_pde_wp | wpc)+
   apply (rule_tac Q'="\<lambda>_. ?P" in hoare_post_imp_R)
    apply wp
   apply clarsimp
  apply simp
  done

crunch arm_global_pd[wp]: invalidate_tlb_by_asid
           "\<lambda>s. P (arm_global_pd (arch_state s))"

crunch global_refs_invs[wp]: invalidate_tlb_by_asid
           "\<lambda>s. P (global_refs s)"

lemmas pd_bits_14 = pd_bits

lemma arch_recycle_slots_kernel_mapping_slots:
  "is_aligned pd pd_bits \<and> sl \<le> (kernel_base >> 20) - 1 \<longrightarrow>
     ucast ((sl << 2) && mask pd_bits >> 2)
               \<notin> kernel_mapping_slots"
  apply (clarsimp simp: kernel_mapping_slots_def
                        kernel_base_shift_cast_le[symmetric]
                        ucast_ucast_mask_shift_helper)
  apply (simp add: pd_bits_14)
  apply (subst(asm) iffD2[OF mask_eq_iff_w2p])
    apply (simp add: word_size)
   apply (rule shiftl_less_t2n)
    apply (erule order_le_less_trans, simp add: kernel_base_def)
   apply simp
  apply (subst(asm) shiftl_shiftr_id)
    apply (simp add: word_bits_def)
   apply (erule order_le_less_trans, simp add: kernel_base_def word_bits_def)
  apply (drule minus_one_helper5[rotated])
   apply (simp add: kernel_base_def)
  apply simp
  done

lemma page_table_pte_atE:
  "\<lbrakk> page_table_at p s; x < 2 ^ pt_bits;
             (x >> 2) << 2 = x; pspace_aligned s \<rbrakk>
       \<Longrightarrow> pte_at (p + x) s"
  apply (drule page_table_pte_atI[where x="x >> 2"], simp_all)
  apply (subst mask_eq_iff_w2p[symmetric])
   apply (simp add: pt_bits_def pageBits_def word_size)
  apply (rule word_eqI)
  apply (simp add: nth_shiftr word_size)
  apply (drule_tac x="Suc (Suc n)" in word_eqD [OF less_mask_eq])
  apply (simp add: word_size)
  apply arith
  done

crunch aligned[wp]: invalidate_tlb_by_asid "pspace_aligned"

crunch valid_arch_state[wp]: invalidate_tlb_by_asid "valid_arch_state"

crunch valid_cap [wp]: unmap_page_table, invalidate_tlb_by_asid,
  page_table_mapped, store_pte, delete_asid_pool, copy_global_mappings,
  arch_finalise_cap
  "valid_cap c"
  (wp: mapM_wp_inv mapM_x_wp')

lemma recycle_cap_cases:
  notes if_split [split del]
  shows "\<lbrace>\<top>\<rbrace>
    recycle_cap is_final cap
   \<lbrace>\<lambda>rv s. rv = cap
    \<or> (\<exists>arch_cap. cap = ArchObjectCap arch_cap
      \<and> rv = ArchObjectCap (arch_reset_mem_mapping arch_cap))
    \<or> is_zombie cap
      \<and> (is_thread_cap rv \<or> is_cnode_cap rv)
      \<and> obj_ref_of rv = obj_ref_of cap
      \<and> obj_size rv = obj_size cap\<rbrace>"
  apply (cases cap, simp_all add: recycle_cap_def)
           apply (wp | simp)+
   apply (rule hoare_pre, wpc)
     apply simp
     apply (wp assert_inv | simp)+
   apply (clarsimp simp: is_cap_simps)
  (* arch object cap cases *)
  apply (clarsimp simp: is_cap_simps arch_recycle_cap_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp)+
  apply (fastforce split: if_split_asm)
  done

global_naming Arch

lemmas (* recycle_cap_cte_cap_to *) [wp,Finalise_AI_asms] =
  ex_cte_cap_to_pres [OF recycle_cap_cte_wp_at recycle_cap_irq_node]

lemmas (* recycle_cap_valid_cap *)[Finalise_AI_asms] =
  valid_cap_typ [OF recycle_cap_typ_at]

(* FIXME: move *)
lemma (* clearMemory_invs *) [wp,Finalise_AI_asms]:
  "\<lbrace>invs\<rbrace> do_machine_op (clearMemory w sz) \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: invs_def valid_state_def clearMemory_vms cur_tcb_def)
  apply (erule use_valid[OF _ clearMemory_valid_irq_states], simp)
  done

lemma arch_recycle_cap_invs_ARCH [Finalise_AI_asms]:
  notes if_split [split del]
  shows "\<lbrace>invs and cte_wp_at (op = (ArchObjectCap cap)) slot\<rbrace>
         arch_recycle_cap is_final cap
         \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: arch_recycle_cap_def)
  apply (rule hoare_pre)
   apply ((wp set_asid_pool_invs_table dmo_ccr_invs
             mapM_x_swp_store_pde_invs_unmap
             hoare_vcg_all_lift delete_asid_pool_unmapped2
             page_table_mapped_wp_weak
             mapM_x_wp'[where P="\<lambda>s. Q (global_refs s)" for Q]
             mapM_x_wp'[where P="\<lambda>s. Q (typ_at T p s)" for Q T p]
             store_pte_typ_at static_imp_wp
           | simp add: fun_upd_def[symmetric] cte_wp_at_caps_of_state
                       valid_cap_simps
           | wpc)+)
  apply (case_tac slot)
  apply clarsimp
  apply (frule caps_of_state_valid_cap, clarsimp)
  apply (frule valid_global_refsD2, clarsimp)
  apply (frule valid_cap_aligned, clarsimp simp: cap_aligned_def)
  apply (intro conjI)
     (* ASID pool case *)
     apply ((fastforce simp: valid_cap_def mask_def split: if_split
                     elim!: vs_lookup_atE)+)[2]
   (* PageTable case*)
   apply clarsimp
   apply (subgoal_tac "(\<exists>a b cap.
               caps_of_state s (a, b) = Some cap \<and>
               (\<lambda>x. x && ~~ mask pt_bits) `
               set [x , x + 4 .e. x + 2 ^ pt_bits - 1]
               \<subseteq> obj_refs cap \<and>
               is_pt_cap cap)")
    apply (case_tac xa)
     apply simp+
    apply (clarsimp simp: valid_cap_simps)
   apply (clarsimp simp: is_cap_simps valid_cap_simps mask_def asid_bits_def
     vmsz_aligned_def upto_enum_step_def pt_bits_def pageBits_def
     image_image word_shift_by_2 split: if_split_asm)
    apply (erule order_le_less_trans, simp)+
   apply (rule_tac x=a in exI, rule_tac x=b in exI)
   apply (clarsimp simp: upto_enum_step_def pt_bits_def pageBits_def is_cap_simps
                         image_image word_shift_by_2 split: if_split_asm)
  apply (frule_tac d="xb << 2" in is_aligned_add_helper)
    apply (rule shiftl_less_t2n)
     apply (erule order_le_less_trans, simp)
    apply (simp_all add: mask_def)[3]
  (* PageDirectory case *)
  apply (intro allI impI)
  apply (subgoal_tac "
           (\<forall>sl\<le>(kernel_base >> 20) - 1.
               ucast (x + (sl << 2) && 2 ^ pd_bits - 1 >> 2)
               \<notin> kernel_mapping_slots) \<and>
           (\<forall>sl\<le>(kernel_base >> 20) - 1.
               x + (sl << 2) && ~~ (2 ^ pd_bits - 1) \<notin> global_refs s)")
  apply (clarsimp simp: valid_cap_def cap_aligned_def pd_bits_14[symmetric]
                        cap_range_def pde_ref_def
                        mask_add_aligned field_simps
                        split: option.splits)
  apply (intro allI conjI impI)
   apply (simp add: kernel_base_def mask_def pd_bits_def pageBits_def)
   apply (frule_tac d="sl << 2" in is_aligned_add_helper)
    apply (rule shiftl_less_t2n)
     apply (erule order_le_less_trans, simp)
    apply (simp add: mask_def kernel_mapping_slots_def
        kernel_base_def word_le_make_less not_le)
   apply (simp add: mask_def kernel_mapping_slots_def kernel_base_def
      word_le_make_less not_le)
   apply (rule le_less_trans[rotated])
    apply (frule_tac 'a = "12" in ucast_mono[where y = "0xE00::word32"])
     apply (simp+)[2]
   apply (intro eq_refl  arg_cong[where f = ucast] shiftl_shiftr_id)
    apply ((simp add:word_bits_def)+)[2]
   apply unat_arith
  apply (simp add: kernel_base_def mask_def pd_bits_def pageBits_def)
  apply (frule_tac d="sl << 2" in is_aligned_add_helper)
   apply (rule shiftl_less_t2n)
    apply (erule order_le_less_trans)
    apply (simp add: word_bits_def mask_def)+
   apply (drule cap_not_in_valid_global_refs)
  apply (simp add: obj_refs_def)+
  done

lemma (* recycle_cap_invs *)[Finalise_AI_asms]:
  "\<lbrace>cte_wp_at (op = cap) slot and invs\<rbrace>
     recycle_cap is_final cap
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (cases cap, simp_all add: recycle_cap_def)
           apply ((wp | simp)+)[9]
   -- "Zombie"
   apply (rename_tac option nat)
   apply (case_tac option, simp_all)
    apply (rule hoare_seq_ext[rotated], rule assert_sp gts_sp gbn_sp)+
    apply (rule hoare_seq_ext)
     apply (wp, simp)[1]
    apply (rule use_bcorres[OF thread_set_bcorres])
    apply (simp add: o_def) (* Nothing cares about the extended state*)
    apply (simp add: thread_set_split_out_set_thread_state[where 'a="unit",
                                       simplified gets_bind_ign dxo_noop bind_return_unit[symmetric]]
                     thread_set_split_out_set_bound_notification[where 'a="unit"]
                     tcb_registers_caps_merge_def)  (* Use the nondeterministic version of set_thread_state and
                                                       go through refinement/bcorres *)
    apply (fold tcb_registers_caps_merge_def)
    apply (rule hoare_pre, wp sts_invs_minor)
      apply (simp add: cte_wp_at_caps_of_state
                      tcb_state_merge_tcb_state_default)
      apply (wp set_bound_notification_it has_reply_cap_cte_lift sbn_invs_minor)
     apply (simp add: cte_wp_at_caps_of_state
                      tcb_state_merge_tcb_state_default
                      tcb_bound_notification_merge_tcb_state_default)
     apply (wp thread_set_no_change_tcb_state
               thread_set_no_change_tcb_bound_notification
               thread_set_caps_of_state_trivial2
               hoare_vcg_disj_lift hoare_vcg_all_lift
               thread_set_invs_trivial [OF ball_tcb_cap_casesI]
               has_reply_cap_cte_lift
                 | simp add: tcb_registers_caps_merge_def)+
       apply (simp add: default_tcb_def)
      apply (simp add: default_tcb_def tcb_registers_caps_merge_def
                       word_bits_def)
     apply (simp add: default_tcb_def tcb_registers_caps_merge_def)
    apply (clarsimp simp: cte_wp_at_caps_of_state default_tcb_def)
    apply (rule conjI, erule pred_tcb_weakenE, (auto)[1])
    apply (frule_tac r="idle_thread s"
              in  valid_global_refsD [OF _ caps_of_state_cteD, rotated])
      apply (simp add: global_refs_def)
     apply clarsimp
    apply (strengthen reply_cap_doesnt_exist_strg)
    apply (fastforce simp: cap_range_def elim!: pred_tcb_weakenE)
   apply (wp arch_recycle_cap_invs_ARCH[where slot=slot] | simp)+
  done

lemma valid_idle_has_null_cap_ARCH[Finalise_AI_asms]:
  "\<lbrakk> if_unsafe_then_cap s; valid_global_refs s; valid_idle s; valid_irq_node s\<rbrakk>
   \<Longrightarrow> caps_of_state s (idle_thread s, v) = Some cap
   \<Longrightarrow> cap = NullCap"
  apply (rule ccontr)
  apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
   apply clarsimp
  apply (clarsimp simp: ex_cte_cap_wp_to_def cte_wp_at_caps_of_state)
  apply (frule(1) valid_global_refsD2)
  apply (case_tac capa, simp_all add: cap_range_def global_refs_def)[1]
  apply (clarsimp simp: valid_irq_node_def valid_idle_def pred_tcb_at_def
                        obj_at_def is_cap_table_def)
  apply (rename_tac word tcb)
  apply (drule_tac x=word in spec, simp)
  done

lemma (* zombie_cap_two_nonidles *)[Finalise_AI_asms]:
  "\<lbrakk> caps_of_state s ptr = Some (Zombie ptr' zbits n); invs s \<rbrakk>
       \<Longrightarrow> fst ptr \<noteq> idle_thread s \<and> ptr' \<noteq> idle_thread s"
  apply (frule valid_global_refsD2, clarsimp+)
  apply (simp add: cap_range_def global_refs_def)
  apply (cases ptr, auto dest: valid_idle_has_null_cap_ARCH[rotated -1])[1]
  done

lemma (* arch_recycle_cap_valid *)[wp, Finalise_AI_asms]:
  "\<lbrace>valid_cap (ArchObjectCap arch_cap)\<rbrace>
    arch_recycle_cap is_final arch_cap
   \<lbrace>valid_cap \<circ> ArchObjectCap\<rbrace>"
  apply (rule hoare_pre)
   apply (rule_tac
     Q="\<lambda>rv s. valid_cap (cap.ArchObjectCap arch_cap) s
     \<and> (rv = arch_cap
        \<or> rv = arch_reset_mem_mapping arch_cap)"
     in hoare_post_imp)
    apply (erule conjE)
    apply (erule disjE)
     apply ((clarsimp simp: valid_cap_def cap_aligned_def | case_tac arch_cap)+)[2]
   apply (simp add: arch_recycle_cap_def)
   apply (intro conjI impI)
    apply (wp unmap_page_table_valid_cap invalidate_tlb_by_asid_valid_cap
              mapM_x_wp' store_pte_valid_cap
              delete_asid_pool_valid_cap copy_global_mappings_valid_cap
              do_machine_op_valid_cap set_asid_pool_typ_ats
           | wpc
           | wp_once hoare_vcg_conj_lift
           | wp_once hoare_vcg_all_lift
           | wp_once hoare_drop_imps
           | simp add: swp_def)+
  apply force
  done

lemma (* recycle_cap_valid *) [wp,Finalise_AI_asms]:
  "\<lbrace>valid_cap cap and valid_objs\<rbrace> recycle_cap is_final cap \<lbrace>valid_cap\<rbrace>"
  apply (simp add: recycle_cap_def)
  apply (cases cap, simp_all)
           apply (wp valid_cap_typ [OF cancel_badged_sends_typ_at]
                     | simp)+
   apply (rule hoare_pre, wpc)
     apply (wp | simp add: valid_cap_def | wp_once hoare_drop_imps)+
   apply (clarsimp simp: cap_aligned_def split: option.split_asm)
  apply (wp | simp)+
  done

end

interpretation Finalise_AI_5?: Finalise_AI_5
  where replaceable_or_arch_update = replaceable_or_arch_update
  proof goal_cases
  interpret Arch .
  case 1 show ?case by (intro_locales; (unfold_locales; fact Finalise_AI_asms)?)
  qed

end