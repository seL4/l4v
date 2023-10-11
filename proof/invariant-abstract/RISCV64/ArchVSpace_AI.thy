(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(*
RISCV-specific VSpace invariants
*)

theory ArchVSpace_AI
imports VSpacePre_AI
begin

context Arch begin global_naming RISCV64

definition kernel_mappings_only :: "(pt_index \<Rightarrow> pte) \<Rightarrow> 'z::state_ext state \<Rightarrow> bool" where
  "kernel_mappings_only pt s \<equiv>
     has_kernel_mappings pt s \<and> (\<forall>idx. idx \<notin> kernel_mapping_slots \<longrightarrow> pt idx = InvalidPTE)"

lemma find_vspace_for_asid_wp[wp]:
  "\<lbrace>\<lambda>s. (vspace_for_asid asid s = None \<longrightarrow> E InvalidRoot s) \<and>
        (\<forall>pt. vspace_for_asid asid s = Some pt \<longrightarrow> Q pt s) \<rbrace>
   find_vspace_for_asid asid \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding find_vspace_for_asid_def
  by wpsimp

crunch pspace_in_kernel_window[wp]: perform_page_invocation "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps)

lemma asid_word_bits [simp]: "asid_bits < word_bits"
  by (simp add: asid_bits_def word_bits_def)

lemma vspace_at_asid_vs_lookup:
  "vspace_at_asid asid pt s \<Longrightarrow>
   vs_lookup_table max_pt_level asid 0 s = Some (max_pt_level, pt)"
  by (simp add: vs_lookup_table_def vspace_at_asid_def vspace_for_asid_def in_omonad)

lemma pt_at_asid_unique:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid' pt s;
     unique_table_refs s;
     valid_vs_lookup s; valid_vspace_objs s; valid_asid_table s;
     pspace_aligned s; valid_caps (caps_of_state s) s \<rbrakk>
       \<Longrightarrow> asid = asid'"
  by (drule vspace_at_asid_vs_lookup)+ (drule (1) unique_vs_lookup_table; simp)

lemma pt_at_asid_unique2:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid pt' s \<rbrakk> \<Longrightarrow> pt = pt'"
  by (clarsimp simp: vspace_at_asid_def)

lemma dmo_pt_at_asid[wp]:
  "do_machine_op f \<lbrace>vspace_at_asid a pt\<rbrace>"
  by (wpsimp simp: do_machine_op_def vspace_at_asid_def)

crunch valid_vs_lookup[wp]: do_machine_op "valid_vs_lookup"

lemmas ackInterrupt_irq_masks = no_irq[OF no_irq_ackInterrupt]

crunches sfence, hwASIDFlush, setVSpaceRoot
  for underlying_memory_inv[wp]: "\<lambda>ms. P (underlying_memory ms)"


lemma ucast_ucast_low_bits:
  fixes x :: machine_word
  shows "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> ucast (ucast x:: asid_low_index) = x"
  apply (simp add: ucast_ucast_mask)
  apply (rule less_mask_eq)
  apply (subst (asm) word_less_sub_le)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_low_bits_def)
  done

lemma asid_high_bits_of_or:
  "x \<le> 2^asid_low_bits - 1 \<Longrightarrow> asid_high_bits_of (base || x) = asid_high_bits_of base"
  apply (rule word_eqI)
  apply (drule le_2p_upper_bits)
   apply (simp add: asid_low_bits_def word_bits_def)
  apply (simp add: asid_high_bits_of_def word_size nth_ucast nth_shiftr asid_low_bits_def word_bits_def)
  done

lemma vs_lookup_clear_asid_table:
  "vs_lookup_table bot_level asid vref (s\<lparr>arch_state := arch_state s \<lparr>riscv_asid_table :=
                                            (riscv_asid_table (arch_state s)) (pptr := None)\<rparr>\<rparr>)
     = Some (level, p)
   \<Longrightarrow> vs_lookup_table bot_level asid vref s = Some (level, p)"
  by (fastforce simp: vs_lookup_table_def in_omonad pool_for_asid_def split: if_split_asm)

lemma vs_lookup_target_clear_asid_table:
  "vs_lookup_target bot_level asid vref (s\<lparr>arch_state := arch_state s \<lparr>riscv_asid_table :=
                                            (riscv_asid_table (arch_state s)) (pptr := None)\<rparr>\<rparr>)
     = Some (level, p)
  \<Longrightarrow> vs_lookup_target bot_level asid vref s = Some (level, p)"
  apply (clarsimp simp: vs_lookup_target_def in_omonad vs_lookup_slot_def split: if_split_asm)
   apply (fastforce dest!: vs_lookup_clear_asid_table)
  apply (erule disjE, fastforce dest!: vs_lookup_clear_asid_table)
  apply clarify
  apply (drule vs_lookup_clear_asid_table)
  apply simp
  apply blast
  done

lemma valid_arch_state_unmap_strg:
  "valid_arch_state s \<longrightarrow>
   valid_arch_state(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_arch_state_def valid_asid_table_def)
  apply (rule conjI)
   apply (clarsimp simp add: ran_def)
   apply blast
  apply (clarsimp simp: inj_on_def)
  done


lemma valid_vspace_objs_unmap_strg:
  "valid_vspace_objs s \<longrightarrow>
   valid_vspace_objs(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vspace_objs_def)
  apply (blast dest: vs_lookup_clear_asid_table)
  done


lemma valid_vs_lookup_unmap_strg:
  "valid_vs_lookup s \<longrightarrow>
   valid_vs_lookup(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(ptr := None)\<rparr>\<rparr>)"
  apply (clarsimp simp: valid_vs_lookup_def)
  apply (blast dest: vs_lookup_target_clear_asid_table)
  done

lemma asid_high_bits_shl:
  "is_aligned base asid_low_bits \<Longrightarrow> ucast (asid_high_bits_of base) << asid_low_bits = base"
  unfolding asid_high_bits_of_def asid_low_bits_def is_aligned_mask
  by word_eqI_solve

lemma valid_asid_map_unmap:
  "valid_asid_map s \<and> is_aligned base asid_low_bits \<longrightarrow>
   valid_asid_map(s\<lparr>arch_state := arch_state s\<lparr>riscv_asid_table := (riscv_asid_table (arch_state s))(asid_high_bits_of base := None)\<rparr>\<rparr>)"
  by (clarsimp simp: valid_asid_map_def)

lemma asid_low_bits_word_bits:
  "asid_low_bits < word_bits"
  by (simp add: asid_low_bits_def word_bits_def)

lemma valid_vs_lookup_arch_update:
  "riscv_asid_table (f (arch_state s)) = riscv_asid_table (arch_state s) \<and>
   riscv_kernel_vspace (f (arch_state s)) = riscv_kernel_vspace (arch_state s)
     \<Longrightarrow> valid_vs_lookup (arch_state_update f s) = valid_vs_lookup s"
  by (simp add: valid_vs_lookup_def)

definition valid_unmap :: "vmpage_size \<Rightarrow> asid * vspace_ref \<Rightarrow> bool" where
  "valid_unmap sz \<equiv> \<lambda>(asid, vptr). 0 < asid \<and> is_aligned vptr (pageBitsForSize sz)"

definition
  "parent_for_refs \<equiv> \<lambda>(_, slot) cap.
     \<exists>m. cap = ArchObjectCap (PageTableCap (table_base slot) m) \<and> m \<noteq> None"

definition
  "same_ref \<equiv> \<lambda>(pte, slot) cap s.
     ((\<exists>p. pte_ref pte = Some p \<and> obj_refs cap = {p}) \<or> pte = InvalidPTE) \<and>
     (\<exists>level asid vref. vs_cap_ref cap = Some (asid, vref_for_level vref level) \<and>
                        vs_lookup_slot level asid vref s = Some (level, slot) \<and>
                        vref \<in> user_region \<and> level \<le> max_pt_level)"

definition
  "valid_page_inv pg_inv \<equiv> case pg_inv of
    PageMap acap ptr m \<Rightarrow>
      cte_wp_at (is_arch_update (ArchObjectCap acap)) ptr
      and (cte_wp_at (\<lambda>c. vs_cap_ref c = None) ptr or (\<lambda>s. cte_wp_at (\<lambda>c. same_ref m c s) ptr s))
      and cte_wp_at is_frame_cap ptr
      and same_ref m (ArchObjectCap acap)
      and valid_slots m
      and valid_arch_cap acap
      and K (is_PagePTE (fst m) \<or> fst m = InvalidPTE)
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
  | PageUnmap acap cslot \<Rightarrow>
     \<lambda>s. \<exists>dev r R sz m.
            acap = FrameCap r R sz dev m \<and>
            case_option True (valid_unmap sz) m \<and>
            cte_wp_at ((=) (ArchObjectCap acap)) cslot s \<and>
            valid_arch_cap acap s
  | PageGetAddr ptr \<Rightarrow> \<top>"

definition
  "valid_pti pti \<equiv> case pti of
     PageTableMap acap cslot pte pt_slot \<Rightarrow>
       pte_at pt_slot and K (wellformed_pte pte \<and> is_PageTablePTE pte) and
       valid_arch_cap acap and
       cte_wp_at (\<lambda>c. is_arch_update (ArchObjectCap acap) c \<and> cap_asid c = None) cslot and
       invalid_pte_at pt_slot and
       (\<lambda>s. \<exists>p' level asid vref.
                vs_cap_ref_arch acap = Some (asid, vref_for_level vref level)
                \<and> vs_lookup_slot level asid vref s = Some (level, pt_slot)
                \<and> valid_pte level pte s
                \<and> pte_ref pte = Some p' \<and> obj_refs (ArchObjectCap acap) = {p'}
                \<and> (\<exists>ao. ko_at (ArchObj ao) p' s \<and> valid_vspace_obj (level-1) ao s)
                \<and> pts_of s p' = Some empty_pt
                \<and> vref \<in> user_region) and
       K (is_PageTableCap acap \<and> cap_asid_arch acap \<noteq> None)
   | PageTableUnmap acap cslot \<Rightarrow>
       cte_wp_at ((=) (ArchObjectCap acap)) cslot
       and real_cte_at cslot
       and valid_arch_cap acap
       and is_final_cap' (ArchObjectCap acap)
       and K (is_PageTableCap acap)
       and (\<lambda>s. \<forall>asid vref. vs_cap_ref_arch acap = Some (asid, vref) \<longrightarrow>
                            vspace_for_asid asid s \<noteq> aobj_ref acap)"

crunches unmap_page
  for aligned [wp]: pspace_aligned
  and "distinct" [wp]: pspace_distinct
  and valid_objs[wp]: valid_objs
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  (wp: crunch_wps simp: crunch_simps)

lemma set_cap_valid_slots[wp]:
  "set_cap cap p \<lbrace>valid_slots slots\<rbrace>"
  apply (cases slots, clarsimp simp: valid_slots_def)
  apply (wpsimp wp: hoare_vcg_ball_lift hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply blast
  done

lemma pt_lookup_from_level_inv[wp]:
  "\<lbrace>Q and E\<rbrace> pt_lookup_from_level level pt_ptr vptr target_pt_ptr \<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>_. E\<rbrace>"
proof (induct level arbitrary: pt_ptr)
  case 0
  then show ?case by (wpsimp simp: pt_lookup_from_level_simps)
next
  case (minus level)
  note IH = minus(1)
  from \<open>0 < level\<close>  show ?case by (subst pt_lookup_from_level_simps) (wpsimp wp: IH)
qed

crunches unmap_page_table
  for aligned[wp]: pspace_aligned
  and valid_objs[wp]: valid_objs
  and "distinct"[wp]: pspace_distinct
  and caps_of_state[wp]: "\<lambda>s. P (caps_of_state s)"
  and typ_at[wp]: "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps)


definition
  "valid_apinv ap \<equiv> case ap of
    Assign asid p slot \<Rightarrow>
      (\<lambda>s. \<exists>pool. asid_pools_of s p = Some pool \<and> pool (ucast asid) = None)
      and cte_wp_at (\<lambda>cap. is_pt_cap cap \<and> cap_asid cap = None) slot
      and K (0 < asid)
      and (\<lambda>s. pool_for_asid asid s = Some p)"

crunch device_state_inv[wp]: ackInterrupt "\<lambda>ms. P (device_state ms)"

lemmas setIRQTrigger_irq_masks = no_irq[OF no_irq_setIRQTrigger]

lemma dmo_setIRQTrigger_invs[wp]: "\<lbrace>invs\<rbrace> do_machine_op (setIRQTrigger irq b) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
   apply (simp add: machine_op_lift_device_state setIRQTrigger_def)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid)
     apply ((wpsimp simp: setIRQTrigger_def machine_op_lift_def machine_rest_lift_def split_def)+)[3]
  apply (erule (1) use_valid[OF _ setIRQTrigger_irq_masks])
  done

lemma dmo_ackInterrupt[wp]: "\<lbrace>invs\<rbrace> do_machine_op (ackInterrupt irq) \<lbrace>\<lambda>y. invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p" in use_valid)
     apply ((clarsimp simp: ackInterrupt_def machine_op_lift_def
                            machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ ackInterrupt_irq_masks])
  done

lemma dmo_setVMRoot[wp]:
  "do_machine_op (setVSpaceRoot pt asid) \<lbrace>invs\<rbrace>"
  apply (wp dmo_invs)
  apply (auto simp: setVSpaceRoot_def machine_op_lift_def machine_rest_lift_def in_monad select_f_def)
  done

lemma dmo_sfence[wp]:
  "do_machine_op sfence \<lbrace>invs\<rbrace>"
  apply (wp dmo_invs)
  apply (auto simp: sfence_def machine_op_lift_def machine_rest_lift_def in_monad select_f_def)
  done

lemma find_vspace_for_asid_inv[wp]:
  "\<lbrace>P and Q\<rbrace> find_vspace_for_asid asid \<lbrace>\<lambda>_. P\<rbrace>, \<lbrace>\<lambda>_. Q\<rbrace>"
  unfolding find_vspace_for_asid_def by wpsimp

lemma set_vm_root_typ_at[wp]:
  "set_vm_root t \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  unfolding set_vm_root_def
  by (wpsimp simp: if_distribR wp: get_cap_wp)

lemma set_vm_root_invs[wp]:
  "set_vm_root t \<lbrace>invs\<rbrace>"
  unfolding set_vm_root_def
  by (wpsimp simp: if_distribR wp: get_cap_wp)

lemma svr_pred_st_tcb[wp]:
  "set_vm_root t' \<lbrace>\<lambda>s. Q (pred_tcb_at proj P t s)\<rbrace>"
  unfolding set_vm_root_def by (wpsimp wp: get_cap_wp)

lemmas set_vm_root_typ_ats [wp] = abs_typ_at_lifts [OF set_vm_root_typ_at]

lemma valid_pte_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pte level pte s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pte level pte s)\<rbrace>"
  apply (cases P rule: bool_to_bool_cases; wpsimp; cases pte)
       apply (wpsimp simp:data_at_def wp: hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  done


lemma set_cap_valid_pte_stronger:
  "set_cap cap p \<lbrace>\<lambda>s. P (valid_pte level pte s)\<rbrace>"
  by (wp valid_pte_lift3 set_cap_typ_at)


(* FIXME: move *)
lemma valid_cap_to_pt_cap:
  "\<lbrakk>valid_cap c s; obj_refs c = {p}; pt_at p s\<rbrakk> \<Longrightarrow> is_pt_cap c"
  by (clarsimp simp: valid_cap_def obj_at_def is_obj_defs is_pt_cap_def valid_arch_cap_ref_def
              split: cap.splits option.splits arch_cap.splits if_splits)

lemma set_cap_invalid_pte[wp]:
  "set_cap cap p' \<lbrace>invalid_pte_at p\<rbrace>"
  unfolding invalid_pte_at_def by wpsimp

lemma valid_cap_obj_ref_pt:
  "\<lbrakk> s \<turnstile> cap; s \<turnstile> cap'; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> is_pt_cap cap \<longrightarrow> is_pt_cap cap'"
  by (auto simp: is_cap_simps valid_cap_def valid_arch_cap_ref_def
                 obj_at_def is_ep is_ntfn is_cap_table is_tcb is_reply is_sc_obj a_type_def
          split: cap.split_asm if_split_asm arch_cap.split_asm option.split_asm)

lemma is_pt_cap_asid_None_table_ref:
  "is_pt_cap cap \<Longrightarrow> (table_cap_ref cap = None) = (cap_asid cap = None)"
  by (auto simp: is_cap_simps table_cap_ref_def cap_asid_def
          split: option.split_asm)

lemma no_cap_to_obj_with_diff_ref_map:
  "\<lbrakk> caps_of_state s p = Some cap; is_pt_cap cap;
     table_cap_ref cap = None;
     unique_table_caps s;
     valid_objs s; obj_refs cap = obj_refs cap' \<rbrakk>
       \<Longrightarrow> no_cap_to_obj_with_diff_ref cap' {p} s"
  apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                        cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid_cap[where p=p])
  apply (frule(1) caps_of_state_valid_cap[where p="(a, b)" for a b])
  apply (drule(1) valid_cap_obj_ref_pt, simp)
  apply (drule(1) unique_table_capsD[rotated, where cps="caps_of_state s"]; simp?)
  apply (simp add: vs_cap_ref_table_cap_ref_eq)
  done

lemmas store_pte_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pte_caps_of_state]

lemma mdb_cte_at_store_pte[wp]:
  "store_pte y pte \<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wpsimp wp: hoare_vcg_disj_lift hoare_vcg_all_lift simp: store_pte_def set_pt_def)
  done

crunches store_pte
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"

(* FIXME: move *)
lemma vs_cap_ref_table_cap_ref_None:
  "vs_cap_ref x = None \<Longrightarrow> table_cap_ref x = None"
  by (simp add: vs_cap_ref_def arch_cap_fun_lift_def vs_cap_ref_arch_def
         split: cap.splits arch_cap.splits)

(* FIXME: move *)
lemma master_cap_eq_is_device_cap_eq:
  "cap_master_cap c = cap_master_cap d \<Longrightarrow> cap_is_device c = cap_is_device d"
  by (simp add: cap_master_cap_def
         split: cap.splits arch_cap.splits)

lemma vs_cap_ref_eq_imp_table_cap_ref_eq':
  "\<lbrakk> vs_cap_ref cap = vs_cap_ref cap'; cap_master_cap cap = cap_master_cap cap' \<rbrakk>
   \<Longrightarrow> table_cap_ref cap = table_cap_ref cap'"
  by (simp add: vs_cap_ref_def vs_cap_ref_arch_def arch_cap_fun_lift_def cap_master_cap_def
           split: cap.splits arch_cap.splits option.splits prod.splits)

lemma arch_update_cap_invs_map:
  "\<lbrace>cte_wp_at (is_arch_update cap and
               (\<lambda>c. \<forall>r. vs_cap_ref c = Some r \<longrightarrow> vs_cap_ref cap = Some r)) p
             and invs and valid_cap cap\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (clarsimp simp: cte_wp_at_caps_of_state
              simp del: imp_disjL)
  apply (frule(1) valid_global_refsD2)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (clarsimp simp: is_cap_simps is_arch_update_def
              simp del: imp_disjL)
  apply (frule master_cap_cap_range, simp del: imp_disjL)
  apply (thin_tac "cap_range a = cap_range b" for a b)
  apply (rule conjI)
   apply (clarsimp simp: is_valid_vtable_root_def vs_cap_ref_def vs_cap_ref_arch_def split: cap.splits)
   apply (simp split: arch_cap.splits option.splits;
          clarsimp simp: cap_master_cap_simps vs_cap_ref_arch_def)
  apply (rule conjI)
   apply (rule ext)
   apply (simp add: cap_master_cap_def split: cap.splits arch_cap.splits)
  apply (rule context_conjI)
   apply (simp add: appropriate_cte_cap_irqs)
   apply (clarsimp simp: cap_irqs_def cap_irq_opt_def cap_master_cap_def
                  split: cap.split)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def cap_master_cap_def
                  split: cap.split_asm)
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply simp
  apply (rule conjI)
   apply (frule master_cap_obj_refs)
   apply (case_tac "table_cap_ref capa =
                    table_cap_ref (ArchObjectCap a)")
    apply (frule unique_table_refs_no_cap_asidE[where S="{p}"])
     apply (simp add: valid_arch_caps_def)
    apply (simp add: no_cap_to_obj_with_diff_ref_def Ball_def)
   apply (case_tac "table_cap_ref capa")
    apply clarsimp
    apply (erule no_cap_to_obj_with_diff_ref_map,
           simp_all)[1]
      apply (clarsimp simp: table_cap_ref_def cap_master_cap_simps
                            is_cap_simps table_cap_ref_arch_def
                     split: cap.split_asm arch_cap.split_asm
                     dest!: cap_master_cap_eqDs)
     apply (simp add: valid_arch_caps_def)
    apply (simp add: valid_pspace_def)
   apply (erule swap)
   apply (rule vs_cap_ref_eq_imp_table_cap_ref_eq')
    apply (frule table_cap_ref_vs_cap_ref_Some)
    apply fastforce
   apply fastforce
  apply (rule conjI)
   apply (clarsimp simp del: imp_disjL)
   apply (clarsimp simp: is_pt_cap_def cap_master_cap_simps
                         cap_asid_def vs_cap_ref_def
                  dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
   apply (drule valid_table_capsD[OF caps_of_state_cteD])
      apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
     apply (simp add: is_pt_cap_def)
    apply (simp add: cap_asid_def split: option.splits)
   apply simp
  apply (clarsimp simp: is_cap_simps is_pt_cap_def cap_master_cap_simps
                        cap_asid_def vs_cap_ref_def ranI
                 dest!: cap_master_cap_eqDs split: option.split_asm if_split_asm
                 elim!: ranE cong: master_cap_eq_is_device_cap_eq
             | rule conjI)+
  apply (clarsimp dest!: master_cap_eq_is_device_cap_eq)
  done

lemma pool_for_asid_ap_at:
  "\<lbrakk> pool_for_asid asid s = Some p; valid_arch_state s \<rbrakk> \<Longrightarrow> asid_pool_at p s"
  by (fastforce dest!: pool_for_asid_validD simp: valid_arch_state_def asid_pools_at_eq)

lemma arch_update_cap_invs_unmap_page:
  "\<lbrace>(\<lambda>s. \<exists>cap'.
             caps_of_state s p = Some cap' \<and>
             (\<forall>p'\<in>obj_refs cap'.
                 \<forall>asid vref.
                    vs_cap_ref cap' = Some (asid, vref) \<longrightarrow>
                    (\<forall>level. vs_lookup_target level asid vref s \<noteq> Some (level, p'))) \<and>
             is_arch_update cap cap')
             and invs and valid_cap cap
             and K (is_frame_cap cap)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: cte_wp_at_caps_of_state)
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps
                        fun_eq_iff appropriate_cte_cap_irqs
                        is_pt_cap_def is_valid_vtable_root_def
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   subgoal by (simp add: cap_range_def)
  apply (rule conjI)
   apply (clarsimp simp: reachable_target_def reachable_frame_cap_def)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: valid_cap_def obj_at_def split: if_split_asm)
  apply (rule conjI[rotated])
   apply (frule(1) cap_refs_in_kernel_windowD)
   apply (simp add: cap_range_def)
  apply (drule unique_table_refs_no_cap_asidE[where S="{p}"])
   apply (simp add: valid_arch_caps_def)
  apply (simp add: no_cap_to_obj_with_diff_ref_def table_cap_ref_def Ball_def)
  done

lemma mask_cap_PageTableCap[simp]:
  "mask_cap R (ArchObjectCap (PageTableCap p data)) = ArchObjectCap (PageTableCap p data)"
  by (clarsimp simp: mask_cap_def cap_rights_update_def acap_rights_update_def)

lemma arch_update_cap_pspace':
  "\<lbrace>cte_wp_at (is_arch_update cap) p and real_cte_at p and valid_pspace and valid_cap cap\<rbrace>
   set_cap cap p
   \<lbrace>\<lambda>_. valid_pspace\<rbrace>"
  apply (simp add: valid_pspace_def)
  apply (rule hoare_pre)
   apply (wp set_cap_valid_objs update_cap_iflive arch_update_cap_zombies)
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def)
  apply (frule cap_master_cap_zobj_refs)
  apply clarsimp
  apply (drule caps_of_state_cteD)
  apply (drule (1) cte_wp_tcb_cap_valid)
  apply (erule real_cte_tcb_valid[rule_format])
  done

lemma arch_update_cap_invs_unmap_page_table:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and real_cte_at p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and (\<lambda>s. pts_of s (obj_ref_of cap) = Some empty_pt)
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>asid vref level. vs_cap_ref c = Some (asid, vref)
                                \<longrightarrow> vs_lookup_target level asid vref s \<noteq> Some (level, obj_ref_of cap)) p s)
             and K (is_pt_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace' arch_update_cap_valid_mdb set_cap_idle
             update_cap_ifunsafe valid_irq_node_typ set_cap_typ_at
             set_cap_irq_handlers set_cap_valid_arch_caps
             set_cap_cap_refs_respects_device_region_spec[where ptr = p])
  apply (simp add: final_cap_at_eq)
  apply (clarsimp simp: cte_wp_at_caps_of_state is_arch_update_def
                        is_cap_simps cap_master_cap_simps is_valid_vtable_root_def
                        appropriate_cte_cap_irqs is_pt_cap_def
                        fun_eq_iff[where f="cte_refs cap" for cap]
                 dest!: cap_master_cap_eqDs
              simp del: imp_disjL)
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   apply (simp add: cap_range_def)
  apply (frule(1) cap_refs_in_kernel_windowD)
  apply (simp add: cap_range_def gen_obj_refs_def image_def)
  apply (rule conjI)
   apply (clarsimp simp: reachable_target_def reachable_frame_cap_def)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: valid_cap_def obj_at_def split: if_split_asm)
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def in_omonad)
  apply fastforce
  done

lemma global_refs_arch_update_eq:
  "riscv_global_pts (f (arch_state s)) = riscv_global_pts (arch_state s) \<Longrightarrow>
   global_refs (arch_state_update f s) = global_refs s"
  by (simp add: global_refs_def)

lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> (level,p)) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
            \<and> pt_at p s
        \<longrightarrow> p \<notin> global_refs s"
  apply clarsimp
  apply (cases "level = asid_pool_level"; simp)
   apply (simp add: vs_lookup_table_def in_omonad)
   apply (drule (1) pool_for_asid_ap_at)
   apply (clarsimp simp: obj_at_def)
  apply (drule (1) vs_lookup_table_target)
  apply (drule valid_vs_lookupD; clarsimp simp: vref_for_level_user_region)
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  done

lemma no_irq_sfence[wp,intro!]: "no_irq sfence"
  by (wpsimp simp: sfence_def no_irq_def machine_op_lift_def machine_rest_lift_def)

lemma pt_lookup_from_level_wp:
  "\<lbrace>\<lambda>s. (\<forall>level pt' pte.
            pt_walk top_level level top_level_pt vref (ptes_of s) = Some (level, pt') \<longrightarrow>
            ptes_of s (pt_slot_offset level pt' vref) = Some pte \<longrightarrow>
            is_PageTablePTE pte \<longrightarrow>
            pte_ref pte = Some pt \<longrightarrow>
            Q (pt_slot_offset level pt' vref) s) \<and>
        ((\<forall>level < top_level.
            pt_walk top_level level top_level_pt vref (ptes_of s) \<noteq> Some (level, pt)) \<longrightarrow>
            E InvalidRoot s)\<rbrace>
  pt_lookup_from_level top_level top_level_pt vref pt
  \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
proof (induct top_level arbitrary: top_level_pt)
  case 0
  then show ?case
    by (wpsimp simp: pt_lookup_from_level_simps)
next
  case (minus top_level)
  note IH=minus(1)
  from \<open>0 < top_level\<close>
  show ?case
    apply (subst pt_lookup_from_level_simps)
    apply (wpsimp wp: IH)
    apply (rule conjI; clarsimp)
     prefer 2
     apply (subst (asm) (2) pt_walk.simps)
     apply (clarsimp)
    apply (rule conjI; clarsimp)
     apply (erule_tac x="top_level" in allE)
     apply (clarsimp simp: in_omonad is_PageTablePTE_def pptr_from_pte_def)
    apply (rule conjI; clarsimp)
     apply (rename_tac pt' pte)
     apply (frule pt_walk_max_level)
     apply (erule_tac x=level in allE)
     apply (erule_tac x=pt' in allE)
     apply simp
     apply (erule mp)
     apply (subst pt_walk.simps)
     apply (simp add: in_omonad bit0.leq_minus1_less)
    apply (subst (asm) (3) pt_walk.simps)
    apply (case_tac "level = top_level - 1"; clarsimp)
    apply (subgoal_tac "level < top_level - 1", fastforce)
    apply (frule bit0.zero_least)
    apply (subst (asm) bit0.leq_minus1_less[symmetric], assumption)
    apply simp
    done
qed

(* weaker than pspace_aligned_pts_ofD, but still sometimes useful because it matches better *)
lemma pts_of_Some_alignedD:
  "\<lbrakk> pts_of s p = Some pt; pspace_aligned s \<rbrakk> \<Longrightarrow> is_aligned p pt_bits"
  by (drule pspace_aligned_pts_ofD; simp)

lemma vs_lookup_target_not_global:
  "\<lbrakk> vs_lookup_target level asid vref s = Some (level, pt); vref \<in> user_region; invs s \<rbrakk>
   \<Longrightarrow> pt \<notin> global_refs s"
  apply (drule (1) valid_vs_lookupD; clarsimp)
  apply (drule valid_global_refsD2; clarsimp)
  apply (simp add: cap_range_def)
  done

lemma reachable_page_table_not_global:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); level \<le> max_pt_level;
     vref \<in> user_region; invs s\<rbrakk>
   \<Longrightarrow> p \<notin> global_refs s"
  apply (drule (1) vs_lookup_table_target)
  apply (erule vs_lookup_target_not_global)
   apply (erule vref_for_level_user_region)
  apply assumption
  done

lemma unmap_page_table_invs[wp]:
  "\<lbrace>invs and K (vaddr \<in> user_region)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_page_table_def)
  apply (rule hoare_pre)
   apply (wp dmo_invs | wpc | simp)+
     apply (rule_tac Q="\<lambda>_. invs" in hoare_post_imp)
      apply safe
       apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                  underlying_memory m p" in use_valid)
         apply ((wp | simp)+)[3]
      apply(erule use_valid, wp no_irq, assumption)
     apply (wpsimp wp: store_pte_invs_unmap pt_lookup_from_level_wp)+
  apply (frule pt_walk_max_level)
  apply (drule (2) pt_lookup_vs_lookupI)
  apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (frule pts_of_Some_alignedD; clarsimp)
  apply (rule conjI)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region, clarsimp)
   apply clarsimp
   apply (frule (1) cap_to_pt_is_pt_cap; clarsimp?)
    apply (fastforce intro: valid_objs_caps)
   apply (fastforce simp: is_cap_simps)
  apply (rule conjI; clarsimp?)
   apply (drule (3) vs_lookup_table_vspace)
   apply (simp add: table_index_max_level_slots)
  apply (drule (1) vs_lookup_table_target)
  apply (drule vs_lookup_target_not_global, erule vref_for_level_user_region; simp)
  done

lemma final_cap_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (is_final_cap' cap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_final_cap' cap s)\<rbrace>"
  by (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state, rule x)

lemmas dmo_final_cap[wp] = final_cap_lift [OF do_machine_op_caps_of_state]
lemmas store_pte_final_cap[wp] = final_cap_lift [OF store_pte_caps_of_state]
lemmas unmap_page_table_final_cap[wp] = final_cap_lift [OF unmap_page_table_caps_of_state]

lemma store_pte_vspace_for_asid[wp]:
  "store_pte p pte \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  by (wp vspace_for_asid_lift)

lemma mapM_swp_store_pte_invs_unmap:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>sl\<in>set slots. table_base sl \<notin> global_refs s \<and>
                        (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base sl))) and
    K (pte = InvalidPTE)\<rbrace>
  mapM (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (wp store_pte_invs hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_all_lift)
   apply (clarsimp simp: wellformed_pte_def)
  apply simp
  done

lemma mapM_x_swp_store_pte_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl \<in> set slots. table_base sl \<notin> global_refs s \<and>
                                    (\<forall>asid. vspace_for_asid asid s \<noteq> Some (table_base sl))) and
    K (pte = InvalidPTE)\<rbrace>
  mapM_x (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pte_invs_unmap)+

lemma vs_lookup_table_step:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, pt'); level \<le> max_pt_level; 0 < level;
     ptes_of s (pt_slot_offset level pt' vref) = Some pte; is_PageTablePTE pte;
     pte_ref pte = Some pt \<rbrakk> \<Longrightarrow>
    vs_lookup_table (level-1) asid vref s = Some (level-1, pt)"
  apply (subst vs_lookup_split_Some[where level'=level]; assumption?)
   apply (simp add: order_less_imp_le)
  apply (subst pt_walk.simps)
  apply (clarsimp simp: in_omonad is_PageTablePTE_def pptr_from_pte_def)
  done

lemma pte_ref_Some_cases:
  "(pte_ref pte = Some ref) = ((is_PageTablePTE pte \<or> is_PagePTE pte) \<and> ref = pptr_from_pte pte)"
  by (cases pte) (auto simp: pptr_from_pte_def)

lemma max_pt_level_eq_minus_one:
  "level - 1 = max_pt_level \<Longrightarrow> level = asid_pool_level"
  unfolding level_defs by auto

lemma store_pte_invalid_vs_lookup_target_unmap:
  "\<lbrace>\<lambda>s. (\<exists>level'. vs_lookup_slot level' asid vref s = Some (level', p) \<and>
                  pte_refs_of s p = Some p') \<and>
         vref \<in> user_region \<and>
         pspace_aligned s \<and> valid_asid_table s \<and> valid_vspace_objs s \<and>
         unique_table_refs s \<and> valid_vs_lookup s \<and> valid_caps (caps_of_state s) s \<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. vs_lookup_target level asid vref s \<noteq> Some (level, p')\<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp simp: obj_at_def)
  apply (prop_tac "level' \<le> max_pt_level")
   apply (clarsimp simp: vs_lookup_slot_def pool_for_asid_vs_lookup split: if_split_asm)
   apply (drule (1) pool_for_asid_validD)
   apply (clarsimp simp: obj_at_def in_omonad)
   apply (frule_tac p=p in pspace_alignedD, assumption)
   apply (simp add: bit_simps)
  apply (frule (5) valid_vspace_objs_strong_slotD)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (clarsimp simp: in_omonad pte_ref_Some_cases)
  apply (rename_tac pt_ptr pte)
  apply (frule (5) vs_lookup_table_is_aligned)
  apply clarsimp
  apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def pool_for_asid_vs_lookup
                  split: if_split_asm)
   apply (prop_tac "asid_pools_of s pt_ptr = None")
    apply (clarsimp simp: opt_map_def)
   apply simp
   apply (prop_tac "vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, p')")
    apply (clarsimp simp: vs_lookup_table_def in_omonad)
   apply (erule disjE)
    (* PageTablePTE: level' would have to be asid_pool_level, contradiction *)
    apply (drule (1) vs_lookup_table_step; simp?)
      apply (rule ccontr)
      apply (clarsimp simp flip: bit0.neq_0_conv simp: is_PageTablePTE_def)
     apply (fastforce simp: pte_ref_Some_cases)
    apply (drule (1) no_loop_vs_lookup_table; simp?)
   (* PagePTE *)
   apply (prop_tac "\<exists>sz. data_at sz p' s")
    apply (fastforce simp: is_PagePTE_def pptr_from_pte_def)
   apply clarsimp
   apply (drule (2) valid_vspace_objs_strongD[where level=max_pt_level]; clarsimp)
   apply (fastforce simp: data_at_def obj_at_def in_omonad)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pt_ptr' pte')
  apply (case_tac "level' \<le> level")
   apply (drule (9) vs_lookup_table_fun_upd_deep_idem)
   apply (frule (5) vs_lookup_table_is_aligned[where bot_level=level])
   apply (clarsimp simp: ptes_of_def fun_upd_apply in_omonad split: if_split_asm)
    apply (drule (1) no_loop_vs_lookup_table; simp)
   apply (rename_tac pt')
   apply (case_tac "level' = level", simp)
   apply (prop_tac "valid_pte level (pt' (table_index (pt_slot_offset level pt_ptr' vref))) s")
    apply (drule (2) valid_vspace_objsD[where bot_level=level])
     apply (simp add: in_omonad)
    apply simp
    apply (drule_tac x="table_index (pt_slot_offset level pt_ptr' vref)" in bspec)
     apply (fastforce dest: table_index_max_level_slots)
    apply fastforce
   apply (erule disjE)
    (* PageTablePTE *)
    apply (prop_tac "is_PageTablePTE (pt' (table_index (pt_slot_offset level pt_ptr' vref)))")
     apply (case_tac "pt' (table_index (pt_slot_offset level pt_ptr' vref))"; simp)
     apply (clarsimp simp: is_PageTablePTE_def obj_at_def data_at_def pptr_from_pte_def)
    apply (drule (1) vs_lookup_table_step; simp?)
      apply (rule ccontr)
      apply (clarsimp simp flip: bit0.neq_0_conv simp: is_PageTablePTE_def)
     apply (clarsimp simp: ptes_of_def in_omonad)
    apply (drule (1) vs_lookup_table_step)
           apply (rule ccontr)
           apply (clarsimp simp flip: bit0.neq_0_conv simp: is_PageTablePTE_def)
          apply (clarsimp simp: ptes_of_def in_omonad)
          apply (rule refl)
         apply simp
        apply (simp add: pte_ref_Some_cases)
    apply (simp add: pte_ref_Some_cases)
    apply (drule (1) no_loop_vs_lookup_table; simp)
   apply (prop_tac "\<not>is_PageTablePTE (pt' (table_index (pt_slot_offset level pt_ptr' vref)))")
     apply (case_tac "pt' (table_index (pt_slot_offset level pt_ptr' vref))"; simp)
     apply (clarsimp simp: is_PagePTE_def obj_at_def data_at_def pptr_from_pte_def)
   apply (drule_tac level=level' and level'=level in vs_lookup_splitD; clarsimp)
   apply (subst (asm) pt_walk.simps)
   apply (clarsimp simp: in_omonad ptes_of_def split: if_split_asm)
  apply (simp add: not_le)
   apply (drule_tac level=level and level'=level' in vs_lookup_splitD; simp?)
  apply clarsimp
  apply (drule (1) vs_lookup_table_fun_upd_deep_idem; simp)
  apply (subst (asm) pt_walk.simps)
  apply (clarsimp simp: in_omonad)
  apply (subst (asm) (3) pte_of_def)
  apply (clarsimp simp: in_omonad fun_upd_apply split: if_split_asm)
  done

lemma pt_lookup_from_level_wrp:
  "\<lbrace>\<lambda>s. \<exists>asid. vspace_for_asid asid s = Some top_level_pt \<and>
               (\<forall>level slot pte.
                   vs_lookup_slot level asid vref s = Some (level, slot) \<longrightarrow>
                   ptes_of s slot = Some pte \<longrightarrow>
                   is_PageTablePTE pte \<longrightarrow>
                   pte_ref pte = Some pt \<longrightarrow>
                   Q slot s) \<and>
               ((\<forall>level<max_pt_level. vs_lookup_table level asid vref s \<noteq> Some (level, pt)) \<longrightarrow>
                   E InvalidRoot s)\<rbrace>
   pt_lookup_from_level max_pt_level top_level_pt vref pt
   \<lbrace>Q\<rbrace>, \<lbrace>E\<rbrace>"
  apply (wp pt_lookup_from_level_wp)
  apply (clarsimp simp: vspace_for_asid_def)
  apply (rule conjI; clarsimp)
   apply (frule pt_walk_max_level)
   apply (erule_tac x=level in allE)
   apply (erule allE, erule impE[where P="f = Some x" for f x])
    apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def in_omonad)
    apply fastforce
   apply simp
  apply (erule allE, erule (1) impE)
  apply (clarsimp simp: vs_lookup_table_def split: if_split_asm)
  done

lemma unmap_page_table_not_target:
  "\<lbrace>\<lambda>s. pt_at pt s \<and> pspace_aligned s \<and> valid_asid_table s \<and> valid_vspace_objs s \<and>
        unique_table_refs s \<and> valid_vs_lookup s \<and> valid_caps (caps_of_state s) s \<and>
        0 < asid \<and> vref \<in> user_region \<and> vspace_for_asid asid s \<noteq> Some pt \<and>
        asid' = asid \<and> pt' = pt \<and> vref' = vref \<rbrace>
   unmap_page_table asid vref pt
   \<lbrace>\<lambda>_ s. vs_lookup_target level asid' vref' s \<noteq> Some (level, pt')\<rbrace>"
  unfolding unmap_page_table_def
  apply (wpsimp wp: store_pte_invalid_vs_lookup_target_unmap pt_lookup_from_level_wrp)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def vs_lookup_slot_def vs_lookup_table_def
                   split: if_split_asm;
          clarsimp simp: vspace_for_asid_def obind_def)
  apply (rule exI, rule conjI, assumption)
  apply (rule conjI; clarsimp)
   apply (fastforce simp: in_omonad)
  apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
   apply (clarsimp simp: pool_for_asid_vs_lookup vs_lookup_slot_def vspace_for_asid_def
                   split: if_split_asm)
  apply (rename_tac slot)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pte)
  apply (prop_tac "0 < level \<and> is_PageTablePTE pte")
   apply (drule (5) valid_vspace_objs_strong_slotD)
   apply clarsimp
   apply (case_tac pte; clarsimp simp: pte_ref_def)
   apply (clarsimp simp: data_at_def obj_at_def)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (drule (4) vs_lookup_table_step, simp)
  apply (prop_tac "level - 1 < max_pt_level", erule (1) bit0.minus_one_leq_less)
  apply fastforce
  done

lemma is_final_cap_caps_of_state_2D:
  "\<lbrakk> caps_of_state s p = Some cap; caps_of_state s p' = Some cap';
     is_final_cap' cap'' s; gen_obj_refs cap \<inter> gen_obj_refs cap'' \<noteq> {};
     gen_obj_refs cap' \<inter> gen_obj_refs cap'' \<noteq> {} \<rbrakk>
       \<Longrightarrow> p = p'"
  apply (clarsimp simp: is_final_cap'_def3)
  apply (frule_tac x="fst p" in spec)
  apply (drule_tac x="snd p" in spec)
  apply (drule_tac x="fst p'" in spec)
  apply (drule_tac x="snd p'" in spec)
  apply (clarsimp simp: cte_wp_at_caps_of_state Int_commute
                        prod_eqI)
  done

crunch underlying_memory[wp]: ackInterrupt, hwASIDFlush, read_stval, setVSpaceRoot, sfence
  "\<lambda>m'. underlying_memory m' p = um"
  (simp: cache_machine_op_defs machine_op_lift_def machine_rest_lift_def split_def)

crunches storeWord, ackInterrupt, hwASIDFlush, read_stval, setVSpaceRoot, sfence
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  and machine_times[wp]: "\<lambda>ms. P (last_machine_time ms) (time_state ms)"
  (simp: crunch_simps storeWord_def)

crunch pspace_respects_device_region[wp]: perform_page_invocation "pspace_respects_device_region"
  (simp: crunch_simps wp: crunch_wps set_object_pspace_respects_device_region
         pspace_respects_device_region_dmo)

lemma mapM_x_store_pte_caps_of_state[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma mapM_x_store_pte_valid_cap[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>valid_cap cap\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

lemma mapM_x_store_pte_final_cap[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>is_final_cap' cap\<rbrace>"
  by (wpsimp wp: final_cap_lift)

lemma mapM_x_store_pte_empty[wp]:
  "\<lbrace> \<lambda>s. slots = [p , p + (1 << pte_bits) .e. p + (1 << pt_bits) - 1] \<and>
         is_aligned p pt_bits \<and> pt_at p s \<rbrace>
   mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace> \<lambda>_ s. pts_of s p = Some empty_pt \<rbrace>"
  apply wp_pre
   apply (rule_tac I="\<lambda>s. slots = [p , p + (1 << pte_bits) .e. p + (1 << pt_bits) - 1] \<and>
                          is_aligned p pt_bits \<and> pt_at p s" and
                   V="\<lambda>xs s. \<forall>p' \<in> set slots - set xs. ptes_of s p' = Some InvalidPTE"
                   in mapM_x_inv_wp2)
    apply (clarsimp simp: obj_at_def in_omonad)
    apply (rule ext)
    apply (rename_tac idx)
    apply (clarsimp simp: ptes_of_def in_omonad)
    apply (prop_tac "p + (ucast idx << pte_bits) \<in> set slots")
     apply clarsimp
     apply (subst upto_enum_step_shift_red, simp)
       apply (simp add: bit_simps)
      apply (simp add: bit_simps)
     apply (clarsimp simp: image_iff)
     apply (rule_tac x="unat idx" in bexI)
      apply (clarsimp simp: ucast_nat_def shiftl_t2n)
     apply (clarsimp simp: bit_simps)
     apply unat_arith
     apply fastforce
    apply (fastforce simp: table_index_plus_ucast table_base_plus_ucast)
   apply (wpsimp wp: store_pte_ptes_of)
  apply simp
  done

lemma vs_lookup_slot_pool_for_asid:
  "(vs_lookup_slot asid_pool_level asid vref s = Some (level, slot)) =
   (pool_for_asid asid s = Some slot \<and> level = asid_pool_level)"
  by (auto simp: vs_lookup_slot_def vs_lookup_table_def in_omonad)

lemma ptes_of_upd:
  "\<lbrakk> pts (table_base p) = Some pt; is_aligned p pte_bits \<rbrakk> \<Longrightarrow>
   (\<lambda>p'. pte_of p' (pts(table_base p \<mapsto> pt(table_index p := pte)))) =
   ((\<lambda>p'. pte_of p' pts)(p \<mapsto> pte))"
  by (rule ext) (auto simp: pte_of_def obind_def split: option.splits dest: pte_ptr_eq)

lemma pt_walk_upd_Invalid:
  "pt_walk top_level level pt_ptr vref (ptes(p \<mapsto> InvalidPTE)) = Some (level, p') \<Longrightarrow>
   pt_walk top_level level pt_ptr vref ptes = Some (level, p')"
  apply (induct top_level arbitrary: pt_ptr, simp)
  apply (subst (asm) (3) pt_walk.simps)
  apply (clarsimp simp: in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
  apply (subst pt_walk.simps)
  apply (clarsimp simp: in_omonad)
  done

lemma store_pte_unreachable:
  "store_pte p InvalidPTE \<lbrace>\<lambda>s. vs_lookup_target level asid vref s \<noteq> Some (level, p')\<rbrace>"
  unfolding store_pte_def set_pt_def
  supply fun_upd_apply[simp del] vs_lookup_slot_pool_for_asid[simp]
  apply (wpsimp wp: set_object_wp simp: obj_at_def)
  apply (prop_tac "asid_pools_of s (table_base p) = None", clarsimp simp: opt_map_def)
  apply (erule notE)
  apply (cases "level = asid_pool_level"; clarsimp simp: vs_lookup_target_def in_omonad)
  apply (clarsimp simp: in_omonad vs_lookup_slot_def simp flip: asid_pool_level_neq
                  split: if_split_asm)
  apply (rename_tac pt_ptr)
  apply (clarsimp simp: in_omonad vs_lookup_table_def ptes_of_upd split: if_split_asm)
  apply (drule pt_walk_upd_Invalid)
  apply (clarsimp cong: conj_cong)
  apply (rule conjI, clarsimp)
  apply (clarsimp simp: ptes_of_def in_omonad fun_upd_apply split: if_split_asm)
  done

lemma mapM_x_store_pte_unreachable:
  "mapM_x (swp store_pte InvalidPTE) slots
   \<lbrace>\<lambda>s. vs_lookup_target level asid vref s \<noteq> Some (level, p)\<rbrace>"
  by (wpsimp wp: mapM_x_wp' store_pte_unreachable)

lemma mapM_x_typ_at[wp]:
  "mapM_x (swp store_pte InvalidPTE) slots \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace>"
  by (wpsimp wp: mapM_x_wp')

crunches unmap_page_table
  for global_refs[wp]: "\<lambda>s. P (global_refs s)"
  and vspace_for_asid[wp]: "\<lambda>s. P (vspace_for_asid asid s)"
  and valid_cap[wp]: "valid_cap cap"

lemma vspace_for_asid_target:
  "vspace_for_asid asid s = Some pt \<Longrightarrow>
   vs_lookup_target asid_pool_level asid 0 s = Some (asid_pool_level, pt)"
  by (clarsimp simp: vs_lookup_target_def vs_lookup_slot_pool_for_asid vspace_for_asid_def in_omonad)

lemma perform_pt_inv_unmap_invs[wp]:
  "\<lbrace>invs and valid_pti (PageTableUnmap cap ct_slot)\<rbrace> perform_pt_inv_unmap cap ct_slot \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pt_inv_unmap_def
  apply (wpsimp wp: arch_update_cap_invs_unmap_page_table get_cap_wp hoare_vcg_ex_lift
                    hoare_vcg_all_lift hoare_vcg_imp_lift' mapM_x_swp_store_pte_invs_unmap
                    mapM_x_store_pte_unreachable hoare_vcg_ball_lift
                    unmap_page_table_not_target real_cte_at_typ_valid
                simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state)
  apply (clarsimp simp: is_arch_update_def is_cap_simps is_PageTableCap_def
                        update_map_data_def valid_cap_def valid_arch_cap_def cap_aligned_def)
  apply (frule caps_of_state_valid_cap, clarsimp)
  apply (rule conjI; clarsimp)
   apply (simp add: valid_cap_def cap_aligned_def)
   apply (erule valid_table_caps_pdD, fastforce)
  apply (rename_tac p asid vref)
  apply (clarsimp simp: wellformed_mapdata_def valid_cap_def cap_aligned_def cap_master_cap_simps)
  apply (rule conjI)
   apply clarsimp
   apply (prop_tac "is_aligned p pt_bits", simp add: bit_simps)
   apply (subst (asm) upto_enum_step_shift_red; simp?)
     apply (simp add: bit_simps)
    apply (simp add: bit_simps)
   apply clarsimp
   apply (subst table_base_plus[simplified shiftl_t2n mult_ac], assumption)
    apply (simp add: mask_def bit_simps)
    apply unat_arith
    apply (subst (asm) unat_of_nat, simp)
   apply (subst table_base_plus[simplified shiftl_t2n mult_ac], assumption)
    apply (simp add: mask_def bit_simps)
    apply unat_arith
    apply (subst (asm) unat_of_nat, simp)
   apply (rule conjI; clarsimp)
    apply (drule valid_global_refsD2, clarsimp)
    apply (simp add: cap_range_def)
   apply (frule vspace_for_asid_target)
   apply (drule valid_vs_lookupD; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, clarsimp simp: in_omonad obj_at_def)
    apply (fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)
  apply (fastforce intro: valid_objs_caps simp: bit_simps)
  done

lemma set_cap_vspace_for_asid[wp]:
  "set_cap p cap \<lbrace>\<lambda>s. P (vspace_for_asid asid s)\<rbrace>"
  by (wpsimp wp: vspace_for_asid_lift)

lemma cap_asid_None_pt:
  "(cap_asid (ArchObjectCap (PageTableCap p m)) = None) = (m = None)"
  by (cases m; clarsimp simp: cap_asid_def)

lemma perform_pt_inv_map_invs[wp]:
  "\<lbrace>invs and valid_pti (PageTableMap cap ct_slot pte slot)\<rbrace>
   perform_pt_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pt_inv_map_def
  apply (wpsimp wp: store_pte_invs arch_update_cap_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps
                        is_PageTableCap_def cap_master_cap_simps invalid_pte_at_def)
  apply (rename_tac cap' p' level vref asid ao)
  apply (prop_tac "is_pt_cap cap'")
   apply (case_tac cap'; simp add: cap_master_cap_simps)
   apply (rename_tac acap, case_tac acap; simp add: cap_master_cap_simps)
  apply (clarsimp simp: is_cap_simps cap_master_cap_simps cap_asid_None_pt)
  apply (frule caps_of_state_valid_cap, fastforce)
  apply (clarsimp simp: vs_lookup_slot_def pool_for_asid_vs_lookup split: if_split_asm)
   apply (drule pool_for_asid_validD, clarsimp)
   apply (clarsimp simp: pte_at_def obj_at_def in_omonad)
   apply (frule_tac p=slot in pspace_alignedD, clarsimp)
   apply (prop_tac "is_aligned slot pt_bits", simp add: bit_simps)
   apply fastforce
  apply clarsimp
  apply (rename_tac pt_ptr)
  apply (prop_tac "is_aligned pt_ptr pt_bits", fastforce dest!: vs_lookup_table_is_aligned)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: valid_cap_def cap_aligned_def valid_arch_cap_def)
  apply (rule conjI)
   apply (erule (3) reachable_page_table_not_global)
  apply (rule conjI, clarsimp)
   apply (rename_tac level' asid' vref')
   apply (prop_tac "level' \<le> max_pt_level")
    apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
    apply (clarsimp simp: vs_lookup_table_def simp flip: asid_pool_level_neq)
    apply (drule_tac p=pt_ptr in pool_for_asid_validD, clarsimp)
    apply (clarsimp simp: in_omonad)
   apply (drule (1) vs_lookup_table_unique_level; simp)
   apply clarsimp
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: is_cap_simps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (rule conjI, clarsimp)
   apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: is_cap_simps)
   apply (thin_tac "caps_of_state s ct_slot = Some cap" for cap)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (rule conjI, clarsimp) (* top-level table, kernel_mapping_slots *)
   apply (drule vspace_for_asid_vs_lookup)
   apply (drule (1) vs_lookup_table_unique_level; clarsimp)
   apply (drule (1) table_index_max_level_slots, simp)
  apply clarsimp
  apply (rename_tac level' asid' vref')
  apply (prop_tac "level' \<le> max_pt_level")
   apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
   apply (clarsimp simp: vs_lookup_table_def simp flip: asid_pool_level_neq)
   apply (drule_tac p=pt_ptr in pool_for_asid_validD, clarsimp)
   apply (clarsimp simp: in_omonad)
  apply (frule_tac level'=level' in vs_lookup_table_unique_level, assumption; clarsimp)
  apply (rule conjI, clarsimp) (* p \<noteq> pt_ptr *)
   apply (drule (1) vs_lookup_table_target)
   apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp, fastforce intro: valid_objs_caps)
   apply (clarsimp simp: is_cap_simps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
  apply (frule pt_slot_offset_vref_for_level; simp)
  apply (cases ct_slot, fastforce)
  done

lemma perform_page_table_invocation_invs[wp]:
  "\<lbrace>invs and valid_pti pti\<rbrace> perform_page_table_invocation pti \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_page_table_invocation_def by (cases pti; wpsimp)

crunch cte_wp_at [wp]: unmap_page "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch typ_at [wp]: unmap_page "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas unmap_page_typ_ats [wp] = abs_typ_at_lifts [OF unmap_page_typ_at]

lemma pt_lookup_slot_cap_to:
  "\<lbrakk> invs s; \<exists>\<rhd>(max_pt_level, pt) s; is_aligned pt pt_bits; vptr \<in> user_region;
     pt_lookup_slot pt vptr (ptes_of s) = Some (level, slot) \<rbrakk>
   \<Longrightarrow> \<exists>p cap. caps_of_state s p = Some cap \<and> is_pt_cap cap \<and> obj_refs cap = {table_base slot} \<and>
               s \<turnstile> cap \<and> cap_asid cap \<noteq> None"
  apply (clarsimp simp: pt_lookup_slot_def pt_lookup_slot_from_level_def)
  apply (frule pt_walk_max_level)
  apply (rename_tac pt_ptr asid vref)
  apply (subgoal_tac "vs_lookup_table level asid vptr s = Some (level, pt_ptr)")
   prefer 2
   apply (drule pt_walk_level)
   apply (clarsimp simp: vs_lookup_table_def in_omonad)
  apply (frule_tac level=level in valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (drule vs_lookup_table_target[where level=level], simp)
  apply (drule valid_vs_lookupD, erule vref_for_level_user_region; clarsimp)
  apply (frule (1) cap_to_pt_is_pt_cap, simp)
   apply (fastforce intro: valid_objs_caps)
  apply (frule pts_of_Some_alignedD, fastforce)
  apply (frule caps_of_state_valid, fastforce)
  apply (fastforce simp: cap_asid_def is_cap_simps)
  done

lemma find_vspace_for_asid_cap_to:
  "\<lbrace>invs\<rbrace>
   find_vspace_for_asid asid
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> obj_refs cap = {rv} \<and>
                      is_pt_cap cap \<and> s \<turnstile> cap \<and> is_aligned rv pt_bits\<rbrace>, -"
  apply wpsimp
  apply (drule vspace_for_asid_vs_lookup)
  apply (frule valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (frule pts_of_Some_alignedD, fastforce)
  apply simp
  apply (drule vs_lookup_table_target, simp)
  apply (drule valid_vs_lookupD; clarsimp simp: vref_for_level_def)
  apply (frule (1) cap_to_pt_is_pt_cap, simp)
   apply (fastforce intro: valid_objs_caps)
  apply (fastforce intro: caps_of_state_valid cap_to_pt_is_pt_cap)
  done

lemma ex_pt_cap_eq:
  "(\<exists>ref cap. caps_of_state s ref = Some cap \<and> obj_refs cap = {p} \<and> is_pt_cap cap) =
   (\<exists>ref asid. caps_of_state s ref = Some (ArchObjectCap (PageTableCap p asid)))"
  by (fastforce simp add: is_pt_cap_def obj_refs_def is_PageTableCap_def)

lemma pt_bits_left_not_asid_pool_size:
  "pt_bits_left asid_pool_level \<noteq> pageBitsForSize sz"
  by (cases sz; simp add: pt_bits_left_def bit_simps asid_pool_level_size)

lemma unmap_page_invs:
  "\<lbrace>invs and K (vptr \<in> user_region \<and> vmsz_aligned vptr sz)\<rbrace>
   unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding unmap_page_def
  apply (wpsimp wp: store_pte_invs_unmap)
  apply (rule conjI; clarsimp)
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (rename_tac level pte pt_ptr)
  apply (drule vs_lookup_level)
  apply (frule (2) valid_vspace_objs_strongD[rotated]; clarsimp)
  apply (frule vs_lookup_table_target, simp)
  apply (frule pts_of_Some_alignedD, clarsimp)
  apply (frule vref_for_level_user_region)
  apply (frule (2) vs_lookup_target_not_global)
  apply simp
  apply (frule (1) valid_vs_lookupD; clarsimp)
  apply (frule (1) cap_to_pt_is_pt_cap; (clarsimp intro!: valid_objs_caps)?)
  apply (rule conjI, fastforce simp: is_cap_simps)
  apply clarsimp
  apply (drule (3) vs_lookup_table_vspace)
  apply (simp add: table_index_max_level_slots)
  done

lemma set_mi_invs[wp]: "\<lbrace>invs\<rbrace> set_message_info t a \<lbrace>\<lambda>x. invs\<rbrace>"
  by (simp add: set_message_info_def, wp)

lemma data_at_orth:
  "data_at a p s
   \<Longrightarrow> \<not> ep_at p s \<and> \<not> ntfn_at p s \<and> \<not> cap_table_at sz p s \<and> \<not> tcb_at p s \<and> \<not> asid_pool_at p s
         \<and> \<not> pt_at p s \<and> \<not> asid_pool_at p s \<and> \<not> reply_at p s \<and> (\<forall>n. \<not> sc_obj_at n p s)"
  unfolding data_at_def obj_at_def a_type_def
  apply (cases "kheap s p", simp)
  by (rename_tac ko, case_tac ko)
     (auto simp: is_ep_def is_ntfn_def is_cap_table_def is_tcb_def is_reply_def is_sc_obj_def)

lemma data_at_frame_cap:
  "\<lbrakk>data_at sz p s; valid_cap cap s; p \<in> obj_refs cap\<rbrakk> \<Longrightarrow> is_frame_cap cap"
  by (cases cap; clarsimp simp: is_frame_cap_def valid_cap_def valid_arch_cap_ref_def data_at_orth
                         split: option.splits arch_cap.splits)

lemma perform_pg_inv_get_addr[wp]:
  "\<lbrace>invs and valid_page_inv (PageGetAddr ptr)\<rbrace> perform_pg_inv_get_addr ptr \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pg_inv_get_addr_def by wpsimp

lemma unmap_page_pool_for_asid[wp]:
  "unmap_page pgsz asid vref pt \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  unfolding unmap_page_def by (wpsimp simp: pool_for_asid_def)

lemma data_at_level:
  "\<lbrakk> data_at pgsz p s; data_at (vmpage_size_of_level level) p s;
     pt_bits_left level' = pageBitsForSize pgsz; level \<le> max_pt_level \<rbrakk> \<Longrightarrow>
   level = level'"
  by (fastforce simp: data_at_def obj_at_def)

lemma pt_lookup_slot_vs_lookup_slotI0:
  "\<lbrakk> vspace_for_asid asid s = Some pt_ptr;
     pt_lookup_slot pt_ptr vref (ptes_of s) = Some (level, slot) \<rbrakk>
   \<Longrightarrow> vs_lookup_slot 0 asid vref s = Some (level, slot)"
  unfolding pt_lookup_slot_def pt_lookup_slot_from_level_def vs_lookup_slot_def
  apply (clarsimp simp: in_omonad)
  apply (drule (1) pt_lookup_vs_lookupI, simp)
  apply (rule_tac x=level in exI)
  apply clarsimp
  apply (drule vs_lookup_level)
  apply (fastforce dest: pt_walk_max_level)
  done

lemma unmap_page_not_target:
  "\<lbrace> data_at pgsz pptr and valid_asid_table and valid_vspace_objs and pspace_aligned
     and unique_table_refs and valid_vs_lookup and (\<lambda>s. valid_caps (caps_of_state s) s)
     and K (0 < asid \<and> vref \<in> user_region \<and> pptr' = pptr \<and> asid' = asid \<and> vref' = vref) \<rbrace>
   unmap_page pgsz asid vref pptr
   \<lbrace>\<lambda>_ s. vs_lookup_target level asid' vref' s \<noteq> Some (level, pptr')\<rbrace>"
  unfolding unmap_page_def
  supply pt_bits_left_not_asid_pool_size[simp]
         vs_lookup_slot_pool_for_asid[simp]
         pool_for_asid_vs_lookup[simp]
  apply (wpsimp wp: store_pte_invalid_vs_lookup_target_unmap)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def vspace_for_asid_def obind_def vs_lookup_slot_def
                         vs_lookup_table_def
                   split: if_split_asm option.splits)
  apply (frule (1) pt_lookup_slot_vs_lookup_slotI0)
  apply (rule conjI; clarsimp simp: in_omonad)
   apply (drule vs_lookup_slot_level)
   apply (rename_tac slot level' pte)
   apply (rule conjI; clarsimp)
    apply (rule conjI, fastforce)
    apply (clarsimp simp: pte_ref_def is_PagePTE_def pptr_from_pte_def)
   apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
    apply (prop_tac "vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, pptr)")
     apply (clarsimp simp: vs_lookup_table_def in_omonad)
    apply (drule (2) valid_vspace_objs_strongD; clarsimp)
    apply (clarsimp simp: data_at_def in_omonad obj_at_def)
   apply (clarsimp simp: in_omonad)
   apply (rename_tac pte')
   apply (frule (5) valid_vspace_objs_strong_slotD[where level=level])
   apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
   apply (rename_tac pt_ptr pt_ptr')
   apply (prop_tac "is_PagePTE pte'")
    apply (case_tac pte'; clarsimp simp: obj_at_def data_at_def)
   apply (case_tac "level = level'", simp add: pte_ref_Some_cases)
   apply (clarsimp simp: is_PagePTE_def)
   apply (drule (3) data_at_level, simp)
  (* lookup has stopped at wrong level for pgsz *)
  apply (rename_tac level')
  apply (clarsimp simp: vs_lookup_target_def split: if_split_asm)
   apply (prop_tac "vs_lookup_table max_pt_level asid vref s = Some (max_pt_level, pptr)")
    apply (clarsimp simp: vs_lookup_table_def in_omonad)
   apply (drule (2) valid_vspace_objs_strongD; clarsimp)
   apply (clarsimp simp: data_at_def in_omonad obj_at_def)
  apply (prop_tac "level' \<le> max_pt_level")
   apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def split: if_split_asm)
   apply (drule pt_walk_max_level, simp)
  apply (clarsimp simp: in_omonad)
  apply (rename_tac pte)
  apply (frule (5) valid_vspace_objs_strong_slotD[where level=level], clarsimp)
  apply (prop_tac "is_PagePTE pte \<and> pgsz = vmpage_size_of_level level")
   apply (case_tac pte; fastforce simp: data_at_def obj_at_def)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (rename_tac pt_ptr' pt_ptr)
  apply (case_tac "level' \<le> level")
   apply (drule vs_lookup_level)
   apply (drule_tac level'=level and level=level' in vs_lookup_splitD; assumption?)
   apply clarsimp
   apply (subst (asm) pt_walk.simps)
   apply (clarsimp simp: is_PagePTE_def split: if_split_asm)
  apply (simp add: not_le)
  apply (prop_tac "level' \<noteq> 0", clarsimp)
  apply (frule vs_lookup_table_stopped; clarsimp)
  apply (drule_tac level'=level' in vs_lookup_splitD; simp?)
  apply (drule vs_lookup_level)
  apply clarsimp
  apply (subst (asm) pt_walk.simps)
  apply clarsimp
  done

lemma perform_pg_inv_unmap[wp]:
  "\<lbrace>invs and valid_page_inv (PageUnmap cap ct_slot)\<rbrace> perform_pg_inv_unmap cap ct_slot \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pg_inv_unmap_def
  apply (wpsimp wp: arch_update_cap_invs_unmap_page hoare_vcg_ex_lift hoare_vcg_ball_lift
                    hoare_vcg_all_lift hoare_vcg_const_imp_lift get_cap_wp unmap_page_cte_wp_at
                    hoare_vcg_imp_lift'
                    unmap_page_not_target unmap_page_invs)
  apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state is_cap_simps is_arch_update_def
                        update_map_data_def cap_master_cap_simps)
  apply (frule caps_of_state_valid, clarsimp)
  apply (case_tac m; simp)
   apply (clarsimp simp: valid_cap_def valid_arch_cap_def cap_aligned_def cap_master_cap_simps)
  apply (clarsimp simp: valid_unmap_def cap_master_cap_simps valid_cap_def wellformed_mapdata_def
                        cap_aligned_def)
  apply (fastforce simp: data_at_def split: if_split_asm intro: valid_objs_caps)
  done

lemma perform_pg_inv_map_invs[wp]:
  "\<lbrace>invs and valid_page_inv (PageMap cap ct_slot (pte, slot))\<rbrace>
   perform_pg_inv_map cap ct_slot pte slot
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_pg_inv_map_def
  apply (wpsimp wp: store_pte_invs arch_update_cap_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift')
  apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps
                        cap_master_cap_simps parent_for_refs_def valid_slots_def same_ref_def)
  apply (rename_tac cref cidx asid vref)
  apply (frule caps_of_state_valid, clarsimp)
  apply (prop_tac "is_FrameCap cap")
   apply (cases cap; simp add: cap_master_cap_simps)
  apply (intro conjI)
  using vs_lookup_slot_unique_level apply blast
       apply (clarsimp simp: is_FrameCap_def cap_master_cap_simps valid_cap_def cap_aligned_def
                             valid_arch_cap_def)
  using reachable_page_table_not_global vs_lookup_slot_table_unfold apply blast
     apply (auto simp: is_PagePTE_def)[1]
    apply (clarsimp simp: is_FrameCap_def)
    apply (drule (1) unique_table_refsD[rotated], solves \<open>simp\<close>; clarsimp)
   apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
   apply (rename_tac pt_ptr)
   apply (frule vs_lookup_table_is_aligned; clarsimp)
   apply (drule vspace_for_asid_vs_lookup)
   apply (drule (1) vs_lookup_table_unique_level; clarsimp)
   apply (drule (1) table_index_max_level_slots, simp)
  apply clarsimp
  apply (rule conjI, clarsimp simp: is_PagePTE_def)
  apply (rule conjI)
   apply (erule allE, erule impE, fastforce)
   apply (clarsimp simp: is_PagePTE_def)
   apply (drule_tac p="(cref,cidx)" in caps_of_state_valid, clarsimp)
   apply (clarsimp simp: valid_cap_def obj_at_def data_at_def)
  apply (rename_tac level' asid' vref' p')
  apply (prop_tac "level' \<le> max_pt_level")
   apply (clarsimp simp flip: asid_pool_level_neq simp: pool_for_asid_vs_lookup)
   apply (drule pool_for_asid_validD, clarsimp)
   apply (drule_tac p="(cref,cidx)" in caps_of_state_valid, clarsimp)
   apply (clarsimp simp: valid_cap_def obj_at_def in_omonad)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (rename_tac pt_ptr)
  apply (frule_tac bot_level=level in vs_lookup_table_is_aligned; clarsimp)
  apply (drule (1) vs_lookup_table_unique_level; clarsimp)
  apply (drule (1) pt_slot_offset_vref_for_level; simp)
  apply (cases ct_slot)
  apply fastforce
  done

lemma perform_page_invs [wp]:
  "\<lbrace>invs and valid_page_inv pg_inv\<rbrace> perform_page_invocation pg_inv \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding perform_page_invocation_def
  by (cases pg_inv; wpsimp)

lemma asid_high_low:
  "\<lbrakk> asid_high_bits_of asid = asid_high_bits_of asid';
     asid_low_bits_of asid = asid_low_bits_of asid' \<rbrakk> \<Longrightarrow>
   asid = asid'"
  unfolding asid_high_bits_of_def asid_low_bits_of_def asid_high_bits_def asid_low_bits_def
  by word_bitwise simp

end

locale asid_pool_map = Arch +
  fixes s ap pool asid ptp pt and s' :: "'a::state_ext state"
  defines "s' \<equiv> s\<lparr>kheap := (kheap s)(ap \<mapsto> ArchObj (ASIDPool (pool(asid_low_bits_of asid \<mapsto> ptp))))\<rparr>"
  assumes ap:  "asid_pools_of s ap = Some pool"
  assumes new: "pool (asid_low_bits_of asid) = None"
  assumes pt:  "pts_of s ptp = Some pt"
  assumes empty: "kernel_mappings_only pt s"
  assumes lookup: "pool_for_asid asid s = Some ap"
  assumes valid_vspace_objs: "valid_vspace_objs s"
  assumes valid_asids: "valid_asid_table s"
  assumes aligned: "is_aligned ptp pt_bits"
begin

lemma arch_state[simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)

lemma pool_for_asid[simp]:
  "pool_for_asid a s' = pool_for_asid a s"
  by (simp add: pool_for_asid_def)

lemma asid_pools_of[simp]:
  "asid_pools_of s' = (asid_pools_of s)(ap \<mapsto> pool(asid_low_bits_of asid \<mapsto> ptp))"
  by (simp add: s'_def)

lemma pts_of[simp]:
  "pts_of s' = pts_of s"
proof -
  from ap
  have "pts_of s ap = None" by (simp add: opt_map_def split: option.splits)
  thus ?thesis by (simp add: s'_def)
qed

lemma empty_for_user:
  "vref \<in> user_region \<Longrightarrow>
   pt (table_index (pt_slot_offset max_pt_level ptp vref)) = InvalidPTE"
  using empty aligned
  by (clarsimp simp: kernel_mappings_only_def table_index_max_level_slots)

lemma vs_lookup_table:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_table level asid' vref s' =
     (if asid' = asid \<and> level \<le> max_pt_level
      then Some (max_pt_level, ptp)
      else vs_lookup_table level asid' vref s)"
  apply clarsimp
  apply (rule conjI; clarsimp)
   using lookup
   apply (clarsimp simp: vs_lookup_table_def vspace_for_pool_def in_omonad pool_for_asid_def)
   apply (rule conjI, clarsimp)
   apply (subst pt_walk.simps)
   using pt aligned
   apply (clarsimp simp: obind_def ptes_of_def empty_for_user)
   apply (simp add: pt_slot_offset_def)
   apply (erule notE)
   apply (rule is_aligned_add)
    apply (erule is_aligned_weaken)
    apply (simp add: bit_simps)
   apply (rule is_aligned_shift)
  apply (clarsimp simp: vs_lookup_table_def)
  apply (rule obind_eqI, simp)
  apply clarsimp
  using ap lookup new
  apply (clarsimp simp: obind_def split: option.splits)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vspace_for_pool_def obind_def split: option.splits if_split_asm)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vspace_for_pool_def obind_def split: option.splits if_split_asm)
   apply (clarsimp simp: pool_for_asid_def)
   using valid_asids
   apply (clarsimp simp: valid_asid_table_def)
   apply (drule (2) inj_on_domD[rotated])
   apply (drule (1) asid_high_low)
   apply clarsimp
  apply (clarsimp simp: vspace_for_pool_def split: if_split_asm)
  done

lemma vs_lookup_slot:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_slot level asid' vref s' =
     (if asid' = asid \<and> level \<le> max_pt_level
      then Some (max_pt_level, pt_slot_offset max_pt_level ptp vref)
      else vs_lookup_slot level asid' vref s)"
  apply (simp add: vs_lookup_slot_def)
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: in_omonad vs_lookup_table)
  apply (rule obind_eqI; clarsimp simp: vs_lookup_table)
  done

lemma pte_refs_of_None:
  "vref \<in> user_region \<Longrightarrow> pte_refs_of s (pt_slot_offset max_pt_level ptp vref) = None"
  using aligned pt
  by (clarsimp simp: ptes_of_def obind_def opt_map_def empty_for_user split: option.splits)

lemma vs_lookup_table_None:
  "level \<le> max_pt_level \<Longrightarrow> vs_lookup_table level asid vref s = None"
  using lookup new ap
  by (clarsimp simp: vs_lookup_table_def obind_def pool_for_asid_def vspace_for_pool_def
               split: option.splits)

lemma vs_lookup_slot_None:
  "level \<le> max_pt_level \<Longrightarrow> vs_lookup_slot level asid vref s = None"
  by (clarsimp simp: vs_lookup_slot_def obind_def vs_lookup_table_None)

lemma vs_lookup_target:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_target level asid' vref s' =
     (if asid' = asid \<and> level = asid_pool_level
      then Some (level, ptp)
      else vs_lookup_target level asid' vref s)"
  apply clarsimp
  apply (rule conjI; clarsimp)
   apply (clarsimp simp: vs_lookup_target_def in_omonad vs_lookup_slot)
   apply (clarsimp simp: vs_lookup_slot_def vs_lookup_table_def in_omonad)
   using lookup
   apply (simp add: pool_for_asid_def vspace_for_pool_def in_omonad)
  apply (cases "asid' = asid")
   apply clarsimp
   apply (clarsimp simp: vs_lookup_target_def)
   apply (clarsimp simp: obind_def vs_lookup_slot_None vs_lookup_slot pte_refs_of_None)
  apply clarsimp
  apply (simp add: vs_lookup_target_def obind_def)
  apply (clarsimp simp: vs_lookup_slot)
  apply (cases "vs_lookup_slot level asid' vref s"; clarsimp)
  apply (rule conjI; clarsimp)
   prefer 2
   apply (simp split: option.splits)
  apply (clarsimp simp: vs_lookup_slot_def split: if_split_asm)
  apply (clarsimp simp: vs_lookup_table_def in_omonad split: if_split_asm)
  apply (erule disjE; clarsimp)
   apply (drule pt_walk_max_level, simp)
  apply (rename_tac ap')
  apply (subgoal_tac "ap' \<noteq> ap \<or> asid_low_bits_of asid' \<noteq> asid_low_bits_of asid")
   using ap
   apply (simp add: vspace_for_pool_def obind_def split: option.splits)
  using lookup valid_asids
  apply (clarsimp simp: valid_asid_table_def pool_for_asid_def)
  apply (drule (2) inj_on_domD[rotated])
  apply (drule (1) asid_high_low)
  apply clarsimp
  done

lemma valid_pool:
  "valid_vspace_obj asid_pool_level (ASIDPool pool) s"
proof -
  from lookup
  have "vs_lookup_table asid_pool_level asid 0 s = Some (asid_pool_level, ap)"
    by (clarsimp simp: vs_lookup_table_def in_omonad)
  with valid_vspace_objs ap
  show ?thesis by (fastforce dest: valid_vspace_objsD simp: in_omonad)
qed

lemma valid_pte:
  "valid_pte level pte s \<Longrightarrow> valid_pte level pte s'"
  using ap
  apply (cases pte; simp add: pt_at_eq)
  apply (clarsimp simp: data_at_def obj_at_def s'_def in_omonad)
  done

lemma valid_vspace_obj:
  "valid_vspace_obj level ao s \<Longrightarrow> valid_vspace_obj level ao s'"
  by (cases ao; simp add: pt_at_eq valid_pte)

end

context Arch begin global_naming RISCV64

lemma set_asid_pool_arch_objs_map:
  "\<lbrace>valid_vspace_objs and valid_arch_state and valid_global_objs and
    valid_kernel_mappings and pspace_aligned and
    (\<lambda>s. asid_pools_of s ap = Some pool) and
    K (pool (asid_low_bits_of asid) = None) and
    (\<lambda>s. pool_for_asid asid s = Some ap) and
    (\<lambda>s. \<exists>pt. pts_of s pt_ptr = Some pt \<and> kernel_mappings_only pt s) \<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> pt_ptr))
  \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  unfolding set_asid_pool_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (frule (5) asid_pool_map.intro)
    apply (clarsimp simp: valid_arch_state_def)
   apply (erule pspace_aligned_pts_ofD, simp)
  apply (subst valid_vspace_objs_def)
  apply (clarsimp simp: asid_pool_map.vs_lookup_table split: if_split_asm)
   apply (clarsimp simp: in_omonad fun_upd_apply kernel_mappings_only_def split: if_split_asm)
  apply (clarsimp simp: in_omonad fun_upd_apply split: if_split_asm)
   prefer 2
   apply (frule (2) valid_vspace_objsD)
    apply (simp add: in_omonad)
   apply (simp add: asid_pool_map.valid_vspace_obj)
  apply (clarsimp simp: obj_at_def fun_upd_apply)
  apply (rule conjI; clarsimp)
  apply (frule asid_pool_map.valid_pool)
  apply (fastforce simp: obj_at_def)
  done

lemma caps_of_state_fun_upd:
  "obj_at (same_caps val) p s \<Longrightarrow>
   (caps_of_state (s\<lparr>kheap := (kheap s) (p \<mapsto> val)\<rparr>)) = caps_of_state s"
  apply (drule caps_of_state_after_update)
  apply (simp add: fun_upd_def)
  done

lemma set_asid_pool_valid_arch_caps_map:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_global_objs and valid_objs
    and valid_vspace_objs and pspace_aligned and
    (\<lambda>s. asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
         (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {pt_ptr} \<and>
                    vs_cap_ref cap = Some (asid, 0)))
    and (\<lambda>s. \<exists>pt. pts_of s pt_ptr = Some pt \<and> kernel_mappings_only pt s)
    and K (pool (asid_low_bits_of asid) = None \<and> 0 < asid)\<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> pt_ptr))
  \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  unfolding set_asid_pool_def
  supply fun_upd_apply[simp del]
  apply (wpsimp wp: set_object_wp)
  apply (frule (5) asid_pool_map.intro)
    apply (clarsimp simp: valid_arch_state_def)
   apply (erule pspace_aligned_pts_ofD, simp)
  apply (clarsimp simp: valid_arch_caps_def)
  apply (simp add: caps_of_state_fun_upd obj_at_def)
  apply (subgoal_tac "pts_of s ap = None")
   prefer 2
   apply (clarsimp simp: opt_map_def)
  apply simp
  apply (clarsimp simp: valid_vs_lookup_def caps_of_state_fun_upd obj_at_def)
  apply (clarsimp simp: asid_pool_map.vs_lookup_target split: if_split_asm)
  by (fastforce simp: vref_for_level_asid_pool user_region_def)

lemma kernel_mappings_only_has:
  "kernel_mappings_only pt s \<Longrightarrow> has_kernel_mappings pt s"
  by (simp add: kernel_mappings_only_def)

lemma toplevel_pt_has_kernel_mappings:
  assumes ap: "pool_for_asid asid s = Some ap"
  assumes pool: "asid_pools_of s ap = Some pool"
  assumes p: "p \<in> ran pool"
  assumes pt: "pts_of s p = Some pt"
  assumes km: "equal_kernel_mappings s"
  assumes vsl: "valid_vs_lookup s"
  shows "has_kernel_mappings pt s"
proof -
  from ap
  have "vs_lookup_table asid_pool_level asid 0 s = Some (asid_pool_level, ap)"
    by (simp add: vs_lookup_table_def in_omonad)
  with pool p
  obtain asid' where
    vs_target: "vs_lookup_target asid_pool_level asid' 0 s = Some (asid_pool_level, p)"
    by (auto dest: vs_lookup_table_ap_step)
  with vsl
  have "asid' \<noteq> 0" by (fastforce simp add: valid_vs_lookup_def)
  with vs_target
  have "vspace_for_asid asid' s = Some p"
    by (clarsimp simp: vspace_for_pool_def in_omonad vs_lookup_target_def vs_lookup_slot_def
                       vs_lookup_table_def vspace_for_asid_def word_neq_0_conv)
  with km pt
  show ?thesis by (simp add: equal_kernel_mappings_def)
qed

lemma set_asid_pool_invs_map:
  "\<lbrace>invs and
    (\<lambda>s. asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
         (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {pt_ptr} \<and>
                    vs_cap_ref cap = Some (asid, 0)))
    and (\<lambda>s. \<exists>pt. pts_of s pt_ptr = Some pt \<and> kernel_mappings_only pt s)
    and K (pool (asid_low_bits_of asid) = None \<and> 0 < asid)\<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> pt_ptr))
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_asid_map_def)
  apply (wpsimp wp: valid_irq_node_typ set_asid_pool_typ_at set_asid_pool_arch_objs_map
                    valid_irq_handlers_lift set_asid_pool_valid_arch_caps_map)
  apply (erule disjE, clarsimp simp: kernel_mappings_only_has)
  apply (erule (4) toplevel_pt_has_kernel_mappings)
  apply (simp add: valid_arch_caps_def)
  done

lemma ako_asid_pools_of:
  "ako_at (ASIDPool pool) ap s = (asid_pools_of s ap = Some pool)"
  by (clarsimp simp: obj_at_def in_omonad)

lemma copy_global_mappings_asid_pools[wp]:
  "copy_global_mappings pt_ptr \<lbrace>\<lambda>s. P (asid_pools_of s)\<rbrace>"
  unfolding copy_global_mappings_def by (wpsimp wp: mapM_x_wp')

lemma copy_global_mappings_pool_for_asid[wp]:
  "copy_global_mappings pt_ptr \<lbrace>\<lambda>s. P (pool_for_asid asid s)\<rbrace>"
  unfolding copy_global_mappings_def by (wpsimp wp: mapM_x_wp' simp: pool_for_asid_def)

lemma copy_global_mappings_caps_of_state[wp]:
  "copy_global_mappings pt_ptr \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace>"
  unfolding copy_global_mappings_def by (wpsimp wp: mapM_x_wp')

lemma store_pte_vs_lookup_target_unreachable:
  "\<lbrace>\<lambda>s. (\<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s) \<and>
        vref \<in> user_region \<and>
        vs_lookup_target bot_level asid vref s \<noteq> Some (level, p') \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv s. vs_lookup_target bot_level asid vref s \<noteq> Some (level, p')\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (subst (asm) vs_lookup_target_unreachable_upd_idem; clarsimp)
  done

lemma store_pte_vs_lookup_table_unreachable:
  "\<lbrace>\<lambda>s. (\<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s) \<and>
        vref \<in> user_region \<and>
        vs_lookup_table bot_level asid vref s \<noteq> Some (level, p') \<and>
        pspace_aligned s \<and> valid_vspace_objs s \<and> valid_asid_table s \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv s. vs_lookup_table bot_level asid vref s \<noteq> Some (level, p')\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  apply (subst (asm) vs_lookup_table_unreachable_upd_idem'; clarsimp)
  done

lemma store_pte_valid_arch_state_unreachable:
  "\<lbrace>valid_arch_state and valid_global_vspace_mappings and (\<lambda>s. table_base p \<notin> global_refs s) \<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  unfolding valid_arch_state_def by (wpsimp wp: store_pte_valid_global_tables)

lemma store_pte_valid_vs_lookup_unreachable:
  "\<lbrace>valid_vs_lookup and pspace_aligned and valid_vspace_objs and valid_asid_table and
    (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s)\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>_. valid_vs_lookup\<rbrace>"
  unfolding valid_vs_lookup_def
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_imp_lift' store_pte_vs_lookup_target_unreachable)
  apply (erule disjE; clarsimp)
  done

lemma store_pte_valid_arch_caps_unreachable:
  "\<lbrace> invs and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s) and
     (\<lambda>s. \<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) asidopt))
                          \<longrightarrow> asidopt \<noteq> None) and
     (\<lambda>s. table_base p \<notin> global_refs s) \<rbrace>
   store_pte p pte
   \<lbrace> \<lambda>_. valid_arch_caps \<rbrace>"
  unfolding valid_arch_caps_def
  apply (wpsimp wp: store_pte_valid_vs_lookup_unreachable store_pte_valid_table_caps)
  by (fastforce simp: invs_def valid_state_def valid_arch_caps_def intro: valid_objs_caps)

lemma store_pte_invs_unreachable:
  "\<lbrace>invs and
    (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, table_base p) s) and
    K (wellformed_pte pte) and
    (\<lambda>s. \<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap (table_base p) asidopt))
                         \<longrightarrow> asidopt \<noteq> None) and
    (\<lambda>s. table_base p \<notin> global_refs s) \<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  apply (wpsimp wp: store_pte_valid_arch_state_unreachable store_pte_valid_arch_caps_unreachable
                    store_pte_equal_kernel_mappings_no_kernel_slots
                    store_pte_valid_global_vspace_mappings
                    store_pte_valid_vspace_objs)
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_arch_state_def
                   valid_arch_caps_def valid_objs_caps
              cong: conj_cong)
  apply (rule conjI, fastforce dest!: vspace_for_asid_vs_lookup)
  apply (fastforce simp: valid_arch_state_def dest: riscv_global_pt_in_global_refs)
  done

lemma invs_valid_global_vspace_mappings[elim!]:
  "invs s \<Longrightarrow> valid_global_vspace_mappings s"
  by (clarsimp simp: invs_def valid_state_def)

lemma is_aligned_pte_offset:
  "is_aligned pt_ptr pt_bits \<Longrightarrow>
   is_aligned (pt_ptr + (i << pte_bits)) pte_bits"
  apply (rule is_aligned_add)
   apply (erule is_aligned_weaken, simp add: bit_simps)
  apply (simp add: is_aligned_shiftl)
  done

lemma ptes_of_from_pt:
  "\<lbrakk> pts pt_ptr = Some pt; is_aligned pt_ptr pt_bits; i \<le> mask ptTranslationBits \<rbrakk> \<Longrightarrow>
   pte_of (pt_ptr + (i << pte_bits)) pts = Some (pt (ucast i))"
  by (clarsimp simp: ptes_of_def in_omonad table_base_plus table_index_plus is_aligned_pte_offset)

lemma ptes_of_from_pt_ucast:
  "\<lbrakk> pts_of s pt_ptr = Some pt; is_aligned pt_ptr pt_bits \<rbrakk> \<Longrightarrow>
   ptes_of s (pt_ptr + (ucast (i::pt_index) << pte_bits)) = Some (pt i)"
  apply (drule (1) ptes_of_from_pt[where i="ucast i"])
   apply (rule ucast_leq_mask, simp add: bit_simps)
  apply (simp add: is_down_def target_size_def source_size_def word_size ucast_down_ucast_id)
  done

lemma copy_global_mappings_copies[wp]:
  "\<lbrace>invs and (\<lambda>s. pts_of s pt_ptr = Some empty_pt \<and> pt_ptr \<notin> global_refs s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_ s. \<exists>pt. pts_of s pt_ptr = Some pt \<and> kernel_mappings_only pt s\<rbrace>"
  unfolding copy_global_mappings_def
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac I="\<lambda>s. (\<exists>pt. pts_of s pt_ptr = Some pt \<and>
                                    (\<forall>idx. idx \<notin> kernel_mapping_slots \<longrightarrow> pt idx = InvalidPTE)) \<and>
                              pt_at (riscv_global_pt (arch_state s)) s \<and>
                              pt_ptr \<noteq> riscv_global_pt (arch_state s) \<and>
                              is_aligned pt_ptr pt_bits \<and>
                              is_aligned global_pt pt_bits \<and>
                              global_pt = riscv_global_pt (arch_state s) \<and>
                              base = pt_index max_pt_level pptr_base \<and>
                              pt_size = 1 << ptTranslationBits" and
                       V="\<lambda>xs s. \<forall>i \<in> set xs. ptes_of s (pt_ptr + (i << pte_bits)) =
                                              ptes_of s (global_pt + (i << pte_bits))"
                       in mapM_x_inv_wp3)
        apply (wp store_pte_typ_ats|wps)+
       apply (clarsimp simp del: fun_upd_apply)
       apply (fold mask_2pm1)[1]
       apply (drule word_enum_decomp)
       apply (clarsimp simp: table_base_plus table_index_plus in_omonad)
       apply (subgoal_tac "ucast a \<in> kernel_mapping_slots")
        prefer 2
        apply (clarsimp simp: kernel_mapping_slots_def pt_index_def)
        apply (drule ucast_mono_le[where x="a && b" and 'b=pt_index_len for a b])
         apply (simp add: bit_simps mask_def)
         apply unat_arith
        apply (simp add: ucast_mask_drop bit_simps)
       apply (clarsimp simp: pt_at_eq ptes_of_from_pt)
       apply (drule (1) bspec)
       apply (clarsimp simp: ptes_of_from_pt in_omonad)
      apply (clarsimp simp: kernel_mappings_only_def)
      apply (clarsimp simp: has_kernel_mappings_def)
      apply (thin_tac "\<forall>idx. idx \<notin> kernel_mapping_slots \<longrightarrow> P idx" for P)
      apply (erule_tac x="ucast i" in allE)
      apply (erule impE)
       apply (simp add: kernel_mapping_slots_def pt_index_def)
       apply word_bitwise
       subgoal
         by (clarsimp simp: word_size bit_simps word_bits_def canonical_bit_def pt_bits_left_def
                            level_defs rev_bl_order_simps)
      apply (clarsimp simp: ptes_of_from_pt_ucast)
     apply wp+
   apply (fastforce elim!: pts_of_Some_alignedD
                    intro: invs_valid_global_arch_objs valid_global_arch_objs_pt_at
                           riscv_global_pt_in_global_refs valid_global_vspace_mappings_aligned)
  done

lemma copy_global_mappings_invs:
  "\<lbrace> invs and K (is_aligned pt_ptr pt_bits) and
     (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s) and
     (\<lambda>s. \<forall>slot asidopt. caps_of_state s slot = Some (ArchObjectCap (PageTableCap pt_ptr asidopt))
                           \<longrightarrow> asidopt \<noteq> None) and
     (\<lambda>s. pt_ptr \<notin> global_refs s)\<rbrace>
   copy_global_mappings pt_ptr
   \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding copy_global_mappings_def
  apply wp
      apply (rule hoare_strengthen_post)
       apply (rule_tac P="invs and K (is_aligned pt_ptr pt_bits) and
                          (\<lambda>s. \<forall>level. \<not> \<exists>\<rhd> (level, pt_ptr) s) and
                          (\<lambda>s. \<forall>slot asidopt. caps_of_state s slot =
                                                Some (ArchObjectCap (PageTableCap pt_ptr asidopt))
                                                  \<longrightarrow> asidopt \<noteq> None) and
                          (\<lambda>s. pt_ptr \<notin> global_refs s \<and>
                               base = pt_index max_pt_level pptr_base \<and>
                               pt_size = 1 << ptTranslationBits)" in mapM_x_wp')
       apply (wpsimp wp: store_pte_invs_unreachable hoare_vcg_all_lift hoare_vcg_imp_lift'
                         store_pte_vs_lookup_table_unreachable)
       apply (fold mask_2pm1)[1]
       apply (clarsimp simp: table_base_plus table_index_plus)
       apply (rule conjI, erule ptes_of_wellformed_pte, clarsimp)
       apply clarsimp
       apply (frule invs_valid_asid_table)
       apply simp
       apply (erule impE, fastforce)+
       apply fastforce
      apply fastforce
     apply wp+
  apply clarsimp
  done

lemma cap_asid_pt_None[simp]:
  "(cap_asid (ArchObjectCap (PageTableCap p m)) = None) = (m = None)"
  by (simp add: cap_asid_def split: option.splits)

lemma perform_asid_pool_invs [wp]:
  "\<lbrace>invs and valid_apinv api\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: perform_asid_pool_invocation_def store_asid_pool_entry_def
                  split: asid_pool_invocation.splits)
  apply (wpsimp wp: set_asid_pool_invs_map hoare_vcg_all_lift hoare_vcg_imp_lift'
                    copy_global_mappings_invs arch_update_cap_invs_map get_cap_wp set_cap_typ_at
                simp: ako_asid_pools_of
         | wp (once) hoare_vcg_ex_lift)+
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_apinv_def cong: conj_cong)
  apply (rename_tac asid pool_ptr slot_ptr slot_idx s pool cap)
  apply (clarsimp simp: is_cap_simps update_map_data_def is_arch_update_def is_arch_cap_def
                        cap_master_cap_simps asid_low_bits_of_def)
  apply (frule caps_of_state_valid, clarsimp)
  apply (clarsimp simp: valid_cap_def cap_aligned_def wellformed_mapdata_def bit_simps)
  apply (frule valid_table_caps_pdD, fastforce)
  apply (frule valid_global_refsD2, fastforce)
  apply (clarsimp simp: cap_range_def)
  apply (rule conjI, clarsimp)
   apply (drule (1) vs_lookup_table_valid_cap; clarsimp)
   apply (frule (1) cap_to_pt_is_pt_cap, simp, fastforce intro: valid_objs_caps)
   apply (drule (1) unique_table_refsD[rotated]; clarsimp)
   apply (clarsimp simp: is_cap_simps)
  apply (rule conjI, clarsimp)
   apply (drule (1) unique_table_capsD[rotated]; clarsimp)
  apply fastforce
  done

lemma invs_aligned_pdD:
  "\<lbrakk> pspace_aligned s; valid_arch_state s \<rbrakk> \<Longrightarrow> is_aligned (riscv_global_pt (arch_state s)) pt_bits"
  by (clarsimp simp: valid_arch_state_def)

lemma do_machine_op_valid_kernel_mappings:
  "do_machine_op f \<lbrace>valid_kernel_mappings\<rbrace>"
  unfolding valid_kernel_mappings_def by wp

lemma valid_vspace_obj_default:
  assumes tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  shows "ArchObj ao = default_object ty dev us d \<Longrightarrow> valid_vspace_obj level ao s'"
  by (cases ty; simp add: default_object_def tyunt)

lemmas setDeadline_irq_masks = no_irq[OF no_irq_setDeadline]
crunch device_state_inv[wp]: setDeadline "\<lambda>ms. P (device_state ms)"

lemma dmo_setDeadline[wp]:
  "do_machine_op (setDeadline t) \<lbrace>invs\<rbrace>"
  apply (wp dmo_invs)
  apply safe
   apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
          in use_valid)
     apply ((clarsimp simp: setDeadline_def machine_op_lift_def
                           machine_rest_lift_def split_def | wp)+)[3]
  apply(erule (1) use_valid[OF _ setDeadline_irq_masks])
  done

end

context begin interpretation Arch .
requalify_facts
  do_machine_op_valid_kernel_mappings
end

end
