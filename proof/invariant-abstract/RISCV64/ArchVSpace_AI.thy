(*
 * Copyright 2019, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
RISCV-specific VSpace invariants
*)

theory ArchVSpace_AI
imports "../VSpacePre_AI"
begin

(* FIXME RISCV: move to lib *)
lemma throw_opt_wp[wp]:
  "\<lbrace>if v = None then E ex else Q (the v)\<rbrace> throw_opt ex v \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding throw_opt_def by wpsimp auto

context Arch begin global_naming RISCV64

lemma find_vspace_for_asid_wp[wp]:
  "\<lbrace>\<lambda>s. (vspace_for_asid asid s = None \<longrightarrow> E InvalidRoot s) \<and>
        (\<forall>pt. vspace_for_asid asid s = Some pt \<longrightarrow> Q pt s) \<rbrace>
   find_vspace_for_asid asid \<lbrace>Q\<rbrace>,\<lbrace>E\<rbrace>"
  unfolding find_vspace_for_asid_def
  by (wpsimp wp: throw_opt_wp)

crunch pspace_in_kernel_window[wp]: perform_page_invocation "pspace_in_kernel_window"
  (simp: crunch_simps wp: crunch_wps)

lemma asid_word_bits [simp]: "asid_bits < word_bits"
  by (simp add: asid_bits_def word_bits_def)

lemma asid_low_high_bits:
  "\<lbrakk> x && mask asid_low_bits = y && mask asid_low_bits;
    ucast (asid_high_bits_of x) = (ucast (asid_high_bits_of y)::machine_word);
    x \<le> 2 ^ asid_bits - 1; y \<le> 2 ^ asid_bits - 1 \<rbrakk>
  \<Longrightarrow> x = y"
  apply (rule word_eqI)
  apply (simp add: upper_bits_unset_is_l2p_64[symmetric] bang_eq nth_ucast word_size)
  apply (clarsimp simp: asid_high_bits_of_def nth_ucast nth_shiftr)
  apply (simp add: asid_high_bits_def asid_bits_def asid_low_bits_def word_bits_def)
  subgoal premises prems[rule_format] for n
  apply (cases "n < asid_low_bits")
   using prems(1)
   apply (fastforce simp: asid_low_bits_def)
  apply (cases "n < asid_bits")
   using prems(2)[where n="n - asid_low_bits"]
   apply (fastforce simp: asid_bits_def asid_low_bits_def)
  using prems(3-)
  by (simp add: linorder_not_less asid_bits_def asid_low_bits_def)
  done

lemma asid_low_high_bits':
  "\<lbrakk> ucast x = (ucast y :: asid_low_index);
    asid_high_bits_of x = asid_high_bits_of y;
    x \<le> 2 ^ asid_bits - 1; y \<le> 2 ^ asid_bits - 1 \<rbrakk>
  \<Longrightarrow> x = y"
  apply (rule asid_low_high_bits)
     apply (rule word_eqI)
     apply (subst (asm) bang_eq)
     apply (simp add: nth_ucast asid_low_bits_def word_size)
    apply (rule word_eqI)
    apply (subst (asm) bang_eq)+
    apply (simp add: nth_ucast asid_low_bits_def)
   apply assumption+
  done


lemma pt_at_asid_unique:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid' pt s;
     unique_table_refs s;
     valid_vs_lookup s; valid_vspace_objs s; valid_global_objs s;
     valid_arch_state s; asid < 2 ^ asid_bits; asid' < 2 ^ asid_bits \<rbrakk>
       \<Longrightarrow> asid = asid'"
  sorry (* FIXME RISCV: being proved in ArchAcc, check there
  apply (clarsimp simp: vspace_at_asid_def)
  apply (drule(1) valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])+
  apply (clarsimp simp: table_cap_ref_ap_eq[symmetric])
  apply (clarsimp simp: table_cap_ref_def
                 split: cap.split_asm arch_cap.split_asm option.split_asm)
  apply (drule(2) unique_table_refsD,
         simp+, clarsimp simp: table_cap_ref_def,
         erule(1) asid_low_high_bits)
   apply simp+
  done *)

lemma pt_at_asid_unique2:
  "\<lbrakk> vspace_at_asid asid pt s; vspace_at_asid asid pt' s \<rbrakk> \<Longrightarrow> pt = pt'"
  by (clarsimp simp: vspace_at_asid_def)

lemma dmo_pd_at_asid [wp]:
  "\<lbrace>vspace_at_asid a pd\<rbrace> do_machine_op f \<lbrace>\<lambda>_. vspace_at_asid a pd\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (simp add: vspace_at_asid_def)
  done


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
  "vs_lookup (s\<lparr>arch_state := arch_state s \<lparr>riscv_asid_table :=
                                            (riscv_asid_table (arch_state s)) (pptr := None)\<rparr>\<rparr>)
             bot_level asid vref  = Some (level, p)
   \<Longrightarrow> vs_lookup s bot_level asid vref = Some (level, p)"
  sorry (* FIXME RISCV *)


lemma vs_lookup_pages_clear_asid_table:
  "vs_lookup_pages (s\<lparr>arch_state := arch_state s \<lparr>riscv_asid_table :=
                                            (riscv_asid_table (arch_state s)) (pptr := None)\<rparr>\<rparr>)
             bot_level asid vref  = Some (level, p)
  \<Longrightarrow> vs_lookup_pages s bot_level asid vref = Some (level, p)"
  sorry (* FIXME RISCV *)


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
  apply (blast dest: vs_lookup_pages_clear_asid_table)
  done


lemma ex_asid_high_bits_plus:
  "asid \<le> mask asid_bits \<Longrightarrow> \<exists>x \<le> 2^asid_low_bits - 1. asid = (ucast (asid_high_bits_of asid) << asid_low_bits) + x"
  apply (rule_tac x="asid && mask asid_low_bits" in exI)
  apply (rule conjI)
   apply (simp add: mask_def)
   apply (rule word_and_le1)
  apply (subst (asm) mask_def)
  apply (simp add: upper_bits_unset_is_l2p_64[symmetric])
  apply (subst word_plus_and_or_coroll)
   apply (rule word_eqI)
   apply (clarsimp simp: word_size nth_ucast nth_shiftl)
  apply (rule word_eqI)
  apply (clarsimp simp: word_size nth_ucast nth_shiftl nth_shiftr asid_high_bits_of_def
                        asid_low_bits_def word_bits_def asid_bits_def)
  apply (rule iffI)
   prefer 2
   apply fastforce
  apply (clarsimp simp: linorder_not_less)
  apply (rule conjI)
   prefer 2
   apply arith
  apply (subgoal_tac "n < 16", simp)
  apply (clarsimp simp add: linorder_not_le [symmetric])
  done


lemma asid_high_bits_shl:
  "\<lbrakk> is_aligned base asid_low_bits; base \<le> mask asid_bits \<rbrakk> \<Longrightarrow> ucast (asid_high_bits_of base) << asid_low_bits = base"
  apply (simp add: mask_def upper_bits_unset_is_l2p_64 [symmetric])
  apply (rule word_eqI[rule_format])
  apply (simp add: is_aligned_nth nth_ucast nth_shiftl nth_shiftr asid_low_bits_def
                   asid_high_bits_of_def word_size asid_bits_def word_bits_def)
  apply (rule iffI, clarsimp)
  apply (rule context_conjI)
   apply (clarsimp simp add: linorder_not_less [symmetric])
  apply simp
  apply (rule conjI)
   prefer 2
   apply simp
  apply (subgoal_tac "n < 16", simp)
  apply (clarsimp simp add: linorder_not_le [symmetric])
  done


lemma valid_asid_map_unmap:
  "valid_asid_map s \<and> is_aligned base asid_low_bits \<and> base \<le> mask asid_bits \<longrightarrow>
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
  "parent_for_refs \<equiv> \<lambda>(_, slot) cap. cap = ArchObjectCap (PageTableCap (table_base slot) None)"

definition
  "same_ref \<equiv> \<lambda>(pte, slot) cap s.
     (\<exists>p. pte_ref pte = Some p \<and> obj_refs cap = {p}) \<and>
     (\<forall>level asid vref. vs_lookup_table level asid vref s = Some (level, slot) \<longrightarrow>
                        vs_cap_ref cap = Some (asid, vref_for_level vref level))"
  (* FIXME RISCV: level might be off by one. We want the part of the vref that goes to the slot,
                  not only to the beginning of the table *)

definition
  "valid_page_inv pg_inv \<equiv> case pg_inv of
    PageMap acap ptr m \<Rightarrow>
      cte_wp_at (is_arch_update (ArchObjectCap acap) and ((=) None \<circ> vs_cap_ref)) ptr
      and cte_wp_at is_frame_cap ptr
      and same_ref m (ArchObjectCap acap)
      and valid_slots m
      and valid_arch_cap acap
      and K (is_PagePTE (fst m))
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
  | PageRemap m \<Rightarrow>
      valid_slots m and K (is_PagePTE (fst m))
      and (\<lambda>s. \<exists>slot. cte_wp_at (parent_for_refs m) slot s)
      and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>cap. same_ref m cap s) slot s)
  | PageUnmap acap cslot \<Rightarrow>
     \<lambda>s. \<exists>dev r R sz m.
            acap = FrameCap r R sz dev m \<and>
            case_option True (valid_unmap sz) m \<and>
            cte_wp_at (is_arch_diminished (ArchObjectCap acap)) cslot s \<and>
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
                vs_cap_ref_arch acap = Some (asid, vref)
                \<and> vs_lookup_slot level asid vref s = Some (level, pt_slot)
                \<and> valid_pte level pte s
                \<and> pte_ref pte = Some p' \<and> obj_refs (ArchObjectCap acap) = {p'}
                \<and> (\<exists>ao. ko_at (ArchObj ao) p' s \<and> valid_vspace_obj (level-1) ao s)
                \<and> vref \<in> user_region) and
       K (is_PageTableCap acap \<and> cap_asid_arch acap \<noteq> None)
   | PageTableUnmap acap cslot \<Rightarrow>
       cte_wp_at (\<lambda>c. is_arch_diminished (ArchObjectCap acap) c) cslot and valid_arch_cap acap
       and is_final_cap' (ArchObjectCap acap)
       and K (is_PageTableCap acap)"

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
  sorry (* FIXME RISCV
  apply (clarsimp simp:valid_slots_def)
  apply (wp hoare_vcg_ball_lift)
  done *)

definition
  "pt_walks top_level pt_ptr vptr target_pt_ptr ptes \<equiv>
     map (\<lambda>level. pt_walk top_level level pt_ptr vptr ptes) [0 .e. top_level]"

lemma pt_lookup_from_level_def:
  "pt_lookup_from_level level pt_ptr vptr target_pt_ptr = doE
     unlessE (0 < level) $ throwError InvalidRoot;
     lookups_opt \<leftarrow> liftE $ gets $ pt_walks level pt_ptr vptr target_pt_ptr o ptes_of;
     target_lookups \<leftarrow> returnOk $ filter (\<lambda>(l,p). p = target_pt_ptr) (map the (rev lookups_opt));
     whenE (target_lookups = []) $ throwError InvalidRoot;
     level \<leftarrow> returnOk $ fst $ hd target_lookups;
     returnOk $ pt_slot_offset (level - 1) target_pt_ptr vptr
   odE"
  sorry (* FIXME RISCV: this one will be fun. Maybe not necessary, and better to work on
                        the recursive version directly. *)

lemma pt_lookup_from_level_inv[wp]:
  "\<lbrace>Q and E\<rbrace> pt_lookup_from_level level pt_ptr vptr target_pt_ptr \<lbrace>\<lambda>_. Q\<rbrace>,\<lbrace>\<lambda>_. E\<rbrace>"
  unfolding pt_lookup_from_level_def by wpsimp

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
      and K (0 < asid \<and> asid \<le> mask asid_bits)
      and (\<lambda>s. pool_for_asid asid s = Some p)"

crunch device_state_inv[wp]: ackInterrupt "\<lambda>ms. P (device_state ms)"

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

crunch pred_tcb_at[wp]: set_vm_root "pred_tcb_at proj P t"
  (simp: crunch_simps)

lemmas set_vm_root_typ_ats [wp] = abs_typ_at_lifts [OF set_vm_root_typ_at]

lemma valid_pte_lift3:
  assumes x: "(\<And>P T p. \<lbrace>\<lambda>s. P (typ_at T p s)\<rbrace> f \<lbrace>\<lambda>rv s. P (typ_at T p s)\<rbrace>)"
  shows "\<lbrace>\<lambda>s. P (valid_pte level pte s)\<rbrace> f \<lbrace>\<lambda>rv s. P (valid_pte level pte s)\<rbrace>"
  apply (insert bool_function_four_cases[where f=P])
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_const_imp_lift hoare_vcg_disj_lift x)+
  apply (erule disjE)
   apply (cases pte)
     apply (simp add: data_at_def | wp hoare_vcg_disj_lift hoare_vcg_const_imp_lift x)+
  apply (erule disjE)
   apply (simp | wp)+
  done


lemma set_cap_valid_pte_stronger:
  "set_cap cap p \<lbrace>\<lambda>s. P (valid_pte level pte s)\<rbrace>"
  by (wp valid_pte_lift3 set_cap_typ_at)

lemma store_pte_vspace_objs_map:
  "\<lbrace>valid_vspace_objs and
   (\<lambda>s. \<forall>ref. pte_ref pte = Some ref \<longrightarrow>
          (\<forall>level. \<exists>\<rhd>(level,table_base p) s \<longrightarrow>
                 (pt_at ref s \<or> data_at (vmpage_size_of_level level) ref s) \<and>
                 (\<forall>ao. aobjs_of s ref = Some ao \<longrightarrow> valid_vspace_obj level ao s)))\<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. valid_vspace_objs\<rbrace>"
  unfolding store_pte_def set_pt_def
  apply (wpsimp wp: set_object_wp)
  sorry (* FIXME RISCV
  apply (clarsimp simp: obj_at_def valid_vspace_objs_def
           simp del: fun_upd_apply
           split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (frule (1) vs_lookup_map_some_pdes.intro, simp add: obj_at_def)
  apply (frule vs_lookup_map_some_pdes.vs_lookup2)
  apply (drule(1) subsetD)
  apply (erule UnE)
   apply (simp only: fun_upd_apply split: if_split_asm)
    apply (rule valid_vspace_obj_same_type)
      apply fastforce
     apply assumption
    apply (clarsimp simp add: a_type_def)
   apply (rule valid_vspace_obj_same_type)
     apply fastforce
    apply assumption
   apply (clarsimp simp: a_type_def)
  apply (clarsimp simp add: vs_lookup_map_some_pdes.new_lookups_def)
  apply (drule(1) bspec)+
  apply (clarsimp simp add: a_type_simps  split: if_split_asm)
  apply (drule mp, erule exI)+
  apply (erule(1) valid_vspace_obj_same_type)
  apply (simp add: a_type_def)
  done
  *)

lemma store_pte_valid_vs_lookup_map:
  "\<lbrace>valid_vs_lookup and valid_arch_state and valid_vspace_objs and
    (\<lambda>s. \<forall>ref. pte_ref pte = Some ref \<longrightarrow>
           (\<forall>level. \<exists>\<rhd>(level, table_base p) s \<longrightarrow>
               (pt_at ref s \<or> data_at (vmpage_size_of_level level) ref s) \<and>
               (\<forall>ao. aobjs_of s ref = Some ao \<longrightarrow> valid_vspace_obj level ao s))) and
    (\<lambda>s. \<forall>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<longrightarrow>
           (\<forall>ref. pte_ref pte = Some ref \<longrightarrow>
              (\<exists>cslot cap.
                 caps_of_state s cslot = Some cap \<and>
                 obj_refs cap = {r} \<and>
                 vs_cap_ref cap = Some (asid, vref_for_level vref level)))) and
    (\<lambda>s. is_PageTablePTE pte \<longrightarrow> (\<forall>ref. pte_ref pte = Some ref \<longrightarrow> pts_of s ref = Some empty_pt))\<rbrace>
   store_pte p pte
   \<lbrace>\<lambda>rv. valid_vs_lookup\<rbrace>"
  sorry (* FIXME RISCV *)

lemma store_pte_invs_map: (* FIXME RISCV: probably missing some preconditions *)
  "\<lbrace>\<lambda>s. invs s \<and>
    (\<forall>ref. pte_ref pte = Some ref \<longrightarrow>
           (\<forall>level. \<exists>\<rhd>(level, table_base p) s \<longrightarrow>
               (pt_at ref s \<or> data_at (vmpage_size_of_level level) ref s) \<and>
               (\<forall>ao. aobjs_of s ref = Some ao \<longrightarrow> valid_vspace_obj level ao s))) \<and>
    (\<forall>level asid vref. vs_lookup_slot level asid vref s = Some (level, p) \<longrightarrow>
           (\<forall>ref. pte_ref pte = Some ref \<longrightarrow>
              (\<exists>cslot cap.
                 caps_of_state s cslot = Some cap \<and>
                 obj_refs cap = {r} \<and>
                 vs_cap_ref cap = Some (asid, vref_for_level vref level)))) \<and>
    (is_PageTablePTE pte \<longrightarrow> (\<forall>ref. pte_ref pte = Some ref \<longrightarrow> pts_of s ref = Some empty_pt)) \<and>
    (\<exists>p' cap. caps_of_state s p' = Some cap \<and> is_pt_cap cap \<and> p \<in> obj_refs cap \<and>
              cap_asid cap \<noteq> None) \<rbrace>
  store_pte p pte \<lbrace>\<lambda>_. invs\<rbrace>"
  unfolding invs_def valid_state_def valid_pspace_def
  sorry (* FIXME RISCV *)

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
                 obj_at_def is_ep is_ntfn is_cap_table is_tcb a_type_def
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
  apply (drule(1) unique_table_capsD[rotated, where cps="caps_of_state s"])
      apply simp
     apply (simp add: is_pt_cap_asid_None_table_ref)
  sorry (* FIXME RISCV
    apply fastforce
   apply assumption
  apply simp
  done *)


lemmas store_pte_cte_wp_at1[wp]
    = hoare_cte_wp_caps_of_state_lift [OF store_pte_caps_of_state]

lemma mdb_cte_at_store_pte[wp]:
  "store_pte y pte \<lbrace>\<lambda>s. mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)\<rbrace>"
  apply (clarsimp simp:mdb_cte_at_def)
  apply (simp only: imp_conv_disj)
  apply (wpsimp wp: hoare_vcg_disj_lift hoare_vcg_all_lift simp: store_pte_def set_pt_def)
  done

crunches store_pte
  for valid_idle[wp]: valid_idle
  and global_refs[wp]: "\<lambda>s. P (global_refs s)"

lemma update_self_reachable:
  "\<lbrakk>vs_lookup_table level asid vref s = Some (level, p);
    valid_asid_table s; valid_vspace_objs s\<rbrakk>
   \<Longrightarrow> vs_lookup_table level asid vref (s\<lparr>kheap := (kheap s) (p \<mapsto> v)\<rparr>) = Some (level, p)"
  sorry (* FIXME RISCV *)


lemma update_self_reachable_target:
  "\<lbrakk>vs_lookup_target level asid vref s = Some (level, p);
    valid_asid_table s; valid_vspace_objs s\<rbrakk>
   \<Longrightarrow> vs_lookup_target level asid vref (s\<lparr>kheap := (kheap s) (p \<mapsto> v)\<rparr>) = Some (level, p)"
  sorry (* FIXME RISCV *)

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
  sorry (* FIXME RISCV
  apply (rule conjI)
   apply (fastforce simp:is_valid_vtable_root_def vs_cap_ref_def split:arch_cap.splits vmpage_size.splits option.splits)
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
                            is_cap_simps
                     split: cap.split_asm arch_cap.split_asm
                     dest!: cap_master_cap_eqDs)
     apply (simp add: valid_arch_caps_def)
    apply (simp add: valid_pspace_def)
   apply (erule swap)
   apply (erule vs_cap_ref_eq_imp_table_cap_ref_eq'[symmetric])
   apply (frule table_cap_ref_vs_cap_ref_Some)
   apply simp
  apply (rule conjI)
   apply (clarsimp simp del: imp_disjL)
   apply (erule disjE)
    apply (clarsimp simp: is_pt_cap_def cap_master_cap_simps
                          cap_asid_def vs_cap_ref_def
                   dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
    apply (drule valid_table_capsD[OF caps_of_state_cteD])
       apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
      apply (simp add: is_pt_cap_def)
     apply (simp add: cap_asid_def)
    apply simp
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps
                          cap_asid_def vs_cap_ref_def
                   dest!: cap_master_cap_eqDs split: option.split_asm prod.split_asm)
   apply (drule valid_table_capsD[OF caps_of_state_cteD])
      apply (clarsimp simp: invs_def valid_state_def valid_arch_caps_def)
     apply (simp add: is_cap_simps)
    apply (simp add: cap_asid_def)
   apply simp
  apply (clarsimp simp: is_cap_simps is_pt_cap_def cap_master_cap_simps
                        cap_asid_def vs_cap_ref_def ranI
                 dest!: cap_master_cap_eqDs split: option.split_asm if_split_asm
                 elim!: ranE cong: master_cap_eq_is_device_cap_eq
             | rule conjI)+
  apply (clarsimp dest!: master_cap_eq_is_device_cap_eq)

  done *)

    (* Want something like
       cte_wp_at (\<lambda>c. \<forall>p'\<in>obj_refs c. \<not>(vs_cap_ref c \<unrhd> p') s \<and> is_arch_update cap c) p
       So that we know the new cap isn't clobbering a cap with necessary mapping info.
       invs is fine here (I suspect) because we unmap the page BEFORE we replace the cap.
    *)

lemma arch_update_cap_invs_unmap_page:
  "\<lbrace>(\<lambda>s. cte_wp_at (\<lambda>c. \<forall>p'\<in>obj_refs c. \<forall>asid vref level. vs_cap_ref c = Some (asid,vref) \<longrightarrow>
           vs_lookup_target level asid vref s \<noteq> Some (level, p') \<and> is_arch_update cap c) p s)
             and invs and valid_cap cap
             and K (is_frame_cap cap)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
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
  sorry (* FIXME RISCV
  apply (rule conjI)
   apply (drule(1) if_unsafe_then_capD [OF caps_of_state_cteD])
    apply (clarsimp simp: cap_master_cap_def)
   apply (erule ex_cte_cap_wp_to_weakenE)
   apply (clarsimp simp: appropriate_cte_cap_def)
  apply (rule conjI)
   apply (drule valid_global_refsD2, clarsimp)
   subgoal by (simp add: cap_range_def)
  apply (rule conjI[rotated])
   apply (frule(1) cap_refs_in_kernel_windowD)
   apply (simp add: cap_range_def)
  apply (drule unique_table_refs_no_cap_asidE[where S="{p}"])
   apply (simp add: valid_arch_caps_def)
  apply (simp add: no_cap_to_obj_with_diff_ref_def table_cap_ref_def Ball_def)
  done *)

lemma arch_update_cap_invs_unmap_page_table:
  "\<lbrace>cte_wp_at (is_arch_update cap) p
             and invs and valid_cap cap
             and (\<lambda>s. cte_wp_at (\<lambda>c. is_final_cap' c s) p s)
             and obj_at (empty_table {}) (obj_ref_of cap)
             and (\<lambda>s. cte_wp_at (\<lambda>c. \<forall>asid vref level. vs_cap_ref c = Some (asid, vref)
                                \<longrightarrow> vs_lookup_target level asid vref s \<noteq> Some (level, p')) p s)
             and K (is_pt_cap cap \<and> vs_cap_ref cap = None)\<rbrace>
  set_cap cap p
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_pspace arch_update_cap_valid_mdb set_cap_idle
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
  sorry (* FIXME RISCV
  apply (intro conjI)
    apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                          cte_wp_at_caps_of_state)
    apply fastforce
   apply (clarsimp simp: obj_at_def empty_table_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply clarsimp
  apply fastforce
  done *)

lemma global_refs_arch_update_eq:
  "riscv_global_pts (f (arch_state s)) = riscv_global_pts (arch_state s) \<Longrightarrow>
   global_refs (arch_state_update f s) = global_refs s"
  by (simp add: global_refs_def)

lemma not_in_global_refs_vs_lookup:
  "(\<exists>\<rhd> (level,p)) s \<and> valid_vs_lookup s \<and> valid_global_refs s
            \<and> valid_arch_state s \<and> valid_global_objs s
            \<and> pt_at p s
        \<longrightarrow> p \<notin> global_refs s"
  sorry (* FIXME RISCV
  apply (clarsimp dest!: valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI])
  apply (drule(1) valid_global_refsD2)
  apply (simp add: cap_range_def)
  apply blast
  done *)


lemma unmap_page_table_invs[wp]:
  "\<lbrace>invs and K (asid \<le> mask asid_bits \<and> vaddr < kernel_base)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: unmap_page_table_def)
  sorry (* FIXME RISCV
  apply (rule hoare_pre)
   apply (wp dmo_invs | wpc | simp)+
      apply (rule_tac Q="\<lambda>_. invs and K (asid \<le> mask asid_bits)" in hoare_post_imp)
       apply safe
        apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                   underlying_memory m p" in use_valid)
          apply ((wp | simp)+)[3]
       apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
   apply (wp store_pde_invs_unmap page_table_mapped_wp | wpc | simp)+
  apply (simp add: lookup_pd_slot_pd pde_ref_def)
  apply (strengthen lookup_pd_slot_kernel_mappings_strg
                    not_in_global_refs_vs_lookup)
  apply (auto simp: vspace_at_asid_def)
  done *)

lemma final_cap_lift:
  assumes x: "\<And>P. \<lbrace>\<lambda>s. P (caps_of_state s)\<rbrace> f \<lbrace>\<lambda>rv s. P (caps_of_state s)\<rbrace>"
  shows      "\<lbrace>\<lambda>s. P (is_final_cap' cap s)\<rbrace> f \<lbrace>\<lambda>rv s. P (is_final_cap' cap s)\<rbrace>"
  by (simp add: is_final_cap'_def2 cte_wp_at_caps_of_state, rule x)

lemmas dmo_final_cap[wp] = final_cap_lift [OF do_machine_op_caps_of_state]
lemmas store_pte_final_cap[wp] = final_cap_lift [OF store_pte_caps_of_state]
lemmas unmap_page_table_final_cap[wp] = final_cap_lift [OF unmap_page_table_caps_of_state]

lemma store_pte_no_lookup_target:
  "\<lbrace>\<lambda>s. vs_lookup_target level asid vref s \<noteq> Some (level, q)\<rbrace>
   store_pte p InvalidPTE
   \<lbrace>\<lambda>_ s. vs_lookup_target level asid vref s \<noteq> Some (level, q)\<rbrace>"
  sorry (* FIXME RISCV: store_pte_InvalidPTE_vs_lookup
  apply (simp add: store_pte_def set_pt_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def)
  apply (erule swap, simp)
  apply (erule vs_lookup_pages_induct)
   apply (simp add: vs_lookup_pages_atI)
  apply (thin_tac "(ref \<unrhd> p) (kheap_update f s)" for ref p f)
  apply (erule vs_lookup_pages_step)
  by (fastforce simp: vs_lookup_pages1_def obj_at_def vs_refs_pages_def
                     graph_of_def image_def
              split: if_split_asm) *)

lemma mapM_swp_store_pte_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl\<in>set slots. table_base sl \<notin> global_refs s) and
    K (pte = InvalidPTE)\<rbrace>
  mapM (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (rule hoare_post_imp)
   prefer 2
   apply (rule mapM_wp')
   apply simp
   apply (rule hoare_pre, wp store_pte_invs hoare_vcg_const_Ball_lift
                             hoare_vcg_ex_lift)
    apply (clarsimp)+
  sorry (* FIXME RISCV *)

lemma mapM_x_swp_store_pte_invs_unmap:
  "\<lbrace>invs and (\<lambda>s. \<forall>sl \<in> set slots. table_base sl \<notin> global_refs s) and
    K (pte = InvalidPTE)\<rbrace>
  mapM_x (swp store_pte pte) slots \<lbrace>\<lambda>_. invs\<rbrace>"
  by (simp add: mapM_x_mapM | wp mapM_swp_store_pte_invs_unmap)+

lemma unmap_page_table_unmapped[wp]:
  "\<lbrace>pspace_aligned and valid_vspace_objs\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. vs_lookup_table level asid vaddr s \<noteq> Some (level', pt) \<rbrace>"
  sorry (* FIXME RISCV
  apply (simp add: unmap_page_table_def lookup_pd_slot_def Let_def
             cong: option.case_cong)
  apply (rule hoare_pre)
   apply ((wp store_pde_unmap_pt page_table_mapped_wp | wpc | simp)+)[1]
  apply (clarsimp simp: vspace_at_asid_def pd_aligned pd_bits_def pageBits_def)
  done *)

lemma unmap_page_table_unmapped2:
  "\<lbrace>pspace_aligned and valid_vspace_objs and pt_at pt and
      K (asid = asid' \<and> vaddr = vaddr' \<and> p = pt)\<rbrace>
     unmap_page_table asid vaddr pt
   \<lbrace>\<lambda>rv s. vs_lookup_table level asid' vaddr' s \<noteq> Some (level', p)\<rbrace>"
  sorry (* FIXME RISCV
  apply (rule hoare_gen_asm)
  apply (simp add: unmap_page_table_def lookup_pd_slot_def Let_def
             cong: option.case_cong)
  apply (rule hoare_pre)
   apply ((wp store_pde_unmap_page | wpc | simp)+)[1]
   apply (rule page_table_mapped_wp)
  apply (clarsimp simp: vspace_at_asid_def pd_aligned pd_bits_def pageBits_def)
  apply (drule vs_lookup_pages_2ConsD)
  apply (clarsimp simp: obj_at_def vs_refs_pages_def
                 dest!: vs_lookup_pages1D
                 split: Structures_A.kernel_object.splits
                        arch_kernel_obj.splits)
  apply (drule vs_lookup_pages_eq_ap[THEN fun_cong, symmetric, THEN iffD1])
  apply (erule swap)
  apply (drule (1) valid_vspace_objsD[rotated 2])
   apply (simp add: obj_at_def)
  apply (erule vs_lookup_step)
  apply (clarsimp simp: obj_at_def vs_refs_def vs_lookup1_def
                        graph_of_def image_def
                 split: if_split_asm)
  apply (drule bspec, fastforce)
  apply (auto simp: obj_at_def data_at_def valid_pde_def pde_ref_def pde_ref_pages_def
                 split: pde.splits)
  done *)

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

crunch underlying_memory[wp]: ackInterrupt, hwASIDFlush, read_sbadaddr, setVSpaceRoot, sfence
  "\<lambda>m'. underlying_memory m' p = um"
  (simp: cache_machine_op_defs machine_op_lift_def machine_rest_lift_def split_def)

crunches storeWord, ackInterrupt, hwASIDFlush, read_sbadaddr, setVSpaceRoot, sfence
  for device_state_inv[wp]: "\<lambda>ms. P (device_state ms)"
  (simp: crunch_simps)

crunch pspace_respects_device_region[wp]: perform_page_invocation "pspace_respects_device_region"
  (simp: crunch_simps wp: crunch_wps set_object_pspace_respects_device_region
         pspace_respects_device_region_dmo)

lemma perform_page_table_invocation_invs[wp]:
  notes no_irq[wp] hoare_pre [wp_pre del]
  shows
  "\<lbrace>invs and valid_pti pti\<rbrace>
   perform_page_table_invocation pti
   \<lbrace>\<lambda>_. invs\<rbrace>"
  sorry (* FIXME RISCV
  apply (cases pti)
   apply (clarsimp simp: valid_pti_def perform_page_table_invocation_def)
   apply (wp dmo_invs)
    apply (rule_tac Q="\<lambda>_. invs" in hoare_post_imp)
     apply safe
     apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                underlying_memory m p" in use_valid)
       apply ((clarsimp simp: machine_op_lift_def
                             machine_rest_lift_def split_def | wp)+)[3]
     apply(erule use_valid, wp no_irq_cleanByVA_PoU no_irq, assumption)
    apply (wp store_pde_map_invs)[1]
   apply simp
   apply (rule hoare_pre, wp arch_update_cap_invs_map arch_update_cap_pspace
             arch_update_cap_valid_mdb set_cap_idle update_cap_ifunsafe
             valid_irq_node_typ valid_pde_lift set_cap_typ_at
             set_cap_irq_handlers set_cap_empty_pde
             hoare_vcg_all_lift hoare_vcg_ex_lift hoare_vcg_imp_lift
             set_cap_arch_obj set_cap_obj_at_impossible set_cap_valid_arch_caps)
   apply (simp; intro conjI; clarsimp simp: cte_wp_at_caps_of_state)
     apply (clarsimp simp: is_pt_cap_def is_arch_update_def cap_master_cap_def
                           vs_cap_ref_simps
                    split: cap.splits arch_cap.splits option.splits)
    apply fastforce
   apply (rule exI, rule conjI, assumption)
   apply (clarsimp simp: is_pt_cap_def is_arch_update_def
                         cap_master_cap_def cap_asid_def vs_cap_ref_simps
                         is_arch_cap_def pde_ref_def pde_ref_pages_def
                  split: cap.splits arch_cap.splits option.splits
                         pde.splits)
   apply (intro allI impI conjI, fastforce)
   apply (clarsimp simp: caps_of_def cap_of_def)
   apply (frule invs_pd_caps)
   apply (drule (1) empty_table_pt_capI)
   apply (clarsimp simp: obj_at_def empty_table_def pte_ref_pages_def)
  apply (clarsimp simp: perform_page_table_invocation_def
                 split: cap.split arch_cap.split)
  apply (rename_tac word option)
  apply (rule hoare_pre)
   apply (wp arch_update_cap_invs_unmap_page_table get_cap_wp)
   apply (simp add: cte_wp_at_caps_of_state)
   apply (wpc, wp, wpc)
   apply (rule hoare_lift_Pf2[where f=caps_of_state])
    apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift)+
        apply (rule hoare_vcg_conj_lift)
         apply (wp dmo_invs)
        apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                  valid_cap_typ[OF do_machine_op_obj_at]
                  mapM_x_swp_store_pte_invs[unfolded cte_wp_at_caps_of_state]
                  mapM_x_swp_store_empty_table
                  valid_cap_typ[OF unmap_page_table_typ_at]
                  unmap_page_table_unmapped3)+
        apply (rule hoare_pre_imp[of _ \<top>], assumption)
        apply (clarsimp simp: valid_def split_def)
        apply safe[1]
         apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p =
                                    underlying_memory m p" in use_valid)
         apply ((clarsimp | wp)+)[3]
               apply(erule use_valid, wp no_irq_cleanCacheRange_PoU, assumption)
       apply (wp hoare_vcg_all_lift hoare_vcg_const_imp_lift
                 valid_cap_typ[OF do_machine_op_obj_at]
                 mapM_x_swp_store_pte_invs[unfolded cte_wp_at_caps_of_state]
                 mapM_x_swp_store_empty_table
                 valid_cap_typ[OF unmap_page_table_typ_at]
                 unmap_page_table_unmapped3 store_pte_no_lookup_pages
              | wp_once hoare_vcg_conj_lift
              | wp_once mapM_x_wp'
              | simp)+
  apply (clarsimp simp: valid_pti_def cte_wp_at_caps_of_state
                        is_arch_diminished_def is_cap_simps
                        is_arch_update_def cap_rights_update_def
                        acap_rights_update_def cap_master_cap_simps
                        update_map_data_def)
  apply (frule (2) diminished_is_update')
  apply (simp add: cap_rights_update_def acap_rights_update_def)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
   apply (drule invs_pd_caps)
   apply (simp add: valid_table_caps_def)
   apply (elim allE, drule(1) mp)
   apply (simp add: is_cap_simps cap_asid_def)
   apply (drule mp, rule refl)
   apply (clarsimp simp: obj_at_def valid_cap_def empty_table_def
                         a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.split_asm
                          arch_kernel_obj.split_asm)
  apply (clarsimp simp: valid_cap_def mask_def[where n=asid_bits]
                        vmsz_aligned_def cap_aligned_def vs_cap_ref_def
                        invs_psp_aligned invs_vspace_objs)
  apply (subgoal_tac "(\<forall>x\<in>set [word , word + 4 .e. word + 2 ^ pt_bits - 1].
                             x && ~~ mask pt_bits = word)")
   apply (intro conjI)
      apply (simp add: cap_master_cap_def)
     apply fastforce
    apply (clarsimp simp: image_def)
    apply (subgoal_tac "word + (ucast x << 2)
                   \<in> set [word, word + 4 .e. word + 2 ^ pt_bits - 1]")
     apply (rule rev_bexI, assumption)
     apply (rule ccontr, erule more_pt_inner_beauty)
     apply simp
    apply (clarsimp simp: upto_enum_step_def linorder_not_less)
    apply (subst is_aligned_no_overflow,
           erule is_aligned_weaken,
           (simp_all add: pt_bits_def pageBits_def)[2])+
    apply (clarsimp simp: image_def word_shift_by_2)
    apply (rule exI, rule conjI[OF _ refl])
    apply (rule plus_one_helper)
    apply (rule order_less_le_trans, rule ucast_less, simp+)
  apply (clarsimp simp: upto_enum_step_def)
  apply (rule conjunct2, rule is_aligned_add_helper)
   apply (simp add: pt_bits_def pageBits_def)
  apply (simp only: word_shift_by_2)
  apply (rule shiftl_less_t2n)
   apply (rule minus_one_helper5)
    apply (simp add: pt_bits_def pageBits_def)+
  done *)

crunch cte_wp_at [wp]: unmap_page "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

crunch typ_at [wp]: unmap_page "\<lambda>s. P (typ_at T p s)"
  (wp: crunch_wps simp: crunch_simps)

lemmas unmap_page_typ_ats [wp] = abs_typ_at_lifts [OF unmap_page_typ_at]

lemma pt_lookup_slot_cap_to:
  "\<lbrakk> invs s; \<exists>\<rhd>(max_pt_level, pt) s; is_aligned pt pt_bits; vptr < kernel_base;
     pt_lookup_slot pt vptr (ptes_of s) = Some (level, slot) \<rbrakk>
   \<Longrightarrow> \<exists>p cap. caps_of_state s p = Some cap \<and> is_pt_cap cap \<and> obj_refs cap = {table_base slot} \<and>
               s \<turnstile> cap \<and> cap_asid cap \<noteq> None"
  sorry (* FIXME RISCV
  apply (simp add: pt_lookup_slot_def)
  apply (wp get_pde_wp | wpc)+
  apply (clarsimp simp: lookup_pd_slot_pd)
  apply (frule(1) valid_vspace_objsD)
   apply fastforce
  apply (drule vs_lookup_step)
   apply (erule vs_lookup1I[OF _ _ refl])
   apply (simp add: vs_refs_def image_def)
   apply (rule rev_bexI)
    apply (erule pde_graph_ofI)
     apply (erule (1) less_kernel_base_mapping_slots)
    apply (simp add: pde_ref_def)
   apply fastforce
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply simp
  apply (elim exEI, clarsimp)
  apply (subst is_aligned_add_helper[THEN conjunct2])
    apply (drule caps_of_state_valid)
     apply fastforce
    apply (clarsimp dest!:valid_cap_aligned simp:cap_aligned_def vs_cap_ref_def
      obj_refs_def obj_ref_of_def pageBitsForSize_def pt_bits_def pageBits_def
      elim!:is_aligned_weaken
      split:arch_cap.split_asm cap.splits option.split_asm vmpage_size.split_asm)
   apply (rule less_le_trans[OF shiftl_less_t2n[where m = 10]])
     apply (rule le_less_trans[OF word_and_le1])
     apply simp
    apply simp
   apply (simp add:pt_bits_def pageBits_def)
  apply (drule caps_of_state_valid)
   apply fastforce
  apply (drule bspec)
   apply (drule(1) less_kernel_base_mapping_slots)
   apply simp
  apply (clarsimp simp: valid_pde_def obj_at_def
                        vs_cap_ref_def is_pt_cap_def valid_cap_simps cap_aligned_def
                 split: cap.split_asm arch_cap.split_asm vmpage_size.splits
                        option.split_asm if_splits)
    apply (erule is_aligned_add[OF is_aligned_weaken],simp
      ,rule is_aligned_shiftl[OF is_aligned_andI1,OF is_aligned_shiftr],simp)+
  done
  *)

lemma find_vspace_for_asid_cap_to:
   "\<lbrace>invs\<rbrace> find_vspace_for_asid asid
   \<lbrace>\<lambda>rv s.  \<exists>a b cap. caps_of_state s (a, b) = Some cap \<and> rv \<in> obj_refs cap
                                \<and> is_pt_cap cap \<and> s \<turnstile> cap
                                \<and> is_aligned rv pt_bits\<rbrace>, -"
  sorry (* FIXME RISCV
  apply (simp add: find_vspace_for_asid_def assertE_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp | wpc)+
  apply clarsimp
  apply (drule vs_lookup_atI)
  apply (frule(1) valid_vspace_objsD, clarsimp)
  apply (drule vs_lookup_step)
   apply (erule vs_lookup1I [OF _ _ refl])
   apply (simp add: vs_refs_def image_def)
   apply (rule rev_bexI)
    apply (erule graph_ofI)
   apply fastforce
  apply (drule valid_vs_lookupD[OF vs_lookup_pages_vs_lookupI], clarsimp)
  apply (simp, elim exEI)
  apply clarsimp
  apply (frule caps_of_state_valid_cap, clarsimp+)
  apply (clarsimp simp: table_cap_ref_ap_eq[symmetric] table_cap_ref_def
                        is_pd_cap_def valid_cap_def cap_aligned_def
                        pd_bits_def pageBits_def
                 split: cap.split_asm arch_cap.split_asm option.split_asm)
  done *)

lemma ex_pt_cap_eq:
  "(\<exists>ref cap. caps_of_state s ref = Some cap \<and>
              p \<in> obj_refs cap \<and> is_pt_cap cap) =
   (\<exists>ref asid. caps_of_state s ref =
               Some (cap.ArchObjectCap (arch_cap.PageTableCap p asid)))"
  by (fastforce simp add: is_pt_cap_def obj_refs_def is_PageTableCap_def)

lemma unmap_page_invs:
  "\<lbrace>invs and K (asid \<le> mask asid_bits \<and> vptr < kernel_base \<and>
                vmsz_aligned vptr sz)\<rbrace>
      unmap_page sz asid vptr pptr
   \<lbrace>\<lambda>rv. invs\<rbrace>"
  sorry (* FIXME RISCV
  apply (simp add: unmap_page_def)
  apply (rule hoare_pre)
   apply (wp flush_page_invs hoare_vcg_const_imp_lift)
    apply (wp hoare_drop_imp[where f="check_mapping_pptr a b c" for a b c]
              hoare_drop_impE_R[where R="\<lambda>x y. x && mask b = c" for b c]
              pt_lookup_slot_inv pt_lookup_slot_cap_to2'
              pt_lookup_slot_cap_to_multiple2
              store_pde_invs_unmap mapM_swp_store_pde_invs_unmap
              mapM_swp_store_pte_invs
           | wpc | simp)+
   apply (strengthen lookup_pd_slot_kernel_mappings_strg
                     lookup_pd_slot_kernel_mappings_set_strg
                     not_in_global_refs_vs_lookup
                     page_directory_at_lookup_mask_aligned_strg
                     page_directory_at_lookup_mask_add_aligned_strg)+
   apply (wp find_vspace_for_asid_page_directory
             hoare_vcg_const_imp_lift_R hoare_vcg_const_Ball_lift_R
          | wp_once hoare_drop_imps)+
  apply (auto simp: vmsz_aligned_def)
  done *)

crunch cte_wp_at [wp]: unmap_page "\<lambda>s. P (cte_wp_at P' p s)"
  (wp: crunch_wps simp: crunch_simps)

lemma reachable_page_table_not_global:
  "\<lbrakk> vs_lookup_table level asid vref s = Some (level, p); vref \<in> user_region;
      valid_kernel_mappings s; valid_vspace_objs s; valid_asid_table s\<rbrakk>
   \<Longrightarrow> p \<notin> (\<Union>level. riscv_global_pts (arch_state s) level)"
  apply clarsimp
  sorry (* FIXME RISCV
  apply (erule (2) vs_lookupE_alt[OF _ _ valid_asid_table_ran])
    apply (clarsimp simp: valid_global_pts_def)
    apply (drule (1) bspec)
    apply (clarsimp simp: obj_at_def a_type_def)
   apply (clarsimp simp: valid_global_pts_def)
   apply (drule (1) bspec)
   apply (clarsimp simp: obj_at_def a_type_def)
  apply (clarsimp simp: valid_kernel_mappings_def valid_kernel_mappings_if_pd_def ran_def)
  apply (drule_tac x="ArchObj (PageDirectory pd)" in spec)
  apply (drule mp, erule_tac x=p\<^sub>2 in exI)
  apply clarsimp
  done *)

lemma unmap_page_no_lookup_target:
  "unmap_page sz asid vaddr pptr \<lbrace>\<lambda>s. vs_lookup_target level asid vaddr s \<noteq> Some (level', p)\<rbrace>"
  sorry (* FIXME RISCV
  apply (rule hoare_pre)
  apply (wp store_pte_no_lookup_pages hoare_drop_imps pt_lookup_slot_inv_validE
         mapM_UNIV_wp store_pde_no_lookup_pages
      | wpc | simp add: unmap_page_def swp_def | strengthen imp_consequent)+
  done *)

lemma unmap_page_unmapped:
  "\<lbrace>pspace_aligned and valid_vspace_objs and data_at sz pptr and
    valid_objs and valid_asid_table and
    K (asid' = asid \<and> vaddr' = vaddr \<and> p = pptr)\<rbrace>
   unmap_page sz asid vaddr pptr
   \<lbrace>\<lambda>rv s. vs_lookup_target level asid' vaddr' s \<noteq> Some (level', p)\<rbrace>"
  sorry (* FIXME RISCV
  apply (rule hoare_gen_asm)

    (* Establish that pptr reachable, otherwise trivial *)
  apply (rule hoare_name_pre_state2)
  apply (case_tac "\<not> (ref \<unrhd> p) s")
   apply (rule hoare_pre(1)[OF unmap_page_no_lookup_target])
   apply clarsimp+

     (* This should be somewhere else but isn't *)
  apply (subgoal_tac "\<exists>xs. [0 :: word32, 4 .e. 0x3C] = 0 # xs")
   prefer 2
   apply (simp add: upto_enum_step_def upto_enum_word upt_rec)
  apply (clarsimp simp: unmap_page_def lookup_pd_slot_def pt_lookup_slot_def Let_def
                        mapM_Cons
                  cong: option.case_cong vmpage_size.case_cong)

    (* Establish that pde in vsref chain isn't kernel mapping,
       otherwise trivial *)
  apply (case_tac "ucast (vaddr >> 20) \<in> kernel_mapping_slots")
   apply (case_tac sz)
       apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages | wp)+)[2]
     apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages2 | wp)+)[1]
    apply ((clarsimp simp: kernel_slot_impossible_vs_lookup_pages2 | wp)+)[1]

      (* Proper cases *)
  apply (wp store_pte_unmap_page
            mapM_UNIV_wp[OF store_pte_no_lookup_pages]
            get_pte_wp get_pde_wp store_pde_unmap_page
            mapM_UNIV_wp[OF store_pde_no_lookup_pages]
            flush_page_vs_lookup flush_page_vs_lookup_pages
            hoare_vcg_all_lift hoare_vcg_const_imp_lift
            hoare_vcg_imp_lift[OF flush_page_pd_at]
            hoare_vcg_imp_lift[OF flush_page_pt_at]
            find_vspace_for_asid_lots
         | wpc | simp add: swp_def check_mapping_pptr_def)+
  apply clarsimp
  apply (case_tac sz, simp_all)
     apply (drule vs_lookup_pages_pteD)
     apply (rule conjI[rotated])
      apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
     apply clarsimp
     apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
     apply (frule (1) pd_aligned)
     apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
     apply (frule valid_vspace_objsD)
       apply (clarsimp simp: obj_at_def a_type_def)
       apply (rule refl)
      apply assumption
     apply (simp, drule bspec, fastforce)
     apply (clarsimp simp: pde_ref_pages_def
                    split: pde.splits
                    dest!: )
       apply (frule pt_aligned[rotated])
        apply (simp add: obj_at_def a_type_def)
        apply (simp split: Structures_A.kernel_object.splits arch_kernel_obj.splits, blast)
       apply (clarsimp simp: obj_at_def)
       apply (simp add: vaddr_segment_nonsense3[where vaddr=vaddr]
                        vaddr_segment_nonsense4[where vaddr=vaddr])
       apply (drule_tac p="ptrFromPAddr x" for x in vs_lookup_vs_lookup_pagesI')
          apply ((simp add: obj_at_def a_type_def)+)[3]
       apply (frule_tac p="ptrFromPAddr a" for a in valid_vspace_objsD)
         apply ((simp add: obj_at_def)+)[2]
       apply (simp add: )
       apply (intro conjI impI)
        apply (simp add: pt_bits_def pageBits_def mask_def)
       apply (erule allE[where x="(ucast ((vaddr >> 12) && mask 8))"])
       apply (fastforce simp: pte_ref_pages_def mask_def obj_at_def a_type_def data_at_def
                             shiftl_shiftr_id[where n=2,
                                             OF _ less_le_trans[OF and_mask_less'[where n=8]],
                                             unfolded mask_def word_bits_def, simplified]
                      split: pte.splits if_splits)
      apply ((clarsimp simp: obj_at_def a_type_def data_at_def)+)[2]

    apply (drule vs_lookup_pages_pteD)
    apply (rule conjI[rotated])
     apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
    apply clarsimp
    apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
    apply (frule (1) pd_aligned)
    apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
    apply (frule valid_vspace_objsD)
      apply (clarsimp simp: obj_at_def a_type_def)
      apply (rule refl)
     apply assumption
    apply (simp, drule bspec, fastforce)
    apply (clarsimp simp: pde_ref_pages_def
                   split: pde.splits
                   dest!: )
      apply (frule pt_aligned[rotated])
       apply (simp add: obj_at_def a_type_def)
       apply (simp split: Structures_A.kernel_object.splits arch_kernel_obj.splits, blast)
      apply (clarsimp simp: obj_at_def)
      apply (simp add: vaddr_segment_nonsense3[where vaddr=vaddr]
                       vaddr_segment_nonsense4[where vaddr=vaddr])
      apply (drule_tac p="ptrFromPAddr x" for x in vs_lookup_vs_lookup_pagesI')
         apply ((simp add: obj_at_def a_type_def)+)[3]
      apply (frule_tac p="ptrFromPAddr a" for a in valid_vspace_objsD)
        apply ((simp add: obj_at_def)+)[2]
      apply (simp add: )
      apply (intro conjI impI)
       apply (simp add: pt_bits_def pageBits_def mask_def)
      apply (erule allE[where x="(ucast ((vaddr >> 12) && mask 8))"])

       apply (fastforce simp: pte_ref_pages_def mask_def obj_at_def a_type_def data_at_def
                             shiftl_shiftr_id[where n=2,
                                             OF _ less_le_trans[OF and_mask_less'[where n=8]],
                                             unfolded mask_def word_bits_def, simplified]
                      split: pte.splits if_splits)
      apply ((clarsimp simp: obj_at_def a_type_def data_at_def)+)[2]
   apply (drule vs_lookup_pages_pdeD)
   apply (rule conjI[rotated])
    apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
   apply clarsimp
   apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
   apply (frule (1) pd_aligned)
   apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
   apply (frule valid_vspace_objsD)
     apply (clarsimp simp: obj_at_def a_type_def)
     apply (rule refl)
    apply assumption
   apply (simp, drule bspec, fastforce)
   apply (clarsimp simp: pde_ref_pages_def
                  split: pde.splits)
     apply (clarsimp simp: obj_at_def data_at_def)
    apply (drule_tac p="rv" in vs_lookup_vs_lookup_pagesI')
       apply ((simp add: obj_at_def a_type_def)+)[3]
    apply (frule_tac p="rv" in valid_vspace_objsD)
      apply ((simp add: obj_at_def)+)[2]
    apply (fastforce simp: data_at_def)
   apply (fastforce simp: obj_at_def a_type_def pd_bits_def pageBits_def data_at_def
                   split: pde.splits)
   apply (fastforce simp: obj_at_def a_type_def data_at_def)

  apply (drule vs_lookup_pages_pdeD)
  apply (rule conjI[rotated])
   apply (fastforce simp add: vs_lookup_pages_eq_ap[THEN fun_cong, symmetric])
  apply clarsimp
  apply (frule_tac p=pd and p'=rv in unique_vs_lookup_pages, erule vs_lookup_pages_vs_lookupI)
  apply (frule (1) pd_aligned)
  apply (simp add: vaddr_segment_nonsense[where vaddr=vaddr] vaddr_segment_nonsense2[where vaddr=vaddr])
  apply (frule valid_vspace_objsD)
    apply (clarsimp simp: obj_at_def a_type_def)
    apply (rule refl)
   apply assumption
  apply (simp, drule bspec, fastforce)
  apply (clarsimp simp: pde_ref_pages_def
                 split: pde.splits)
    apply (fastforce simp: obj_at_def data_at_def)
   apply (drule_tac p="rv" in vs_lookup_vs_lookup_pagesI')
      apply ((simp add: obj_at_def a_type_def)+)[3]
   apply (frule_tac p="rv" in valid_vspace_objsD)
     apply ((simp add: obj_at_def)+)[2]
   apply (simp add: )
   apply (drule bspec[where x="ucast (vaddr >> 20)"], simp)
   apply (fastforce simp: obj_at_def a_type_def pd_bits_def pageBits_def data_at_def
                  split: pde.splits)
  apply (clarsimp simp: obj_at_def a_type_def pd_bits_def pageBits_def)
  done*)

lemma set_mi_invs[wp]: "\<lbrace>invs\<rbrace> set_message_info t a \<lbrace>\<lambda>x. invs\<rbrace>"
  by (simp add: set_message_info_def, wp)

lemma data_at_orth:
  "data_at a p s
   \<Longrightarrow> \<not> ep_at p s \<and> \<not> ntfn_at p s \<and> \<not> cap_table_at sz p s \<and> \<not> tcb_at p s \<and> \<not> asid_pool_at p s
         \<and> \<not> pt_at p s \<and> \<not> asid_pool_at p s"
  apply (clarsimp simp: data_at_def obj_at_def a_type_def)
  apply (case_tac "kheap s p",simp)
  subgoal for ko by (case_tac ko,auto simp add: is_ep_def is_ntfn_def is_cap_table_def is_tcb_def)
  done

lemma data_at_frame_cap:
  "\<lbrakk>data_at sz p s; valid_cap cap s; p \<in> obj_refs cap\<rbrakk> \<Longrightarrow> is_frame_cap cap"
  by (cases cap; clarsimp simp: is_frame_cap_def valid_cap_def valid_arch_cap_ref_def data_at_orth
                         split: option.splits arch_cap.splits)

lemma perform_page_invs [wp]:
  "\<lbrace>invs and valid_page_inv pg_inv\<rbrace> perform_page_invocation pg_inv \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (simp add: perform_page_invocation_def)
  sorry (* FIXME RISCV
  apply (cases pg_inv, simp_all)
     \<comment> \<open>PageMap\<close>
     apply (rename_tac asid cap cslot_ptr sum)
     apply clarsimp
     apply (rule hoare_pre)
      apply (wp get_master_pte_wp get_master_pde_wp mapM_swp_store_pde_invs_unmap store_pde_invs_unmap' hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_arch_obj arch_update_cap_invs_map
             | wpc
             | simp add: pte_check_if_mapped_def pde_check_if_mapped_def del: fun_upd_apply
             | subst cte_wp_at_caps_of_state)+
       apply (wp_once hoare_drop_imp)
       apply (wp arch_update_cap_invs_map)
       apply (rule hoare_vcg_conj_lift)
        apply (rule hoare_lift_Pf[where f=vs_lookup, OF _ set_cap.vs_lookup])
        apply (rule_tac f="valid_pte xa" in hoare_lift_Pf[OF _ set_cap_valid_pte_stronger])
        apply wp
       apply (rule hoare_lift_Pf2[where f=vs_lookup, OF _ set_cap.vs_lookup])
       apply ((wp dmo_ccr_invs arch_update_cap_invs_map
                 hoare_vcg_const_Ball_lift
                 hoare_vcg_const_imp_lift hoare_vcg_all_lift set_cap_typ_at
                 hoare_vcg_ex_lift hoare_vcg_ball_lift set_cap_arch_obj
                 set_cap.vs_lookup
              | wpc | simp add: same_refs_def del: fun_upd_apply split del: if_split
              | subst cte_wp_at_caps_of_state)+)
      apply (wp_once hoare_drop_imp)
      apply (wp arch_update_cap_invs_map hoare_vcg_ex_lift set_cap_arch_obj)
     apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state neq_Nil_conv
                           valid_slots_def empty_refs_def parent_for_refs_def
                 simp del: fun_upd_apply del: exE
                    split: sum.splits)
      apply (rule conjI)
       apply (clarsimp simp: is_cap_simps is_arch_update_def
                             cap_master_cap_simps
                      dest!: cap_master_cap_eqDs)
      apply clarsimp
      apply (rule conjI)
       apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
       apply (rule conjI)
        apply (clarsimp simp: is_arch_update_def is_pt_cap_def is_pg_cap_def
                              cap_master_cap_def image_def
                        split: Structures_A.cap.splits arch_cap.splits)
       apply (clarsimp simp: is_pt_cap_def cap_asid_def image_def neq_Nil_conv Collect_disj_eq
                      split: Structures_A.cap.splits arch_cap.splits option.splits)
      apply (rule conjI)
       apply (drule same_refs_lD)
       apply clarsimp
       apply fastforce
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (erule exEI)
      apply clarsimp
     apply (rule conjI)
      apply clarsimp
      apply (rule_tac x=aa in exI, rule_tac x=ba in exI)
      apply (clarsimp simp: is_arch_update_def
                            cap_master_cap_def is_cap_simps
                     split: Structures_A.cap.splits arch_cap.splits)
     apply (rule conjI)
      apply (rule_tac x=a in exI, rule_tac x=b in exI, rule_tac x=cap in exI)
      apply (clarsimp simp: same_refs_def)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
      apply (drule_tac cap=capc and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
        apply assumption+
      apply (clarsimp simp: cap_range_def)
     apply (clarsimp)
     apply (rule conjI)
      apply (clarsimp simp: pde_at_def obj_at_def a_type_def)
      apply (clarsimp split: Structures_A.kernel_object.split_asm
                            if_split_asm arch_kernel_obj.splits)
     apply (erule ballEI)
     apply (clarsimp simp: pde_at_def obj_at_def
                            caps_of_state_cteD'[where P=\<top>, simplified])
     apply (drule_tac cap=capc and ptr="(aa,ba)"
                    in valid_global_refsD[OF invs_valid_global_refs])
       apply assumption+
     apply (drule_tac x=sl in imageI[where f="\<lambda>x. x && ~~ mask pd_bits"])
     apply (drule (1) subsetD)
     apply (clarsimp simp: cap_range_def)
   \<comment> \<open>PageRemap\<close>
    apply (rule hoare_pre)
     apply (wp get_master_pte_wp get_master_pde_wp hoare_vcg_ex_lift mapM_x_swp_store_pde_invs_unmap
              | wpc | simp add: pte_check_if_mapped_def pde_check_if_mapped_def
              | (rule hoare_vcg_conj_lift, rule_tac slots=x2a in store_pde_invs_unmap'))+
    apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state
                          valid_slots_def empty_refs_def neq_Nil_conv
                    split: sum.splits)
     apply (clarsimp simp: parent_for_refs_def same_refs_def is_cap_simps cap_asid_def split: option.splits)
     apply (rule conjI, fastforce)
     apply (rule conjI)
      apply clarsimp
      apply (rule_tac x=ac in exI, rule_tac x=bc in exI, rule_tac x=capa in exI)
      apply clarsimp
      apply (erule (2) ref_is_unique[OF _ _ reachable_page_table_not_global])
              apply ((simp add: invs_def valid_state_def valid_arch_state_def
                                   valid_arch_caps_def valid_pspace_def valid_objs_caps)+)[9]
      apply fastforce
     apply( frule valid_global_refsD2)
      apply (clarsimp simp: cap_range_def parent_for_refs_def)+
    apply (rule conjI, rule impI)
     apply (rule exI, rule exI, rule exI)
     apply (erule conjI)
     apply clarsimp
    apply (rule conjI, rule impI)
     apply (rule_tac x=ac in exI, rule_tac x=bc in exI, rule_tac x=capa in exI)
     apply (clarsimp simp: same_refs_def pde_ref_def pde_ref_pages_def
                valid_pde_def invs_def valid_state_def valid_pspace_def)
     apply (drule valid_objs_caps)
     apply (clarsimp simp: valid_caps_def)
     apply (drule spec, drule spec, drule_tac x=capa in spec, drule (1) mp)
     apply (case_tac aa, (clarsimp simp add: data_at_pg_cap)+)[1]
    apply (clarsimp simp: pde_at_def obj_at_def a_type_def)

    apply (rule conjI)
     apply clarsimp
     apply (drule_tac ptr="(ab,bb)" in
            valid_global_refsD[OF invs_valid_global_refs caps_of_state_cteD])
       apply simp+
     apply force
    apply (erule ballEI)
    apply clarsimp
    apply (drule_tac ptr="(ab,bb)" in
            valid_global_refsD[OF invs_valid_global_refs caps_of_state_cteD])
      apply simp+
    apply force

   \<comment> \<open>PageUnmap\<close>
   apply (rename_tac arch_cap cslot_ptr)
   apply (rule hoare_pre)
    apply (wp dmo_invs arch_update_cap_invs_unmap_page get_cap_wp
              hoare_vcg_const_imp_lift | wpc | simp)+
      apply (rule_tac Q="\<lambda>_ s. invs s \<and>
                               cte_wp_at (\<lambda>c. is_pg_cap c \<and>
                                 (\<forall>ref. vs_cap_ref c = Some ref \<longrightarrow>
                                        \<not> (ref \<unrhd> obj_ref_of c) s)) cslot_ptr s"
                   in hoare_strengthen_post)
       prefer 2
       apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps
                             update_map_data_def
                             is_arch_update_def cap_master_cap_simps)
       apply (drule caps_of_state_valid, fastforce)
       apply (clarsimp simp: valid_cap_def cap_aligned_def vs_cap_ref_def
                      split: option.splits vmpage_size.splits cap.splits)
      apply (simp add: cte_wp_at_caps_of_state)
      apply (wp unmap_page_invs hoare_vcg_ex_lift hoare_vcg_all_lift
                hoare_vcg_imp_lift unmap_page_unmapped)+
   apply (clarsimp simp: valid_page_inv_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: is_arch_diminished_def)
   apply (drule (2) diminished_is_update')
   apply (clarsimp simp: is_cap_simps cap_master_cap_simps is_arch_update_def
                         update_map_data_def cap_rights_update_def
                         acap_rights_update_def)
   using valid_validate_vm_rights[simplified valid_vm_rights_def]
   apply (auto simp: valid_cap_def cap_aligned_def mask_def vs_cap_ref_def data_at_def
                   split: vmpage_size.splits option.splits if_splits)[1]

  \<comment> \<open>PageFlush\<close>
  apply (rule hoare_pre)
   apply (wp dmo_invs set_vm_root_for_flush_invs
             hoare_vcg_const_imp_lift hoare_vcg_all_lift
          | simp)+
    apply (rule hoare_pre_imp[of _ \<top>], assumption)
    apply (clarsimp simp: valid_def)
    apply (thin_tac "p \<in> fst (set_vm_root_for_flush a b s)" for p a b)
    apply(safe)
     apply (drule_tac Q="\<lambda>_ m'. underlying_memory m' p = underlying_memory m p"
            in use_valid)
       apply ((clarsimp | wp)+)[3]
    apply(erule use_valid, wp no_irq_do_flush no_irq, assumption)
   apply(wp set_vm_root_for_flush_invs | simp add: valid_page_inv_def tcb_at_invs)+
  done
  *)

end

locale asid_pool_map = Arch +
  fixes s ap pool asid ptp and s' :: "'a::state_ext state"
  defines "s' \<equiv> s\<lparr>kheap := kheap s(ap \<mapsto> ArchObj (ASIDPool (pool(asid_low_bits_of asid \<mapsto> ptp))))\<rparr>"
  assumes ap:  "asid_pools_of s ap = Some pool"
  assumes new: "pool (asid_low_bits_of asid) = None"
  assumes pt:  "pts_of s ptp = Some empty_pt"
  (* FIXME RISCV: empty_pt is wrong, need to capture kernel mappings, which should be present at
                  this stage *)
  assumes lookup: "pool_for_asid asid s = Some ap"
begin

lemma arch_state[simp]:
  "arch_state s' = arch_state s"
  by (simp add: s'_def)


(* FIXME RISCV: since empty_pt is wrong, this is only true for vref in user region;
                we might also need something about kernel mappings, but maybe not for vs_lookup *)
lemma vs_lookup_table:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_table level asid' vref s' =
     (if asid' = asid \<and> level = max_pt_level
      then Some (level, ptp)
      else vs_lookup_table level asid' vref s)"
  sorry

(* FIXME RISCV: see above, statement might need tweak *)
lemma vs_lookup_target:
  "vref \<in> user_region \<Longrightarrow>
   vs_lookup_target level asid' vref s' =
     (if asid' = asid \<and> level = asid_pool_level
      then Some (level, ptp)
      else vs_lookup_target level asid' vref s)"
  sorry

end

context Arch begin global_naming RISCV64

lemma set_asid_pool_arch_objs_map:
  "\<lbrace>valid_vspace_objs and valid_arch_state and valid_global_objs and
    valid_kernel_mappings and
    (\<lambda>s. asid_pools_of s ap = Some pool) and
    K (pool (asid_low_bits_of asid) = None) and
    (\<lambda>s. pool_for_asid asid s = Some ap) and
    (\<lambda>s. obj_at (empty_table (set (second_level_tables (arch_state s)))) pt s) \<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> pt))
  \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  sorry  (* FIXME RISCV: lemma statement --
            need to capture kernel mappings, which should be present at this stage
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp del: fun_upd_apply
                  split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (frule (2) valid_vspace_objsD)
  apply (clarsimp simp: valid_vspace_objs_def simp del: valid_vspace_obj.simps)
  apply (case_tac "p = ap")
   apply (clarsimp simp: obj_at_def
               simp del: fun_upd_apply valid_vspace_obj.simps)
   apply (clarsimp simp: ran_def)
   apply (case_tac "a = asid")
    apply clarsimp
    apply (rule typ_at_same_type)
      apply (simp add: obj_at_def a_type_simps)
     prefer 2
     apply assumption
    apply (simp add: a_type_def)
   apply clarsimp
   apply (erule allE, erule impE, rule exI, assumption)+
   apply (erule typ_at_same_type)
    prefer 2
    apply assumption
   apply (simp add: a_type_def)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (frule (3) asid_pool_map.intro)
  apply (subst (asm) asid_pool_map.vs_lookup, assumption)
  apply clarsimp
  apply (erule disjE)
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_vspace_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_rtrancl)
  apply (erule disjE)
   apply clarsimp
   apply (erule_tac x=p in allE, simp)
   apply (erule impE, blast)
   apply (erule valid_vspace_obj_same_type)
    apply (simp add: obj_at_def a_type_def)
   apply (simp add: a_type_def)
  apply (clarsimp simp: asid_pool_map.new_lookups_def empty_table_def)
  done  *)

lemma set_asid_pool_valid_arch_caps_map:
  "\<lbrace>valid_arch_caps and valid_arch_state and valid_global_objs and valid_objs
    and valid_vspace_objs and
    (\<lambda>s. asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
         (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {pt} \<and>
                    vs_cap_ref cap = Some (asid, 0)))
    and pt_at pt
    and (\<lambda>s. obj_at (empty_table (set (second_level_tables (arch_state s)))) pt s)
    and K (pool (asid_low_bits_of asid) = None)\<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> pt))
  \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  sorry
  (* FIXME RISCV: lemma statement --
            need to capture kernel mappings, which should be present at this stage
  apply (simp add: set_asid_pool_def set_object_def)
  apply (wp get_object_wp)
  apply clarsimp
  apply (frule obj_at_not_pt_not_in_global_pts[where p=pd], clarsimp+)
  apply (simp add: a_type_def)
  apply (frule obj_at_not_pt_not_in_global_pts[where p=ap], clarsimp+)
  apply (clarsimp simp: obj_at_def valid_arch_caps_def
                        caps_of_state_after_update)
  apply (clarsimp simp: a_type_def
                 split: Structures_A.kernel_object.split_asm if_split_asm
                        arch_kernel_obj.split_asm)
  apply (frule(3) asid_pool_map.intro)
  apply (simp add: fun_upd_def[symmetric])
  apply (rule conjI)
   apply (simp add: valid_vs_lookup_def
                    caps_of_state_after_update[folded fun_upd_def]
                    obj_at_def)
   apply (subst asid_pool_map.vs_lookup_pages2, assumption)
   apply simp
   apply (clarsimp simp: asid_pool_map.new_lookups_def)
   apply (frule(2) vs_lookup_vs_lookup_pagesI, simp add: valid_arch_state_def)
   apply (simp add: second_level_tables_def)
   apply (drule(2) ref_is_unique)
        apply (simp add: valid_vs_lookup_def)
       apply clarsimp+
     apply (simp add: valid_arch_state_def)
    apply (rule valid_objs_caps, simp)
   apply fastforce
  apply (simp add: valid_table_caps_def
                   caps_of_state_after_update[folded fun_upd_def] obj_at_def
              del: imp_disjL)
  apply (clarsimp simp del: imp_disjL)
  apply (drule(1) caps_of_state_valid_cap)+
  apply (auto simp add: valid_cap_def is_pt_cap_def is_pd_cap_def obj_at_def
                        a_type_def)[1]
  done *)

lemma set_asid_pool_invs_map:
  "\<lbrace>invs and
    (\<lambda>s. asid_pools_of s ap = Some pool \<and> pool_for_asid asid s = Some ap \<and>
         (\<exists>ptr cap. caps_of_state s ptr = Some cap \<and> obj_refs cap = {pt} \<and>
                    vs_cap_ref cap = Some (asid, 0)))
    and pt_at pt
    and (\<lambda>s. obj_at (empty_table (set (second_level_tables (arch_state s)))) pt s)
    and K (pool (asid_low_bits_of asid) = None)\<rbrace>
  set_asid_pool ap (pool(asid_low_bits_of asid \<mapsto> pt))
  \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (simp add: invs_def valid_state_def valid_pspace_def valid_asid_map_def)
  apply (wp valid_irq_node_typ set_asid_pool_typ_at set_asid_pool_arch_objs_map valid_irq_handlers_lift
                            set_asid_pool_valid_arch_caps_map)
  apply clarsimp
  apply auto
  sorry (* FIXME RISCV *)

lemma perform_asid_pool_invs [wp]:
  "\<lbrace>invs and valid_apinv api\<rbrace> perform_asid_pool_invocation api \<lbrace>\<lambda>_. invs\<rbrace>"
  apply (clarsimp simp: perform_asid_pool_invocation_def split: asid_pool_invocation.splits)
  sorry (* FIXME RISCV
  apply (wp arch_update_cap_invs_map set_asid_pool_invs_map
            get_cap_wp set_cap_typ_at
            empty_table_lift[unfolded pred_conj_def, OF _ set_cap_obj_at_other]
            set_cap_obj_at_other
               |wpc|simp|wp_once hoare_vcg_ex_lift)+
  apply (clarsimp simp: valid_apinv_def cte_wp_at_caps_of_state is_arch_update_def is_cap_simps cap_master_cap_simps)
  apply (frule caps_of_state_cteD)
  apply (drule cte_wp_valid_cap, fastforce)
  apply (simp add: valid_cap_def cap_aligned_def)
  apply (clarsimp simp: cap_asid_def split: option.splits)
  apply (rule conjI)
   apply (clarsimp simp: vs_cap_ref_def)
  apply (rule conjI)
   apply (erule vs_lookup_atE)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: cte_wp_at_cases obj_at_def)
  apply (rule conjI)
   apply (rule exI)
   apply (rule conjI, assumption)
   apply (rule conjI)
    apply (rule_tac x=a in exI)
    apply (rule_tac x=b in exI)
    apply (clarsimp simp: vs_cap_ref_def mask_asid_low_bits_ucast_ucast)
   apply (clarsimp simp: asid_low_bits_def[symmetric] ucast_ucast_mask
                         word_neq_0_conv[symmetric])
   apply (erule notE, rule asid_low_high_bits, simp_all)[1]
   apply (simp add: asid_high_bits_of_def)
  apply (rule conjI)
   apply (erule(1) valid_table_caps_pdD [OF _ invs_pd_caps])
  apply (rule conjI)
   apply clarsimp
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp: obj_at_def cte_wp_at_cases a_type_def)
   apply (clarsimp split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (clarsimp simp: obj_at_def)
  done *)

lemma invs_aligned_pdD:
  "\<lbrakk> pspace_aligned s; valid_arch_state s \<rbrakk> \<Longrightarrow> is_aligned (riscv_global_pt (arch_state s)) pt_bits"
  apply (clarsimp simp: valid_arch_state_def)
  sorry (* FIXME RISCV; this has probably been proved already at this point
  apply (drule (1) pt_aligned)
  apply (simp add: bit_simps)
  done *)

lemma do_machine_op_valid_kernel_mappings:
  "do_machine_op f \<lbrace>valid_kernel_mappings\<rbrace>"
  unfolding valid_kernel_mappings_def by wp

lemma valid_vspace_obj_default:
  assumes tyunt: "ty \<noteq> Structures_A.apiobject_type.Untyped"
  shows "ArchObj ao = default_object ty dev us \<Longrightarrow> valid_vspace_obj level ao s'"
  by (cases ty; simp add: default_object_def tyunt)

end

context begin interpretation Arch .
requalify_facts
  do_machine_op_valid_kernel_mappings
end

end
