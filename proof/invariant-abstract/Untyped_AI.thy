(*
 * Copyright 2022, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

(* Proofs about untyped invocations. *)

theory Untyped_AI
imports
  ArchDetype_AI
  "Lib.MonadicRewrite"
begin

unbundle l4v_word_context (* because of Lib.MonadicRewrite *)

context begin interpretation Arch .

requalify_consts
  region_in_kernel_window
  arch_default_cap
  second_level_tables
  safe_ioport_insert

requalify_facts
  set_cap_valid_arch_caps_simple
  set_cap_kernel_window_simple
  set_cap_ioports'
  safe_ioport_insert_triv

end

primrec
  valid_untyped_inv_wcap :: "Invocations_A.untyped_invocation \<Rightarrow> cap option
    \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_untyped_inv_wcap (Retype slot reset ptr_base ptr ty us slots dev)
   = (\<lambda>co s. \<exists>sz idx. (cte_wp_at (\<lambda>c. c = (UntypedCap dev ptr_base sz idx)
               \<and> (co = None \<or> co = Some c)) slot s
          \<and> range_cover ptr sz (obj_bits_api ty us) (length slots)
          \<and> (idx \<le> unat (ptr - ptr_base) \<or> (reset \<and> ptr = ptr_base))
          \<and> (ptr && ~~ mask sz) = ptr_base)
          \<and> (reset \<longrightarrow> descendants_of slot (cdt s) = {})
          \<and> (ty = CapTableObject \<longrightarrow> us > 0)
          \<and> (ty = Untyped \<longrightarrow> us \<ge> untyped_min_bits)
          \<and> distinct (slot#slots)
          \<and> (\<forall>slot\<in>set slots. cte_wp_at ((=) cap.NullCap) slot s
                    \<and> ex_cte_cap_wp_to is_cnode_cap slot s \<and> real_cte_at slot s)
          \<and> ty \<noteq> ArchObject ASIDPoolObj \<and> 0 < length slots
          \<and> (dev \<longrightarrow> ((ty = Untyped) \<or> is_frame_type ty)))"
abbreviation
  "valid_untyped_inv ui \<equiv> valid_untyped_inv_wcap ui None"

lemma valid_untyped_inv_wcap:
  "valid_untyped_inv ui
    = (\<lambda>s. \<exists>sz idx. valid_untyped_inv_wcap ui (Some
        (case ui of Retype slot reset ptr_base ptr ty us slots dev
            \<Rightarrow> UntypedCap dev (ptr && ~~ mask sz) sz idx)) s)"
  apply (cases ui)
  apply (clarsimp simp: fun_eq_iff cte_wp_at_caps_of_state
    intro!: arg_cong[where f=Ex] conj_cong[OF refl])
  apply auto
  done

locale Untyped_AI_of_bl_nat_to_cref =
  assumes of_bl_nat_to_cref:
    "\<lbrakk> x < 2 ^ bits; bits < word_bits \<rbrakk>
      \<Longrightarrow> (of_bl (nat_to_cref bits x) :: machine_word) = of_nat x"

lemma cnode_cap_bits_range:
  "\<lbrakk> cte_wp_at P p s; invs s \<rbrakk> \<Longrightarrow>
     (\<exists>c. P c \<and> (is_cnode_cap c \<longrightarrow>
                 (\<lambda>n. n > 0 \<and> n < (word_bits - cte_level_bits) \<and> is_aligned (obj_ref_of c) (n + cte_level_bits)) (bits_of c)))"
  apply (frule invs_valid_objs)
  apply (drule(1) cte_wp_at_valid_objs_valid_cap)
  apply clarsimp
  apply (rule exI, erule conjI)
  apply (clarsimp simp: is_cap_simps valid_cap_def bits_of_def)
  apply (erule (1) obj_at_valid_objsE)
  apply (case_tac ko, simp_all add: is_cap_table_def)[1]
  apply (clarsimp simp: valid_obj_def valid_cs_def well_formed_cnode_n_def
                        valid_cs_size_def length_set_helper
                        word_bits_def)
  apply (drule invs_psp_aligned)
  apply (unfold pspace_aligned_def)
  apply (frule domI, drule (1) bspec)
  apply (clarsimp simp: ex_with_length add.commute split: if_split_asm)
  done


(* FIXME: move *)
lemma cte_wp_at_wellformed_strengthen:
  "cte_at p s \<and> valid_objs s \<longrightarrow> cte_wp_at wellformed_cap p s"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule (1) caps_of_state_valid_cap)
  apply (simp add: valid_cap_def2)
  done


(* FIXME: move *)
lemma get_cap_cte_wp_at_P:
  "\<lbrace>cte_wp_at P p\<rbrace> get_cap p \<lbrace>\<lambda>rv s. cte_wp_at (%c. c = rv) p s \<and> P rv\<rbrace>"
  apply (rule hoare_weaken_pre)
  apply (rule get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done


lemma lookup_cap_ex:
  "\<lbrace>valid_objs\<rbrace> lookup_cap t x \<lbrace>\<lambda>rv s. valid_objs s \<and>
                                (\<exists>p1 p2 m c'. rv = mask_cap m c' \<and>
                                  cte_wp_at (\<lambda>c. c = c') (p1, p2) s)\<rbrace>,-"
  apply (simp add: lookup_cap_def split_def)
  apply wp
    apply (rule_tac P1=wellformed_cap in hoare_strengthen_post[OF get_cap_cte_wp_at_P])
    apply clarsimp
    apply (rule exI)+
    apply (subst cap_mask_UNIV, simp)
    apply fastforce
   apply (wpsimp|strengthen cte_wp_at_wellformed_strengthen)+
  done


lemma is_cnode_mask:
  "is_cnode_cap (mask_cap m c) = is_cnode_cap c"
  by (case_tac c, simp_all add: mask_cap_def cap_rights_update_def is_cap_simps split:bool.splits)


lemma Suc_length_not_empty:
  "length xs = length xs' \<Longrightarrow> Suc 0 \<le> length xs' = (xs \<noteq> [])"
  by (fastforce simp: le_simps)


lemmas Suc_length_not_empty' = Suc_length_not_empty [OF refl]


(* FIXME: hides Invariants_AI.caps_of_state_valid,
   FIXME: duplicate of Invariants_AI.caps_of_state_valid_cap *)
lemma caps_of_state_valid:
  "\<lbrakk>invs s; caps_of_state s p = Some cap \<rbrakk> \<Longrightarrow> s \<turnstile> cap"
  apply (rule cte_wp_valid_cap)
   apply (simp add: cte_wp_at_caps_of_state)
  apply clarsimp
  done

lemma mask_CNodeD:
  "mask_cap M' cap = cap.CNodeCap r bits g \<Longrightarrow>
  cap = cap.CNodeCap r bits g"
  by (cases cap, auto simp: mask_cap_def cap_rights_update_def split:bool.splits)

(* FIXME: move *)
lemma unat_2p_sub_1:
  "k < len_of TYPE('a)
  \<Longrightarrow> unat (2 ^ k - 1 :: 'a :: len word) = unat (2 ^ k :: 'a word) - 1"
  by (simp add: unat_minus_one)


lemma compute_free_index_wp:
  "\<lbrace>\<top>\<rbrace> const_on_failure idx
   (doE y \<leftarrow> ensure_no_children slot;
        returnOk (0::nat)
    odE)
   \<lbrace>\<lambda>rv s. rv \<le> idx\<rbrace>"
  apply (rule hoare_pre)
  apply (wp const_on_failure_wp)
  apply clarsimp
  done


lemma dui_inv[wp]:
  "\<lbrace>P\<rbrace> decode_untyped_invocation label args slot (UntypedCap dev w n idx) cs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_untyped_invocation_def whenE_def
                   split_def data_to_obj_type_def unlessE_def
              split del: if_split cong: if_cong)
  apply (rule hoare_pre)
   apply (simp split del: if_split
              | wp (once) mapME_x_inv_wp hoare_drop_imps const_on_failure_wp
              | assumption
              | simp add: lookup_target_slot_def
              | wpcw
              | wp)+
  done

lemma map_ensure_empty_cte_wp_at:
  "\<lbrace>cte_wp_at P p\<rbrace> mapME_x ensure_empty xs \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>,-"
  unfolding mapME_x_def sequenceE_x_def by (induct xs; wpsimp)


lemma map_ensure_empty:
  "\<lbrace>P\<rbrace> mapME_x ensure_empty xs \<lbrace>\<lambda>rv s. (\<forall>x \<in> set xs. cte_wp_at ((=) cap.NullCap) x s) \<and> P s\<rbrace>,-"
  apply (induct xs)
   apply (simp add: mapME_x_def sequenceE_x_def)
   apply wp
  apply (simp add: mapME_x_def sequenceE_x_def)
  apply (unfold validE_R_def)
  apply (rule bindE_wp)
   apply (rule hoare_vcg_conj_liftE1)
    apply (fold sequenceE_x_def mapME_x_def)[1]
    apply (rule map_ensure_empty_cte_wp_at)
   apply assumption
  apply (simp add: ensure_empty_def whenE_def)
  apply (rule hoare_pre, wp get_cap_wp)
  apply clarsimp
  done


lemma ensure_no_children_sp:
  "\<lbrace>P\<rbrace> ensure_no_children slot \<lbrace>\<lambda>rv s. descendants_of slot (cdt s) = {} \<and> P s\<rbrace>,-"
  apply (simp add: ensure_no_children_descendants)
  apply (clarsimp simp: valid_def validE_def validE_R_def split_def in_monad
                        | rule conjI)+
  done


lemma data_to_obj_type_inv:
  "\<lbrace>P\<rbrace> data_to_obj_type v \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: data_to_obj_type_def)
  apply (intro conjI impI; wpsimp)
  done


lemma data_to_obj_type_inv2 [wp]:
  "\<lbrace>P\<rbrace> data_to_obj_type v \<lbrace>\<lambda>rv. P\<rbrace>,-"
  by (wp data_to_obj_type_inv)


lemma get_cap_gets:
  "\<lbrace>valid_objs\<rbrace>
    get_cap ptr
   \<lbrace>\<lambda>rv s. \<exists>cref msk. cte_wp_at (\<lambda>cap. rv = mask_cap msk cap) cref s\<rbrace>"
  apply (wp get_cap_wp)
  apply (intro allI impI)
  apply (rule_tac x=ptr in exI)
  apply (rule_tac x=UNIV in exI)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (frule (1) caps_of_state_valid_cap)
  apply (clarsimp simp add: valid_cap_def2)
  done


lemma lookup_cap_gets:
  "\<lbrace>valid_objs\<rbrace> lookup_cap t c \<lbrace>\<lambda>rv s. \<exists>cref msk. cte_wp_at (\<lambda>cap. rv = mask_cap msk cap) cref s\<rbrace>,-"
  unfolding lookup_cap_def fun_app_def split_def
  apply (rule hoare_pre, wp get_cap_gets)
  apply simp
  done


lemma dui_sp_helper:
  "(\<And>s. P s \<Longrightarrow> valid_objs s) \<Longrightarrow>
   \<lbrace>P\<rbrace> if val = 0 then returnOk root_cap
       else doE node_slot \<leftarrow>
                  lookup_target_slot root_cap (to_bl (args ! 2)) (unat (args ! 3));
                  liftE $ get_cap node_slot
            odE \<lbrace>\<lambda>rv s. (rv = root_cap \<or> (\<exists>slot. cte_wp_at ((=) rv) slot s)) \<and> P s\<rbrace>, -"
  apply (simp add: split_def lookup_target_slot_def)
  apply (intro impI conjI)
   apply wpsimp
  apply (wp get_cap_wp)
   apply (rule hoare_strengthen_postE_R [where Q'="\<lambda>rv. valid_objs and P"]
          ; wpsimp simp: cte_wp_at_caps_of_state)
  apply simp
  done

locale Untyped_AI_arch =
  fixes state_ext_t :: "('state_ext::state_ext) itself"
  assumes data_to_obj_type_sp:
  "\<And>P x. \<lbrace>P\<rbrace> data_to_obj_type x \<lbrace>\<lambda>ts (s::'state_ext state). ts \<noteq> ArchObject ASIDPoolObj \<and> P s\<rbrace>, -"
  assumes dui_inv_wf[wp]:
  "\<And>w sz idx slot cs label args dev.\<lbrace>invs and cte_wp_at ((=) (UntypedCap dev w sz idx)) slot
     and (\<lambda>(s::'state_ext state). \<forall>cap \<in> set cs. is_cnode_cap cap
                      \<longrightarrow> (\<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
    and (\<lambda>s. \<forall>x \<in> set cs. s \<turnstile> x)\<rbrace>
     decode_untyped_invocation label args slot (UntypedCap dev w sz idx) cs
   \<lbrace>valid_untyped_inv\<rbrace>,-"
    assumes retype_ret_valid_caps_captable:
  "\<And>ptr sz dev us n s.\<lbrakk>pspace_no_overlap_range_cover ptr sz (s::'state_ext state) \<and> 0 < us \<and> range_cover ptr sz (obj_bits_api CapTableObject us) n \<and> ptr \<noteq> 0
       \<rbrakk>
         \<Longrightarrow> \<forall>y\<in>{0..<n}. s
                \<lparr>kheap := foldr (\<lambda>p kh. kh(p \<mapsto> default_object CapTableObject dev us)) (map (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api CapTableObject us)) [0..<n])
                           (kheap s)\<rparr> \<turnstile> CNodeCap (ptr_add ptr (y * 2 ^ obj_bits_api CapTableObject us)) us []"
  assumes retype_ret_valid_caps_aobj:
  "\<And>ptr sz s x6 us n dev. \<lbrakk>pspace_no_overlap_range_cover ptr sz (s::'state_ext state) \<and> x6 \<noteq> ASIDPoolObj \<and> range_cover ptr sz (obj_bits_api (ArchObject x6) us) n \<and> ptr \<noteq> 0 \<comment> \<open>; tp = ArchObject x6\<close>\<rbrakk>
            \<Longrightarrow> \<forall>y\<in>{0..<n}. s
                   \<lparr>kheap := foldr (\<lambda>p kh. kh(p \<mapsto> default_object (ArchObject x6) dev us)) (map (\<lambda>p. ptr_add ptr (p * 2 ^ obj_bits_api (ArchObject x6) us)) [0..<n])
                              (kheap s)\<rparr> \<turnstile> ArchObjectCap (arch_default_cap x6 (ptr_add ptr (y * 2 ^ obj_bits_api (ArchObject x6) us)) us dev)"

  assumes init_arch_objects_descendants_range[wp]:
  "\<And>x cref ty ptr n us y. \<lbrace>\<lambda>(s::'state_ext state). descendants_range x cref s \<rbrace> init_arch_objects ty ptr n us y
          \<lbrace>\<lambda>rv s. descendants_range x cref s\<rbrace>"
  assumes  init_arch_objects_caps_overlap_reserved[wp]:
  "\<And>S ty ptr n us y. \<lbrace>\<lambda>(s::'state_ext state). caps_overlap_reserved S s\<rbrace>
   init_arch_objects ty ptr n us y
   \<lbrace>\<lambda>rv s. caps_overlap_reserved S s\<rbrace>"
  assumes delete_objects_rewrite:
  "\<And>sz ptr. \<lbrakk> word_size_bits \<le> sz; sz\<le> word_bits; ptr && ~~ mask sz = ptr \<rbrakk>
      \<Longrightarrow> delete_objects ptr sz =
            do y \<leftarrow> modify (clear_um {ptr + of_nat k |k. k < 2 ^ sz});
               modify (detype {ptr && ~~ mask sz..ptr + 2 ^ sz - 1} :: 'state_ext state \<Rightarrow> 'state_ext state)
            od"
  assumes obj_is_device_vui_eq:
  "valid_untyped_inv ui (s :: 'state_ext state)
    \<Longrightarrow> case ui of
        Retype slot reset ptr_base ptr tp us slots dev
        \<Rightarrow> obj_is_device tp dev = dev"

lemmas is_aligned_triv2 = Aligned.is_aligned_triv

lemma strengthen_imp_ex2: "(P \<longrightarrow> Q x y) \<Longrightarrow> (P \<longrightarrow> (\<exists>x y. Q x y))"
 by auto


lemma p2_minus:
  "sz < len_of TYPE('a) \<Longrightarrow>
   of_nat (2 ^ len_of TYPE('a) - 2 ^ sz) = ((mask (len_of TYPE('a)) && ~~ mask sz):: 'a :: len word)"
   apply (rule word_unat.Rep_inverse')
   apply (simp add: mask_out_sub_mask)
   apply (simp add: unat_sub word_and_le2 mask_and_mask)
   apply (simp add: min_def mask_def word_size unat_minus)
   done

lemma range_cover_bound':
  fixes ptr :: "'a :: len word"
  assumes cover: "range_cover ptr sz sbit n"
  assumes le : "x < n"
  shows "unat (ptr + of_nat x * 2 ^ sbit) + 2 ^ sbit  \<le> 2 ^ len_of TYPE('a)"
proof -
  have l: "unat (ptr && ~~ mask sz) + 2^ sz \<le> 2^ len_of TYPE('a)"
    using cover
    apply -
    apply (rule le_diff_conv2[THEN iffD1])
     apply (simp add: range_cover_def)
     apply (rule unat_le_helper)
     apply (subst p2_minus)
      apply (erule range_cover.sz)
     apply (rule neg_mask_mono_le)
    apply (simp add: mask_def)
   done

  have n: "unat ((ptr && mask sz) + of_nat x * 2 ^ sbit) + 2^sbit \<le> 2 ^ sz"
    apply (rule le_trans[OF _ range_cover.range_cover_compare_bound[OF cover]])
    apply (rule le_trans[where j = "(x+1) * 2^sbit + unat (ptr && mask sz)"])
     apply clarsimp
     apply (rule le_trans[OF unat_plus_gt])
     using le
     apply (simp add: range_cover.unat_of_nat_shift[OF cover])
    apply simp
    using le
    apply (case_tac n,simp+)
    done
  show ?thesis
  using cover le
  apply -
  apply (frule iffD1[OF meta_eq_to_obj_eq[OF range_cover_def]])
  apply (clarsimp)
  apply (frule range_cover_le[where n=x])
   apply simp
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
  apply (subst add.commute)
  apply (subst add.assoc)
  apply (subst unat_plus_simple[THEN iffD1])
   apply (rule is_aligned_no_wrap')
   apply (rule is_aligned_neg_mask[OF le_refl])
   apply (simp add: range_cover_def)
   apply (simp add: word_less_nat_alt)
   apply (rule le_less_trans[OF unat_plus_gt])
   apply (erule range_cover.range_cover_compare[OF cover])
  apply (subst add.assoc)
  apply (rule le_trans[OF _ l])
  apply simp
  apply (simp add: n)
  done
qed


lemma range_cover_stuff:
  notes unat_power_lower_machine = unat_power_lower[where 'a=machine_word_len]
  notes unat_of_nat_machine = unat_of_nat_eq[where 'a=machine_word_len]
  notes is_aligned_neg_mask_eq[simp del]
  notes is_aligned_neg_mask_weaken[simp del]
  shows
  "\<lbrakk>0 < n;n \<le> unat ((2::machine_word) ^ sz - of_nat rv >> bits);
  rv \<le> 2^ sz; sz < word_bits; is_aligned w sz\<rbrakk> \<Longrightarrow>
   rv \<le> unat (alignUp (w + of_nat rv) bits - w) \<and>
   (alignUp (w + of_nat rv) bits) && ~~ mask sz = w \<and>
   range_cover (alignUp (w + ((of_nat rv)::machine_word)) bits) sz bits n"
  apply (clarsimp simp: range_cover_def)
  proof (intro conjI)
    assume not_0 : "0<n"
    assume bound : "n \<le> unat ((2::machine_word) ^ sz - of_nat rv >> bits)" "rv\<le> 2^sz"
      "sz < word_bits"
    assume al: "is_aligned w sz"
    have space: "(2::machine_word) ^ sz - of_nat rv \<le> 2^ sz"
      apply (rule word_sub_le[OF word_of_nat_le])
      apply (clarsimp simp: bound unat_power_lower_machine)
      done
    show cmp: "bits \<le> sz"
      using not_0 bound
      apply -
      apply (rule ccontr)
      apply (clarsimp simp: not_le)
      apply (drule le_trans)
      apply (rule word_le_nat_alt[THEN iffD1])
      apply (rule le_shiftr[OF space])
      apply (subgoal_tac "(2::machine_word)^sz >> bits = 0")
       apply simp
      apply (rule and_mask_eq_iff_shiftr_0[THEN iffD1])
      apply (simp add: and_mask_eq_iff_le_mask)
      apply (case_tac "word_bits \<le> bits")
       apply (simp add: word_bits_def mask_def power_overflow)
      apply (subst le_mask_iff_lt_2n[THEN iffD1])
       apply (simp add: word_bits_def)
      apply (simp add: word_less_nat_alt[THEN iffD2] unat_power_lower_machine)
      done
    have shiftr_t2n[simp]:"(2::machine_word)^sz >> bits = 2^ (sz - bits)"
      using bound cmp
      apply (case_tac "sz = 0",simp)
      apply (subgoal_tac "(1::machine_word) << sz >> bits = 2^ (sz -bits)")
       apply simp
      apply (subst shiftl_shiftr1)
       apply (simp_all add: word_size)
      apply (word_eqI_solve simp: word_bits_conv)
      done

    have cmp2[simp]: "alignUp (of_nat rv) bits < (2 :: machine_word) ^ sz"
      using bound cmp not_0
      apply -
      apply (case_tac "rv = 0")
       apply simp
       apply (clarsimp simp: alignUp_def2)
       apply (subst mask_eq_x_eq_0[THEN iffD1])
       apply (simp add: and_mask_eq_iff_le_mask mask_def)
       apply (simp add: p2_gt_0[where 'a=machine_word_len, folded word_bits_def])
      apply (simp add: alignUp_def3)
      apply (subgoal_tac "1 \<le> unat (2 ^ sz - of_nat rv >> bits)")
      prefer 2
       apply (erule le_trans[rotated])
       apply clarsimp
      apply (thin_tac "n \<le> M" for M)
      apply (simp add: shiftr_div_2n')
      apply (simp add: td_gal[symmetric])
      apply (subst (asm) unat_sub)
       apply (simp add: word_of_nat_le unat_power_lower_machine)
      apply (simp add: le_diff_conv2 word_of_nat_le unat_le_helper word_less_nat_alt)
      apply (rule le_less_trans[OF unat_plus_gt])
      apply (rule less_le_trans[where y = "2^bits + unat (of_nat rv)"])
      apply simp
      apply (rule le_less_trans[OF _ measure_unat])
      apply (rule word_le_nat_alt[THEN iffD1])
      apply (rule word_and_le2)
      apply (erule of_nat_neq_0)
       apply (subst word_bits_def[symmetric])
       apply (erule le_less_trans)
       apply simp
      apply simp
      done

    show "n + unat (alignUp (w + ((of_nat rv)::machine_word)) bits && mask sz >> bits) \<le> 2 ^ (sz - bits)"
      using not_0 bound cmp
     apply -
     apply (erule le_trans[OF add_le_mono])
      apply (rule le_refl)
     apply (clarsimp simp: power_sub field_simps td_gal[symmetric])
     apply (subst (2) mult.commute)
     apply (subst unat_shiftl_absorb)
      apply (rule order_trans[OF le_shiftr])
       apply (rule word_and_le1)
      apply (simp add: shiftr_mask2 word_bits_def)
      apply (simp add: mask_def)
      apply (rule word_sub_1_le)
      apply (simp add: word_bits_def)+
     apply (simp add: shiftl_t2n[symmetric] field_simps shiftr_shiftl1)
     apply (subst is_aligned_neg_mask_eq)
      apply (rule is_aligned_andI1,simp)
     apply (subst mult.commute)
     apply (subst unat_shiftl_absorb[where p = "sz - bits"])
        apply (rule order_trans[OF le_shiftr])
         apply (rule space)
       apply (simp add: word_bits_def power_minus_is_div)+
     apply (simp add: shiftl_t2n[symmetric] field_simps shiftr_shiftl1)
     apply (subst is_aligned_diff_neg_mask[OF is_aligned_weaken])
       apply (rule is_aligned_triv)
      apply (simp add: word_bits_def)+
     apply (subst unat_sub)
      apply (rule order_trans[OF word_and_le2])
      apply (simp add: less_imp_le)
     apply (subst diff_add_assoc[symmetric])
      apply (rule unat_le_helper)
      apply (rule order_trans[OF word_and_le2])
      apply (simp add: less_imp_le[OF cmp2])
     apply (clarsimp simp: field_simps word_bits_def is_aligned_neg_mask_eq)
     apply (simp add: le_diff_conv word_le_nat_alt[symmetric] word_and_le2)
     apply (simp add: alignUp_plus[OF is_aligned_weaken[OF al]]
                      is_aligned_add_helper[THEN conjunct1, OF al cmp2])
     done
   show "rv \<le> unat (alignUp (w + of_nat rv) bits - w)"
     using bound not_0 cmp al
     apply -
     apply (clarsimp simp: alignUp_plus[OF is_aligned_weaken])
     apply (case_tac "rv = 0")
      apply simp
     apply (rule le_trans[OF _ word_le_nat_alt[THEN iffD1,OF alignUp_ge]])
       apply (subst unat_of_nat_machine)
        apply (erule le_less_trans)
        apply (rule power_strict_increasing)
         apply (simp_all add: word_bits_def)[4]
     apply (rule alignUp_is_aligned_nz[where x = "2^sz"])
        apply (rule is_aligned_weaken[OF is_aligned_triv2])
        apply (simp_all add: word_bits_def)[2]
      apply (subst word_of_nat_le)
       apply (subst unat_power_lower_machine)
        apply ((simp add: word_bits_def)+)[3]
     apply simp
     apply (erule of_nat_neq_0)
     apply (erule le_less_trans)
     apply (rule power_strict_increasing)
      apply (simp add: word_bits_def)+
     done
   show "alignUp (w + of_nat rv) bits && ~~ mask sz = w"
    using bound not_0 cmp al
    apply (clarsimp simp: alignUp_plus[OF is_aligned_weaken]
                          mask_out_add_aligned[symmetric])
    apply (clarsimp simp: and_not_mask)
    apply (subgoal_tac "alignUp ((of_nat rv)::machine_word) bits >> sz = 0")
     apply simp
    apply (simp add: le_mask_iff[symmetric] mask_def)
    done
  qed (simp add: word_bits_def)

context Arch begin
  (*FIXME: generify proof that uses this *)
  lemmas range_cover_stuff_arch = range_cover_stuff[unfolded word_bits_def, simplified]
end


lemma cte_wp_at_range_cover:
  "\<lbrakk>bits < word_bits; rv\<le> 2^ sz; invs s;
    cte_wp_at ((=) (UntypedCap dev w sz idx)) p s;
    0 < n; n \<le> unat ((2::machine_word) ^ sz - of_nat rv >> bits)\<rbrakk>
   \<Longrightarrow> range_cover (alignUp (w + of_nat rv) bits) sz bits n"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid)
  apply (clarsimp simp: valid_cap_def valid_untyped_def cap_aligned_def)
  apply (drule range_cover_stuff)
   apply simp_all
  apply clarsimp
  done


lemma le_mask_le_2p:
  "\<lbrakk>idx \<le> unat ((ptr::machine_word) && mask sz);sz < word_bits\<rbrakk> \<Longrightarrow> idx < 2^ sz"
  apply (erule le_less_trans)
  apply (rule unat_less_helper)
  apply simp
  apply (rule le_less_trans)
  apply (rule word_and_le1)
  apply (simp add: mask_def)
  done


lemma diff_neg_mask[simp]:
  "ptr - (ptr && ~~ mask sz) = (ptr && mask sz)"
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
  apply simp
  done


lemma cte_wp_at_caps_descendants_range_inI:
  "\<lbrakk> invs s;cte_wp_at (\<lambda>c. c = UntypedCap dev (ptr && ~~ mask sz) sz idx) cref s;
    idx \<le> unat (ptr && mask sz);sz < word_bits \<rbrakk> \<Longrightarrow> descendants_range_in {ptr .. (ptr && ~~mask sz) + 2^sz - 1} cref s"
  apply (frule invs_mdb)
  apply (frule(1) le_mask_le_2p)
  apply (clarsimp simp: descendants_range_in_def cte_wp_at_caps_of_state )
  apply (frule(1) descendants_of_cte_at)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule untyped_cap_descendants_range[rotated])
    apply simp+
   apply (simp add: invs_valid_pspace)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule disjoint_subset2[rotated])
  apply clarsimp
  apply (rule le_plus'[OF word_and_le2])
  apply simp
  apply (erule word_of_nat_le)
  done


lemma nasty_range:
  fixes word :: "'a :: len word"
  assumes szb: "bz < len_of TYPE('a)"
  and al:  "is_aligned word bz"
  and br:  "ptr \<in> {word.. word+2^bz - 1}"
  and sr:  "sz \<le> bz"
  shows "\<exists>idx::'a :: len word. idx < (2::'a :: len word)^(bz - sz) \<and>
         ptr \<in> {word + idx * 2^ sz .. word + (idx * 2^ sz) + (2^ sz - 1)}"
proof -
 have offset: "ptr - word < 2^ bz"
   using br szb
   apply (subst word_less_sub_le[symmetric],simp)
   apply (rule word_diff_ls')
   apply (clarsimp simp: field_simps)+
   done
 have t2n_sym: "\<And>z. (2::'a :: len word)^z = (1:: 'a :: len word)<<z"
   by (simp add: shiftl_t2n)
 have le_helper: "\<And>b c. \<lbrakk>\<And>a. (a::'a :: len word)< b \<Longrightarrow> a< c\<rbrakk> \<Longrightarrow> b\<le>c"
   apply (rule ccontr)
   apply (clarsimp simp: not_le dest!: meta_spec)
   by auto
 have ptr_word: "(ptr - word >> sz) * 2 ^ sz = (ptr &&~~ mask sz) - word"
  apply (subst mult.commute)
  apply (clarsimp simp: shiftl_t2n[symmetric] shiftr_shiftl1 word_and_le2)
  apply (simp only: diff_conv_add_uminus)
  apply (subst add.commute[where a = "ptr && ~~ mask sz"])
  apply (subst mask_out_add_aligned)
  defer
  apply (simp add: field_simps)
  apply (rule is_aligned_minus)
  apply (rule is_aligned_weaken[OF al sr])
  done
 show ?thesis
 using szb sr br
 apply clarsimp
 apply (rule_tac x = "(ptr - word) >> sz" in exI)
 apply (intro conjI)
   apply (rule less_le_trans)
   apply (rule shiftr_less_t2n[where m = "bz - sz"])
     apply (simp add: offset)
   apply simp
  apply (rule le_plus)
   apply (subst mult.commute)
   apply (simp add: shiftl_t2n[symmetric] shiftr_shiftl1 word_and_le2)
  apply clarsimp
 apply (simp add: ptr_word p_assoc_help)
 apply (rule order_trans[OF _ word_plus_mono_right])
   apply (rule order_eq_refl)
   apply (subst word_plus_and_or_coroll2[where x = "ptr",symmetric])
   apply (subst add.commute)
   apply simp
  apply (rule order_trans[OF word_and_le1])
  apply (clarsimp simp: mask_def)
 apply (rule is_aligned_no_overflow'[OF is_aligned_neg_mask])
 apply simp+
done
qed

lemma check_children_wp:
  "\<lbrace>\<lambda>s. if descendants_of slot (cdt s) = {} then Q True s else Q False s \<rbrace>
   const_on_failure False
    (doE y \<leftarrow> ensure_no_children slot;
    returnOk True
    odE) \<lbrace>Q\<rbrace>"
  including no_pre
  apply (clarsimp simp: const_on_failure_def ensure_no_children_descendants bindE_assoc)
  apply wp
  apply (clarsimp simp: valid_def validE_def if_splits)
  apply (intro conjI impI)
  apply (clarsimp simp: in_monad free_index_of_def)+
  done


lemma alignUp_eq:
  "\<lbrakk>is_aligned (w :: 'a :: len word) sz; a \<le> 2^ sz; us \<le> sz; sz < len_of TYPE('a);
    alignUp (w + a) us = w\<rbrakk>
   \<Longrightarrow> a = 0"
  apply (clarsimp simp: alignUp_plus[OF is_aligned_weaken])
  apply (rule ccontr)
  apply (drule alignUp_is_aligned_nz[rotated -1,where x = "2^ sz"])
    apply (rule is_aligned_weaken[OF is_aligned_triv2])
    apply simp+
  done

lemma map_ensure_empty_wp:
  "\<lbrace> \<lambda>s. (\<forall>x\<in>set xs. cte_wp_at ((=) NullCap) x s) \<longrightarrow> P () s \<rbrace>
      mapME_x ensure_empty xs \<lbrace>P\<rbrace>, -"
  by (rule hoare_strengthen_postE_R, rule map_ensure_empty, simp)

lemma cases_imp_eq:
  "((P \<longrightarrow> Q \<longrightarrow> R) \<and> (\<not> P \<longrightarrow> Q \<longrightarrow> S)) = (Q \<longrightarrow> (P \<longrightarrow> R) \<and> (\<not> P \<longrightarrow> S))"
  by blast

lemma inj_bits:
  "\<lbrakk> of_nat x * 2^bits = of_nat y * (2^bits :: machine_word);
     x < bnd; y < bnd; bits \<le> word_bits; bnd \<le> 2 ^ (word_bits - bits) \<rbrakk>
     \<Longrightarrow> of_nat x = (of_nat y :: machine_word)"
  apply (cases "bits = 0", simp)
  apply (fold shiftl_t2n [where n=bits, simplified, simplified mult.commute])
  apply (simp only: word_bl.Rep_inject[symmetric]
                    bl_shiftl)
  apply (drule(1) order_less_le_trans)+
  apply (drule of_nat_mono_maybe[rotated, where 'a=machine_word_len])
   apply (rule power_strict_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply (drule of_nat_mono_maybe[rotated, where 'a=machine_word_len])
   apply (rule power_strict_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply (simp only: word_unat_power[symmetric])
  apply (erule ssubst [OF less_is_drop_replicate])+
  apply (simp add: word_bits_def word_size)
  done


lemma of_nat_shiftR:
  "a < 2 ^ word_bits \<Longrightarrow>
   unat (of_nat (shiftR a b)::machine_word) = unat ((of_nat a :: machine_word) >> b)"
  apply (subst shiftr_div_2n')
  apply (clarsimp simp: shiftR_nat)
  apply (subst unat_of_nat_eq[where 'a=machine_word_len])
   apply (simp only: word_bits_def)
   apply (erule le_less_trans[OF div_le_dividend])
  apply (subst unat_of_nat_eq[where 'a=machine_word_len])
   apply (simp only: word_bits_def)
  apply simp
  done


lemma valid_untypedD:
  "\<lbrakk> s \<turnstile> UntypedCap dev ptr bits idx; kheap s p = Some ko; pspace_aligned s\<rbrakk> \<Longrightarrow>
   obj_range p ko \<inter> cap_range (UntypedCap dev ptr bits idx) \<noteq> {} \<longrightarrow>
      obj_range p ko  \<subseteq> cap_range (UntypedCap dev ptr bits idx)
      \<and> obj_range p ko \<inter> usable_untyped_range (UntypedCap dev ptr bits idx) = {}"
  by (clarsimp simp: valid_untyped_def valid_cap_def cap_range_def obj_range_def)
     (meson order_trans)

lemma pspace_no_overlap_detype':
  "\<lbrakk> s \<turnstile> UntypedCap dev ptr bits idx; pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> pspace_no_overlap {ptr .. ptr + 2 ^ bits - 1} (detype {ptr .. ptr + 2 ^ bits - 1} s)"
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff
        simp: obj_range_def add_diff_eq[symmetric] pspace_no_overlap_def)
  apply (frule(2) valid_untypedD)
  apply (rule ccontr)
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                            Int_atLeastAtMost atLeastatMost_empty_iff is_aligned_neg_mask_eq
                      simp: valid_cap_def cap_aligned_def obj_range_def cap_range_def is_aligned_neg_mask_eq p_assoc_help)
  apply (drule_tac c= x in set_mp)
   apply simp+
  done

lemma pspace_no_overlap_detype:
  "\<lbrakk> s \<turnstile> UntypedCap dev ptr bits idx; pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> pspace_no_overlap_range_cover ptr bits (detype {ptr .. ptr + 2 ^ bits - 1} s)"
  apply (drule(2) pspace_no_overlap_detype'[rotated])
  apply (drule valid_cap_aligned)
  apply (clarsimp simp: cap_aligned_def field_simps)
  done

lemma zip_take_length[simp]:
  "zip (take (length ys) xs) ys = zip xs ys"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply simp
  apply simp
  done

(* FIXME: move *)
lemma int_not_empty_subsetD:
  "\<lbrakk> A\<inter> B = {}; A\<noteq> {};B\<noteq> {}\<rbrakk> \<Longrightarrow> \<not> A \<subset> B \<and> \<not> B\<subset> A \<and> \<not> A = B"
  by auto

(* FIXME: move *)
lemma subset_not_psubset: " A \<subseteq> B \<Longrightarrow> \<not> B \<subset> A" by clarsimp

lemma mdb_Null_descendants:
  "\<lbrakk> cte_wp_at ((=) cap.NullCap) p s; valid_mdb s \<rbrakk> \<Longrightarrow>
      descendants_of p (cdt s) = {}"
  apply (clarsimp simp add: valid_mdb_def cte_wp_at_caps_of_state swp_def)
  apply (erule(1) mdb_cte_at_Null_descendants)
  done

lemma mdb_Null_None:
  "\<lbrakk> cte_wp_at ((=) cap.NullCap) p s; valid_mdb s \<rbrakk> \<Longrightarrow>
      cdt s p = None"
  apply (clarsimp simp add: valid_mdb_def cte_wp_at_caps_of_state swp_def)
  apply (erule(1) mdb_cte_at_Null_None)
  done

lemma not_waiting_reply_slot_no_descendants:
  "\<lbrakk> st_tcb_at (Not \<circ> awaiting_reply) t s;
     valid_reply_caps s; valid_objs s; valid_mdb s \<rbrakk>
       \<Longrightarrow> descendants_of (t, tcb_cnode_index 2) (cdt s) = {}"
  apply (rule ccontr, erule nonemptyE)
  apply (clarsimp simp: valid_mdb_def reply_mdb_def reply_masters_mdb_def)
  apply (frule_tac ref="tcb_cnode_index 2" in tcb_at_cte_at[OF st_tcb_at_tcb_at])
   apply (simp add: domI)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule(1) tcb_cap_valid_caps_of_stateD)
  apply (clarsimp simp: tcb_cap_valid_def st_tcb_at_tcb_at)
  apply (clarsimp simp: st_tcb_def2)
  apply (erule disjE)
   apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)
   apply (elim allE impE)
    apply fastforce
   apply (clarsimp)
   apply (drule(1) bspec)
   apply (subgoal_tac "has_reply_cap t s")
    apply (erule notE[rotated], strengthen reply_cap_doesnt_exist_strg)
    apply (simp add: st_tcb_def2)
   apply (erule exE)
   apply (drule caps_of_state_cteD)+
   apply (fastforce simp add:has_reply_cap_def is_reply_cap_to_def elim:cte_wp_at_lift
                    intro:  caps_of_state_cteD)
  apply clarsimp
  apply (frule mdb_Null_descendants[OF caps_of_state_cteD])
   apply (simp add: valid_mdb_def reply_mdb_def reply_masters_mdb_def)
  apply simp
  done


crunch ups[wp]: set_cdt "\<lambda>s. P (ups_of_heap (kheap s))"
crunch cns[wp]: set_cdt "\<lambda>s. P (cns_of_heap (kheap s))"


(* FIXME: move *)
lemma list_all2_zip_split:
  "\<lbrakk> list_all2 P as cs; list_all2 Q bs ds \<rbrakk> \<Longrightarrow>
   list_all2 (\<lambda>x y. P (fst x) (fst y) \<and> Q (snd x) (snd y))
              (zip as bs) (zip cs ds)"
  apply (induct as arbitrary: bs cs ds)
   apply simp
  apply (case_tac cs; simp)
  apply (case_tac bs; simp)
  apply (case_tac ds; simp)
  done

lemma set_cdt_tcb_valid[wp]:
  "\<lbrace>tcb_cap_valid cap ptr\<rbrace> set_cdt m \<lbrace>\<lambda>rv. tcb_cap_valid cap ptr\<rbrace>"
  by (simp add: set_cdt_def, wp, simp add: tcb_cap_valid_def)


lemma tcb_cap_valid_rvk[simp]:
  "tcb_cap_valid cap ptr (is_original_cap_update f s)
     = tcb_cap_valid cap ptr s"
  by (simp add: tcb_cap_valid_def)


lemma tcb_cap_valid_more_update[simp]:
  "tcb_cap_valid cap ptr (trans_state f s)
     = tcb_cap_valid cap ptr s"
  by (simp add: tcb_cap_valid_def)

lemma create_cap_wps[wp]:
  "\<lbrace>pspace_aligned\<rbrace> create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  "\<lbrace>pspace_distinct\<rbrace> create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  "\<lbrace>cte_wp_at P p' and K (p' \<noteq> cref)\<rbrace>
       create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. cte_wp_at P p'\<rbrace>"
  "\<lbrace>valid_objs and valid_cap (default_cap tp oref sz dev)
            and real_cte_at cref\<rbrace>
       create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  "\<lbrace>valid_cap cap\<rbrace> create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. valid_cap cap\<rbrace>"
  apply (safe intro!: hoare_gen_asm)
      apply (simp_all add: create_cap_def)
      apply (wp set_cap_cte_wp_at' set_cdt_cte_wp_at
                set_cap_valid_objs set_cdt_valid_objs
                set_cdt_valid_cap set_cap_valid_cap
              | simp split del: if_split
                           add: real_cte_tcb_valid)+
  done


lemma default_non_Null[simp]:
  "cap.NullCap \<noteq> default_cap tp oref sz dev"
  by (cases tp, simp_all)

locale vo_abs = vmdb_abs +
  assumes valid_objs: "valid_objs s"
begin
lemma cs_valid_cap:
  "cs p = Some c \<Longrightarrow> s \<turnstile> c"
  using valid_objs
  apply (simp add: cs_def)
  apply (drule cte_wp_at_valid_objs_valid_cap [rotated, where P="(=) c"])
   apply (simp add: cte_wp_at_caps_of_state)
  apply clarsimp
  done


lemma cs_cap_aligned:
  "cs p = Some c \<Longrightarrow> cap_aligned c"
  apply (drule cs_valid_cap)
  apply (simp add: valid_cap_def)
  done
end

lemma untyped_ranges_aligned_disjoing_or_subset:
  "\<lbrakk>cap_aligned c1;cap_aligned c2\<rbrakk> \<Longrightarrow>
    untyped_range c1 \<subseteq> untyped_range c2
    \<or> untyped_range c2 \<subseteq> untyped_range c1
    \<or> untyped_range c1 \<inter> untyped_range c2 = {}"
  apply (simp add: cap_aligned_def)
  apply (elim conjE)
  apply (drule(1) aligned_ranges_subset_or_disjoint)
  apply (case_tac c1)
    apply simp_all
  apply (case_tac c2)
    apply simp_all
  done


locale mdb_create_cap = vo_abs + mdb_insert_abs +
  fixes cap
  assumes c_dest: "cs dest = Some cap.NullCap"
  assumes c_src:  "cs src = Some cap"
  assumes ut:     "is_untyped_cap cap"
begin
lemmas no_dest_mdb [simp] = null_no_mdb [OF c_dest]


lemma d_rangeD:
  "\<lbrakk>descendants_range ac p s; m \<Turnstile> p \<rightarrow> p'\<rbrakk> \<Longrightarrow> \<exists>c. cs p' = Some c \<and> untyped_range c \<inter> untyped_range ac = {}"
  apply (drule(1) descendants_rangeD[where s= s,folded m_def cs_def])
  apply clarsimp
  apply (drule disjoint_subset2[OF untyped_range_in_cap_range])
  apply (drule disjoint_subset[OF untyped_range_in_cap_range])
  apply simp
  done


lemma subseteq_imp_not_subset: "A \<subseteq> B \<Longrightarrow> \<not> B \<subset> A" by fastforce


lemma cap_bits_default_untyped_cap:
  "is_untyped_cap (default_cap tp oref sz dev) \<Longrightarrow>
   cap_bits (default_cap tp oref sz dev) = sz"
  by (case_tac tp,simp_all)


lemma untyped_inc':
  assumes inc: "untyped_inc m cs"
  assumes d: "descendants_range (default_cap tp oref sz dev) src s"
  assumes r: "untyped_range (default_cap tp oref sz dev) \<subseteq> untyped_range cap"
  assumes al: "cap_aligned (default_cap tp oref sz dev)"
  assumes noint: "untyped_range (default_cap tp oref sz dev) \<inter> usable_untyped_range cap = {}"
  shows "untyped_inc (m(dest \<mapsto> src)) (cs(dest \<mapsto> default_cap tp oref sz dev))"
  using inc r c_src al ut noint
  unfolding untyped_inc_def descendants_of_def
  apply (intro allI impI)
  apply (rule conjI)
    apply (simp add: parency del: split_paired_All split: if_split_asm)
    apply (rule untyped_ranges_aligned_disjoing_or_subset[OF _ cs_cap_aligned])
     apply simp
    apply simp
    apply (rule untyped_ranges_aligned_disjoing_or_subset[OF cs_cap_aligned _ ])
     apply simp
    apply simp
  apply (case_tac "p' = src")
   apply (simp add: parency del: split_paired_All split: if_split_asm)
      apply (erule_tac x=src in allE)
      apply (erule_tac x=p in allE)
      apply (simp add: c_dest)
     apply (simp add: subseteq_imp_not_subset)
     apply (intro impI)
     apply (drule(1) usable_range_subseteq[OF cs_cap_aligned])
     apply simp
     apply (drule Int_absorb1)
     apply simp
    apply (simp add: c_dest)
   apply (erule_tac x = src in allE)
   apply (erule_tac x = p in allE)
   apply simp
   apply (elim conjE)
   apply (rule conjI)
    apply (intro impI)
     apply (elim disjE)
     apply (clarsimp+)[3]
   apply (erule subset_splitE)
      apply clarsimp
     apply (intro conjI impI)
       apply simp+
    apply (intro conjI impI,clarsimp+)[1]
   apply (intro conjI impI,clarsimp+)[1]
  apply (simp add: parency del: split_paired_All split: if_split_asm)
    apply (erule_tac x=src in allE)
    apply (erule_tac x=p' in allE)
    apply simp
    apply (elim conjE)
    apply (erule subset_splitE)
       apply (intro conjI)
        apply (intro impI)
        apply blast
       apply blast
      apply (intro conjI)
        apply (intro impI)
        apply (drule trancl_trans)
        apply fastforce
       apply simp
     apply (intro impI)
     apply (cut_tac p' = p' in d_rangeD[OF d])
      apply simp+
     apply (drule(1) untyped_range_non_empty[OF _ cs_cap_aligned])
     apply (drule(1) untyped_range_non_empty)
     apply (rule int_not_empty_subsetD)
       apply (simp add:Int_ac)
      apply simp
     apply simp
    apply simp
    apply (intro conjI)
     apply (intro impI)
      apply (erule disjE)
       apply (drule trancl_trans)
        apply fastforce
       apply simp
      apply (simp add: subseteq_imp_not_subset)
    apply (drule(1) untyped_range_non_empty[OF _ cs_cap_aligned])
    apply (drule(1) untyped_range_non_empty)
    apply (elim disjE)
     apply (cut_tac p' = p' in d_rangeD[OF d])
      apply clarsimp
     apply simp
     apply fastforce
    apply clarsimp
    apply (drule(1) untyped_range_non_empty[OF _ cs_cap_aligned])
    apply (drule(1) untyped_range_non_empty)
    apply (thin_tac "P \<longrightarrow> Q" for P Q)+
     apply blast
   apply (erule_tac x = src in allE)
   apply (erule_tac x = p in allE)
   apply simp
   apply (elim conjE)
   apply (erule subset_splitE)
      apply simp
      apply (thin_tac "P \<longrightarrow> Q" for P Q)+
      apply blast
     apply (intro conjI)
       apply (intro impI)
       apply (drule trancl_trans)
        apply fastforce
       apply simp
      apply clarsimp
     apply simp
     apply (elim conjE)
     apply (thin_tac "P \<longrightarrow> Q" for P Q)+
     apply (thin_tac "P \<inter> Q = {}" for P Q)+
     apply (intro impI)
     apply (drule d_rangeD[OF d])
     apply simp
     apply (drule(1) untyped_range_non_empty[OF _ cs_cap_aligned])+
     apply (drule(1) untyped_range_non_empty)+
     apply (intro conjI)
       apply (rule notI)
       apply (drule(1) disjoint_subset2[OF psubset_imp_subset,rotated])
       apply simp
      apply (rule notI)
      apply (drule(1) disjoint_subset[OF psubset_imp_subset,rotated])
      apply simp
     apply blast
    apply simp
    apply (intro conjI)
       apply (intro impI)
       apply (erule disjE)
       apply (drule trancl_trans)
        apply fastforce
       apply simp
      apply fastforce
     apply (clarsimp simp: subseteq_imp_not_subset)
     apply (drule(1) usable_range_subseteq[OF cs_cap_aligned] )
     apply blast
    apply (rule impI)
    apply simp
    apply (drule(1) untyped_range_non_empty[OF _ cs_cap_aligned])+
    apply (drule(1) untyped_range_non_empty)+
    apply (elim conjE | simp)+
    apply (drule d_rangeD[OF d])
    apply simp
    apply (intro conjI)
      apply (rule notI)
      apply (drule(1) disjoint_subset2[OF psubset_imp_subset,rotated])
      apply simp
     apply (rule notI)
     apply (drule(1) disjoint_subset[OF psubset_imp_subset,rotated])
     apply simp
    apply blast
   apply (thin_tac "P \<longrightarrow> Q" for P Q)+
   apply (drule disjoint_subset2)
    apply (simp (no_asm) add:Int_ac)
   apply (drule(1) untyped_range_non_empty[OF _ cs_cap_aligned])+
   apply (drule(1) untyped_range_non_empty)+
   apply blast
  apply (erule_tac x= src in allE)
  apply (erule_tac x = p' in allE)
  apply simp
  apply (intro impI conjI)
    apply simp+
  done

end

lemma default_cap_replies[simp]:
  "\<not> is_reply_cap (default_cap otype oref sz dev)"
  "\<not> is_master_reply_cap (default_cap otype oref sz dev)"
  by (cases otype, simp_all add: is_cap_simps)+


lemma inter_non_emptyD:
 "\<lbrakk>A \<subseteq> B; A \<inter> C \<noteq> {}\<rbrakk> \<Longrightarrow> B \<inter> C \<noteq> {}"
  by blast


lemma cap_class_default_cap:
  "cap_class (default_cap tp oref sz dev) = PhysicalClass"
  apply (case_tac tp)
  apply (simp_all add: default_cap_def physical_arch_cap_has_ref aobj_ref_default)
  done


lemma untyped_incD2:
  "\<lbrakk>cs p = Some c; is_untyped_cap c; cs p' = Some c'; is_untyped_cap c'; untyped_inc m cs\<rbrakk>
  \<Longrightarrow> untyped_range c \<inter> untyped_range c' \<noteq> {} \<longrightarrow> p \<in> descendants_of p' m \<and> untyped_range c \<subseteq> untyped_range c'
    \<or> p' \<in> descendants_of p m \<and> untyped_range c'\<subseteq> untyped_range c
    \<or> p = p'"
  apply (drule(4) untyped_incD)
  apply (rule ccontr)
  apply (elim conjE subset_splitE)
    apply clarsimp+
  done

lemma create_cap_mdb[wp]:
  "\<lbrace>valid_mdb
      and valid_objs
      and cte_wp_at (\<lambda>c. is_untyped_cap c \<and>
                         obj_refs (default_cap tp oref sz dev) \<subseteq> untyped_range c \<and>
                         untyped_range (default_cap tp oref sz dev) \<subseteq> untyped_range c
                         \<and> untyped_range (default_cap tp oref sz dev) \<inter> usable_untyped_range c = {}) p
      and descendants_range (default_cap tp oref sz dev) p
      and cte_wp_at ((=) cap.NullCap) cref
      and K (cap_aligned (default_cap tp oref sz dev))\<rbrace>
      create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  apply (simp add: valid_mdb_def2 create_cap_def set_cdt_def)
  apply (wp set_cap_caps_of_state2 | simp)+
  apply clarsimp
  apply (subgoal_tac "mdb_insert_abs (cdt s) p cref")
   prefer 2
   apply (rule mdb_insert_abs.intro)
     apply (clarsimp simp: cte_wp_at_def)
    apply (clarsimp simp: valid_mdb_def2
                   elim!: mdb_Null_None mdb_Null_descendants)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (fold fun_upd_def)
  apply (intro conjI)
           apply (rule mdb_cte_atI)
           apply (simp add: is_cap_simps split: if_split_asm)
            apply (drule(1) mdb_cte_atD,clarsimp)+
          apply (simp add: untyped_mdb_def descendants_of_def mdb_insert_abs.parency
                      del: split_paired_All)
          apply (intro allI conjI impI)
               apply (clarsimp simp: is_cap_simps)
              apply (clarsimp simp: is_cap_simps)
             apply (erule_tac x=p in allE)
             apply (erule_tac x=ptr' in allE)
             apply (simp del: split_paired_All)
             apply (erule impE, blast)
             apply (erule (1) trancl_trans)
            apply (simp del: split_paired_All)
           apply (erule_tac x=p in allE)
           apply (erule_tac x=ptr' in allE)
           apply (simp del: split_paired_All)
           apply (erule impE, blast)
           apply (drule(1) descendants_rangeD)
           apply (simp del: split_paired_All add: cap_range_def)
           apply blast
          apply (drule_tac x=ptr in spec)
          apply (drule_tac x=cref in spec)
          apply (simp del: split_paired_All)
          apply (frule(1) inter_non_emptyD[rotated])
          apply (drule_tac c = cap and c' = capa in untyped_incD2)
              apply simp+
          apply (clarsimp simp add: descendants_of_def simp del: split_paired_All)
          apply (drule(1) descendants_rangeD)
          apply (clarsimp simp del: split_paired_All simp: cap_range_def)
          apply blast
         apply (erule(1) mdb_insert_abs.descendants_inc)
          apply simp
         apply (clarsimp simp: is_cap_simps cap_range_def cap_class_default_cap)
        apply (clarsimp simp: no_mloop_def)
        apply (frule_tac p = "(a,b)" and p'="(a,b)" in mdb_insert_abs.parency)
        apply (simp split: if_split_asm)
        apply (erule disjE)
         apply (drule_tac m = "cdt s" in mdb_cte_at_Null_descendants)
          apply (clarsimp simp: untyped_mdb_def)
         apply (clarsimp simp: descendants_of_def simp del: split_paired_All)
        apply clarsimp
       apply (rule mdb_create_cap.untyped_inc')
            apply (rule mdb_create_cap.intro)
              apply (rule vo_abs.intro)
               apply (rule vmdb_abs.intro)
               apply (simp add: valid_mdb_def swp_def cte_wp_at_caps_of_state)
              apply (erule vo_abs_axioms.intro)
             apply assumption
            apply (erule (2) mdb_create_cap_axioms.intro)
           apply assumption+
      apply (simp add: ut_revocable_def del: split_paired_All)
     apply (simp add: irq_revocable_def del: split_paired_All)
    apply (simp add: reply_master_revocable_def del: split_paired_All)
   apply (simp add: reply_mdb_def)
   apply (subgoal_tac "\<And>t m R. default_cap tp oref sz dev \<noteq> cap.ReplyCap t m R")
    apply (rule conjI)
     apply (fastforce simp: reply_caps_mdb_def descendants_of_def
                            mdb_insert_abs.parency
                  simp del: split_paired_All split_paired_Ex
                     elim!: allEI exEI)
    apply (fastforce simp: reply_masters_mdb_def descendants_of_def
                           mdb_insert_abs.parency
                 simp del: split_paired_All split_paired_Ex
                    elim!: allEI)
   apply (cases tp, simp_all)[1]
  apply (erule valid_arch_mdb_untypeds)
  done

lemma create_cap_descendants_range[wp]:
 "\<lbrace>descendants_range c p and
   K (cap_range c \<inter> cap_range (default_cap tp oref sz dev) = {}) and
   cte_wp_at ((\<noteq>) cap.NullCap) p and
   cte_wp_at ((=) cap.NullCap) cref and
   valid_mdb\<rbrace>
  create_cap tp sz p dev (cref,oref)
  \<lbrace>\<lambda>rv. descendants_range c p\<rbrace>"
  apply (simp add: create_cap_def descendants_range_def cte_wp_at_caps_of_state set_cdt_def)
  apply (wp set_cap_caps_of_state2 | simp del: fun_upd_apply)+
  apply (clarsimp simp: cte_wp_at_caps_of_state swp_def valid_mdb_def simp del: fun_upd_apply)
  apply (subst (asm) mdb_insert_abs.descendants_child)
   apply (rule mdb_insert_abs.intro)
     apply clarsimp
    apply (erule (1) mdb_cte_at_Null_None)
   apply (erule (1) mdb_cte_at_Null_descendants)
  apply clarsimp
  apply (rule conjI, clarsimp)
   apply blast
  apply clarsimp
  done

(* FIXME: Move to top *)
lemma caps_overlap_reservedD:
  "\<lbrakk>caps_overlap_reserved S s; caps_of_state s slot = Some cap;
    is_untyped_cap cap\<rbrakk>
   \<Longrightarrow> usable_untyped_range cap \<inter> S = {}"
  apply (simp add: caps_overlap_reserved_def)
  apply (erule ballE)
    apply (erule(1) impE)
   apply simp
  apply fastforce
  done

lemma cap_range_inter_emptyD:
  "cap_range a \<inter> cap_range b = {} \<Longrightarrow> untyped_range a \<inter> untyped_range b = {}"
  apply (drule disjoint_subset2[OF untyped_range_in_cap_range])
  apply (drule disjoint_subset[OF untyped_range_in_cap_range])
  apply simp
  done

lemma create_cap_overlap_reserved [wp]:
 "\<lbrace>caps_overlap_reserved (untyped_range c) and
   K (cap_range c \<inter> cap_range (default_cap tp oref sz dev) = {}) and
   cte_wp_at ((\<noteq>) cap.NullCap) p and
   cte_wp_at ((=) cap.NullCap) cref and
   valid_mdb and K (cap_aligned (default_cap tp oref sz dev))\<rbrace>
  create_cap tp sz p dev (cref,oref)
  \<lbrace>\<lambda>rv s. caps_overlap_reserved (untyped_range c) s\<rbrace>"
  apply (simp add: create_cap_def caps_overlap_reserved_def cte_wp_at_caps_of_state set_cdt_def)
  apply (wp set_cap_caps_of_state2 | simp del: fun_upd_apply)+
  apply (clarsimp simp: ran_def split: if_splits)
  apply (case_tac "cref = (a,b)")
   apply simp
   apply (erule(1) disjoint_subset[OF usable_range_subseteq])
   apply (simp add:Int_ac cap_range_inter_emptyD)
  apply simp
  apply (erule(2) caps_overlap_reservedD)
  done


crunch typ_at[wp]: create_cap "\<lambda>s. P (typ_at T p s)"
  (simp: crunch_simps)

lemmas create_cap_cap_table_at[wp] =
    cap_table_at_lift_valid [OF create_cap_typ_at]

lemma retype_region_invs_extras:
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty dev\<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev\<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev\<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and (\<lambda>s. \<exists>slot. cte_wp_at (\<lambda>c.  {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} \<subseteq> cap_range c \<and> cap_is_device c = dev) slot s)
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty dev \<lbrace>\<lambda>rv. valid_vspace_objs\<rbrace>"
  apply (wp hoare_strengthen_post [OF retype_region_post_retype_invs],
    auto simp: post_retype_invs_def split: if_split_asm)+
  done

lemma set_tuple_pick:
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>x \<in> set (xs rv s). Q x rv s\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>tup \<in> set (zip (xs rv s) (ys rv s)). Q (fst tup) rv s\<rbrace>"
  "\<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>y \<in> set (ys rv s). R y rv s\<rbrace> \<Longrightarrow>
   \<lbrace>P\<rbrace> f \<lbrace>\<lambda>rv s. \<forall>tup \<in> set (zip (xs rv s) (ys rv s)). R (snd tup) rv s\<rbrace>"
  apply (safe elim!: hoare_strengthen_post)
   apply (clarsimp simp: set_zip)+
  done


lemma obj_at_foldr_intro:
  "P obj \<and> p \<in> set xs \<Longrightarrow> obj_at P p (s \<lparr> kheap := foldr (\<lambda>p ps. ps (p \<mapsto> obj)) xs (kheap s) \<rparr>)"
  by (clarsimp simp: obj_at_def foldr_upd_app_if)


context Untyped_AI_arch begin
lemma retype_ret_valid_caps:
  "\<lbrace>pspace_no_overlap_range_cover ptr sz
      and K (tp = Structures_A.CapTableObject \<longrightarrow> us > 0)
      and K (tp = Untyped \<longrightarrow> untyped_min_bits \<le> us)
      and K (tp \<noteq> ArchObject ASIDPoolObj)
      and K (range_cover ptr sz (obj_bits_api tp us) n \<and> ptr \<noteq> 0)\<rbrace>
        retype_region ptr n us tp dev\<lbrace>\<lambda>rv (s::'state_ext state). \<forall>y\<in>set rv. s \<turnstile> default_cap tp y us dev\<rbrace>"
  apply (simp add: retype_region_def split del: if_split cong: if_cong)
  apply wp
  apply (simp only: trans_state_update[symmetric] more_update.valid_cap_update)
  apply wp
  apply (case_tac tp,simp_all)
   defer
      apply ((clarsimp simp:valid_cap_def default_object_def cap_aligned_def
        is_obj_defs well_formed_cnode_n_def empty_cnode_def
        dom_def  ptr_add_def | rule conjI | intro conjI obj_at_foldr_intro imageI
      | rule is_aligned_add_multI[OF _ le_refl],
        (simp add:range_cover_def word_bits_def obj_bits_api_def)+)+)[3]
    apply (rule_tac ptr=ptr and sz=sz in retype_ret_valid_caps_captable; simp)
   apply (rule_tac ptr=ptr and sz=sz in retype_ret_valid_caps_aobj; simp)
  apply (clarsimp simp:valid_cap_def default_object_def cap_aligned_def
        is_obj_defs well_formed_cnode_n_def empty_cnode_def
        dom_def ptr_add_def | intro conjI obj_at_foldr_intro
        imageI
      | rule is_aligned_add_multI[OF _ le_refl]
      | fastforce simp:range_cover_def obj_bits_api_def
          word_bits_def a_type_def)+
   apply (clarsimp simp:valid_cap_def valid_untyped_def)
   apply (drule(1) pspace_no_overlap_obj_range)
   apply (frule range_cover_cell_subset)
    apply (erule of_nat_mono_maybe[rotated])
    apply (drule range_cover.range_cover_n_less)
    apply (simp add:word_bits_def)
   apply (simp add:obj_bits_api_def field_simps
               del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
           Int_atLeastAtMost atLeastatMost_empty_iff)
   apply blast
  apply (erule(2) range_cover_no_0)
 done
end

(* FIXME: move to Lib *)
lemma set_zip_helper:
  "t \<in> set (zip xs ys) \<Longrightarrow> fst t \<in> set xs \<and> snd t \<in> set ys"
  by (clarsimp simp add: set_zip)


lemma ex_cte_cap_protects:
  "\<lbrakk> ex_cte_cap_wp_to P p s; cte_wp_at ((=) (UntypedCap dev ptr bits idx)) p' s;
     descendants_range_in S p' s; untyped_children_in_mdb s; S\<subseteq> untyped_range (UntypedCap dev ptr bits idx);
     valid_global_refs s \<rbrakk>
      \<Longrightarrow> fst p \<notin> S"
  apply (drule ex_cte_cap_to_obj_ref_disj, erule disjE)
   apply clarsimp
   apply (erule(1) untyped_children_in_mdbEE[where P="\<lambda>c. fst p \<in> obj_refs c" for c])
      apply simp
     apply assumption
    apply (rule notemptyI[where x="fst p"])
    apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                              Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex)
    apply blast
    apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (drule(2) descendants_range_inD)
    apply (clarsimp simp:cap_range_def)
    apply blast
  apply clarsimp
  apply (drule_tac irq=irq in valid_globals_irq_node, assumption)
  apply (clarsimp simp del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex)
  apply blast
  done


lemma untyped_range_default_empty:
  "tp \<noteq> Untyped \<Longrightarrow> untyped_range (default_cap tp sz us dev) = {}"
  by (cases tp, auto)


lemma obj_refs_default_cap:
  "obj_refs (default_cap tp oref sz dev) \<subseteq> {oref}"
  apply (cases tp, simp_all add: aobj_ref_default)
  done


lemma obj_refs_default_nut:
  "tp \<noteq> Untyped \<Longrightarrow> obj_refs (default_cap tp oref sz dev) = {oref}"
  apply (cases tp, simp_all add: aobj_ref_default)
  done


lemma range_cover_subset':
  "\<lbrakk>range_cover ptr sz sbit n; n \<noteq> 0\<rbrakk>
  \<Longrightarrow> {ptr ..ptr + of_nat n * 2 ^ sbit - 1} \<subseteq> {ptr..(ptr && ~~ mask sz) + 2^ sz - 1}"
  apply clarsimp
  apply (frule range_cover_cell_subset[OF _ of_nat_mono_maybe,where y1 = "(n - 1)"])
    apply (drule range_cover.range_cover_n_less)
     apply (simp add:word_bits_def)
   apply simp
  apply (clarsimp simp:range_cover_def)
  apply (erule impE)
   apply (clarsimp simp:p_assoc_help)
   apply (rule is_aligned_no_wrap'[OF is_aligned_add_multI[OF _ le_refl refl ]])
   apply (fastforce simp:range_cover_def)+
  apply (clarsimp)
  apply (subst (asm) add.assoc)
  apply (subst (asm) distrib_right[where b = "1::'a::len word",simplified,symmetric])
  apply simp
  done

context Untyped_AI_arch begin
lemma retype_region_ranges':
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) n)\<rbrace>
   retype_region ptr n us tp dev
   \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. cap_range (default_cap tp y us dev) \<subseteq> {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api tp us)) - 1}\<rbrace>"
  apply (simp add:valid_def)
  apply clarify
  apply (drule use_valid[OF _ retype_region_ret])
   apply simp
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                            Int_atLeastAtMost atLeastatMost_empty_iff)
  apply (rule subsetD[OF subset_trans])
    apply (rule range_cover_subset,assumption)
     apply clarsimp
     apply assumption
    apply fastforce
   apply simp
  apply (case_tac tp)
       apply (simp_all add: cap_range_def obj_bits_api_def ptr_add_def)
      apply (subst add.commute, rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
        apply (fastforce simp: range_cover_def)
       apply (simp_all add: word_bits_def is_aligned_mult_triv2[where n=tcb_bits, simplified])[2]
     apply (subst add.commute, rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
       apply (fastforce simp: range_cover_def)
      apply (simp add: word_bits_def is_aligned_mult_triv2[where n=endpoint_bits, simplified])+
    apply (subst add.commute, rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
      apply (fastforce simp: range_cover_def)
     apply (simp add: word_bits_def is_aligned_mult_triv2[where n=ntfn_bits, simplified])+
   apply (clarsimp simp: is_aligned_def)
   apply (simp add: p_assoc_help)
   apply (rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
     apply (fastforce simp: range_cover_def)
    apply (rule is_aligned_mult_triv2)
   apply (simp add: range_cover_def)
  apply (simp add: p_assoc_help)
  apply (rule is_aligned_no_wrap'[OF is_aligned_add_multI[OF _ le_refl refl]])
   apply (simp add: range_cover_def)+
  done

lemma retype_region_ranges:
  "\<lbrace>cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz
          \<and> obj_ref_of c = ptr && ~~ mask sz) p and
    pspace_no_overlap_range_cover ptr sz and
    valid_pspace and K (range_cover ptr sz (obj_bits_api tp us) n)
   \<rbrace>
  retype_region ptr n us tp dev
   \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. cte_wp_at
           (\<lambda>c. cap_range (default_cap tp y us dev) \<subseteq> untyped_range c )
           p s\<rbrace>"
   apply (clarsimp simp: cte_wp_at_caps_of_state valid_def)
   apply (frule_tac P1 = "(=) cap" in use_valid[OF _ retype_region_cte_at_other])
     apply simp
    apply (fastforce simp: cte_wp_at_caps_of_state)
   apply (clarsimp simp: cte_wp_at_caps_of_state)
   apply (frule use_valid[OF _ retype_region_ranges'])
    apply (fastforce simp: cte_wp_at_caps_of_state)
   apply (drule(1) bspec)
   apply (drule(1) subsetD)
   apply (rule_tac A = "{x..y}" for x y in subsetD[rotated])
   apply assumption
   apply simp
   apply (erule subset_trans[OF range_cover_subset'])
    apply (frule use_valid[OF _ retype_region_ret])
    apply simp
    apply fastforce
   apply (clarsimp simp: is_cap_simps)
   apply (erule order_trans[OF word_and_le2])
   done
end

lemma map_snd_zip_prefix_help:
  "map (\<lambda>tup. cap_range (default_cap tp (snd tup) us dev)) (zip xs ys) \<le>
   map (\<lambda>x. cap_range (default_cap tp x us dev)) ys"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply auto
  done

context Untyped_AI_arch begin
lemma retype_region_distinct_sets:
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) n)\<rbrace>
  retype_region ptr n us tp dev
  \<lbrace>\<lambda>rv s. distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) us dev)) (zip xs rv))\<rbrace>"
  apply (simp add: distinct_sets_prop)
  apply (rule hoare_gen_asm[where P'="\<top>", simplified])
  apply (rule hoare_strengthen_post [OF retype_region_ret])
  apply (rule distinct_prop_prefixE [rotated])
   apply (rule map_snd_zip_prefix_help [unfolded less_eq_list_def])
  apply (clarsimp simp: retype_addrs_def distinct_prop_map)
  apply (rule distinct_prop_distinct)
   apply simp
  apply (subgoal_tac  "of_nat y * (2::machine_word) ^ obj_bits_api tp us \<noteq> of_nat x * 2 ^ obj_bits_api tp us")
   apply (case_tac tp) defer
        apply (simp add:cap_range_def ptr_add_def)+
   apply (clarsimp simp: ptr_add_def word_unat_power[symmetric]
                      shiftl_t2n[simplified mult.commute, symmetric])
   apply (erule(2) of_nat_shift_distinct_helper[where 'a=machine_word_len and n = "obj_bits_api tp us"])
     apply simp
    apply (simp add:range_cover_def)
   apply (erule range_cover.range_cover_n_le)
  apply (clarsimp simp: add_diff_eq[symmetric]
                  simp del: Int_atLeastAtMost
                  dest!: less_two_pow_divD)
  apply (simp add: obj_bits_api_def ptr_add_def shiftl_t2n[simplified mult.commute, symmetric] del: Int_atLeastAtMost)
  apply (rule aligned_neq_into_no_overlap)
    apply simp
   apply (simp_all add:range_cover_def shiftl_t2n mult.commute)
   apply (rule is_aligned_add_multI[OF _ le_refl refl])
   apply (simp add:range_cover_def)+
  apply (rule is_aligned_add_multI[OF _ le_refl refl])
  apply (simp add:range_cover_def)
  done

end

declare dmo_aligned [wp]

crunch pdistinct[wp]: do_machine_op "pspace_distinct"

crunch vmdb[wp]: do_machine_op "valid_mdb"

crunch mdb[wp]: do_machine_op "\<lambda>s. P (cdt s)"

lemmas dmo_valid_cap[wp] = valid_cap_typ [OF do_machine_op_obj_at]

lemma delete_objects_pspace_no_overlap[wp]:
  "\<lbrace>\<lambda>s. (\<exists>dev idx. s \<turnstile> (UntypedCap dev ptr bits idx))
      \<and> pspace_aligned s \<and> valid_objs s \<and> (S = {ptr .. ptr + 2 ^ bits - 1})\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_. pspace_no_overlap S\<rbrace>"
  apply (unfold delete_objects_def)
  apply wp
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: pspace_no_overlap_detype')
  done

lemma retype_region_descendants_range:
  "\<lbrace>\<lambda>s. descendants_range x cref s
    \<and> pspace_no_overlap_range_cover ptr sz s \<and> valid_pspace s
    \<and> range_cover ptr sz (obj_bits_api ty us) n\<rbrace> retype_region ptr n us ty dev
          \<lbrace>\<lambda>rv s. descendants_range x cref s\<rbrace>"
  apply (simp add:descendants_range_def)
  apply (rule hoare_pre)
  apply (wps retype_region_mdb)
  apply (wp hoare_vcg_ball_lift retype_cte_wp_at)
  apply fastforce
  done

lemma cap_range_def2:
  "cap_range (default_cap ty ptr us dev) = (if ty = Untyped then {ptr..ptr + 2 ^ us - 1} else {ptr})"
  apply (case_tac ty)
  by (simp_all add: cap_range_def)

context Untyped_AI_arch begin
lemma retype_region_descendants_range_ret:
  "\<lbrace>\<lambda>s. (range_cover ptr sz (obj_bits_api ty us) n)
    \<and> pspace_no_overlap_range_cover ptr sz s
    \<and> valid_pspace s
    \<and> range_cover ptr sz (obj_bits_api ty us) n
    \<and> descendants_range_in {ptr..ptr + of_nat n * 2^(obj_bits_api ty us) - 1} cref s
  \<rbrace>
  retype_region ptr n us ty dev
          \<lbrace>\<lambda>rv (s::'state_ext state). \<forall>y\<in>set rv. descendants_range (default_cap ty y us dev) cref s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp: valid_def)
  apply (frule retype_region_ret[unfolded valid_def,simplified,THEN spec,THEN bspec])
  apply (clarsimp)
  apply (rename_tac x)
  apply (erule use_valid[OF _ retype_region_descendants_range])
  apply (intro conjI,simp_all)
   apply (clarsimp simp: descendants_range_def descendants_range_in_def)
  apply (drule(1) bspec)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule disjoint_subset2[rotated])
  apply (frule(1) range_cover_subset)
   apply simp
  apply (erule subset_trans[rotated])
  apply (subgoal_tac "ptr + of_nat x * 2 ^ obj_bits_api ty us
          \<le> ptr + of_nat x * 2 ^ obj_bits_api ty us + 2 ^ obj_bits_api ty us - 1")
   prefer 2
   apply (rule is_aligned_no_overflow)
     apply (rule is_aligned_add_multI)
        apply (fastforce simp: range_cover_def)+
  apply (auto simp add: cap_range_def2 ptr_add_def obj_bits_api_def)
  done
end

lemma caps_overlap_reserved_def2:
  "caps_overlap_reserved S =
   (\<lambda>s. (\<forall>cap \<in> ran (null_filter (caps_of_state s)).
           is_untyped_cap cap \<longrightarrow> usable_untyped_range cap \<inter> S = {}))"
  apply (rule ext)
  apply (clarsimp simp: caps_overlap_reserved_def)
  apply (intro iffI ballI impI)
    apply (elim ballE impE)
      apply simp
     apply simp
    apply (simp add: ran_def null_filter_def split: if_split_asm option.splits)
  apply (elim ballE impE)
    apply simp
   apply simp
  apply (clarsimp simp: ran_def null_filter_def is_cap_simps
              simp del: split_paired_All split_paired_Ex split: if_splits)
  apply (drule_tac x = "(a,b)" in spec)
  apply simp
  done

lemma set_cap_valid_mdb_simple:
  "\<lbrace>\<lambda>s. valid_objs s \<and> valid_mdb s \<and> descendants_range_in {ptr .. ptr+2^sz - 1} cref s
   \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr \<and> cap_is_device c = dev) cref s\<rbrace>
  set_cap (UntypedCap dev ptr sz idx) cref
 \<lbrace>\<lambda>rv s'. valid_mdb s'\<rbrace>"
  apply (simp add: valid_mdb_def)
  apply (rule hoare_pre)
  apply (wp set_cap_mdb_cte_at)
  apply (wps set_cap_rvk_cdt_ct_ms)
  apply wp
  apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps
    reply_master_revocable_def irq_revocable_def reply_mdb_def)
  unfolding fun_upd_def[symmetric]
  apply clarsimp
  proof(intro conjI impI)
  fix s f r bits dev
  assume obj:"valid_objs s"
  assume mdb:"untyped_mdb (cdt s) (caps_of_state s)"
  assume cstate:"caps_of_state s cref = Some (UntypedCap dev r bits f)" (is "?m cref = Some ?srccap")
  show "untyped_mdb (cdt s) ((caps_of_state s)(cref \<mapsto> UntypedCap dev r bits idx))"
  apply (rule untyped_mdb_update_free_index
     [where capa = ?srccap and m = "caps_of_state s" and src = cref,
       unfolded free_index_update_def,simplified,THEN iffD2])
   apply (simp add: cstate mdb)+
  done
  assume inc: "untyped_inc (cdt s) (caps_of_state s)"
  assume drange: "descendants_range_in {r..r + 2 ^ bits - 1} cref s"
  have untyped_range_simp: "untyped_range (UntypedCap dev r bits f) = untyped_range (UntypedCap dev r bits idx)"
    by simp
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  show "untyped_inc (cdt s) ((caps_of_state s)(cref \<mapsto> UntypedCap dev r bits idx))"
  using inc cstate drange
  apply (unfold untyped_inc_def)
   apply (intro allI impI)
   apply (drule_tac x = p in spec)
   apply (drule_tac x = p' in spec)
   apply (case_tac "p = cref")
    apply (simp)
    apply (case_tac "p' = cref")
     apply simp
    apply (simp add: untyped_range_simp)
    apply (intro conjI impI)
     apply (simp)
     apply (elim conjE)
     apply (thin_tac "Q \<longrightarrow> P" for P Q)+
     apply (frule(2) descendants_range_inD[rotated])
     apply (drule caps_of_state_valid_cap[OF _ obj])
     apply (drule sym)
     apply (rule disjoint_subset2[OF usable_range_subseteq])
     apply (simp add: valid_cap_def cap_aligned_def untyped_range.simps)+
    apply (elim disjE conjE)
     apply (frule(2) descendants_range_inD[rotated])
     apply (drule caps_of_state_valid_cap[OF _ obj])+
     apply (drule sym)
     apply (simp add: untyped_range.simps)
     apply (drule(1) untyped_range_non_empty[OF _ valid_cap_aligned])
     apply simp+
  apply (case_tac "p' = cref")
   apply simp
   apply (intro conjI)
      apply (elim conjE)
      apply (thin_tac "P\<longrightarrow>Q" for P Q)+
      apply (simp add: untyped_range_simp)+
     apply (intro impI)
     apply (elim conjE | simp)+
     apply (thin_tac "P\<longrightarrow>Q" for P Q)+
     apply (frule(2) descendants_range_inD[rotated])
     apply (drule caps_of_state_valid_cap[OF _ obj])
     apply (drule sym)
     apply (rule disjoint_subset2[OF usable_range_subseteq])
     apply ((clarsimp simp: valid_cap_def cap_aligned_def untyped_range.simps)+)[3]
    apply (intro impI)
    apply (elim conjE subset_splitE | simp)+
        apply (thin_tac "P\<longrightarrow>Q" for P Q)+
        apply (clarsimp simp: untyped_range.simps)
      apply simp
      apply (elim conjE)
      apply (thin_tac "P\<longrightarrow>Q" for P Q)+
      apply (clarsimp simp: untyped_range.simps)
     apply simp
     apply (erule disjE)
      apply (clarsimp simp: blah)
     apply (clarsimp simp: blah)
    apply (drule_tac t = c' in sym)
    apply (simp add: untyped_range.simps)
   apply (drule_tac t= c' in sym)
   apply (intro impI)
   apply (simp add: untyped_range.simps)
   apply (elim disjE conjE)
    apply simp
   apply (frule(2) descendants_range_inD[rotated])
   apply (drule caps_of_state_valid_cap[OF _ obj])+
   apply simp
   apply (drule(1) untyped_range_non_empty[OF _ valid_cap_aligned])
   apply simp+
  done
  assume "ut_revocable (is_original_cap s) (caps_of_state s)"
  thus "ut_revocable (is_original_cap s) ((caps_of_state s)(cref \<mapsto> UntypedCap dev r bits idx))"
  using cstate
  by (fastforce simp: ut_revocable_def)
  assume "valid_arch_mdb (is_original_cap s) (caps_of_state s)"
  thus "valid_arch_mdb (is_original_cap s) ((caps_of_state s)(cref \<mapsto> UntypedCap dev r bits idx))"
  using cstate
  by (fastforce elim!: valid_arch_mdb_untypeds)
  assume "reply_caps_mdb (cdt s) (caps_of_state s)"
  thus "reply_caps_mdb (cdt s) ((caps_of_state s)(cref \<mapsto> UntypedCap dev r bits idx))"
  using cstate
  apply (simp add: reply_caps_mdb_def del: split_paired_All)
  apply (intro allI impI conjI)
   apply (drule spec)+
   apply (erule(1) impE)
  apply (erule exE)+
  apply (rule_tac x = ptr' in exI)
  apply clarsimp
  done
  assume "reply_masters_mdb (cdt s) (caps_of_state s)"
  thus "reply_masters_mdb (cdt s) ((caps_of_state s)(cref \<mapsto> UntypedCap dev r bits idx))"
   apply (simp add: reply_masters_mdb_def del: split_paired_All)
   apply (intro allI impI ballI)
   apply (erule exE)
   apply (elim allE impE)
    apply simp
   using cstate
   apply fastforce
   done
  assume misc:
    "mdb_cte_at (swp (cte_wp_at ((\<noteq>) cap.NullCap)) s) (cdt s)"
    "descendants_inc (cdt s) (caps_of_state s)"
    "caps_of_state s cref = Some (UntypedCap dev r bits f)"
  thus "descendants_inc (cdt s) ((caps_of_state s)(cref \<mapsto> UntypedCap dev r bits idx))"
   apply -
   apply (erule descendants_inc_minor)
    apply (clarsimp simp: swp_def cte_wp_at_caps_of_state)
   apply (clarsimp simp: untyped_range.simps)
   done
 qed



lemma set_free_index_valid_pspace_simple:
  "\<lbrace>\<lambda>s. valid_mdb s \<and> valid_pspace s \<and> pspace_no_overlap_range_cover ptr sz s
   \<and> descendants_range_in {ptr .. ptr+2^sz - 1} cref s
   \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr) cref s
   \<and> idx \<le> 2^ sz\<rbrace>
  set_cap (UntypedCap dev ptr sz idx) cref
 \<lbrace>\<lambda>rv s'. valid_pspace s'\<rbrace>"
  apply (clarsimp simp: valid_pspace_def)
  apply (wp set_cap_valid_objs update_cap_iflive set_cap_zombies')
   apply (clarsimp simp: cte_wp_at_caps_of_state is_cap_simps)+
  apply (frule(1) caps_of_state_valid_cap)
  apply (clarsimp simp: valid_cap_def cap_aligned_def )
  apply (intro conjI)
   apply (simp add: valid_untyped_def)
   apply (intro impI allI)
   apply (elim allE allE impE)
     apply simp+
  apply (drule(1) pspace_no_overlap_obj_range)
  apply (simp add: field_simps)
  apply (clarsimp simp add: pred_tcb_at_def tcb_cap_valid_def obj_at_def is_tcb
          valid_ipc_buffer_cap_def split: option.split)
  apply (drule(2) tcb_cap_slot_regular)
  apply (clarsimp simp: tcb_cap_cases_def is_cap_simps split: if_splits)
    apply (fastforce simp: is_nondevice_page_cap_simps)
   apply (clarsimp split: thread_state.splits simp: is_reply_cap_def)
  done

lemma set_untyped_cap_refs_respects_device_simple:
  "\<lbrace>K (is_untyped_cap cap) and cte_wp_at ((=) cap) cref and cap_refs_respects_device_region \<rbrace> set_cap (UntypedCap (cap_is_device cap) (obj_ref_of cap) (cap_bits cap) idx) cref
    \<lbrace>\<lambda>rv s. cap_refs_respects_device_region s\<rbrace>"
  apply (wp set_cap_cap_refs_respects_device_region)
  apply (clarsimp simp del: split_paired_Ex)
  apply (rule_tac x = cref in exI)
  apply (erule cte_wp_at_weakenE)
  apply (case_tac cap,auto)
  done

lemma set_untyped_cap_caps_overlap_reserved:
  "\<lbrace>\<lambda>s. invs s \<and> S \<subseteq> {ptr..ptr + 2 ^ sz - 1} \<and>
  usable_untyped_range (UntypedCap dev ptr sz idx') \<inter> S = {} \<and>
  descendants_range_in S cref s \<and> cte_wp_at ((=) (UntypedCap dev ptr sz idx)) cref s\<rbrace>
  set_cap (UntypedCap dev ptr sz idx') cref
 \<lbrace>\<lambda>rv s. caps_overlap_reserved S s\<rbrace>"
  apply (unfold caps_overlap_reserved_def)
  apply wp
  apply (clarsimp simp: cte_wp_at_caps_of_state caps_overlap_reserved_def
              simp del: usable_untyped_range.simps split: if_split_asm)
  apply (frule invs_mdb)
  apply (erule ranE)
  apply (simp split: if_split_asm del: usable_untyped_range.simps add: valid_mdb_def)
  apply (drule untyped_incD)
   apply ((simp add: is_cap_simps)+)[4]
  apply clarify
  apply (erule subset_splitE)
     apply (simp del: usable_untyped_range.simps)
     apply (thin_tac "P \<longrightarrow> Q" for P Q)+
     apply (elim conjE)
     apply blast
    apply (simp del: usable_untyped_range.simps)
    apply (thin_tac "P\<longrightarrow>Q" for P Q)+
    apply (elim conjE)
    apply (drule(2) descendants_range_inD)
    apply simp
    apply (drule_tac B = S in disjoint_subset[rotated,OF _ usable_range_subseteq])
       apply (rule valid_cap_aligned)
        apply (erule(1) caps_of_state_valid)
      apply simp+
   apply (elim disjE)
     apply clarsimp
     apply (drule(2) descendants_range_inD)
     apply simp
     apply (drule_tac B=S in  disjoint_subset[rotated,OF _ usable_range_subseteq])
        apply (rule valid_cap_aligned)
       apply (erule(1) caps_of_state_valid)
      apply simp+
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (rule disjoint_subset[OF usable_range_subseteq])
     apply (rule valid_cap_aligned)
    apply (erule(1) caps_of_state_valid)
   apply simp+
  apply blast
  done


lemma set_cap_caps_no_overlap:
  "\<lbrace>cte_wp_at (\<lambda>c. untyped_range c = untyped_range cap) cref and caps_no_overlap ptr sz\<rbrace>  set_cap cap cref
  \<lbrace>\<lambda>r s. caps_no_overlap ptr sz s\<rbrace>"
  apply (simp add: caps_no_overlap_def)
  apply wp
  apply (clarsimp simp: cte_wp_at_caps_of_state caps_no_overlap_def
              simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
                        Int_atLeastAtMost atLeastatMost_empty_iff )
  apply (erule ranE)
  apply (simp split: if_splits
    del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff )
   apply (drule bspec)
    apply fastforce
   apply (clarsimp simp
      del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff )
   apply (erule(1) set_mp)
  apply (drule_tac x = capa in bspec)
   apply fastforce
  apply (clarsimp simp
      del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff )
  apply (erule(1) set_mp)
  done


lemma caps_overlap_reserved_detype:
  "caps_overlap_reserved S s \<Longrightarrow> caps_overlap_reserved S (detype H s)"
  apply (clarsimp simp: caps_overlap_reserved_def )
  apply (erule ranE)
  apply (clarsimp split: if_splits)
  apply (drule bspec)
   apply fastforce
  apply simp
  done


lemma caps_no_overlap_detype:
  "caps_no_overlap ptr sz s \<Longrightarrow> caps_no_overlap ptr sz (detype H s)"
   apply (clarsimp simp: caps_no_overlap_def)
   apply (erule ranE)
   apply (clarsimp split: if_splits)
   apply (drule bspec,fastforce)
   apply clarsimp
   apply (erule subsetD)
   apply simp
   done


lemma not_inD:"\<lbrakk>x \<notin> A; y \<in> A\<rbrakk> \<Longrightarrow>x \<noteq> y"
  by clarsimp


lemma caps_of_state_no_overlapD:
  "\<lbrakk>caps_of_state s slot = Some cap; valid_objs s; pspace_aligned s;
    pspace_no_overlap S s\<rbrakk>
   \<Longrightarrow> (fst slot) \<notin> S"
  apply (drule caps_of_state_cteD)
  apply (clarsimp simp: cte_wp_at_cases obj_at_def
              simp del: atLeastAtMost_iff atLeastatMost_subset_iff
                        atLeastLessThan_iff Int_atLeastAtMost)
  apply (elim disjE)
   apply clarify
   apply (frule(2) p_in_obj_range)
   apply (erule(1) pspace_no_overlapE)
   apply (drule(1) IntI)
   unfolding obj_range_def
   apply (drule notemptyI)+
   apply (simp add: Int_ac p_assoc_help
               del: atLeastAtMost_iff atLeastatMost_subset_iff
                    atLeastLessThan_iff Int_atLeastAtMost)
  apply clarify
  apply (frule(2) p_in_obj_range)
  apply (erule(1) pspace_no_overlapE)
  apply (drule(1) IntI)
  unfolding obj_range_def
  apply (drule notemptyI)+
  apply (simp add: Int_ac p_assoc_help add.commute
              del: atLeastAtMost_iff atLeastatMost_subset_iff
         atLeastLessThan_iff Int_atLeastAtMost)
  done


lemma op_equal: "(\<lambda>x. x = c) = ((=) c)" by (rule ext) auto

lemma descendants_range_in_subseteq:
  "\<lbrakk>descendants_range_in A p ms ;B\<subseteq> A\<rbrakk> \<Longrightarrow> descendants_range_in B p ms"
  by (auto simp: descendants_range_in_def cte_wp_at_caps_of_state dest!: bspec)


lemma cte_wp_at_pspace_no_overlapI:
  "\<lbrakk>invs s;
    cte_wp_at (\<lambda>c. c = UntypedCap dev (ptr && ~~ mask sz) sz idx) cref s;
    idx \<le> unat (ptr && mask sz); sz < word_bits\<rbrakk>
   \<Longrightarrow> pspace_no_overlap_range_cover ptr sz s"
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (frule caps_of_state_valid_cap)
    apply (simp add: invs_valid_objs)
  apply (clarsimp simp: valid_cap_def valid_untyped_def)
  apply (unfold pspace_no_overlap_def)
  apply (intro allI impI)
  apply (drule spec)+
  apply (erule(1) impE)
  apply (simp only: obj_range_def[symmetric] p_assoc_help[symmetric])
  apply (frule(1) le_mask_le_2p)
   apply (rule ccontr)
   apply (erule impE)
    apply (rule ccontr)
    apply simp
    apply (drule disjoint_subset2[rotated,
      where B'="{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"])
     apply clarsimp
     apply (rule word_and_le2)
    apply simp
   apply clarsimp
   apply (drule_tac A'="{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"
        in disjoint_subset[rotated])
    apply clarsimp
    apply (rule le_plus'[OF word_and_le2])
    apply simp
    apply (erule word_of_nat_le)
   apply blast
  done


lemma descendants_range_caps_no_overlapI:
  "\<lbrakk>invs s; cte_wp_at ((=) (UntypedCap dev (ptr && ~~ mask sz) sz idx)) cref s;
  descendants_range_in {ptr .. (ptr && ~~ mask sz) +2^sz - 1} cref s\<rbrakk> \<Longrightarrow> caps_no_overlap ptr sz s"
  apply (frule invs_mdb)
  apply (clarsimp simp: valid_mdb_def cte_wp_at_caps_of_state)
  apply (unfold caps_no_overlap_def)
  apply (intro ballI impI)
  apply (erule ranE)
  apply (subgoal_tac "is_untyped_cap cap")
  prefer 2
   apply (rule untyped_range_is_untyped_cap)
   apply blast
  apply (drule untyped_incD)
     apply simp+
  apply (elim conjE)
  apply (erule subset_splitE)
      apply (erule subset_trans[OF _ psubset_imp_subset,rotated])
       apply (clarsimp simp: word_and_le2)
     apply simp
     apply (elim conjE)
     apply (thin_tac "P\<longrightarrow>Q" for P Q)+
     apply (drule(2) descendants_range_inD)
     apply simp
    apply simp
   apply (erule subset_trans[OF _  equalityD1,rotated])
   apply (clarsimp simp: word_and_le2)
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (drule disjoint_subset[rotated,
       where A' = "{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"])
  apply (clarsimp simp: word_and_le2 Int_ac)+
  done


lemma shiftr_then_mask_commute:
  "(x >> n) && mask m = (x && mask (m + n)) >> n"
  using test_bit_size[where w=x]
  by (auto intro: word_eqI simp add: word_size nth_shiftr)


lemma cte_wp_at_caps_no_overlapI:
  "\<lbrakk> invs s;cte_wp_at (\<lambda>c. c = UntypedCap dev (ptr && ~~ mask sz) sz idx) cref s;
  idx \<le> unat (ptr && mask sz);sz < word_bits \<rbrakk> \<Longrightarrow> caps_no_overlap ptr sz s"
  apply (frule invs_mdb)
  apply (frule(1) le_mask_le_2p)
  apply (clarsimp simp: valid_mdb_def cte_wp_at_caps_of_state)
  apply (frule caps_of_state_valid_cap)
    apply (simp add: invs_valid_objs)
  apply (unfold caps_no_overlap_def)
  apply (intro ballI impI)
  apply (erule ranE)
  apply (subgoal_tac "is_untyped_cap cap")
  prefer 2
   apply (rule untyped_range_is_untyped_cap)
   apply blast
  apply (drule untyped_incD)
     apply simp+
  apply (elim conjE)
  apply (erule subset_splitE)
      apply (erule subset_trans[OF _ psubset_imp_subset,rotated])
       apply (clarsimp simp: word_and_le2)
     apply simp
     apply (thin_tac "P\<longrightarrow>Q" for P Q)+
     apply (elim conjE)
     apply (drule disjoint_subset2[rotated,
       where B' = "{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"])
      apply clarsimp
      apply (rule le_plus'[OF word_and_le2])
      apply simp
      apply (erule word_of_nat_le)
     apply simp
    apply simp
   apply (erule subset_trans[OF _  equalityD1,rotated])
   apply (clarsimp simp: word_and_le2)
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (drule disjoint_subset[rotated,
       where A' = "{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"])
  apply (clarsimp simp: word_and_le2 Int_ac)+
  done


lemma add_minus_neg_mask:
 "ptr + a - (ptr && ~~ mask sz) = (ptr && mask sz) + a"
 apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
 apply simp
 done


lemma range_cover_idx_compare:
  "\<lbrakk>range_cover ptr sz sbit n;
    unat ((ptr && mask sz) + of_nat n * 2 ^ sbit) < 2 ^ sz;
    ptr \<noteq> ptr && ~~ mask sz; idx \<le> 2 ^ sz; idx \<le> unat (ptr && mask sz)\<rbrakk>
   \<Longrightarrow> (ptr && ~~ mask sz) + of_nat idx \<le> ptr + (of_nat n << sbit)"
  apply (subst not_less[symmetric])
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
  apply (subst add.commute)
  apply (simp add: not_less)
  apply (subst add.assoc)
  apply (rule word_add_le_mono2)
    apply (rule order_trans[OF word_of_nat_le])
    apply simp
   apply (erule range_cover.range_cover_base_le)
  apply (subst unat_plus_simple[THEN iffD1])
   apply (erule range_cover.range_cover_base_le)
  apply (subst unat_add_lem[THEN iffD1,symmetric])
   apply (frule range_cover.unat_of_nat_shift[OF _ le_refl le_refl])
   apply (simp add: shiftl_t2n field_simps del: add.commute add.assoc)
   apply (rule le_less_trans)
    apply (subst add.commute)
    apply (erule range_cover.range_cover_compare_bound)
   apply (simp add: range_cover_def)
  apply (rule less_diff_conv[THEN iffD1])
  apply (rule less_le_trans)
   apply (simp add: shiftl_t2n field_simps)
  apply (subst le_diff_conv2)
   apply (rule less_imp_le[OF unat_lt2p])
  apply (subst add.commute)
  apply (subst unat_power_lower[where 'a='a, symmetric])
   apply (simp add: range_cover_def)
  apply (rule is_aligned_no_wrap_le[OF is_aligned_neg_mask[OF le_refl]])
  apply (simp add: range_cover_def)+
  done


locale invoke_untyped_proofs =
 fixes s cref reset ptr_base ptr tp us slots ptr' sz idx dev
  assumes vui: "valid_untyped_inv_wcap (Retype cref reset ptr_base ptr tp us slots dev)
      (Some (UntypedCap dev (ptr && ~~ mask sz) sz idx)) s"
  and misc: "ct_active s" "invs s"
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
begin

abbreviation(input)
  "retype_range == {ptr..ptr + of_nat (length slots) * 2 ^ (obj_bits_api tp us) - 1}"

abbreviation(input)
  "usable_range ==  {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"

lemma not_0_ptr[simp]: "ptr\<noteq> 0"
  using misc vui
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) caps_of_state_valid)
  apply (clarsimp simp: valid_cap_def)
  done

lemma cover: "range_cover ptr sz (obj_bits_api tp us) (length slots)"
  using vui
  by (clarsimp simp:cte_wp_at_caps_of_state)

lemma misc2:
  "distinct slots"
  "slots \<noteq> []"
  using vui
  by (auto simp:cte_wp_at_caps_of_state)

lemma subset_stuff[simp]:
  "retype_range \<subseteq> usable_range"
  apply (rule range_cover_subset'[OF cover])
  apply (simp add:misc2)
  done

lemma cte_wp_at:
  "cte_wp_at ((=) (UntypedCap dev (ptr && ~~ mask sz) sz idx)) cref s"
  using vui
  by (clarsimp simp: cte_wp_at_caps_of_state)


lemma idx_cases:
  "(idx \<le> unat (ptr - (ptr && ~~ mask sz)) \<or> reset \<and> ptr = ptr && ~~ mask sz)"
  using vui
  by (clarsimp simp: cte_wp_at_caps_of_state)

lemma desc_range:
  "reset \<longrightarrow> descendants_range_in S cref s"
  using vui
  by (clarsimp simp: empty_descendants_range_in)

lemma descendants_range[simp]:
  "descendants_range_in usable_range cref s"
  "descendants_range_in retype_range cref s"
proof -
  have "descendants_range_in usable_range cref s"
    using misc idx_cases cte_wp_at cover
    apply -
    apply (erule disjE)
    apply (erule cte_wp_at_caps_descendants_range_inI[OF _ _ _ range_cover.sz(1)
        [where 'a=machine_word_len, folded word_bits_def]])
       apply (simp add:cte_wp_at_caps_of_state desc_range)+
    done
  thus "descendants_range_in usable_range cref s"
    by simp
  thus "descendants_range_in retype_range cref s"
    by (rule descendants_range_in_subseteq[OF _ subset_stuff])
qed

lemma vc[simp] : "s \<turnstile>UntypedCap dev (ptr && ~~ mask sz) sz idx"
  using misc cte_wp_at
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (erule caps_of_state_valid)
  apply simp
  done

lemma ps_no_overlap[simp]: "\<not> reset \<longrightarrow> pspace_no_overlap_range_cover ptr sz s"
  using misc cte_wp_at cover idx_cases
  apply clarsimp
  apply (erule cte_wp_at_pspace_no_overlapI[OF  _ _ _
                 range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def]])
    apply (simp add: cte_wp_at_caps_of_state)
   apply simp+
  done

lemma caps_no_overlap[simp]: "caps_no_overlap ptr sz s"
  using cte_wp_at misc cover idx_cases
  apply -
  apply (erule disjE)
   apply (erule cte_wp_at_caps_no_overlapI[OF  _ _ _ range_cover.sz(1)
       [where 'a=machine_word_len, folded word_bits_def]])
    apply (simp add:cte_wp_at_caps_of_state)+
  apply (erule descendants_range_caps_no_overlapI)
   apply (simp add:cte_wp_at_caps_of_state desc_range)+
  done

lemma idx_compare'[simp]:"unat ((ptr && mask sz) + (of_nat (length slots)<< (obj_bits_api tp us))) \<le> 2 ^ sz"
  apply (rule le_trans[OF unat_plus_gt])
  apply (simp add:range_cover.unat_of_nat_n_shift[OF cover] range_cover_unat)
  apply (insert range_cover.range_cover_compare_bound[OF cover])
  apply simp
  done

lemma ex_cte_no_overlap:
  "\<And>P slot. ex_cte_cap_wp_to P slot s \<Longrightarrow> fst slot \<notin> usable_range"
   using cte_wp_at
   apply clarsimp
   apply (drule ex_cte_cap_to_obj_ref_disj,erule disjE)
    using misc
    apply clarsimp
    apply (rule_tac ptr' = "(aa,b)" in untyped_children_in_mdbEE[OF invs_untyped_children])
         apply simp+
    apply (clarsimp simp:untyped_range.simps)
    apply (drule_tac B'="usable_range" in disjoint_subset2[rotated])
      apply (clarsimp simp:blah word_and_le2)
    apply blast
   apply (drule descendants_range_inD[OF descendants_range(1)])
    apply (simp add:cte_wp_at_caps_of_state)+
   apply (clarsimp simp:cap_range_def)
   apply blast
  apply clarsimp
  apply (drule_tac irq = irq in valid_globals_irq_node[rotated])
   using misc
   apply (clarsimp simp: invs_def valid_state_def )
  apply (clarsimp simp:untyped_range.simps)
  apply (drule_tac B = "{ptr && ~~ mask sz..(ptr && ~~ mask sz) + 2 ^ sz - 1}" in subsetD[rotated])
   apply (clarsimp simp:blah word_and_le2)
  apply simp
  done

lemma cref_inv: "fst cref \<notin> usable_range"
  apply (insert misc cte_wp_at)
   apply (drule if_unsafe_then_capD)
     apply (simp add:invs_def valid_state_def)
    apply clarsimp
  apply (drule ex_cte_no_overlap)
  apply simp
  done

lemma slots_invD: "\<And>x. x \<in> set slots \<Longrightarrow>
  x \<noteq> cref \<and> fst x \<notin> usable_range \<and>  ex_cte_cap_wp_to (\<lambda>_. True) x s"
  using misc cte_wp_at vui
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) bspec)+
  apply clarsimp
  apply (frule ex_cte_no_overlap)
  apply (auto elim: ex_cte_cap_wp_to_weakenE)
  done

lemma usable_range_disjoint:
  "usable_untyped_range (UntypedCap dev (ptr && ~~ mask sz) sz
   (unat ((ptr && mask sz) + of_nat (length slots) * 2 ^ obj_bits_api tp us))) \<inter>
   {ptr..ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1} = {}"
  proof -
  have idx_compare''[simp]:
   "unat ((ptr && mask sz) + (of_nat (length slots) * (2::machine_word) ^ obj_bits_api tp us)) < 2 ^ sz
    \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1
    < ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us"
  apply (rule word_leq_le_minus_one,simp)
  apply (rule neq_0_no_wrap)
  apply (rule machine_word_plus_mono_right_split)
  apply (simp add:shiftl_t2n range_cover_unat[OF cover] field_simps)
  apply (simp add:range_cover.sz[where 'a=machine_word_len, folded word_bits_def, OF cover])+
  done
  show ?thesis
   apply (clarsimp simp:mask_out_sub_mask blah)
   apply (drule idx_compare'')
   apply (simp add:not_le[symmetric])
   done
qed

lemma detype_locale:"ptr && ~~ mask sz = ptr
    \<Longrightarrow> detype_locale (UntypedCap dev (ptr && ~~ mask sz) sz idx) cref s"
  using cte_wp_at descendants_range misc
  by (simp add:detype_locale_def descendants_range_def2 blah invs_untyped_children)

lemma detype_descendants_range_in:
  "ptr && ~~ mask sz = ptr \<Longrightarrow> descendants_range_in usable_range cref (detype usable_range s)"
  using misc cte_wp_at
  apply -
  apply (frule detype_invariants)
         apply (simp)
        using descendants_range
        apply (clarsimp simp: blah descendants_range_def2)
        apply (simp add: invs_untyped_children blah
              invs_valid_reply_caps invs_valid_reply_masters)+
  apply (subst valid_mdb_descendants_range_in)
   apply (clarsimp dest!:invs_mdb simp:detype_clear_um_independent)
  apply (frule detype_locale)
  apply (drule detype_locale.non_filter_detype[symmetric])
  apply (simp add:blah)
  using descendants_range(1)
  apply -
  apply (subst (asm)valid_mdb_descendants_range_in)
  apply (simp add:invs_mdb)
  apply simp
  done

lemma detype_invs:
  "ptr && ~~ mask sz = ptr \<Longrightarrow> invs (detype usable_range (clear_um usable_range s))"
  apply (insert misc cte_wp_at descendants_range)
  apply clarsimp
  apply (frule detype_invariants, simp_all)
      apply (clarsimp simp:blah descendants_range_def2)
      apply ((simp add: invs_untyped_children blah
          invs_valid_reply_caps invs_valid_reply_masters)+)
  done

lemmas simps
    = caps_no_overlap descendants_range
      slots_invD cref_inv ps_no_overlap subset_stuff

lemma szw: "sz < word_bits"
  using cte_wp_at_valid_objs_valid_cap[OF cte_wp_at] misc
  by (clarsimp simp: valid_cap_def cap_aligned_def invs_valid_objs)

lemma idx_le_new_offs:
  "\<not> reset
   \<Longrightarrow> idx \<le> unat ((ptr && mask sz) + (of_nat (length slots) << obj_bits_api tp us))"
  using misc idx_cases range_cover.range_cover_base_le[OF cover]
  apply (simp only: simp_thms)
  apply (erule order_trans)
  apply (simp add: word_le_nat_alt[symmetric])
  done

end

lemmas aligned_after_mask =
  is_aligned_andI1[where x=ptr and n=a and y="mask sz" for ptr sz a]

lemma detype_clear_um_simps[simp]:
 "caps_no_overlap ptr sz (clear_um H s)
  = caps_no_overlap ptr sz s"
 "pspace_no_overlap S (clear_um H s)
  = pspace_no_overlap S s"
 "descendants_range_in S p (clear_um H s)
  = descendants_range_in S p s"
  apply (clarsimp simp: caps_no_overlap_def pspace_no_overlap_def
                        clear_um.pspace descendants_range_in_def
                  cong: if_cong)+
  apply (simp add: clear_um_def)
  done

crunch pred_tcb_at[wp]: create_cap "pred_tcb_at proj P t"
  (simp: crunch_simps)

crunch tcb[wp]: create_cap "tcb_at t"
  (simp: crunch_simps)


lemma valid_untyped_cap_inc:
  "\<lbrakk>s \<turnstile> UntypedCap dev (ptr&&~~ mask sz) sz idx;
    idx \<le> unat (ptr && mask sz); range_cover ptr sz sb n\<rbrakk>
   \<Longrightarrow> s \<turnstile> UntypedCap dev (ptr && ~~ mask sz) sz
                          (unat ((ptr && mask sz) + of_nat n * 2 ^ sb))"
 apply (clarsimp simp: valid_cap_def cap_aligned_def valid_untyped_def simp del: usable_untyped_range.simps)
 apply (intro conjI allI impI)
  apply (elim allE conjE impE)
    apply simp
   apply simp
   apply (erule disjoint_subset[rotated])
   apply (frule(1) le_mask_le_2p[OF _
                     range_cover.sz(1)[where 'a=machine_word_len, folded word_bits_def]])
   apply clarsimp
   apply (rule word_plus_mono_right)
   apply (rule word_of_nat_le)
   apply (simp add: unat_of_nat_eq[where 'a=machine_word_len] range_cover_unat field_simps)
   apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask[OF le_refl]])
   apply (simp add: word_less_nat_alt)
  apply (simp add: range_cover_unat range_cover.unat_of_nat_shift shiftl_t2n field_simps)
  apply (subst add.commute)
  apply (simp add: range_cover.range_cover_compare_bound)
  done

(* FIXME: move maybe *)
lemma tcb_cap_valid_untyped_cong:
  "tcb_cap_valid (UntypedCap dev1 a1 b1 c) =
   tcb_cap_valid (UntypedCap dev2 a2 b2 c2)"
  apply (rule ext)+
  apply (clarsimp simp:tcb_cap_valid_def valid_ipc_buffer_cap_def split:option.splits)
  apply (simp add: tcb_cap_cases_def
                   is_arch_cap_def is_nondevice_page_cap_simps is_cap_simps
            split: thread_state.split)
  done

lemma tcb_cap_valid_untyped_to_thread:
  "tcb_cap_valid (UntypedCap dev a1 b1 c) =
   tcb_cap_valid (cap.ThreadCap 0)"
  apply (rule ext)+
  apply (clarsimp simp:tcb_cap_valid_def valid_ipc_buffer_cap_def split:option.splits)
  apply (simp add: tcb_cap_cases_def is_cap_simps
                   is_arch_cap_def is_nondevice_page_cap_simps
            split: thread_state.split)
  done

(* FIXME: move *)
lemma ex_nonz_cap_to_overlap:
  "\<lbrakk>ex_nonz_cap_to t s; cte_wp_at ((=) cap) p s; is_untyped_cap cap; invs s;
    descendants_range cap p s \<rbrakk>
   \<Longrightarrow> \<not> t \<in> untyped_range cap"
   apply (rule ccontr)
   apply (clarsimp simp: ex_nonz_cap_to_def descendants_range_def2
     cte_wp_at_caps_of_state caps_no_overlap_def zobj_refs_to_obj_refs)
   apply (frule invs_mdb)
   apply (clarsimp simp: valid_mdb_def)
   apply (frule_tac cap' = capa in untyped_mdbD)
      apply simp+
     apply blast
    apply simp
   apply (drule(2) descendants_range_inD)
   apply (simp add: cap_range_def)
   apply blast
   done


lemma detype_valid_untyped:
  "\<lbrakk>invs s; detype S s \<turnstile> UntypedCap dev ptr sz idx1;
    {ptr .. ptr + 2 ^ sz - 1} \<subseteq> S; idx2 \<le> 2 ^ sz\<rbrakk>
   \<Longrightarrow> detype S s \<turnstile> UntypedCap dev ptr sz idx2"
  apply (clarsimp simp: detype_def valid_cap_def valid_untyped_def cap_aligned_def)
  apply (drule_tac x = p in spec)
  apply clarsimp
  apply (drule p_in_obj_range)
   apply (simp add: invs_psp_aligned invs_valid_objs)+
  apply (drule(1) subset_trans[rotated])
  apply blast
  done

lemma do_machine_op_pspace_no_overlap[wp]:
  "\<lbrace>pspace_no_overlap S\<rbrace> do_machine_op f \<lbrace>\<lambda>r. pspace_no_overlap S\<rbrace>"
  apply (clarsimp simp: pspace_no_overlap_def do_machine_op_def)
  apply (wp hoare_vcg_all_lift)
     apply (simp add: split_def)
     apply wp+
  apply clarsimp
  done

lemma mapME_append:
  "mapME f (xs @ ys) = doE
    xs_r \<leftarrow> mapME f xs;
    ys_r \<leftarrow> mapME f ys;
    returnOk (xs_r @ ys_r)
  odE"
  by (induct xs, simp_all add: mapME_Nil mapME_Cons bindE_assoc)
lemma mapME_validE_nth_induct:
  "\<lbrakk> \<And>i ys. i < length xs \<Longrightarrow> \<lbrace>P i ys\<rbrace> f (zs ! i) \<lbrace>\<lambda>y. P (Suc i) (y # ys)\<rbrace>, \<lbrace>E\<rbrace>;
        \<And>i. i < length xs \<Longrightarrow> zs ! i = xs ! i \<rbrakk>
    \<Longrightarrow> \<lbrace>P 0 []\<rbrace> mapME f xs \<lbrace>\<lambda>ys. P (length xs) (rev ys)\<rbrace>, \<lbrace>E\<rbrace>"
proof (induct xs rule: rev_induct)
  case Nil
  show ?case
    by (wp | simp add: mapME_Nil)+
next
  case (snoc x xs)
  from snoc.prems have x: "x = zs ! length xs"
    by simp
  from snoc.prems have zs: "\<And>i. i < length xs \<Longrightarrow> xs ! i = zs ! i"
    by (metis length_append_singleton less_SucI nth_append)
  show ?case
    apply (simp add: mapME_append mapME_Cons mapME_Nil bindE_assoc x)
    apply (wp snoc.hyps snoc.prems | simp add: zs)+
    done
qed

lemma mapME_x_mapME:
  "mapME_x m l = (mapME m l >>=E (%_. returnOk ()))"
  apply (simp add: mapME_x_def sequenceE_x_def mapME_def sequenceE_def)
  apply (induct l, simp_all add: Let_def bindE_assoc)
  done

lemmas mapME_validE_nth = mapME_validE_nth_induct[OF _ refl]
lemma mapME_x_validE_nth:
  "\<lbrakk> \<And>i. i < length xs \<Longrightarrow> \<lbrace>P i\<rbrace> f (xs ! i) \<lbrace>\<lambda>y. P (Suc i)\<rbrace>, \<lbrace>E\<rbrace> \<rbrakk>
    \<Longrightarrow> \<lbrace>P 0\<rbrace> mapME_x f xs \<lbrace>\<lambda>_. P (length xs)\<rbrace>, \<lbrace>E\<rbrace>"
  by (wp mapME_validE_nth | simp add: mapME_x_mapME)+

lemma alignUp_ge_nat:
  "0 < m
    \<Longrightarrow> (n :: nat) \<le> ((n + m - 1) div m) * m"
  apply (cases n)
   apply (simp_all add: Suc_le_eq)
  apply (metis add.commute add_less_cancel_left dividend_less_div_times)
  done

lemma alignUp_le_nat:
  "0 < m \<Longrightarrow> n \<le> (b :: nat) \<Longrightarrow> m dvd b
    \<Longrightarrow> ((n + m - 1) div m) * m \<le> b"
  apply (clarsimp simp: dvd_def)
  apply (rule less_Suc_eq_le[THEN iffD1])
  apply (simp add: td_gal_lt[symmetric])
  apply (subst less_eq_Suc_le, simp add: mult.commute)
  done

lemma filter_upt_eq:
  assumes mono: "\<forall>a b. a \<le> b \<longrightarrow> f b \<longrightarrow> f a"
  and preds: "\<not> f k" "k \<noteq> 0 \<longrightarrow> f (k - 1)" "k \<le> j"
  shows "filter f (upt i j) = upt i k"
proof -
  have mono': "\<And>a b. a \<le> b \<longrightarrow> f b \<longrightarrow> f a"
    by (metis mono)

  have f: "f = (\<lambda>x. x < k)"
    apply (rule ext)
    apply (cut_tac a=k and b=x in mono')
    apply (cut_tac a=x and b="k - 1" in mono')
    apply (cut_tac preds(1))
    apply (cases "k = 0")
     apply (simp add: preds)
    apply (simp add: preds[simplified])
    apply (cases k, auto)
    done

  show ?thesis
    apply (rule sorted_distinct_set_unique,
      simp_all add: sorted_filter[where f=id, simplified])
    apply (cut_tac preds)
    apply (auto simp add: f)
    done
qed

lemma nat_diff_less2:
  fixes x :: nat
  shows "\<lbrakk> x < y + z; 0 < y\<rbrakk> \<Longrightarrow> x - z < y"
  apply (cases "z \<le> x")
   apply (metis nat_diff_less)
  apply simp
  done

lemma upt_mult_lt_prop:
  assumes n: "n \<le> 2 ^ a"
  assumes b: "b \<le> a"
  shows "\<exists>bd. [i\<leftarrow>[0..<2 ^ (a - b)]. i * 2 ^ b < n]
        = [0 ..< bd] \<and> n \<le> bd * 2 ^ b \<and> bd * 2 ^ b \<le> 2 ^ a
          \<and> (bd - 1) * 2 ^ b \<le> n"
proof -
  let ?al = "(n + (2 ^ b - 1)) div 2 ^ b"

  have sub1: "0 < n \<Longrightarrow> (?al - 1) * 2 ^ b < n"
    apply (cases "?al = 0")
     apply simp
    apply (simp add: diff_mult_distrib)
    apply (rule nat_diff_less2, simp_all)
    apply (rule order_le_less_trans, rule div_mult_le)
    apply simp
    done

  have le1: "(n + 2 ^ b - Suc 0) div 2 ^ b * 2 ^ b \<le> 2 ^ a"
    apply (rule alignUp_le_nat[simplified], simp_all add: n)
    apply (simp add: b le_imp_power_dvd)
    done

  note le2 = div_le_mono[OF le1, where k="2 ^ b", simplified]

  show ?thesis
    apply (cases "n = 0")
     apply (simp add: exI[where x=0])
    apply (rule exI[where x="?al"])
    apply (strengthen filter_upt_eq)
    apply (simp add: linorder_not_less conj.commute)
    apply (simp add: alignUp_ge_nat[simplified] sub1[simplified]
                     sub1[THEN order_less_imp_le, simplified]
                     power_minus_is_div[OF b] le1 le2)
    apply (auto elim: order_le_less_trans[rotated])
    done
qed

lemma delete_objects_ex_cte_cap_wp_to:
  notes untyped_range.simps[simp del]
  shows
  "\<lbrace>ex_cte_cap_wp_to P slot and invs and
      cte_wp_at (\<lambda>cp. is_untyped_cap cp \<and> {ptr_base .. ptr_base + 2 ^ sz - 1} \<subseteq> untyped_range cp)
          src_slot and (\<lambda>s. descendants_of src_slot (cdt s) = {})\<rbrace>
    delete_objects ptr_base sz
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to P slot s\<rbrace>"
  apply (simp add: delete_objects_def ex_cte_cap_wp_to_def)
  apply (rule hoare_pre)
   apply (rule hoare_lift_Pf2 [where f="interrupt_irq_node"])
    apply (wp hoare_vcg_ex_lift | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (intro exI conjI, assumption+)
  apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
  apply (case_tac "the (caps_of_state s src_slot)", simp_all)
  apply (frule ex_cte_cap_protects, simp add: cte_wp_at_caps_of_state,
    rule empty_descendants_range_in, (assumption | clarsimp)+)
  done

lemma do_machine_op_ex_cte_cap_wp_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P slot\<rbrace>
    do_machine_op oper
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to P slot s\<rbrace>"
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: ex_cte_cap_wp_to_def)
  done

lemma  delete_objects_real_cte_at[wp]:
  "\<lbrace>\<lambda>s. real_cte_at p s \<and> fst p \<notin> {ptr_base .. ptr_base + 2 ^ sz - 1}\<rbrace>
    delete_objects ptr_base sz
  \<lbrace>\<lambda>rv. real_cte_at p\<rbrace>"
  by (wp | simp add: delete_objects_def)+

lemma  delete_objects_ct_in_state[wp]:
  "\<lbrace>\<lambda>s. ct_in_state P s \<and> cur_thread s \<notin> {ptr_base .. ptr_base + 2 ^ sz - 1}\<rbrace>
    delete_objects ptr_base sz
  \<lbrace>\<lambda>rv. ct_in_state P\<rbrace>"
  apply (rule hoare_pre)
   apply (wp | simp add: delete_objects_def ct_in_state_def
                         st_tcb_at_def
             | simp add: detype_def)+
   apply (rule hoare_lift_Pf2[where f=cur_thread])
    apply wp+
  apply (clarsimp simp: ct_in_state_def st_tcb_at_def)
  done

(* FIXME: move? *)
lemma pspace_no_overlap_subset:
  "pspace_no_overlap S s \<Longrightarrow> T \<subseteq> S
    \<Longrightarrow> pspace_no_overlap T s"
  by (clarsimp simp: pspace_no_overlap_def disjoint_subset2)

crunch cur_thread[wp]: delete_objects "\<lambda>s. P (cur_thread s)"
  (simp: detype_def)

lemma ct_in_state_trans_state[simp]:
  "ct_in_state P (trans_state a s) = ct_in_state P s"
  by (simp add: ct_in_state_def)

lemmas unat_of_nat_word_bits
  = unat_of_nat_eq[where 'a = machine_word_len, unfolded word_bits_len_of, simplified]

lemma caps_of_state_pspace_no_overlapD:
  "\<lbrakk> caps_of_state s cref = Some (UntypedCap dev ptr sz idx); invs s;
    idx < 2 ^ sz \<rbrakk>
   \<Longrightarrow> pspace_no_overlap_range_cover (ptr + of_nat idx) sz s"
  apply (frule(1) caps_of_state_valid)
  apply (clarsimp simp: valid_cap_simps cap_aligned_def)
  apply (cut_tac neg_mask_add_aligned[where p=ptr and q="of_nat idx" and n=sz])
    apply (rule cte_wp_at_pspace_no_overlapI[where idx=idx and cref=cref], simp_all)
    apply (simp add: cte_wp_at_caps_of_state)
   apply (simp add: mask_out_sub_mask)
   apply (subst unat_of_nat_word_bits, erule order_less_le_trans, simp_all)
  apply (rule word_of_nat_less)
  apply (erule order_less_le_trans)
  apply simp
  done


lemma set_untyped_cap_invs_simple:
  "\<lbrace>\<lambda>s. descendants_range_in {ptr .. ptr+2^sz - 1} cref s
  \<and> pspace_no_overlap_range_cover ptr sz s \<and> invs s
  \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz
      \<and> cap_is_device c = dev\<and> obj_ref_of c = ptr) cref s \<and> idx \<le> 2^ sz\<rbrace>
  set_cap (UntypedCap dev ptr sz idx) cref
 \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_def valid_state_def)
  apply (rule hoare_pre)
   apply (wp set_free_index_valid_pspace_simple set_cap_valid_mdb_simple
     set_cap_idle update_cap_ifunsafe set_cap_valid_arch_caps_simple)
   apply (simp add:valid_irq_node_def)
   apply wps
   apply (wp hoare_vcg_all_lift set_cap_irq_handlers
     set_cap_irq_handlers cap_table_at_lift_valid set_cap_ioports'
     set_cap_typ_at set_cap_valid_arch_caps_simple set_cap_kernel_window_simple
     set_cap_cap_refs_respects_device_region)
  apply (clarsimp simp del: split_paired_Ex)
  apply (strengthen exI[where x=cref])
  apply (clarsimp simp:cte_wp_at_caps_of_state is_cap_simps valid_pspace_def)
  apply (intro conjI; clarsimp?)
        apply (clarsimp simp: fun_eq_iff)
       apply (clarsimp split:cap.splits simp:is_cap_simps appropriate_cte_cap_def)
      apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
       apply clarsimp
      apply (clarsimp simp: is_cap_simps ex_cte_cap_wp_to_def appropriate_cte_cap_def
                            cte_wp_at_caps_of_state)
     apply (clarsimp dest!:valid_global_refsD2 simp:cap_range_def)
    apply (simp add:valid_irq_node_def)
   apply (clarsimp simp:valid_irq_node_def)
  apply (clarsimp intro!: safe_ioport_insert_triv simp: is_cap_simps)
  done

lemma reset_untyped_cap_invs_etc:
  "\<lbrace>invs and valid_untyped_inv_wcap ui
      (Some (UntypedCap dev ptr sz idx))
         and ct_active
         and K (\<exists>ptr_base ptr' ty us slots. ui = Retype slot True ptr_base ptr' ty us slots dev)\<rbrace>
    reset_untyped_cap slot
  \<lbrace>\<lambda>_. invs and valid_untyped_inv_wcap ui (Some (UntypedCap dev ptr sz 0))
      and ct_active
      and pspace_no_overlap {ptr .. ptr + 2 ^ sz - 1}\<rbrace>, \<lbrace>\<lambda>_. invs\<rbrace>"
  (is "\<lbrace>invs and valid_untyped_inv_wcap ?ui (Some ?cap) and ct_active and _\<rbrace>
    ?f \<lbrace>\<lambda>_. invs and ?vu2 and ct_active and ?psp\<rbrace>, \<lbrace>\<lambda>_. invs\<rbrace>")
  apply (simp add: reset_untyped_cap_def)
  apply (rule bindE_wp_fwd)
   apply ((wp (once) get_cap_sp)+)[1]
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp: cte_wp_at_caps_of_state bits_of_def split del: if_split)
  apply (subgoal_tac "is_aligned ptr sz")
   prefer 2
   apply (frule caps_of_state_valid_cap, clarsimp)
   apply auto[1]
  apply (cases "idx = 0")
   apply (clarsimp simp: free_index_of_def)
   apply wp
   apply clarsimp
   apply (frule(1) caps_of_state_pspace_no_overlapD, simp+)
   apply (simp add: word_bw_assocs field_simps)
  apply (clarsimp simp: free_index_of_def split del: if_split)
  apply (rule_tac B="\<lambda>_. invs and valid_untyped_inv_wcap ?ui (Some ?cap)
        and ct_active and ?psp" in bindE_wp_fwd)
   apply clarsimp
   apply (rule hoare_pre)
    apply (wp hoare_vcg_ex_lift hoare_vcg_const_Ball_lift
              delete_objects_ex_cte_cap_wp_to[where src_slot=slot]
              )
   apply (clarsimp simp: cte_wp_at_caps_of_state ct_in_state_def)
   apply (frule if_unsafe_then_capD[OF caps_of_state_cteD], clarsimp+)
   apply (drule(1) ex_cte_cap_protects[OF _ caps_of_state_cteD _ _ order_refl])
      apply (simp add: empty_descendants_range_in)
     apply clarsimp+
   apply (strengthen ballEI[mk_strg I E] refl)
   apply (strengthen exI[where x="fst slot"], strengthen exI[where x="snd slot"])
   apply (strengthen ex_cte_cap_protects[OF _ caps_of_state_cteD _ _ order_refl, mk_strg D E])
   apply (simp add: empty_descendants_range_in invs_untyped_children
                    invs_valid_global_refs descendants_range_def bits_of_def)
   apply (strengthen refl)
   apply (drule st_tcb_ex_cap, clarsimp, fastforce)
   apply (drule ex_nonz_cap_to_overlap[where p=slot],
     (simp add: cte_wp_at_caps_of_state descendants_range_def)+)
   apply (drule caps_of_state_valid_cap | clarify)+
   apply (intro conjI; clarify?; blast)[1]
  apply (cases "dev \<or> sz < resetChunkBits")
   apply (simp add: bits_of_def)
   apply (simp add: unless_def)
   apply (rule hoare_pre)
    apply (wp set_untyped_cap_invs_simple set_cap_cte_wp_at set_cap_no_overlap
              hoare_vcg_const_Ball_lift set_cap_cte_cap_wp_to
              ct_in_state_thread_state_lift)
    apply (strengthen empty_descendants_range_in)
    apply (rule hoare_lift_Pf2 [where f="interrupt_irq_node"])
     apply (wp hoare_vcg_const_Ball_lift hoare_vcg_const_imp_lift
               hoare_vcg_ex_lift ct_in_state_thread_state_lift)+
   apply (clarsimp simp add: bits_of_def field_simps cte_wp_at_caps_of_state
                             empty_descendants_range_in)
  apply (cut_tac a=sz and b=resetChunkBits and n=idx in upt_mult_lt_prop)
    apply (frule caps_of_state_valid_cap, clarsimp+)
    apply (simp add: valid_cap_def)
   apply simp
  apply (clarsimp simp: bits_of_def free_index_of_def)
  apply (rule hoare_pre, rule hoare_strengthen_postE,
    rule_tac P="\<lambda>i. invs and ?psp and ct_active and valid_untyped_inv_wcap ?ui
        (Some (UntypedCap dev ptr sz (if i = 0 then idx else (bd - i) * 2 ^ resetChunkBits)))"
      and E="\<lambda>_. invs"
      in mapME_x_validE_nth)
     apply (rule hoare_pre)
      apply (wp set_untyped_cap_invs_simple
                set_cap_no_overlap set_cap_cte_wp_at
                preemption_point_inv
                hoare_vcg_ex_lift hoare_vcg_const_imp_lift
                hoare_vcg_const_Ball_lift set_cap_cte_cap_wp_to
                | strengthen empty_descendants_range_in
                | simp
                | rule irq_state_independent_A_conjI
                | simp add: cte_wp_at_caps_of_state
                | wp (once) ct_in_state_thread_state_lift
                | (rule irq_state_independent_A_def[THEN meta_eq_to_obj_eq, THEN iffD2],
                  simp add: ex_cte_cap_wp_to_def ct_in_state_def))+
     apply (clarsimp simp: bits_of_def field_simps cte_wp_at_caps_of_state nth_rev)
     apply (strengthen order_trans[where z="2 ^ sz", rotated, mk_strg I E])
     apply (clarsimp split: if_split_asm)
      apply auto[1]
     apply (auto elim: order_trans[rotated])[1]
    apply (clarsimp simp: cte_wp_at_caps_of_state split: if_split_asm)
   apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma get_cap_prop_known:
  "\<lbrace>cte_wp_at (\<lambda>cp. f cp = v) slot and Q v\<rbrace> get_cap slot \<lbrace>\<lambda>rv. Q (f rv)\<rbrace>"
  apply (wp get_cap_wp)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  done

lemma reset_untyped_cap_pred_tcb_at:
  "\<lbrace>invs and pred_tcb_at proj P t and cte_wp_at (\<lambda>cp. t \<notin> cap_range cp \<and> is_untyped_cap cp) slot\<rbrace>
   reset_untyped_cap slot
   \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>, \<lbrace>\<lambda>_. pred_tcb_at proj P t\<rbrace>"
  apply (simp add: reset_untyped_cap_def)
  apply (rule hoare_pre)
   apply (wp mapME_x_inv_wp preemption_point_inv | simp add: unless_def)+
    apply (simp add: delete_objects_def)
    apply (wp get_cap_wp hoare_vcg_const_imp_lift | simp)+
  apply (auto simp: cte_wp_at_caps_of_state cap_range_def
                        bits_of_def is_cap_simps)
  done

lemma create_cap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap
     and cte_wp_at ((=) cap.NullCap) cref\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp new_cap_iflive set_cdt_cte_wp_at | simp)+
  done

crunch cap_to_again[wp]: set_cdt "ex_cte_cap_wp_to P p"
  (simp: ex_cte_cap_wp_to_def)

lemma create_cap_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap
     and ex_cte_cap_wp_to (appropriate_cte_cap (default_cap tp oref sz dev)) cref
     and cte_wp_at ((=) cap.NullCap) cref\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv. if_unsafe_then_cap\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp new_cap_ifunsafe set_cdt_cte_wp_at | simp)+
  done

lemma set_cdt_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     set_cdt m
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: set_cdt_def)
  apply wp
  apply (clarsimp elim!: state_refs_of_pspaceI)
  done

lemma set_cdt_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
     set_cdt m
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: set_cdt_def)
  apply wp
  apply (clarsimp elim!: state_hyp_refs_of_pspaceI)
  done

lemma state_refs_of_rvk[simp]:
  "state_refs_of (is_original_cap_update f s) = state_refs_of s"
  by (simp add: state_refs_of_def)


lemma create_cap_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  unfolding create_cap_def by wpsimp

lemma create_cap_state_hyp_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_hyp_refs_of s)\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv s. P (state_hyp_refs_of s)\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp | simp)+
  done

lemma create_cap_zombies[wp]:
  "\<lbrace>zombies_final and cte_wp_at ((=) cap.NullCap) cref
     and (\<lambda>s. \<forall>r\<in>obj_refs (default_cap tp oref sz dev). \<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  unfolding create_cap_def set_cdt_def by (wpsimp wp: new_cap_zombies)

lemma create_cap_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> create_cap tp sz p dev tup \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  unfolding create_cap_def split_def set_cdt_def by wpsimp

lemma create_cap_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace>
     create_cap tp sz p dev tup
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  unfolding create_cap_def split_def set_cdt_def by (wpsimp wp: set_cap_idle)


crunch it[wp]: create_cap "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps)


lemma default_cap_reply:
  "default_cap tp ptr sz dev \<noteq> cap.ReplyCap ptr' bool R"
  by (cases tp; simp)

lemma create_cap_valid_reply_caps[wp]:
  "\<lbrace>valid_reply_caps\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  apply (simp add: valid_reply_caps_def has_reply_cap_def
                   cte_wp_at_caps_of_state create_cap_def is_reply_cap_to_def
                   set_cdt_def)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  apply (clarsimp simp: default_cap_reply)
  apply (erule conjI [OF allEI], fastforce)
  apply (simp add: unique_reply_caps_def default_cap_reply)
  done


lemma create_cap_valid_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  apply (simp add: valid_reply_masters_def cte_wp_at_caps_of_state
                   create_cap_def is_master_reply_cap_to_def)
  apply (wp | simp add: default_cap_reply)+
  done


lemma create_cap_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs
      and cte_wp_at (\<lambda>c. cap_range (default_cap tp oref sz dev) \<subseteq> cap_range c) p\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  apply (simp add: valid_global_refs_def valid_refs_def
                   cte_wp_at_caps_of_state create_cap_def pred_conj_def)
  apply (simp only: imp_conv_disj)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply (subgoal_tac "global_refs s \<inter> cap_range (default_cap tp oref sz dev) = {}")
   apply auto[1]
  apply (erule disjoint_subset2)
  apply (cases p, simp)
  done


crunch arch_state[wp]: create_cap "\<lambda>s. P (arch_state s)"
  (simp: crunch_simps)

lemma create_cap_aobj_at:
  "arch_obj_pred P' \<Longrightarrow>
  \<lbrace>\<lambda>s. P (obj_at P' pd s)\<rbrace> create_cap type bits ut is_dev cref \<lbrace>\<lambda>r s. P (obj_at P' pd s)\<rbrace>"
  unfolding create_cap_def split_def set_cdt_def
  by (wpsimp wp: set_cap.aobj_at)

lemma create_cap_valid_arch_state[wp]:
  "\<lbrace>valid_arch_state\<rbrace> create_cap type bits ut is_dev cref \<lbrace>\<lambda>_. valid_arch_state\<rbrace>"
  by (wp valid_arch_state_lift_aobj_at create_cap_aobj_at)

crunch irq_node[wp]: create_cap "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)

lemmas create_cap_valid_irq_node[wp]
    = valid_irq_node_typ [OF create_cap_typ_at create_cap_irq_node]


lemma default_cap_irqs[simp]:
  "cap_irqs (default_cap tp oref sz dev) = {}"
  by (cases tp, simp_all)


lemma create_cap_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def)
  apply (simp add: create_cap_def Ball_def)
  apply (simp only: imp_conv_disj)
  apply (wpsimp wp: hoare_vcg_all_lift hoare_vcg_disj_lift)
  apply (auto simp: ran_def split: if_split_asm)
  done


crunch valid_vspace_objs[wp]: create_cap "valid_vspace_objs"
  (simp: crunch_simps)

locale Untyped_AI_nonempty_table =
  fixes state_ext_t :: "('state_ext::state_ext) itself"
  fixes nonempty_table :: "machine_word set \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
  assumes create_cap_valid_arch_caps[wp]:
  "\<And>tp oref sz dev cref p.\<lbrace>valid_arch_caps
      and valid_cap (default_cap tp oref sz dev)
      and (\<lambda>(s::'state_ext state). \<forall>r\<in>obj_refs (default_cap tp oref sz dev).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
      and cte_wp_at ((=) cap.NullCap) cref
      and K (tp \<noteq> ArchObject ASIDPoolObj)\<rbrace>
     create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  assumes create_cap_cap_refs_in_kernel_window[wp]:
  "\<And>tp oref sz p dev cref.\<lbrace>cap_refs_in_kernel_window and cte_wp_at (\<lambda>c. cap_range (default_cap tp oref sz dev) \<subseteq> cap_range c) p\<rbrace>
     create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. (cap_refs_in_kernel_window::'state_ext state \<Rightarrow> bool)\<rbrace>"
  assumes nonempty_default[simp]:
  "\<And>tp S us dev. tp \<noteq> Untyped \<Longrightarrow> \<not> nonempty_table S (default_object tp dev us)"
  assumes nonempty_table_caps_of:
  "\<And>S ko. nonempty_table S ko \<Longrightarrow> caps_of ko = {}"
  assumes init_arch_objects_nonempty_table:
  "\<lbrace>(\<lambda>s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
         \<and> valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s) and
    K (\<forall>ref\<in>set refs. is_aligned ref (obj_bits_api tp us))\<rbrace>
        init_arch_objects tp ptr bits us refs
   \<lbrace>\<lambda>rv. \<lambda>s :: 'state_ext state. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)\<rbrace>"
  assumes create_cap_ioports[wp]:
  "\<And>tp oref sz dev cref p. \<lbrace>valid_ioports and cte_wp_at (\<lambda>_. True) cref\<rbrace>
        create_cap tp sz p dev (cref,oref) \<lbrace>\<lambda>rv (s::'state_ext state). valid_ioports s\<rbrace>"


crunch v_ker_map[wp]: create_cap "valid_kernel_mappings"
  (simp: crunch_simps)


crunch eq_ker_map[wp]: create_cap "equal_kernel_mappings"
  (simp: crunch_simps)

lemma create_cap_asid_map[wp]:
  "\<lbrace>valid_asid_map\<rbrace> create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  unfolding create_cap_def set_cdt_def by wpsimp

crunch only_idle[wp]: create_cap only_idle
  (simp: crunch_simps)

crunch pspace_in_kernel_window[wp]: create_cap "pspace_in_kernel_window"
  (simp: crunch_simps)

lemma set_original_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> create_cap tp sz p dev slot \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (cases slot)
  apply (wpsimp wp: set_cdt_cos_ioc set_cap_caps_of_state
              simp: create_cap_def set_original_set_cap_comm cte_wp_at_caps_of_state)
  apply (cases tp; simp)
  done

interpretation create_cap: non_vspace_non_mem_op "create_cap tp sz p slot dev"
  apply (cases slot)
  apply (simp add: create_cap_def set_cdt_def)
  apply unfold_locales
  apply (rule hoare_pre, (wp set_cap.vsobj_at | wpc |simp add: create_cap_def set_cdt_def bind_assoc)+)+
  done

(*  by (wp set_cap.vsobj_at | simp)+ *) (* ARMHYP might need this *)

crunch valid_irq_states[wp]: create_cap "valid_irq_states"
crunch pspace_respects_device_region[wp]: create_cap pspace_respects_device_region

lemma cap_range_subseteq_weaken:
 "\<lbrakk>obj_refs c \<subseteq> untyped_range cap; untyped_range c \<subseteq> untyped_range cap\<rbrakk>
 \<Longrightarrow> cap_range c \<subseteq> cap_range cap"
 by (fastforce simp add: cap_range_def)

lemma create_cap_refs_respects_device:
  "\<lbrace>cap_refs_respects_device_region and cte_wp_at (\<lambda>c. cap_is_device (default_cap tp oref sz dev)  = cap_is_device c \<and>is_untyped_cap c \<and> cap_range (default_cap tp oref sz dev) \<subseteq> cap_range c) p\<rbrace>
  create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv s. cap_refs_respects_device_region s\<rbrace>"
  apply (simp add: create_cap_def)
  apply (rule hoare_pre)
   apply (wp set_cap_cap_refs_respects_device_region hoare_vcg_ex_lift
     set_cdt_cte_wp_at | simp del: split_paired_Ex)+
  apply (rule_tac x = p in exI)
  apply clarsimp
  apply (erule cte_wp_at_weakenE)
  apply (fastforce simp: is_cap_simps)
  done

lemma (in Untyped_AI_nonempty_table) create_cap_invs[wp]:
  "\<lbrace>invs
      and cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_is_device (default_cap tp oref sz dev)  = cap_is_device c
                         \<and> obj_refs (default_cap tp oref sz dev) \<subseteq> untyped_range c \<and>
                         untyped_range (default_cap tp oref sz dev) \<subseteq> untyped_range c
                         \<and> untyped_range (default_cap tp oref sz dev) \<inter> usable_untyped_range c = {}) p
      and descendants_range (default_cap tp oref sz dev) p
      and cte_wp_at ((=) cap.NullCap) cref
      and valid_cap (default_cap tp oref sz dev)
      and ex_cte_cap_wp_to (appropriate_cte_cap (default_cap tp oref sz dev)) cref
      and real_cte_at cref
      and (\<lambda>(s::'state_ext state). \<forall>r\<in>obj_refs (default_cap tp oref sz dev).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
      and K (p \<noteq> cref \<and> tp \<noteq> ArchObject ASIDPoolObj)\<rbrace>
     create_cap tp sz p dev (cref, oref) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (wp create_cap_refs_respects_device | simp add: valid_cap_def)+
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_pspace_def)
  apply (frule_tac p1 = p in valid_cap_aligned[OF caps_of_state_valid])
    apply simp
  apply (simp add: invs_def valid_state_def valid_pspace_def )
  apply (simp add: cap_range_def)
  done

lemma create_cap_ex_cap_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p' and cte_wp_at ((=) cap.NullCap) cref\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p'\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp set_cap_cte_cap_wp_to set_cdt_cte_wp_at
            | simp | wps set_cdt_irq_node)+
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done

lemma create_cap_no_cap[wp]:
  "\<lbrace>\<lambda>s. (\<forall>p'. \<not> cte_wp_at P p' s) \<and> \<not> P (default_cap tp oref sz dev)\<rbrace>
     create_cap tp sz p dev (cref, oref)
   \<lbrace>\<lambda>rv s. \<forall>oref' cref'. \<not> cte_wp_at P (oref', cref') s\<rbrace>"
  unfolding create_cap_def cte_wp_at_caps_of_state by wpsimp

lemma (in Untyped_AI_nonempty_table) create_cap_nonempty_tables[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) p s)\<rbrace>
     create_cap tp sz p' dev (cref, oref)
   \<lbrace>\<lambda>rv s. P (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) p s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=arch_state, OF create_cap_arch_state])
   apply (simp add: create_cap_def set_cdt_def)
   apply (wp set_cap_obj_at_impossible|simp)+
  apply (clarsimp simp: nonempty_table_caps_of)
  done

lemma cap_range_not_untyped:
  "\<not> is_untyped_cap c \<Longrightarrow> cap_range c = obj_refs c"
  apply (case_tac c)
  apply (simp_all add: is_cap_simps cap_range_def)
  done

lemma cap_range_inter_emptyI:
  "\<lbrakk>is_untyped_cap a = is_untyped_cap b; untyped_range a \<inter> untyped_range b ={};
    obj_refs a \<inter> obj_refs b = {}\<rbrakk>
   \<Longrightarrow> cap_range a \<inter> cap_range b = {}"
  apply (case_tac "is_untyped_cap a")
   apply (simp_all add: cap_range_not_untyped)
  done

lemma (in Untyped_AI_nonempty_table) create_caps_invs_inv:
  assumes create_cap_Q[wp]:
    "\<lbrace>invs and Q and cte_wp_at (\<lambda>c. is_untyped_cap c
            \<and> cap_range (default_cap tp oref sz dev) \<subseteq> untyped_range c
            \<and> {oref .. oref + 2 ^ (obj_bits_api tp us) - 1} \<subseteq> untyped_range c) p
        and cte_wp_at ((=) NullCap) cref
        and valid_cap (default_cap tp oref sz dev)\<rbrace>
         create_cap tp sz p dev (cref,oref) \<lbrace>\<lambda>_. Q \<rbrace>"
  shows
  "\<lbrace>(\<lambda>s. invs (s::('state_ext::state_ext) state) \<and> Q s
       \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> obj_is_device tp dev = cap_is_device c)  p s
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
           cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz dev) \<subseteq> untyped_range c
           \<and> {snd tup .. snd tup + 2 ^ (obj_bits_api tp us) - 1} \<subseteq> untyped_range c
           \<and> (untyped_range (default_cap tp (snd tup) sz dev) \<inter> usable_untyped_range c = {})) p s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
           descendants_range (default_cap tp (snd tup) sz dev) p s)
       \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz dev)) ((cref,oref)#list))
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
           cte_wp_at ((=) cap.NullCap) (fst tup) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
              valid_cap (default_cap tp (snd tup) sz dev) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
              ex_cte_cap_wp_to is_cnode_cap (fst tup) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
              real_cte_at (fst tup) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list). \<forall>r \<in> obj_refs (default_cap tp (snd tup) sz dev).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> Structures_A.obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
       \<and> distinct (p # (map fst ((cref,oref)#list)))
       \<and> tp \<noteq> ArchObject ASIDPoolObj) \<rbrace>
     create_cap tp sz p dev (cref,oref)
   \<lbrace>(\<lambda>r s.
         invs s \<and> Q s
       \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> obj_is_device tp dev = cap_is_device c)  p s
       \<and> (\<forall>tup \<in> set list.
           cte_wp_at (\<lambda>c.
           cap_range (default_cap tp (snd tup) sz dev) \<subseteq> untyped_range c
           \<and> {snd tup .. snd tup + 2 ^ (obj_bits_api tp us) - 1} \<subseteq> untyped_range c
           \<and> (untyped_range (default_cap tp (snd tup) sz dev) \<inter> usable_untyped_range c = {})) p s)
       \<and> (\<forall>tup \<in> set list.
           descendants_range (default_cap tp (snd tup) sz dev) p s)
       \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz dev)) list)
       \<and> (\<forall>tup \<in> set list.
           cte_wp_at ((=) cap.NullCap) (fst tup) s)
       \<and> (\<forall>tup \<in> set list.
              valid_cap (default_cap tp (snd tup) sz dev) s)
       \<and> (\<forall>tup \<in> set list.
              ex_cte_cap_wp_to is_cnode_cap (fst tup) s)
       \<and> (\<forall>tup \<in> set list.
              real_cte_at (fst tup) s)
       \<and> (\<forall>tup \<in> set list. \<forall>r \<in> obj_refs (default_cap tp (snd tup) sz dev).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> Structures_A.obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
       \<and> distinct (p # (map fst list))
       \<and> tp \<noteq> ArchObject ASIDPoolObj) \<rbrace>"
  apply (rule hoare_pre)
  apply (wp hoare_vcg_const_Ball_lift | clarsimp)+
  apply (clarsimp simp: conj_comms invs_mdb distinct_sets_prop distinct_prop_map
                        ex_cte_cap_to_cnode_always_appropriate_strg)
  apply (simp add: cte_wp_at_caps_of_state[where p=p]
      | erule exE conjE)+
  apply (intro conjI)
      apply (clarsimp simp:image_def)
      apply (drule(1) bspec)+
      apply simp
     apply (fastforce simp:cap_range_def)
    apply (clarsimp simp:is_cap_simps)
    apply (simp only: UN_extend_simps UNION_empty_conv)
    apply (drule(1) bspec)+
    apply clarsimp
    apply blast
   apply (clarsimp simp: cap_range_def)
  apply (clarsimp simp: cap_range_def)
  done

lemma (in Untyped_AI_nonempty_table) create_caps_invs:
  assumes create_cap_Q[wp]: "\<And>cref oref.
    \<lbrace>invs and Q and cte_wp_at (\<lambda>c. is_untyped_cap c
            \<and> cap_range (default_cap tp oref sz dev) \<subseteq> untyped_range c
            \<and> {oref .. oref + 2 ^ (obj_bits_api tp us) - 1} \<subseteq> untyped_range c) p
        and cte_wp_at ((=) NullCap) cref
        and valid_cap (default_cap tp oref sz dev)
        and K (cref \<in> set crefs \<and> oref \<in> set (retype_addrs ptr tp (length slots) us))\<rbrace>
         create_cap tp sz p dev (cref,oref) \<lbrace>\<lambda>_. Q \<rbrace>"
  shows
  "\<lbrace>(\<lambda>s. invs (s::('state_ext::state_ext) state)  \<and> (Q::('state_ext::state_ext) state \<Rightarrow> bool) s
       \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> obj_is_device tp dev = cap_is_device c) p s
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
           cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz dev) \<subseteq> untyped_range c
           \<and> {snd tup .. snd tup + 2 ^ (obj_bits_api tp us) - 1} \<subseteq> untyped_range c
           \<and> (untyped_range (default_cap tp (snd tup) sz dev) \<inter> usable_untyped_range c = {})) p s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
           descendants_range (default_cap tp (snd tup) sz dev) p s)
       \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz dev)) (zip crefs orefs))
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
           cte_wp_at ((=) cap.NullCap) (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              valid_cap (default_cap tp (snd tup) sz dev) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              ex_cte_cap_wp_to is_cnode_cap (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              real_cte_at (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs). \<forall>r \<in> obj_refs (default_cap tp (snd tup) sz dev).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> Structures_A.obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)
       \<and> distinct (p # (map fst (zip crefs orefs)))
       \<and> tp \<noteq> ArchObject ASIDPoolObj)
       and K (set orefs \<subseteq> set (retype_addrs ptr tp (length slots) us))\<rbrace>
     mapM_x (create_cap tp sz p dev) (zip crefs orefs)
   \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (subgoal_tac "set (zip crefs orefs) \<subseteq> set crefs \<times> set (retype_addrs ptr tp (length slots) us)")
   prefer 2
   apply (auto dest!: set_zip_helper)[1]
  apply (induct ("zip crefs orefs"))
   apply (simp add: mapM_x_def sequence_x_def)
   apply wpsimp
  apply (clarsimp simp add: mapM_x_def sequence_x_def)
  apply (rule bind_wp)
   apply assumption
  apply (thin_tac "valid a b c" for a b c)
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post)
    apply (rule_tac list=list and us=us in create_caps_invs_inv)
    apply (rule hoare_pre, rule create_cap_Q)
    apply (clarsimp | drule(1) bspec)+
  done

lemma retype_region_cte_at_other':
  "\<lbrace>pspace_no_overlap_range_cover ptr sz and cte_wp_at P p
     and valid_pspace and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wpsimp wp: retype_region_cte_at_other)
  done

lemma retype_region_ex_cte_cap_to:
  "\<lbrace>pspace_no_overlap_range_cover ptr sz and ex_cte_cap_wp_to P p
     and valid_pspace and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (wp hoare_vcg_ex_lift retype_region_cte_at_other'
               | wps retype_region_irq_node)+
  apply auto
  done

lemma retype_region_obj_ref_range:
  "\<lbrakk> \<And>r. \<lbrace>P r\<rbrace> retype_region ptr n us ty dev\<lbrace>\<lambda>rv. Q r\<rbrace> \<rbrakk>
  \<Longrightarrow>
   \<lbrace>(\<lambda>s. \<forall>r \<in> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}. P r s) and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty dev
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. \<forall>r \<in> obj_refs (default_cap tp x us dev). Q r s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift [OF retype_region_ret, simplified])
   apply (rule hoare_vcg_const_Ball_lift)
   apply assumption
  apply (clarsimp)
  apply (drule subsetD[OF obj_refs_default_cap])
  apply (drule_tac x = r in  bspec)
   apply (simp add: ptr_add_def)
   apply (drule(1) range_cover_mem)
   apply simp
  apply simp
  done

lemma retype_region_not_cte_wp_at:
  "\<lbrace>(\<lambda>s. \<not> cte_wp_at P p s) and valid_pspace and
     caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api tp us - 1} and
     valid_mdb and pspace_no_overlap_range_cover ptr sz and caps_no_overlap ptr sz and
     (\<lambda>s. \<exists>cref. cte_wp_at (\<lambda>c. up_aligned_area ptr sz \<subseteq> cap_range c \<and> cap_is_device c = dev) cref s) and
     K (\<not> P cap.NullCap \<and> (tp = CapTableObject \<longrightarrow> 0 < us) \<and> range_cover ptr sz (obj_bits_api tp us) n)\<rbrace>
     retype_region ptr n us tp dev
   \<lbrace>\<lambda>rv s. \<not> cte_wp_at P p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: P_null_filter_caps_of_cte_wp_at[symmetric])
  apply (wpsimp wp: retype_region_caps_of)
  apply auto
  done


lemma retype_region_refs_distinct[wp]:
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) n)\<rbrace> retype_region ptr n us tp dev
   \<lbrace>\<lambda>rv s. distinct_prop
             (\<lambda>x y. obj_refs (default_cap tp (snd x) us dev)
                  \<inter> obj_refs (default_cap tp (snd y) us dev) = {})
             (zip xs rv)\<rbrace>"
  apply simp
  apply (rule hoare_gen_asm[where P'="\<top>", simplified])
  apply (rule hoare_strengthen_post [OF retype_region_ret])
  apply (subst distinct_prop_map[symmetric, where f=snd])
  apply (rule distinct_prop_prefixE [OF _ map_snd_zip_prefix [unfolded less_eq_list_def]])
  apply (clarsimp simp: retype_addrs_def distinct_prop_map
                        word_unat_power[symmetric] power_sub[symmetric]
                        power_add[symmetric] mult.commute
          | rule conjI distinct_prop_distinct [where xs="upt a b" for a b]
                 set_eqI diff_le_mono
          | erule(3) ptr_add_distinct_helper ptr_add_distinct_helper [OF _ not_sym]
          | drule subsetD [OF obj_refs_default_cap]
                  less_two_pow_divD)+
   apply (simp add: range_cover_def word_bits_def)
  apply (erule range_cover.range_cover_n_le[where 'a=machine_word_len])
  done


lemma unsafe_protected:
  "\<lbrakk> cte_wp_at P p s; cte_wp_at ((=) (UntypedCap dev ptr bits idx)) p' s;
     descendants_range_in S p' s; invs s; S \<subseteq> untyped_range (UntypedCap dev ptr bits idx);
     \<And>cap. P cap \<Longrightarrow> cap \<noteq> cap.NullCap \<rbrakk>
     \<Longrightarrow> fst p \<notin> S"
  apply (rule ex_cte_cap_protects)
      apply (erule if_unsafe_then_capD)
       apply (clarsimp simp: invs_def valid_state_def)
      apply simp
     apply assumption+
    apply clarsimp+
  done

lemma cap_to_protected:
  "\<lbrakk> ex_cte_cap_wp_to P p s; cte_wp_at ((=) (UntypedCap dev ptr bits idx)) p' s;
     descendants_range (UntypedCap dev ptr bits idx) p' s; invs s \<rbrakk>
     \<Longrightarrow> ex_cte_cap_wp_to P p (detype {ptr .. ptr + 2 ^ bits - 1} s)"
  apply (clarsimp simp: ex_cte_cap_wp_to_def, simp add: detype_def descendants_range_def2)
  apply (intro exI conjI, assumption)
  apply (case_tac "a = fst p")
   apply (frule(1) ex_cte_cap_protects
     [rotated,where P=P])
      apply clarsimp+
    apply (simp add: ex_cte_cap_wp_to_def)
    apply fastforce+
  apply (drule(2) unsafe_protected[rotated])
    apply simp+
    apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply auto
  done

(* FIXME: move *)
lemma ge_mask_eq: "len_of TYPE('a) \<le> n \<Longrightarrow> (x::'a::len word) && mask n = x"
  by (simp add: mask_def p2_eq_0[THEN iffD2])

(* FIXME: replace do_machine_op_obj_at in KHeap_R by the lemma below *)
lemma do_machine_op_obj_at_arch_state[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (Q (arch_state s)) p s)\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>_ s. P (obj_at (Q (arch_state s)) p s)\<rbrace>"
  by (clarsimp simp: do_machine_op_def split_def | wp)+

lemma (in Untyped_AI_nonempty_table) retype_nonempty_table[wp]:
  "\<lbrace>\<lambda>(s::('state_ext::state_ext) state). \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)\<rbrace>
     retype_region ptr sz us tp dev
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) r s)\<rbrace>"
  apply (simp add: retype_region_def split del: if_split)
  apply (rule hoare_pre)
   apply (wp|simp del: fun_upd_apply)+
  apply (clarsimp simp del: fun_upd_apply)
  apply (simp add: foldr_upd_app_if)
  apply (clarsimp simp: obj_at_def split: if_split_asm)
  done


lemma invs_arch_state_strg:
  "invs s \<longrightarrow> valid_arch_state s"
  by (clarsimp simp: invs_def valid_state_def)


lemma invs_psp_aligned_strg:
  "invs s \<longrightarrow> pspace_aligned s"
  by (clarsimp simp: invs_def valid_state_def)


(* FIXME: move *)
lemma invs_cap_refs_in_kernel_window[elim!]:
  "invs s \<Longrightarrow> cap_refs_in_kernel_window s"
  by (simp add: invs_def valid_state_def)

lemma (in Untyped_AI_nonempty_table) set_cap_nonempty_tables[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) p s)\<rbrace>
     set_cap cap cref
   \<lbrace>\<lambda>rv s. P (obj_at (nonempty_table (set (second_level_tables (arch_state s)))) p s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=arch_state, OF set_cap_arch])
   apply (wp set_cap_obj_at_impossible)
  apply (clarsimp simp: nonempty_table_caps_of)
  done


lemma ex_cte_cap_wp_to_def_msu[simp]:
  "ex_cte_cap_wp_to P x (machine_state_update f s)  = ex_cte_cap_wp_to P x s"
  by (simp add: ex_cte_cap_wp_to_def)

lemma (in Untyped_AI_arch) retype_region_caps_reserved:
  "\<lbrace>cte_wp_at (is_untyped_cap) p and caps_overlap_reserved {ptr..ptr + of_nat (n * 2 ^ obj_bits_api tp us) - 1}
  and K (range_cover ptr sz (obj_bits_api tp us) n) and pspace_no_overlap_range_cover ptr sz and valid_pspace \<rbrace>
  retype_region ptr n us tp dev
 \<lbrace>\<lambda>rv (s::('state_ext::state_ext) state). \<forall>y\<in>set rv. cte_wp_at (\<lambda>a. untyped_range (default_cap tp y us dev) \<inter> usable_untyped_range a = {}) p s\<rbrace>"
  apply (clarsimp simp: valid_def cte_wp_at_caps_of_state)
  apply (frule use_valid[OF _ retype_region_ranges'])
   apply fastforce
  apply (drule(1) bspec)
  apply (frule_tac P1 = "(=) cap" in use_valid[OF _ retype_region_cte_at_other])
    apply simp+
   apply (fastforce simp: cte_wp_at_caps_of_state)
  apply (clarsimp simp: cte_wp_at_caps_of_state caps_overlap_reserved_def)
  apply (drule bspec)
   apply fastforce
  apply (clarsimp simp: cap_range_def)
  apply blast
  done

lemma untyped_mdb_descendants_range:
  "\<lbrakk>caps_of_state s p = Some ucap; is_untyped_cap ucap; valid_mdb s; descendants_range_in S p s; S \<subseteq> untyped_range ucap;
   caps_of_state s slot = Some cap; x\<in> obj_refs cap \<rbrakk>\<Longrightarrow> x\<notin> S"
  apply (clarsimp simp: valid_mdb_def)
  apply (drule untyped_mdbD)
     apply simp+
    apply (rule ccontr)
    apply (clarsimp)
    apply blast
   apply simp
   apply (drule(2) descendants_range_inD)
  apply (simp add: cap_range_def,blast)
  done

lemma global_refs_detype[simp]: "global_refs (detype S s) = global_refs s"
  by (simp add: detype_def)

lemma ex_cte_cap_wp_to_clear_um[simp]:
  "ex_cte_cap_wp_to P p (clear_um T s) = ex_cte_cap_wp_to P p s"
  by (clarsimp simp: ex_cte_cap_wp_to_def clear_um_def)


locale Untyped_AI =
  Untyped_AI_of_bl_nat_to_cref +
  Untyped_AI_arch state_ext_t +
  Untyped_AI_nonempty_table state_ext_t nonempty_table
  for state_ext_t :: "'state_ext :: state_ext itself"
  and nonempty_table

lemma set_cap_device_and_range:
  "\<lbrace>\<top>\<rbrace> set_cap (UntypedCap dev (ptr && ~~ mask sz) sz idx) aref
   \<lbrace>\<lambda>rv s. (\<exists>slot. cte_wp_at (\<lambda>c. cap_is_device c = dev \<and> up_aligned_area ptr sz \<subseteq> cap_range c) slot s)\<rbrace>"
   apply (rule hoare_pre)
   apply (clarsimp simp: cte_wp_at_caps_of_state simp del: split_paired_All split_paired_Ex)
   apply (wp set_cap_cte_wp_at' hoare_vcg_ex_lift)
   apply (rule_tac x="aref" in exI)
   apply (auto intro: word_and_le2 simp: p_assoc_help)
   done




lemma set_free_index_invs_UntypedCap:
  "\<lbrace>\<lambda>s. invs s \<and> (\<exists>cap. free_index_of cap \<le> idx
        \<and> is_untyped_cap cap \<and> idx \<le> 2^cap_bits cap
        \<and> free_index_update (\<lambda>_. idx) cap = UntypedCap dev ptr sz idx
        \<and> cte_wp_at ((=) cap) cref s)\<rbrace>
   set_cap (UntypedCap dev ptr sz idx) cref
   \<lbrace>\<lambda>rv s'. invs s'\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply clarsimp
  apply (cut_tac cap=cap and idx=idx in set_free_index_invs)
  apply clarsimp
  apply (erule hoare_pre)
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (case_tac cap, simp_all add: free_index_of_def)
  done

lemma retype_region_aligned_for_init_sz:
  "\<lbrace>\<lambda>s. range_cover ptr sz (obj_bits_api new_type obj_sz) n
      \<and> obj_bits_api new_type obj_sz = some_us_sz\<rbrace>
     retype_region ptr n obj_sz new_type is_dev
   \<lbrace>\<lambda>rv s. \<forall>ref \<in> set rv. is_aligned ref some_us_sz\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre, rule hoare_strengthen_post,
    rule retype_region_aligned_for_init, auto)
  done

lemma (in strengthen_implementation) strengthen_Not[strg]:
  "\<lbrakk> st (\<not> F) (\<longrightarrow>) P P' \<rbrakk>
    \<Longrightarrow> st F (\<longrightarrow>) (\<not> P) (\<not> P')"
  by (cases F, auto)

lemma retype_region_ret_folded_general:
  "\<lbrace>\<lambda>s. P (retype_addrs y ty n bits)\<rbrace> retype_region y n bits ty dev
   \<lbrace>\<lambda>r s. P r\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (rule hoare_pre, rule hoare_strengthen_post,
    rule retype_region_ret_folded, auto)
  done

lemma retype_region_post_retype_invs_folded:
  "\<lbrace>P\<rbrace> retype_region y n bits ty dev \<lbrace>\<lambda>r. post_retype_invs ty r\<rbrace>
    \<Longrightarrow> \<lbrace>P\<rbrace> retype_region y n bits ty dev \<lbrace>\<lambda>r. post_retype_invs ty (retype_addrs y ty n bits)\<rbrace>"
  apply (rule hoare_strengthen_post,
    rule hoare_vcg_conj_lift[OF retype_region_ret_folded, simplified],
    assumption)
  apply clarsimp
  done

lemma tup_in_fst_image_set_zipD:
  "x \<in> fst ` set (zip xs ys) \<Longrightarrow> x \<in> set xs"
  by (auto dest!: set_zip_helper)

lemma distinct_map_fst_zip:
  "distinct xs \<Longrightarrow> distinct (map fst (zip xs ys))"
  apply (induct xs arbitrary: ys, simp_all)
  apply (case_tac ys, simp_all)
  apply (metis tup_in_fst_image_set_zipD)
  done

lemma retype_region_ranges_obj_bits_api:
  "\<lbrace>cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz
          \<and> obj_ref_of c = ptr && ~~ mask sz) p and
    pspace_no_overlap_range_cover ptr sz and
    valid_pspace and K (range_cover ptr sz (obj_bits_api tp us) n)
   \<rbrace>
  retype_region ptr n us tp dev
   \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. cte_wp_at
           (\<lambda>c. {y .. y + 2 ^ (obj_bits_api tp us) - 1} \<subseteq> untyped_range c )
           p s\<rbrace>"
   apply (clarsimp simp:cte_wp_at_caps_of_state valid_def)
   apply (frule_tac P1 = "(=) cap" in use_valid[OF _ retype_region_cte_at_other])
     apply simp
    apply (fastforce simp:cte_wp_at_caps_of_state)
   apply (clarsimp simp:cte_wp_at_caps_of_state del: subsetI)
   apply (frule use_valid[OF _ retype_region_ret_folded], simp+)
   apply (rule order_trans, erule(1) retype_addrs_range_subset)
   apply (clarsimp simp: is_cap_simps word_and_le2 del: subsetI)
   done

context Untyped_AI begin

lemma invoke_untyp_invs':
 assumes create_cap_Q: "\<And>tp sz cref slot oref reset ptr us slots dev.
     ui = Invocations_A.Retype slot reset (ptr && ~~ mask sz) ptr tp us slots dev
    \<Longrightarrow> \<lbrace>invs and Q and cte_wp_at (\<lambda>c. is_untyped_cap c
            \<and> cap_range (default_cap tp oref us dev) \<subseteq> untyped_range c
            \<and> {oref .. oref + 2 ^ (obj_bits_api tp us) - 1} \<subseteq> untyped_range c) slot
            and cte_wp_at ((=) NullCap) cref
            and K (cref \<in> set slots \<and> oref \<in> set (retype_addrs ptr tp (length slots) us))
            and K (range_cover ptr sz (obj_bits_api tp us) (length slots))\<rbrace>
         create_cap tp us slot dev (cref,oref) \<lbrace>\<lambda>_. Q\<rbrace>"
 assumes init_arch_Q: "\<And>tp slot reset sz slots ptr n us refs dev.
   ui = Invocations_A.Retype slot reset (ptr && ~~ mask sz) ptr tp us slots dev
    \<Longrightarrow> \<lbrace>Q and post_retype_invs tp refs
       and cte_wp_at (\<lambda>c. \<exists>idx. c = UntypedCap dev (ptr && ~~ mask sz) sz idx) slot
       and K (refs = retype_addrs ptr tp n us
         \<and> range_cover ptr sz (obj_bits_api tp us) n)\<rbrace>
     init_arch_objects tp ptr n us refs \<lbrace>\<lambda>_. Q\<rbrace>"
 assumes retype_region_Q: "\<And>ptr us tp slot reset sz slots dev.
    ui = Invocations_A.Retype slot reset (ptr && ~~ mask sz) ptr tp us slots dev
    \<Longrightarrow> \<lbrace>\<lambda>s. invs s \<and> Q s
         \<and> cte_wp_at (\<lambda>c. \<exists>idx. c = UntypedCap dev (ptr && ~~ mask sz) sz idx) slot s
         \<and> pspace_no_overlap {ptr..(ptr && ~~ mask sz) + (2 ^ sz - 1)} s
         \<and> range_cover ptr sz (obj_bits_api tp us) (length slots)
         \<and> (tp = CapTableObject \<longrightarrow> 0 < us)
         \<and> caps_overlap_reserved {ptr..ptr + of_nat ((length slots) * 2 ^ obj_bits_api tp us) - 1} s
         \<and> caps_no_overlap ptr sz s \<rbrace>
        retype_region ptr (length slots) us tp dev \<lbrace>\<lambda>_.Q\<rbrace>"
 assumes set_cap_Q[wp]: "\<And>ptr sz idx cref dev.
        \<lbrace>\<lambda>s. Q s \<and> invs s
        \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr) cref s
        \<and> (case ui of Invocations_A.Retype slot reset ptr' ptr tp us slots dev'
            \<Rightarrow> cref = slot \<and> dev' = dev)
        \<and> idx \<le> 2^ sz\<rbrace>
     set_cap (UntypedCap dev ptr sz idx) cref
   \<lbrace>\<lambda>rv. Q\<rbrace>"
 assumes reset_Q: "\<lbrace>Q'\<rbrace> reset_untyped_cap (case ui of Retype src_slot _ _ _ _ _ _ _ \<Rightarrow> src_slot) \<lbrace>\<lambda>_. Q\<rbrace>"
 shows
  "\<lbrace>(invs ::'state_ext state \<Rightarrow> bool)
        and (\<lambda>s. (case ui of Retype _ reset _ _ _ _ _ _ \<Rightarrow> reset) \<longrightarrow> Q' s)
        and Q and valid_untyped_inv ui and ct_active\<rbrace>
    invoke_untyped ui \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>, \<lbrace>\<lambda>_ s. invs s \<and> Q s\<rbrace>"
  apply (cases ui)
  apply (rule hoare_name_pre_stateE)
  apply (clarsimp simp only: valid_untyped_inv_wcap untyped_invocation.simps)
  proof -
    fix cref oref reset ptr_base ptr tp us slots s sz idx dev
    assume ui: "ui = Retype (cref, oref) reset ptr_base ptr tp us slots dev"
    assume Q: "Q s" and Q': "reset \<longrightarrow> Q' s"
    assume invs: "invs s" "ct_active s"
    assume vui: "valid_untyped_inv_wcap (Retype (cref, oref) reset ptr_base ptr tp us slots dev)
        (Some (UntypedCap dev (ptr && ~~ mask sz) sz idx)) s"
      (is "valid_untyped_inv_wcap _ (Some ?orig_cap) s")

   have cte_at: "cte_wp_at ((=) ?orig_cap) (cref,oref) s"
       (is "?cte_cond s")
       using vui by (clarsimp simp add:cte_wp_at_caps_of_state)

    note blah[simp del] = untyped_range.simps usable_untyped_range.simps
          atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

    note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]

    have p_neq_0:"ptr \<noteq> 0"
      using cte_at invs
      apply (clarsimp simp:cte_wp_at_caps_of_state)
      apply (drule(1) caps_of_state_valid)+
      apply (simp add:valid_cap_def)
      done

   have cover: "range_cover ptr sz (obj_bits_api tp us) (length slots)"
     using vui
     by (clarsimp simp:cte_wp_at_caps_of_state)

   note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]

   note set_cap_free_index_invs_spec = set_free_index_invs[where
      cap = "UntypedCap dev (ptr && ~~ mask sz) sz (if reset then 0 else idx)",
      unfolded free_index_update_def free_index_of_def,simplified]

    have slot_not_in: "(cref, oref) \<notin> set slots"
      using vui cte_at
      by (auto simp: cte_wp_at_caps_of_state)

    note reset_Q' = reset_Q[simplified ui, simplified]

    have ptr_base: "ptr_base = ptr && ~~ mask sz"
      using vui by (clarsimp simp: cte_wp_at_caps_of_state)

    note ui' = ui[unfolded ptr_base]

    note msimp[simp] = neg_mask_add_mask
    let ?ui = "Retype (cref, oref) reset ptr_base ptr tp us slots dev"
    show "\<lbrace>(=) s\<rbrace> invoke_untyped ?ui \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>, \<lbrace>\<lambda>_ s. invs s \<and> Q s\<rbrace>"
      using cover
      apply (simp add:mapM_x_def[symmetric] invoke_untyped_def)
      apply (rule_tac B="\<lambda>_ s. invs s \<and> Q s \<and> ct_active s
          \<and> valid_untyped_inv_wcap ?ui
            (Some (UntypedCap dev (ptr && ~~ mask sz) sz (if reset then 0 else idx))) s
          \<and> (reset \<longrightarrow> pspace_no_overlap {ptr && ~~ mask sz..(ptr && ~~ mask sz) + 2 ^ sz - 1} s)
          " in bindE_wp_fwd)
       apply (simp only: whenE_def)
       apply (rule hoare_pre, wp)
         apply (rule hoare_strengthen_postE, rule combine_validE,
             rule reset_untyped_cap_invs_etc, rule valid_validE, rule reset_Q')
          apply (clarsimp simp only: pred_conj_def if_True, blast)
         apply (wp | simp)+
       apply (cut_tac vui Q Q' invs)
       apply (clarsimp simp: cte_wp_at_caps_of_state slot_not_in)
       apply blast

      apply (simp add: cte_wp_at_conj ball_conj_distrib
                       split del: if_split
              | wp hoare_vcg_const_Ball_lift set_tuple_pick
                   retype_region_ex_cte_cap_to [where sz = sz]
                   retype_region_obj_ref_range [where sz = sz]
                   hoare_vcg_all_lift
                     [of _ _ "%a _ p. \<forall>b. ~ cte_wp_at P (a,b) p" for P]
                   hoare_vcg_all_lift
                     [of _ _ "%b _ p. ~ cte_wp_at P (a,b) p" for P a]
                   retype_region_not_cte_wp_at [where sz = sz]
                   init_arch_objects_invs_from_restricted
                   retype_ret_valid_caps [where sz = sz]
                   retype_region_global_refs_disjoint [where sz = sz]
                   retype_region_post_retype_invs [where sz = sz]
                   retype_region_cte_at_other[where sz = sz]
                   retype_region_invs_extras[where sz = sz]
                   retype_region_ranges [where sz = sz]
                   retype_region_ranges_obj_bits_api[where sz=sz]
                   retype_region_caps_reserved [where sz = sz]
                   retype_region_distinct_sets [where sz = sz]
                   create_caps_invs[where ptr=ptr and slots=slots and us=us]
                   create_cap_Q[OF ui']
                   init_arch_Q[OF ui']
                   retype_region_Q[OF ui']
                   retype_region_descendants_range_ret[where sz = sz]
                   retype_region_obj_at_other2
                     [where P="is_cap_table n" for n]
                   distinct_tuple_helper
                   init_arch_objects_wps
                   init_arch_objects_nonempty_table
              | wp (once) retype_region_ret_folded_general)+
        apply ((wp hoare_vcg_const_imp_lift hoare_drop_imp
                   retype_region_invs_extras[where sz = sz]
                   retype_region_aligned_for_init[where sz = sz]
                   set_free_index_invs_UntypedCap
                   set_cap_caps_no_overlap set_cap_no_overlap
                   set_untyped_cap_caps_overlap_reserved
            | strengthen tup_in_fst_image_set_zipD[mk_strg D]
                         distinct_map_fst_zip
            | simp add: ptr_base
            | wp (once) retype_region_ret_folded_general)+)[1]
       apply (clarsimp simp:conj_comms,simp cong:conj_cong)
       apply (simp add:ball_conj_distrib conj_comms)
       apply (strengthen invs_mdb invs_valid_pspace
                caps_region_kernel_window_imp[where p="(cref, oref)"]
                invs_cap_refs_in_kernel_window
                exI[where x="(cref, oref)"]
              | clarsimp simp: conj_comms
              | simp cong: conj_cong)+
       apply (rule_tac P = "bits_of cap = sz"
                    in hoare_gen_asm)
       apply (simp add:bits_of_def)
       apply (wp set_cap_no_overlap hoare_vcg_ball_lift
                 set_free_index_invs_UntypedCap
                 set_cap_cte_wp_at set_cap_descendants_range_in
                 set_cap_caps_no_overlap
                 set_untyped_cap_caps_overlap_reserved[where
                   idx="if reset then 0 else idx"]
                 set_cap_cte_cap_wp_to
                 hoare_vcg_ex_lift
               | wp (once) hoare_drop_imps)+
       apply (wp set_cap_cte_wp_at_neg hoare_vcg_all_lift get_cap_wp)+

      apply (clarsimp simp: slot_not_in field_simps ui free_index_of_def
                   split del: if_split)
      apply ((strengthen cover refl)+)?
      apply (simp only: cte_wp_at_caps_of_state, clarify,
        simp only: option.simps, simp(no_asm_use) split del: if_split, clarify)
      apply (clarsimp simp: bits_of_def untyped_range.simps
                            if_split[where P="\<lambda>v. v \<le> unat x" for x])

      apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
      apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps
                           conj_comms
                 split del: if_split)
      apply (frule invoke_untyped_proofs.intro[where cref="(cref, oref)" and reset=reset, rotated 1],
        simp_all add: cte_wp_at_caps_of_state split del: if_split)
       apply (rule conjI, (rule refl | assumption))+
       apply clarsimp
      apply (simp add: invoke_untyped_proofs.simps p_neq_0)
      apply (simp add: arg_cong[OF mask_out_sub_mask, where f="\<lambda>y. x - y" for x]
                       field_simps invoke_untyped_proofs.idx_le_new_offs
                       invoke_untyped_proofs.idx_compare'
                       exI invoke_untyped_proofs.simps
                       word_bw_assocs)
      apply (frule cte_wp_at_pspace_no_overlapI,
        simp add: cte_wp_at_caps_of_state, simp+,
        simp add: invoke_untyped_proofs.szw)
      apply (cut_tac s=s in obj_is_device_vui_eq[where ui=ui])
       apply (clarsimp simp: ui cte_wp_at_caps_of_state)
      apply (simp_all add: field_simps ui)

      apply (intro conjI)

            (* slots not in retype_addrs *)
            apply (clarsimp dest!:retype_addrs_subset_ptr_bits)
            apply (drule(1) invoke_untyped_proofs.slots_invD)
            apply (drule(1) subsetD)
            apply (simp add:p_assoc_help)

           (* not global refs*)
           apply (simp add: Int_commute, erule disjoint_subset2[rotated])
           apply (simp add: atLeastatMost_subset_iff word_and_le2)

          (* idx less_eq new offs *)
          apply (auto dest: invoke_untyped_proofs.idx_le_new_offs)[1]

          (* not empty tables *)
          apply clarsimp
          apply (drule(1) pspace_no_overlap_obj_not_in_range, clarsimp+)[1]

         (* set ineqs *)
         apply (simp add: atLeastatMost_subset_iff word_and_le2)

        apply (erule order_trans[OF invoke_untyped_proofs.subset_stuff])
        apply (simp add: atLeastatMost_subset_iff word_and_le2)

       (* new untyped range disjoint *)
       apply (drule invoke_untyped_proofs.usable_range_disjoint)
       apply (clarsimp simp: field_simps mask_out_sub_mask shiftl_t2n)

      (* something about caps *)
      apply clarsimp
      apply (frule untyped_mdb_descendants_range, clarsimp+,
        erule invoke_untyped_proofs.descendants_range, simp_all+)[1]
      apply (simp add: untyped_range_def atLeastatMost_subset_iff word_and_le2)
      done
qed

lemmas invoke_untyp_invs[wp] =
  invoke_untyp_invs'[where Q=\<top> and Q'=\<top>, simplified,
    simplified hoare_TrueI, simplified]

lemmas invoke_untyped_Q
    = invoke_untyp_invs'[THEN validE_valid, THEN hoare_conjD2[unfolded pred_conj_def]]

lemma invoke_untyped_pred_tcb_at:
  "\<lbrace>\<lambda>s. pred_tcb_at proj Q t s \<and> invs s \<and> st_tcb_at ((Not \<circ> inactive) and (Not \<circ> idle)) t s
        \<and> ct_active s \<and> valid_untyped_inv ui s\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_ s :: 'state_ext state. pred_tcb_at proj Q t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_Q,
         (wp init_arch_objects_wps | simp)+)
     apply (rule hoare_name_pre_state, clarsimp)
     apply (wp retype_region_st_tcb_at)
     apply fastforce
    apply (wp reset_untyped_cap_pred_tcb_at | simp)+
  apply (cases ui, clarsimp)
  apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
   apply (clarsimp split: Structures_A.thread_state.splits)
  apply (drule ex_nonz_cap_to_overlap,
         ((simp add: cte_wp_at_caps_of_state is_cap_simps descendants_range_def2
                     empty_descendants_range_in)+))
  done

lemma invoke_untyped_st_tcb_at[wp]:
  "\<lbrace>invs and st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t
         and ct_active and valid_untyped_inv ui\<rbrace>
   invoke_untyped ui
   \<lbrace>\<lambda>_. \<lambda>s :: 'state_ext state. st_tcb_at P t s\<rbrace>"
  apply (rule hoare_pre, rule invoke_untyped_pred_tcb_at)
  by (fastforce simp: pred_tcb_at_def  obj_at_def)

lemma invoked_untyp_tcb[wp]:
  "\<lbrace>invs and st_tcb_at active tptr
        and valid_untyped_inv ui and ct_active\<rbrace>
     invoke_untyped ui \<lbrace>\<lambda>rv. \<lambda>s :: 'state_ext state. tcb_at tptr s\<rbrace>"
  apply (simp add: tcb_at_st_tcb_at)
  apply (rule hoare_pre, wp invoke_untyped_st_tcb_at)
  apply (clarsimp elim!: pred_tcb_weakenE)
  apply fastforce
  done

end

lemma sts_mdb[wp]:
  "\<lbrace>\<lambda>s. P (cdt s)\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv s. P (cdt s)\<rbrace>"
  by (simp add: set_thread_state_def | wp)+

lemma sts_ex_cap[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  by (wp ex_cte_cap_to_pres)

lemmas sts_real_cte_at[wp] =
    cap_table_at_lift_valid [OF set_thread_state_typ_at]

lemma sts_valid_untyped_inv:
  "\<lbrace>valid_untyped_inv ui\<rbrace> set_thread_state t st \<lbrace>\<lambda>rv. valid_untyped_inv ui\<rbrace>"
  apply (cases ui, simp add: descendants_range_in_def)
  apply (wp hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_imp_lift | wps)+
  apply clarsimp
  done

lemma update_untyped_cap_valid_objs:
  "\<lbrace> valid_objs and valid_cap cap
      and cte_wp_at (is_untyped_cap) p and K (is_untyped_cap cap)\<rbrace>
    set_cap cap p \<lbrace> \<lambda>rv. valid_objs \<rbrace>"
  apply (wp set_cap_valid_objs)
  apply (clarsimp simp: is_cap_simps cte_wp_at_caps_of_state)
  apply (drule tcb_cap_valid_caps_of_stateD, simp+)
  apply (simp add: tcb_cap_valid_untyped_to_thread)
  done

lemma valid_untyped_pspace_no_overlap:
  "pspace_no_overlap {ptr .. ptr + 2 ^ sz - 1} s
    \<Longrightarrow> valid_untyped (UntypedCap dev ptr sz idx) s"
  apply (clarsimp simp: valid_untyped_def split del: if_split)
  apply (drule(1) pspace_no_overlap_obj_range)
  apply simp
  done

(* FIXME: move *)
lemma snd_set_zip_in_set:
  "x\<in> snd ` set (zip a b) \<Longrightarrow> x\<in> set b"
  apply (clarsimp)
  apply (erule in_set_zipE)
  apply simp
  done

end
