(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

(* Proofs about untyped invocations. *)

theory Untyped_AI
imports Detype_AI
begin

primrec
  valid_untyped_inv :: "Invocations_A.untyped_invocation \<Rightarrow> 'z::state_ext state \<Rightarrow> bool"
where
 "valid_untyped_inv (Invocations_A.Retype slot ptr_base ptr ty us slots)
   = (\<lambda>s. \<exists>sz idx. (cte_wp_at (\<lambda>c. c = (cap.UntypedCap ptr_base sz idx)) slot s
          \<and> range_cover ptr sz (obj_bits_api ty us) (length slots) 
          \<and> (idx \<le> unat (ptr - ptr_base) \<or> ptr = ptr_base ) \<and> (ptr && ~~ mask sz) = ptr_base)
          \<and> (ptr = ptr_base \<longrightarrow> descendants_range_in {ptr_base..ptr_base + 2^ sz - 1} slot s)
          \<and> (ty = CapTableObject \<longrightarrow> us > 0)
          \<and> (ty = Untyped \<longrightarrow> us \<ge> 4)
          \<and> distinct (slot#slots)
          \<and> (\<forall>slot\<in>set slots. cte_wp_at (op = cap.NullCap) slot s
                    \<and> ex_cte_cap_wp_to is_cnode_cap slot s \<and> real_cte_at slot s)
          \<and> ty \<noteq> ArchObject ASIDPoolObj \<and> 0 < length slots)"


lemma of_bl_nat_to_cref:
    "\<lbrakk> x < 2 ^ bits; bits < 32 \<rbrakk>
      \<Longrightarrow> (of_bl (nat_to_cref bits x) :: word32) = of_nat x"
  apply (clarsimp intro!: less_mask_eq
                  simp: nat_to_cref_def of_drop_to_bl
                        word_size word_less_nat_alt word_bits_def)
  apply (subst unat_of_nat)
  apply (erule order_le_less_trans [OF mod_le_dividend])
  done


lemma cnode_cap_bits_range:
  "\<lbrakk> cte_wp_at P p s; invs s \<rbrakk> \<Longrightarrow>
     (\<exists>c. P c \<and> (is_cnode_cap c \<longrightarrow>
                 (\<lambda>n. n > 0 \<and> n < 28 \<and> is_aligned (obj_ref_of c) (n + 4)) (bits_of c)))"
  apply (frule invs_valid_objs)
  apply (drule(1) cte_wp_at_valid_objs_valid_cap)
  apply clarsimp
  apply (rule exI, erule conjI)
  apply (clarsimp simp: is_cap_simps valid_cap_def bits_of_def)
  apply (erule (1) obj_at_valid_objsE)
  apply (case_tac ko, simp_all add: is_cap_table_def)[1]
  apply (clarsimp simp: valid_obj_def valid_cs_def well_formed_cnode_n_def
                        valid_cs_size_def length_set_helper
                        word_bits_def cte_level_bits_def)
  apply (drule invs_psp_aligned)
  apply (unfold pspace_aligned_def)
  apply (frule domI, drule (1) bspec)
  apply (clarsimp simp: obj_bits.simps ex_with_length add.commute 
                        cte_level_bits_def 
                  split: split_if_asm)
  apply (clarsimp simp: well_formed_cnode_n_def length_set_helper)
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
   apply (rule_tac P1=wellformed_cap
                in hoare_strengthen_post[OF get_cap_cte_wp_at_P])
   apply clarsimp
   apply (rule exI)+
   apply (subst cap_mask_UNIV, simp)
   apply fastforce
  apply (rule hoare_pre, wp)
   apply (strengthen cte_wp_at_wellformed_strengthen)
   apply wp
  apply simp
  done


lemma is_cnode_mask:
  "is_cnode_cap (mask_cap m c) = is_cnode_cap c"
  by (case_tac c, simp_all add: mask_cap_def cap_rights_update_def is_cap_simps)


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
  by (cases cap, auto simp: mask_cap_def cap_rights_update_def)

(* FIXME: move *)
lemma unat_2p_sub_1:
  "k < len_of TYPE('a)
  \<Longrightarrow> unat (2 ^ k - 1 :: 'a :: len word) = unat (2 ^ k :: 'a word) - 1"
  by (simp add: unat_minus_one p2_eq_0)


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
  "\<lbrace>P\<rbrace> decode_untyped_invocation label args slot (cap.UntypedCap w n idx) cs \<lbrace>\<lambda>rv. P\<rbrace>"
  apply (simp add: decode_untyped_invocation_def whenE_def
                   split_def data_to_obj_type_def unlessE_def
              split del: split_if cong: if_cong)
  apply (rule hoare_pre)
   apply (simp split del: split_if
              | wp_once mapME_x_inv_wp hoare_drop_imps const_on_failure_wp
              | assumption 
              | simp add: lookup_target_slot_def
              | wpcw)+
  done


lemma map_ensure_empty_cte_wp_at:
  "\<lbrace>cte_wp_at P p\<rbrace> mapME_x ensure_empty xs \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>,-"
  apply (simp add: mapME_x_def sequenceE_x_def)
  apply (induct xs, simp_all)
   apply wp
   apply assumption
  apply (simp add: ensure_empty_def whenE_def)
  apply (wp get_cap_wp)
  apply clarsimp
  done


lemma map_ensure_empty:
  "\<lbrace>P\<rbrace> mapME_x ensure_empty xs \<lbrace>\<lambda>rv s. (\<forall>x \<in> set xs. cte_wp_at (op = cap.NullCap) x s) \<and> P s\<rbrace>,-"
  apply (induct xs)
   apply (simp add: mapME_x_def sequenceE_x_def)
   apply wp
  apply (simp add: mapME_x_def sequenceE_x_def)
  apply (unfold validE_R_def)
  apply (rule seqE[rotated])
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
  apply (intro conjI impI)
  apply wp
  apply (rule hoare_pre, wpcw, wp)
  apply simp
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
            odE \<lbrace>\<lambda>rv s. (rv = root_cap \<or> (\<exists>slot. cte_wp_at (diminished rv) slot s)) \<and> P s\<rbrace>, -"
  apply (simp add: split_def lookup_target_slot_def)
  apply (intro impI conjI)
   apply (rule hoare_pre, wp)
   apply simp
  apply (wp get_cap_wp)
  apply (fold validE_R_def)
  apply (rule hoare_post_imp_R [where Q'="\<lambda>rv. valid_objs and P"])
   apply wp
   apply simp
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (simp add: diminished_def)
  apply (elim allE, drule(1) mp)
  apply (elim allE, subst(asm) cap_mask_UNIV)
   apply (frule caps_of_state_valid_cap, simp, simp add: valid_cap_def2)
  apply simp
  done


lemma cnode_cap_ex_cte:
  "\<lbrakk> is_cnode_cap cap; cte_wp_at (\<lambda>c. \<exists>m. cap = mask_cap m c) p s;
     s \<turnstile> cap; valid_objs s; pspace_aligned s \<rbrakk> \<Longrightarrow>
    ex_cte_cap_wp_to is_cnode_cap (obj_ref_of cap, nat_to_cref (bits_of cap) x) s"
  apply (simp only: ex_cte_cap_wp_to_def)
  apply (rule exI, erule cte_wp_at_weakenE)
  apply (clarsimp simp: is_cap_simps bits_of_def)
  apply (case_tac c, simp_all add: mask_cap_def cap_rights_update_def)
  apply (clarsimp simp: nat_to_cref_def word_bits_def)
  apply (erule(2) valid_CNodeCapE)
  apply (simp add: word_bits_def cte_level_bits_def)
  done


lemma inj_on_nat_to_cref:
  "bits < 32 \<Longrightarrow> inj_on (nat_to_cref bits) {..< 2 ^ bits}"
  apply (rule inj_onI)
  apply (drule arg_cong[where f="\<lambda>x. replicate (32 - bits) False @ x"]) 
  apply (subst(asm) word_bl.Abs_inject[where 'a=32, symmetric])
    apply (simp add: nat_to_cref_def word_bits_def)
   apply (simp add: nat_to_cref_def word_bits_def)
  apply (simp add: of_bl_rep_False of_bl_nat_to_cref)
  apply (erule word_unat.Abs_eqD)
   apply (simp only: unats_def mem_simps)
   apply (erule order_less_le_trans)
   apply (rule power_increasing, simp+)
  apply (simp only: unats_def mem_simps)
  apply (erule order_less_le_trans)
  apply (rule power_increasing, simp+)
  done


lemma data_to_obj_type_sp:
  "\<lbrace>P\<rbrace> data_to_obj_type x \<lbrace>\<lambda>ts s. ts \<noteq> ArchObject ASIDPoolObj \<and> P s\<rbrace>, -"
  unfolding data_to_obj_type_def
  apply (rule hoare_pre)
   apply (wp|wpc)+
  apply clarsimp
  apply (simp add: arch_data_to_obj_type_def split: split_if_asm)
  done

lemma alignUp_def2:
  "alignUp a sz = a + 2 ^ sz - 1 && ~~ mask sz"
   unfolding alignUp_def[unfolded complement_def]
   by (simp add:mask_def[symmetric,unfolded shiftl_t2n,simplified])


lemma is_aligned_triv2:
  "is_aligned (2^a) a"
   apply (case_tac "word_bits\<le> a")
   apply (simp add:is_aligned_triv)+
   done


lemma alignUp_def3:
  "alignUp a sz = 2^ sz + (a - 1 && ~~ mask sz)" (is "?lhs = ?rhs")
   apply (simp add:alignUp_def2)
   apply (subgoal_tac "2 ^ sz + a - 1 && ~~ mask sz = ?rhs")
    apply (clarsimp simp:field_simps)
   apply (subst mask_out_add_aligned)
   apply (rule is_aligned_triv2)
   apply (simp add:field_simps)
   done


lemma  alignUp_plus:
  "is_aligned w us \<Longrightarrow> alignUp (w + a) us  = w + alignUp a us"
  apply (clarsimp simp:alignUp_def2 add.assoc)
  apply (simp add: mask_out_add_aligned field_simps)
  done


lemma alignUp_distance:
  "(alignUp (q :: 'a :: len word) sz) - q \<le> mask sz"
  apply (case_tac "len_of TYPE('a) \<le> sz")
   apply (simp add:alignUp_def2 mask_def power_overflow)
  apply (case_tac "is_aligned q sz")
  apply (clarsimp simp:alignUp_def2 p_assoc_help)
   apply (subst mask_out_add_aligned[symmetric],simp)+
   apply (simp add:mask_lower_twice word_and_le2)
   apply (simp add:and_not_mask)
   apply (subst le_mask_iff[THEN iffD1])
    apply (simp add:mask_def)
   apply simp
  apply (clarsimp simp:alignUp_def3)
  apply (subgoal_tac "2 ^ sz - (q - (q - 1 && ~~ mask sz)) \<le> 2 ^ sz - 1")
   apply (simp add:field_simps mask_def)
  apply (rule word_sub_mono)
   apply simp
   apply (rule ccontr)
   apply (clarsimp simp:not_le)
   apply (drule eq_refl)
   apply (drule order_trans[OF _ word_and_le2])
   apply (subgoal_tac "q \<noteq>  0")
    apply (drule minus_one_helper[rotated])
     apply simp
    apply simp
   apply (fastforce)
  apply (simp add: word_sub_le_iff)
  apply (subgoal_tac "q - 1 && ~~ mask sz = (q - 1) - (q - 1 && mask sz)")
   apply simp
   apply (rule order_trans)
    apply (rule word_add_le_mono2)
     apply (rule word_and_le1)
    apply (subst unat_plus_simple[THEN iffD1,symmetric])
     apply (simp add:not_le mask_def)
     apply (rule word_sub_1_le)
     apply simp
    apply (rule unat_lt2p)
   apply (simp add:mask_def)
  apply (simp add:mask_out_sub_mask)
  apply (rule word_sub_1_le)
  apply simp
  done


lemma is_aligned_diff_neg_mask:
  "is_aligned p sz \<Longrightarrow> (p - q && ~~ mask sz) = (p - ((alignUp q sz) && ~~ mask sz))"
  apply (clarsimp simp only:word_and_le2 diff_conv_add_uminus)
  apply (subst mask_out_add_aligned[symmetric])
   apply simp+
  apply (rule sum_to_zero)
  apply (subst add.commute)
  apply (subst  mask_out_add_aligned)
   apply (simp add:is_aligned_neg_mask)
  apply simp
  apply (subst and_not_mask[where w = "(alignUp q sz && ~~ mask sz) - q "])
  apply (subst le_mask_iff[THEN iffD1])
   apply (simp add:is_aligned_neg_mask_eq)
   apply (rule alignUp_distance)
  apply simp
done


lemma strengthen_imp_ex2: "(P \<longrightarrow> Q x y) \<Longrightarrow> (P \<longrightarrow> (\<exists>x y. Q x y))"
 by auto


lemma p2_minus:
  "sz < len_of TYPE('a) \<Longrightarrow>
   of_nat (2 ^ len_of TYPE('a) - 2 ^ sz) = ((mask (len_of TYPE('a)) && ~~ mask sz):: 'a :: len word)"
   apply (rule word_unat.Rep_inverse')
   apply (simp add:mask_out_sub_mask)
   apply (simp add:unat_sub word_and_le2 mask_and_mask)
   apply (simp add:min_def mask_def word_size unat_minus)
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
     apply (simp add:range_cover_def)
     apply (rule unat_le_helper)
     apply (subst p2_minus)
      apply (erule range_cover.sz)
     apply (rule neg_mask_mono_le)
    apply (simp add:mask_def)
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
   apply (simp add:word_less_nat_alt)
   apply (rule le_less_trans[OF unat_plus_gt])
   apply (erule range_cover.range_cover_compare[OF cover])
  apply (subst add.assoc)
  apply (rule le_trans[OF _ l])
  apply simp
  apply (simp add: n)
  done
qed


lemma range_cover_stuff:
  "\<lbrakk>0 < n;n \<le> unat ((2::word32) ^ sz - of_nat rv >> bits);
  rv \<le> 2^ sz; sz < word_bits; is_aligned w sz\<rbrakk> \<Longrightarrow>
   rv \<le> unat (alignUp (w + of_nat rv) bits - w) \<and>
   (alignUp (w + of_nat rv) bits) && ~~ mask sz = w \<and>
   range_cover (alignUp (w + ((of_nat rv)::word32)) bits) sz bits n"
  apply (clarsimp simp:range_cover_def)
  proof (intro conjI)
    assume not_0 : "0<n"
    assume bound : "n \<le> unat ((2::word32) ^ sz - of_nat rv >> bits)" "rv\<le> 2^sz" 
      "sz < word_bits"
    assume al: "is_aligned w sz"
    have space: "(2::word32) ^ sz - of_nat rv \<le> 2^ sz"
      apply (rule word_sub_le[OF word_of_nat_le])
      apply (clarsimp simp:bound unat_power_lower32)
      done
    show cmp: "bits \<le> sz"
      using not_0 bound
      apply -
      apply (rule ccontr)
      apply (clarsimp simp:not_le)
      apply (drule le_trans)
      apply (rule word_le_nat_alt[THEN iffD1])
      apply (rule le_shiftr[OF space])
      apply (subgoal_tac "(2::word32)^sz >> bits = 0")
       apply simp
      apply (rule and_mask_eq_iff_shiftr_0[THEN iffD1])
      apply (simp add:and_mask_eq_iff_le_mask)
      apply (case_tac "word_bits \<le> bits")
       apply (simp add:word_bits_def mask_def power_overflow)
      apply (subst le_mask_iff_lt_2n[THEN iffD1])
       apply (simp add:word_bits_def)
      apply (simp add: word_less_nat_alt[THEN iffD2] unat_power_lower32)
      done
    have shiftr_t2n[simp]:"(2::word32)^sz >> bits = 2^ (sz - bits)"
      using bound cmp
      apply (case_tac "sz = 0",simp)
      apply (subgoal_tac "(1::word32) << sz >> bits = 2^ (sz -bits)")
       apply simp
      apply (subst shiftl_shiftr1)
      apply (simp add:word_size word_bits_def shiftl_t2n word_1_and_bl)+
     done

    have cmp2[simp]: "alignUp (of_nat rv) bits < (2 :: word32) ^ sz"
      using bound cmp not_0
      apply -
      apply (case_tac "rv = 0")
       apply simp
       apply (clarsimp simp:alignUp_def2)
       apply (subst mask_eq_x_eq_0[THEN iffD1])
       apply (simp add:and_mask_eq_iff_le_mask mask_def)
       apply (simp add: p2_gt_0[where 'a=32, folded word_bits_def])
      apply (simp add:alignUp_def3)
      apply (subgoal_tac "1 \<le> unat (2 ^ sz - of_nat rv >> bits)")
      prefer 2
       apply (erule le_trans[rotated])
       apply clarsimp
      apply (thin_tac "n \<le> M" for M)
      apply (simp add:shiftr_div_2n')
      apply (simp add:td_gal[symmetric])
      apply (subst (asm) unat_sub)
       apply (simp add: word_of_nat_le unat_power_lower32)
      apply (simp add:le_diff_conv2 word_of_nat_le unat_le_helper word_less_nat_alt)
      apply (rule le_less_trans[OF unat_plus_gt])
      apply (rule less_le_trans[where y = "2^bits + unat (of_nat rv)"])
      apply (simp add: unat_power_lower32)
      apply (rule le_less_trans[OF _ measure_unat])
      apply (rule word_le_nat_alt[THEN iffD1])
      apply (rule word_and_le2)
      apply (erule of_nat_neq_0)
       apply (subst word_bits_def[symmetric])
       apply (erule le_less_trans)
       apply simp
      apply (simp add: unat_power_lower32)
      done
    
    show "n + unat (alignUp (w + ((of_nat rv)::word32)) bits && mask sz >> bits) \<le> 2 ^ (sz - bits)"
      using not_0 bound cmp
     apply -
     apply (erule le_trans[OF add_le_mono])
      apply (rule le_refl)
     apply (clarsimp simp:power_sub field_simps td_gal[symmetric])
     apply (subst (2) mult.commute) 
     apply (subst unat_shiftl_absorb)
      apply (rule order_trans[OF le_shiftr])
       apply (rule word_and_le1)
      apply (simp add:shiftr_mask2 word_bits_def)
      apply (simp add:mask_def)
      apply (rule word_sub_1_le)
      apply (simp add:word_bits_def)+
     apply (simp add:shiftl_t2n[symmetric] field_simps shiftr_shiftl1)
     apply (subst is_aligned_neg_mask_eq)
      apply (rule is_aligned_andI1,simp)
     apply (subst mult.commute)
     apply (subst unat_shiftl_absorb[where p = "sz - bits"])
        apply (rule order_trans[OF le_shiftr])
         apply (rule space)
       apply (simp add:shiftr_div_2n_w word_bits_def)+
     apply (simp add:shiftl_t2n[symmetric] field_simps shiftr_shiftl1)
     apply (subst is_aligned_diff_neg_mask[OF is_aligned_weaken])
       apply (rule is_aligned_triv)
      apply (simp add:word_bits_def)+
     apply (subst unat_sub)
      apply (rule order_trans[OF word_and_le2])
      apply (simp add:less_imp_le)
     apply (subst diff_add_assoc[symmetric])
      apply (rule unat_le_helper)
      apply (rule order_trans[OF word_and_le2])
      apply (simp add: less_imp_le[OF cmp2])
     apply (clarsimp simp:field_simps word_bits_def is_aligned_neg_mask_eq)
     apply (simp add:le_diff_conv word_le_nat_alt[symmetric] word_and_le2)
     apply (simp add: alignUp_plus[OF is_aligned_weaken[OF al]]
                      is_aligned_add_helper[THEN conjunct1, OF al cmp2])
     done
   show "rv \<le> unat (alignUp (w + of_nat rv) bits - w)"
     using bound not_0 cmp al
     apply -
     apply (clarsimp simp:alignUp_plus[OF is_aligned_weaken])
     apply (case_tac "rv = 0")
      apply simp
     apply (rule le_trans[OF _ word_le_nat_alt[THEN iffD1,OF alignUp_ge]])
      apply (subst unat_of_nat32)
      apply (erule le_less_trans)
       apply simp
       apply (simp_all add: word_bits_def)[2]
     apply (rule alignUp_is_aligned_nz[where x = "2^sz"])
      apply (rule is_aligned_weaken[OF is_aligned_triv2])
      apply (simp_all add: word_bits_def)[2]
     apply (subst word_of_nat_le)
     apply (subst unat_power_lower32)
     apply simp+
    apply (erule of_nat_neq_0)
    apply (erule le_less_trans)
    apply (subst word_bits_def[symmetric])
    apply simp
    done
   show "alignUp (w + of_nat rv) bits && ~~ mask sz = w"
    using bound not_0 cmp al
    apply (clarsimp simp:alignUp_plus[OF is_aligned_weaken] 
      mask_out_add_aligned[symmetric])
    apply (clarsimp simp:and_not_mask)
    apply (subgoal_tac "alignUp ((of_nat rv)::word32) bits >> sz = 0")
     apply simp
    apply (simp add:le_mask_iff[symmetric] mask_def)
    done
   show "sz < 32" by (simp add: bound(3)[unfolded word_bits_def, simplified])
   qed
   

lemma cte_wp_at_range_cover:
  "\<lbrakk>bits < word_bits; rv\<le> 2^ sz; invs s;
    cte_wp_at (op = (cap.UntypedCap w sz idx)) p s;
    0 < n; n \<le> unat ((2::word32) ^ sz - of_nat rv >> bits)\<rbrakk>
   \<Longrightarrow> range_cover (alignUp (w + of_nat rv) bits) sz bits n"
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (frule(1) caps_of_state_valid)
  apply (clarsimp simp:valid_cap_def valid_untyped_def cap_aligned_def)
  apply (drule range_cover_stuff)
   apply simp_all
  apply clarsimp
  done



lemma le_mask_le_2p:
  "\<lbrakk>idx \<le> unat ((ptr::word32) && mask sz);sz < word_bits\<rbrakk> \<Longrightarrow> idx < 2^ sz"
  apply (erule le_less_trans)
  apply (rule unat_less_helper)
  apply simp
  apply (rule le_less_trans)
  apply (rule word_and_le1)
  apply (simp add:mask_def)
  done


lemma diff_neg_mask[simp]:
  "ptr - (ptr && ~~ mask sz) = (ptr && mask sz)"
  apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
  apply simp
  done


lemma cte_wp_at_caps_descendants_range_inI:
  "\<lbrakk> invs s;cte_wp_at (\<lambda>c. c = cap.UntypedCap (ptr && ~~ mask sz) sz idx) cref s;
    idx \<le> unat (ptr && mask sz);sz < word_bits \<rbrakk> \<Longrightarrow> descendants_range_in {ptr .. (ptr && ~~mask sz) + 2^sz - 1} cref s"
  apply (frule invs_mdb)
  apply (frule(1) le_mask_le_2p)
  apply (clarsimp simp:descendants_range_in_def cte_wp_at_caps_of_state )
  apply (frule(1) descendants_of_cte_at)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule untyped_cap_descendants_range[rotated])
    apply simp+
   apply (simp add:invs_valid_pspace)
  apply (clarsimp simp:cte_wp_at_caps_of_state usable_untyped_range.simps)
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
   apply (clarsimp simp:field_simps)+
   done
 have t2n_sym: "\<And>z. (2::'a :: len word)^z = (1:: 'a :: len word)<<z"
   by (simp add:shiftl_t2n)
 have le_helper: "\<And>b c. \<lbrakk>\<And>a. (a::'a :: len word)< b \<Longrightarrow> a< c\<rbrakk> \<Longrightarrow> b\<le>c"
   apply (rule ccontr)
   apply (clarsimp simp:not_le dest!:meta_spec)
   by auto
 have ptr_word: "(ptr - word >> sz) * 2 ^ sz = (ptr &&~~ mask sz) - word"
  apply (subst mult.commute)
  apply (clarsimp simp:shiftl_t2n[symmetric] shiftr_shiftl1 word_and_le2)
  apply (simp only: diff_conv_add_uminus)
  apply (subst add.commute[where a = "ptr && ~~ mask sz"])
  apply (subst mask_out_add_aligned)
  defer
  apply (simp add:field_simps)
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
     apply (simp add:offset)
   apply simp
  apply (rule le_plus)
   apply (subst mult.commute)
   apply (simp add: shiftl_t2n[symmetric] shiftr_shiftl1 word_and_le2)
  apply clarsimp
 apply (simp add:ptr_word p_assoc_help)
 apply (rule order_trans[OF _ word_plus_mono_right])
   apply (rule order_eq_refl)
   apply (subst word_plus_and_or_coroll2[where x = "ptr",symmetric])
   apply (subst add.commute)
   apply simp
  apply (rule order_trans[OF word_and_le1])
  apply (clarsimp simp:mask_def)
 apply (rule is_aligned_no_overflow'[OF is_aligned_neg_mask])
 apply simp+
done
qed


lemma check_free_index_wp:
  "\<lbrace>\<lambda>s. if descendants_of slot (cdt s) = {} then Q 0 s else Q idx s \<rbrace>
   const_on_failure (free_index_of (cap.UntypedCap w sz idx))
    (doE y \<leftarrow> ensure_no_children slot;
    returnOk 0
    odE) \<lbrace>Q\<rbrace>"
  apply (clarsimp simp:const_on_failure_def ensure_no_children_descendants bindE_assoc)
  apply wp
  apply (clarsimp simp:valid_def validE_def if_splits)
  apply (intro conjI impI)
  apply (clarsimp simp:in_monad free_index_of_def)+
  done


lemma alignUp_eq:
  "\<lbrakk>is_aligned (w :: 'a :: len word) sz; a \<le> 2^ sz; us \<le> sz; sz < len_of TYPE('a);
    alignUp (w + a) us = w\<rbrakk>
   \<Longrightarrow> a = 0"
  apply (clarsimp simp:alignUp_plus[OF is_aligned_weaken])
  apply (rule ccontr)
  apply (drule alignUp_is_aligned_nz[rotated -1,where x = "2^ sz"])
    apply (rule is_aligned_weaken[OF is_aligned_triv2])
    apply simp+
  done

lemma map_ensure_empty_wp:
  "\<lbrace> \<lambda>s. (\<forall>x\<in>set xs. cte_wp_at (op = NullCap) x s) \<longrightarrow> P () s \<rbrace>
      mapME_x ensure_empty xs \<lbrace>P\<rbrace>, -"
  by (rule hoare_post_imp_R, rule map_ensure_empty, simp)

lemma cases_imp_eq:
  "((P \<longrightarrow> Q \<longrightarrow> R) \<and> (\<not> P \<longrightarrow> Q \<longrightarrow> S)) = (Q \<longrightarrow> (P \<longrightarrow> R) \<and> (\<not> P \<longrightarrow> S))"
  by blast

lemma dui_inv_wf[wp]:
  "\<lbrace>invs and cte_wp_at (op = (cap.UntypedCap w sz idx)) slot 
     and (\<lambda>s. \<forall>cap \<in> set cs. is_cnode_cap cap 
                      \<longrightarrow> (\<forall>r\<in>cte_refs cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s))
    and (\<lambda>s. \<forall>x \<in> set cs. s \<turnstile> x)\<rbrace>
     decode_untyped_invocation label args slot (cap.UntypedCap w sz idx) cs
   \<lbrace>valid_untyped_inv\<rbrace>,-"
proof -
  have inj: "\<And>node_cap s. \<lbrakk>is_cnode_cap node_cap; 
    unat (args ! 5) \<le> 2 ^ bits_of node_cap - unat (args ! 4);valid_cap node_cap s\<rbrakk> \<Longrightarrow>
    inj_on (Pair (obj_ref_of node_cap) \<circ> nat_to_cref (bits_of node_cap))
                      {unat (args ! 4)..<unat (args ! 4) + unat (args ! 5)}"
    apply (simp add:comp_def)
    apply (rule inj_on_split)
    apply (rule subset_inj_on [OF inj_on_nat_to_cref])
     apply (clarsimp simp: is_cap_simps bits_of_def valid_cap_def 
       word_bits_def cap_aligned_def)
     apply clarsimp
     apply (rule less_le_trans)
      apply assumption
     apply (simp add:le_diff_conv2)
    done
  have nasty_strengthen:
    "\<And>S a f s. (\<forall>x\<in>S. cte_wp_at (op = cap.NullCap) (a, f x) s)
    \<Longrightarrow> cte_wp_at (\<lambda>c. c \<noteq> cap.NullCap) slot s
    \<longrightarrow> slot \<notin> (Pair a \<circ> f) ` S"
    by (auto simp:cte_wp_at_caps_of_state)
  show ?thesis
  apply (simp add: decode_untyped_invocation_def unlessE_def[symmetric]
                   unlessE_whenE
           split del: split_if)
  apply (rule validE_R_sp[OF whenE_throwError_sp]
              validE_R_sp[OF data_to_obj_type_sp]
              validE_R_sp[OF dui_sp_helper] validE_R_sp[OF map_ensure_empty])+
  apply clarsimp
  apply (rule hoare_pre)
  apply (wp whenE_throwError_wp[THEN validE_validE_R] check_free_index_wp
            map_ensure_empty_wp)
  apply (clarsimp simp: distinct_map cases_imp_eq)
  apply (subgoal_tac "s \<turnstile> node_cap")
   prefer 2
   apply (erule disjE)
    apply (drule bspec [where x = "cs ! 0"],clarsimp)+
    apply fastforce
   apply clarsimp
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (drule(1) caps_of_state_valid[rotated])+
   apply (clarsimp simp:is_cap_simps diminished_def mask_cap_def 
     cap_rights_update_def ,simp split:cap.splits)
  apply (subgoal_tac "\<forall>r\<in>cte_refs node_cap (interrupt_irq_node s). ex_cte_cap_wp_to is_cnode_cap r s")
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (frule(1) caps_of_state_valid[rotated])
   apply (clarsimp simp:not_less)
   apply (frule(2) inj)
   apply (clarsimp simp:comp_def)
   apply (frule(1) caps_of_state_valid)
   apply (simp add: nasty_strengthen[unfolded o_def] cte_wp_at_caps_of_state)
   apply (intro conjI)
    apply (intro impI)
    apply (frule range_cover_stuff[where rv = 0 and sz = sz])
     apply ((fastforce dest!:valid_cap_aligned simp:cap_aligned_def)+)[4]
    apply (clarsimp simp:valid_cap_simps cap_aligned_def)
    apply (frule alignUp_idem[OF is_aligned_weaken,where a = w])
      apply (erule range_cover.sz)
     apply (simp add:range_cover_def)
    apply (clarsimp simp:get_free_ref_def is_aligned_neg_mask_eq empty_descendants_range_in)
    apply (drule_tac x = "(obj_ref_of node_cap,nat_to_cref (bits_of node_cap) slota)" in bspec)
     apply (clarsimp simp:is_cap_simps nat_to_cref_def word_bits_def
       bits_of_def valid_cap_simps cap_aligned_def)+
   apply (frule(1) range_cover_stuff[where sz = sz])
     apply (clarsimp dest!:valid_cap_aligned simp:cap_aligned_def word_bits_def)+
    apply simp+
   apply (clarsimp simp:get_free_ref_def)
   apply (frule cte_wp_at_caps_descendants_range_inI
     [where ptr = w and sz = sz and idx = 0 and cref = slot])
       apply (clarsimp simp:cte_wp_at_caps_of_state is_aligned_neg_mask_eq)
      apply simp
     apply (simp add:range_cover_def word_bits_def)
    apply (simp add:is_aligned_neg_mask_eq)
   apply (clarsimp)
   apply (erule disjE)
    apply (drule_tac x= "cs!0" in bspec)
     apply clarsimp
    apply simp
   apply (clarsimp simp:cte_wp_at_caps_of_state ex_cte_cap_wp_to_def)
   apply (rule_tac x=aa in exI,rule exI,rule exI)
   apply (rule conjI, assumption)
    apply (clarsimp simp:diminished_def is_cap_simps mask_cap_def
      cap_rights_update_def , simp split:cap.splits )
   done
qed


lemma inj_16:
  "\<lbrakk> of_nat x * 16 = of_nat y * (16 :: word32);
     x < bnd; y < bnd; bnd \<le> 2 ^ (word_bits - 4) \<rbrakk>
     \<Longrightarrow> of_nat x = (of_nat y :: word32)"
  apply (fold shiftl_t2n [where n=4, simplified, simplified mult.commute])
  apply (simp only: word_bl.Rep_inject[symmetric]
                    bl_shiftl)
  apply (drule(1) order_less_le_trans)+
  apply (drule of_nat_mono_maybe[rotated, where 'a=32])
   apply (rule power_strict_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply (drule of_nat_mono_maybe[rotated, where 'a=32])
   apply (rule power_strict_increasing)
    apply (simp add: word_bits_def)
   apply simp
  apply (simp only: word_unat_power[symmetric])
  apply (erule ssubst [OF less_is_drop_replicate])+
  apply (simp add: word_bits_def word_size)
  done


lemma of_nat_shiftR:
  "a < 2 ^ word_bits \<Longrightarrow>
   unat (of_nat (shiftR a b)::word32) = unat ((of_nat a :: word32) >> b)"
  apply (subst shiftr_div_2n')
  apply (clarsimp simp:shiftR_nat)
  apply (subst unat_of_nat32)
   apply (erule le_less_trans[OF div_le_dividend])
  apply (simp add:unat_of_nat32)
  done


lemma valid_untypedD:
  "\<lbrakk> s \<turnstile> cap.UntypedCap ptr bits idx; kheap s p = Some ko; pspace_aligned s\<rbrakk> \<Longrightarrow> 
  obj_range p ko \<inter> cap_range (cap.UntypedCap ptr bits idx) \<noteq> {} \<longrightarrow> 
  (obj_range p ko  \<subseteq> cap_range (cap.UntypedCap ptr bits idx) \<and> obj_range p ko \<inter> usable_untyped_range (cap.UntypedCap ptr bits idx) = {})"
  by (clarsimp simp:valid_untyped_def valid_cap_def cap_range_def obj_range_def)


lemma pspace_no_overlap_detype:
  "\<lbrakk> s \<turnstile> cap.UntypedCap ptr bits idx; pspace_aligned s; valid_objs s \<rbrakk>
     \<Longrightarrow> pspace_no_overlap ptr bits (detype {ptr .. ptr + 2 ^ bits - 1} s)"
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff is_aligned_neg_mask_eq
        simp: obj_range_def add_diff_eq[symmetric] pspace_no_overlap_def
        )
  apply (frule(2) valid_untypedD)
  apply (rule ccontr)
  apply (clarsimp simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff is_aligned_neg_mask_eq 
        simp:valid_cap_def cap_aligned_def obj_range_def cap_range_def is_aligned_neg_mask_eq p_assoc_help)
  apply (drule_tac x= x in set_mp)
   apply simp+
  done


lemma zip_take_length[simp]:
  "zip (take (length ys) xs) ys = zip xs ys"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply simp
  apply simp
  done


lemma int_not_emptyD:
  "\<lbrakk> A\<inter> B = {}; A\<noteq> {};B\<noteq> {}\<rbrakk> \<Longrightarrow> \<not> A \<subset> B \<and> \<not> B\<subset> A \<and> \<not> A = B"
  by auto

lemma subset_not_psubset: " A \<subseteq> B \<Longrightarrow> \<not> B \<subset> A" by clarsimp

lemma mdb_Null_descendants:
  "\<lbrakk> cte_wp_at (op = cap.NullCap) p s; valid_mdb s \<rbrakk> \<Longrightarrow>
      descendants_of p (cdt s) = {}"
  apply (clarsimp simp add: valid_mdb_def cte_wp_at_caps_of_state swp_def)
  apply (erule(1) mdb_cte_at_Null_descendants)
  done

lemma mdb_Null_None:
  "\<lbrakk> cte_wp_at (op = cap.NullCap) p s; valid_mdb s \<rbrakk> \<Longrightarrow>
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
   apply (elim allE, drule(1) mp, clarsimp)
   apply (drule(1) bspec)
   apply (drule has_reply_cap_cte_wpD[OF caps_of_state_cteD])
   apply (erule notE[rotated], strengthen reply_cap_doesnt_exist_strg)
   apply (simp add: st_tcb_def2)
  apply clarsimp
  apply (frule mdb_Null_descendants[OF caps_of_state_cteD])
   apply (simp add: valid_mdb_def reply_mdb_def reply_masters_mdb_def)
  apply simp
  done

lemma more_revokables[simp]:
  "pspace_distinct (is_original_cap_update f s) = pspace_distinct s"
  "pspace_aligned (is_original_cap_update f s) = pspace_aligned s"
  by (simp add: pspace_distinct_def pspace_aligned_def)+


lemma more_mdbs[wp]:
  "\<lbrace>pspace_aligned\<rbrace> set_cdt m \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  "\<lbrace>pspace_distinct\<rbrace> set_cdt m \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  by (simp add: set_cdt_def pspace_aligned_def pspace_distinct_def | wp)+

crunch irq_node[wp]: set_thread_state "\<lambda>s. P (interrupt_irq_node s)"
crunch irq_states[wp]: update_cdt "\<lambda>s. P (interrupt_states s)"
crunch ups[wp]: set_cdt "\<lambda>s. P (ups_of_heap (kheap s))"
crunch cns[wp]: set_cdt "\<lambda>s. P (cns_of_heap (kheap s))"


lemma list_all2_zip_split:
  "\<lbrakk> list_all2 P as cs; list_all2 Q bs ds \<rbrakk> \<Longrightarrow>
   list_all2 (\<lambda>x y. P (fst x) (fst y) \<and> Q (snd x) (snd y))
              (zip as bs) (zip cs ds)"
  apply (induct as arbitrary: bs cs ds)
   apply simp
  apply (case_tac cs, simp+)
  apply (case_tac bs, simp+)
  apply (case_tac ds, simp+)
  done


lemma valid_cap_rvk[simp]:
  "(is_original_cap_update f s) \<turnstile> cap = s \<turnstile> cap"
  by (fastforce elim: valid_cap_pspaceI)


crunch irq_states[wp]: update_cdt "\<lambda>s. P (interrupt_states s)"

crunch ups[wp]: set_cdt "\<lambda>s. P (ups_of_heap (kheap s))"

crunch cns[wp]: set_cdt "\<lambda>s. P (cns_of_heap (kheap s))"


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
  "\<lbrace>pspace_aligned\<rbrace> create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  "\<lbrace>pspace_distinct\<rbrace> create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  "\<lbrace>cte_wp_at P p' and K (p' \<noteq> cref)\<rbrace>
       create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. cte_wp_at P p'\<rbrace>"
  "\<lbrace>valid_objs and valid_cap (default_cap tp oref sz)
            and real_cte_at cref\<rbrace>
       create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  "\<lbrace>valid_cap cap\<rbrace> create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. valid_cap cap\<rbrace>"
  apply (safe intro!: hoare_gen_asm)
      apply (simp_all add: create_cap_def)
      apply (wp set_cap_cte_wp_at' set_cdt_cte_wp_at
                set_cap_valid_objs set_cdt_valid_objs
                set_cdt_valid_cap set_cap_valid_cap
              | simp split del: split_if
                           add: real_cte_tcb_valid)+
  done


lemma default_non_Null[simp]:
  "cap.NullCap \<noteq> default_cap tp oref sz"
  by (cases tp, simp_all)


locale vo_abs = vmdb_abs +
  assumes valid_objs: "valid_objs s"
begin
lemma cs_valid_cap:
  "cs p = Some c \<Longrightarrow> s \<turnstile> c"
  using valid_objs
  apply (simp add: cs_def)
  apply (drule cte_wp_at_valid_objs_valid_cap [rotated, where P="op = c"])
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
  apply (simp add:cap_aligned_def)
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
  "is_untyped_cap (default_cap tp oref sz) \<Longrightarrow>
   cap_bits (default_cap tp oref sz) = sz" 
  by (case_tac tp,simp_all)


lemma untyped_inc':
  assumes inc: "untyped_inc m cs"
  assumes d: "descendants_range (default_cap tp oref sz) src s" 
  assumes r: "untyped_range (default_cap tp oref sz) \<subseteq> untyped_range cap"
  assumes al: "cap_aligned (default_cap tp oref sz)"
  assumes noint: "untyped_range (default_cap tp oref sz) \<inter> usable_untyped_range cap = {}"
  shows "untyped_inc (m(dest \<mapsto> src)) (cs(dest \<mapsto> default_cap tp oref sz))"
  using inc r c_src al ut noint
  unfolding untyped_inc_def descendants_of_def
  apply (intro allI impI)
  apply (rule conjI)
    apply (simp add: parency del: split_paired_All split: split_if_asm)
    apply (rule untyped_ranges_aligned_disjoing_or_subset[OF _ cs_cap_aligned])
     apply simp
    apply simp
    apply (rule untyped_ranges_aligned_disjoing_or_subset[OF cs_cap_aligned _ ])
     apply simp
    apply simp
  apply (case_tac "p' = src")
   apply (simp add: parency del: split_paired_All split: split_if_asm)
      apply (erule_tac x=src in allE)
      apply (erule_tac x=p in allE)
      apply (simp add:c_dest)
     apply (simp add:subseteq_imp_not_subset)
     apply (intro impI)
     apply (drule(1) usable_range_subseteq[OF cs_cap_aligned])
     apply simp
     apply (drule Int_absorb1)
     apply simp
    apply (simp add:c_dest)
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
  apply (simp add: parency del: split_paired_All split: split_if_asm)
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
     apply (rule int_not_emptyD)
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
      apply (simp add:subseteq_imp_not_subset)
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
     apply (clarsimp simp:subseteq_imp_not_subset)
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
  "\<not> is_reply_cap (default_cap otype oref sz)"
  "\<not> is_master_reply_cap (default_cap otype oref sz)"
  by (cases otype, simp_all add: is_cap_simps)+


lemma inter_non_emptyD:
 "\<lbrakk>A \<subseteq> B; A \<inter> C \<noteq> {}\<rbrakk> \<Longrightarrow> B \<inter> C \<noteq> {}"
  by blast


lemma cap_class_default_cap: 
  "cap_class (default_cap tp oref sz) = PhysicalClass"
  apply (case_tac tp)
  apply (simp_all add:default_cap_def arch_default_cap_def split:aobject_type.splits)+
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
                         obj_refs (default_cap tp oref sz) \<subseteq> untyped_range c \<and>
                         untyped_range (default_cap tp oref sz) \<subseteq> untyped_range c
                         \<and> untyped_range (default_cap tp oref sz) \<inter> usable_untyped_range c = {}) p
      and descendants_range (default_cap tp oref sz) p
      and cte_wp_at (op = cap.NullCap) cref
      and K (cap_aligned (default_cap tp oref sz))\<rbrace>
      create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
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
          apply (simp add: is_cap_simps split: split_if_asm)
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
          apply (simp del:split_paired_All add:cap_range_def)
          apply blast
         apply (drule_tac x=ptr in spec)
         apply (drule_tac x=cref in spec)
         apply (simp del:split_paired_All)
         apply (frule(1) inter_non_emptyD[rotated])
         apply (drule_tac c = cap and c' = capa in untyped_incD2)
             apply simp+
         apply (clarsimp simp add:descendants_of_def simp del:split_paired_All)
         apply (drule(1) descendants_rangeD)
         apply (clarsimp simp del:split_paired_All simp: cap_range_def)
         apply blast
        apply (erule(1) mdb_insert_abs.descendants_inc)
         apply simp
        apply (clarsimp simp:is_cap_simps cap_range_def cap_class_default_cap)
       apply (clarsimp simp: no_mloop_def)
       apply (frule_tac p = "(a,b)" and p'="(a,b)" in mdb_insert_abs.parency)
       apply (simp split:split_if_asm)
       apply (erule disjE)
        apply (drule_tac m = "cdt s" in mdb_cte_at_Null_descendants)
         apply (clarsimp simp:untyped_mdb_def)
        apply (clarsimp simp:descendants_of_def simp del:split_paired_All)
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
  apply (subgoal_tac "\<And>t m. default_cap tp oref sz \<noteq> cap.ReplyCap t m")
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
  done

lemma create_cap_descendants_range[wp]:
 "\<lbrace>descendants_range c p and 
   K (cap_range c \<inter> cap_range (default_cap tp oref sz) = {}) and
   cte_wp_at (op \<noteq> cap.NullCap) p and
   cte_wp_at (op = cap.NullCap) cref and 
   valid_mdb\<rbrace> 
  create_cap tp sz p (cref,oref) 
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
  apply (simp add:caps_overlap_reserved_def)
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
   K (cap_range c \<inter> cap_range (default_cap tp oref sz) = {}) and
   cte_wp_at (op \<noteq> cap.NullCap) p and
   cte_wp_at (op = cap.NullCap) cref and 
   valid_mdb and K (cap_aligned (default_cap tp oref sz))\<rbrace> 
  create_cap tp sz p (cref,oref) 
  \<lbrace>\<lambda>rv s. caps_overlap_reserved (untyped_range c) s\<rbrace>"
  apply (simp add: create_cap_def caps_overlap_reserved_def cte_wp_at_caps_of_state set_cdt_def)
  apply (wp set_cap_caps_of_state2 | simp del: fun_upd_apply)+
  apply (clarsimp simp: ran_def split:if_splits)
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
  "\<lbrace>invs and pspace_no_overlap ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty \<lbrace>\<lambda>rv. pspace_aligned\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. valid_objs\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap ptr sz and caps_no_overlap ptr sz 
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. pspace_distinct\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap ptr sz and caps_no_overlap ptr sz 
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. valid_mdb\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap ptr sz and caps_no_overlap ptr sz
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. valid_global_objs\<rbrace>"
  "\<lbrace>invs and pspace_no_overlap ptr sz and caps_no_overlap ptr sz 
     and caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api ty us - 1}
     and region_in_kernel_window {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
     and K (ty = CapTableObject \<longrightarrow> 0 < us)
     and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
      retype_region ptr n us ty \<lbrace>\<lambda>rv. valid_arch_state\<rbrace>"
  apply (wp hoare_strengthen_post [OF retype_region_post_retype_invs],
    auto simp: post_retype_invs_def split: split_if_asm)+
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


lemma asid_bits_ge_0: "(0::word32) < 2 ^ asid_bits" by (simp add: asid_bits_def)


lemma retype_ret_valid_caps:
  "\<lbrace>pspace_no_overlap ptr sz
      and K (tp = Structures_A.CapTableObject \<longrightarrow> us > 0)
      and K (tp = Untyped \<longrightarrow> us \<ge> 4)
      and K (tp \<noteq> ArchObject ASIDPoolObj)
      and K (range_cover ptr sz (obj_bits_api tp us) n \<and> ptr \<noteq> 0)\<rbrace>
        retype_region ptr n us tp \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. s \<turnstile> default_cap tp y us\<rbrace>"
  apply (simp add: retype_region_def split del: split_if cong: if_cong)
  apply wp
  apply (simp only: trans_state_update[symmetric] more_update.valid_cap_update)
  apply wp
  apply (case_tac tp,simp_all)
   defer
      apply ((clarsimp simp:valid_cap_def default_object_def cap_aligned_def 
        cte_level_bits_def slot_bits_def is_obj_defs well_formed_cnode_n_def empty_cnode_def
        dom_def arch_default_cap_def ptr_add_def | rule conjI | intro conjI obj_at_foldr_intro imageI
      | rule is_aligned_add_multI[OF _ le_refl],
        (simp add:range_cover_def word_bits_def obj_bits_api_def slot_bits_def)+)+)[4]
    apply (rename_tac aobject_type)
    apply (case_tac aobject_type)
      apply (clarsimp simp:valid_cap_def default_object_def cap_aligned_def 
        cte_level_bits_def slot_bits_def is_obj_defs well_formed_cnode_n_def empty_cnode_def
        dom_def arch_default_cap_def ptr_add_def | intro conjI obj_at_foldr_intro
        imageI valid_vm_rights_def
      | rule is_aligned_add_multI[OF _ le_refl]
      | fastforce simp:range_cover_def obj_bits_api_def
        default_arch_object_def valid_vm_rights_def  word_bits_def a_type_def)+
  apply (clarsimp simp:valid_cap_def valid_untyped_def)
  apply (drule(2) pspace_no_overlap_obj_range[OF _ _ range_cover_cell_subset])
   apply (erule of_nat_mono_maybe[rotated])
    apply (drule range_cover.range_cover_n_less)
    apply (simp add:word_bits_def)
  apply (simp add:obj_bits_api_def)
  apply (erule(2) range_cover_no_0)
 done


lemma set_zip_helper:
  "t \<in> set (zip xs ys) \<Longrightarrow> fst t \<in> set xs \<and> snd t \<in> set ys"
  by (clarsimp simp add: set_zip)


lemma silly_helpers:
  "n < 32 \<Longrightarrow> n < word_bits"
  "word_bits - (pageBits + n) < 32"
  by (simp_all add: word_bits_def pageBits_def)


lemma two_power_increasing_less_1:
  "\<lbrakk> n \<le> m; m \<le> len_of TYPE('a)\<rbrakk> \<Longrightarrow> (2 :: 'a  :: len word) ^ n - 1 \<le> 2 ^ m - 1"
  apply (cases "m = len_of TYPE('a)")
   apply simp
  apply (rule word_sub_mono)
     apply (simp add: word_le_nat_alt)
    apply simp
   apply (rule order_less_imp_le)
   apply (rule word_power_less_1)
   apply simp
  apply (rule order_less_imp_le)
  apply (rule word_power_less_1)
  apply simp
  done


lemma word_sub_mono3:
  "\<lbrakk> x + y \<le> x + z; (x :: ('a :: len) word) \<le> x + y; x \<le> x + z \<rbrakk> \<Longrightarrow> y \<le> z"
  apply (subst(asm) add.commute)
  apply (subst(asm) add.commute,
         erule word_sub_mono2)
    apply simp
   apply (subst add.commute, subst olen_add_eqv, simp add: add.commute)
  apply (subst add.commute, subst olen_add_eqv, simp add: add.commute)
  done


lemma word_sub_mono4:
  "\<lbrakk> y + x \<le> z + x; (y :: ('a :: len) word) \<le> y + x; z \<le> z + x \<rbrakk> \<Longrightarrow> y \<le> z"
  apply (subst(asm) add.commute)
  apply (subst(asm) add.commute,
         erule word_sub_mono2)
    apply simp
   apply (simp add: add.commute)+
  done


lemma eq_or_less_helperD:
  "\<lbrakk> n = unat (2 ^ m - 1 :: 'a :: len word) \<or> n < unat (2 ^ m - 1 :: 'a word); m < len_of TYPE('a) \<rbrakk> \<Longrightarrow> n < 2 ^ m"
  apply (simp add: unat_sub word_1_le_power)
  apply (subgoal_tac "2 ^ m \<ge> (1 :: nat)")
   apply arith
  apply simp
  done


lemma of_nat_shift_distinct_helper:
  "\<lbrakk> x < bnd; y < bnd; x \<noteq> y; (of_nat x :: 'a :: len word) << n = of_nat y << n;
        n < len_of TYPE('a); bnd \<le> 2 ^ (len_of TYPE('a) - n) \<rbrakk>
     \<Longrightarrow> P"
  apply (cases "n = 0")
   apply (simp add: word_unat.Abs_inject unats_def)
  apply (subgoal_tac "bnd < 2 ^ len_of TYPE('a)")
   apply (erule(1) shift_distinct_helper[rotated, rotated, rotated])
      defer
      apply (erule(1) of_nat_mono_maybe[rotated])
     apply (erule(1) of_nat_mono_maybe[rotated])
    apply (simp add: word_unat.Abs_inject unats_def)
   apply (erule order_le_less_trans)
   apply (rule power_strict_increasing)
    apply simp
   apply simp
  apply (simp add: word_less_nat_alt)
  apply (simp add: unat_minus_one [OF of_nat_neq_0]
                   word_unat.Abs_inverse unats_def)
  done


lemmas of_nat_shift_distinct_helper32 = of_nat_shift_distinct_helper[where 'a=32, folded word_bits_def]


lemma ptr_add_distinct_helper:
  "\<lbrakk> ptr_add (p :: word32) (x * 2 ^ n) = ptr_add p (y * 2 ^ n); x \<noteq> y;
     x < bnd; y < bnd; n < word_bits;
     bnd \<le> 2 ^ (word_bits - n) \<rbrakk>
     \<Longrightarrow> P"
  apply (clarsimp simp: ptr_add_def word_unat_power[symmetric]
                        shiftl_t2n[symmetric, simplified mult.commute])
  apply (erule(5) of_nat_shift_distinct_helper32)
  done


lemma ex_cte_cap_protects:
  "\<lbrakk> ex_cte_cap_wp_to P p s; cte_wp_at (op = (cap.UntypedCap ptr bits idx)) p' s;
     descendants_range_in S p' s; untyped_children_in_mdb s; S\<subseteq> untyped_range (cap.UntypedCap ptr bits idx);
     valid_global_refs s \<rbrakk>
      \<Longrightarrow> fst p \<notin> S"
  apply (drule ex_cte_cap_to_obj_ref_disj, erule disjE)
   apply clarsimp
   apply (erule(1) untyped_children_in_mdbEE[where P="\<lambda>c. fst p \<in> obj_refs c" for c])
      apply simp
     apply assumption
    apply (rule notemptyI[where x="fst p"])
    apply (clarsimp simp del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
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
  "tp \<noteq> Untyped \<Longrightarrow> untyped_range (default_cap tp sz us) = {}"
  by (cases tp, auto)


lemma obj_refs_default_cap:
  "obj_refs (default_cap tp oref sz) \<subseteq> {oref}"
  apply (cases tp, simp_all)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all add: arch_default_cap_def)
  done


lemma obj_refs_default_nut:
  "tp \<noteq> Untyped \<Longrightarrow> obj_refs (default_cap tp oref sz) = {oref}"
  apply (cases tp, simp_all)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all add: arch_default_cap_def)
  done


lemma range_cover_subset':
  "\<lbrakk>range_cover ptr sz sbit n; n \<noteq> 0\<rbrakk>
  \<Longrightarrow> {ptr ..ptr + of_nat n * 2 ^ sbit - 1} \<subseteq> {ptr..(ptr && ~~ mask sz) + 2^ sz - 1}"
  apply clarsimp
  apply (frule range_cover_cell_subset[OF _ of_nat_mono_maybe,where Y1 = "(n - 1)"])
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


lemma retype_region_ranges':
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) n)\<rbrace>
   retype_region ptr n us tp
   \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. cap_range (default_cap tp y us) \<subseteq> {ptr..ptr + of_nat (n * 2 ^ (obj_bits_api tp us)) - 1}\<rbrace>"
  apply (simp add:valid_def)
  apply clarify
  apply (drule use_valid[OF _ retype_region_ret])
  apply simp
  apply (clarsimp simp del:atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
        Int_atLeastAtMost atLeastatMost_empty_iff)
    apply (rule subsetD[OF subset_trans])
      apply (rule range_cover_subset,assumption)
      apply clarsimp
       apply assumption
      apply fastforce
    apply simp
  apply (case_tac tp)
      apply (simp_all add:cap_range_def obj_bits_api_def ptr_add_def)+
      apply (subst add.commute[where a = "0x1FF"])
      apply (rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
       apply (fastforce simp:range_cover_def)
       apply (simp add:word_bits_def is_aligned_mult_triv2[where n = 9,simplified])+
     apply (subst add.commute[where a = "0xF"])
     apply (rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
      apply (fastforce simp:range_cover_def)
      apply (simp add:word_bits_def is_aligned_mult_triv2[where n = 4,simplified])+
    apply (subst add.commute[where a = "0xF"])
    apply (rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
     apply (fastforce simp:range_cover_def)
     apply (simp add:word_bits_def is_aligned_mult_triv2[where n = 4,simplified])+
     apply (clarsimp simp:is_aligned_def)
    apply (simp add:p_assoc_help)
    apply (rule is_aligned_no_wrap'[OF aligned_add_aligned[OF _ _ le_refl]])
    apply (fastforce simp:range_cover_def)
    apply (rule is_aligned_mult_triv2)
     apply (simp add:range_cover_def)
   apply (drule sym)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type)
   apply (simp_all add: aobj_ref_def arch_default_cap_def p_assoc_help)
   apply ((rule is_aligned_no_wrap'[OF is_aligned_add_multI[OF _ le_refl refl]],
     (simp add:range_cover_def arch_kobj_size_def)+)[1])+
  done


lemma retype_region_ranges:
  "\<lbrace>cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr_base) p and 
    pspace_no_overlap ptr sz and
    valid_pspace and K (ptr_base = ptr && ~~ mask sz) and K (range_cover ptr sz (obj_bits_api tp us) n)
   \<rbrace> 
  retype_region ptr n us tp
   \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. cte_wp_at
           (\<lambda>c. cap_range (default_cap tp y us) \<subseteq> untyped_range c )
           p s\<rbrace>"
   apply (clarsimp simp:cte_wp_at_caps_of_state valid_def)
   apply (frule_tac P1 = "op = cap" in use_valid[OF _ retype_region_cte_at_other])
     apply simp
    apply (fastforce simp:cte_wp_at_caps_of_state)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
   apply (frule use_valid[OF _ retype_region_ranges'])
    apply (fastforce simp:cte_wp_at_caps_of_state)
   apply (drule(1) bspec)
   apply (drule(1) subsetD)
   apply (rule_tac A = "{x..y}" for x y in subsetD[rotated])
   apply assumption
   apply simp
   apply (erule subset_trans[OF range_cover_subset'])
    apply (frule use_valid[OF _ retype_region_ret])
    apply simp
    apply fastforce
   apply (clarsimp simp:is_cap_simps)
   apply (erule order_trans[OF word_and_le2])
   done


lemma map_snd_zip_prefix_help: 
  "map (\<lambda>tup. cap_range (default_cap tp (snd tup) us)) (zip xs ys) \<le>
   map (\<lambda>x. cap_range (default_cap tp x us)) ys"
  apply (induct xs arbitrary: ys)
   apply simp
  apply (case_tac ys)
   apply auto
  done


lemma retype_region_distinct_sets:
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) n)\<rbrace> 
  retype_region ptr n us tp 
  \<lbrace>\<lambda>rv s. distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) us)) (zip xs rv))\<rbrace>"
  apply (simp add: distinct_sets_prop)
  apply (rule hoare_gen_asm[where P'="\<top>", simplified])
  apply (rule hoare_strengthen_post [OF retype_region_ret])
  apply (rule distinct_prop_prefixE [rotated])
   apply (rule map_snd_zip_prefix_help [unfolded less_eq_list_def])
  apply (clarsimp simp: retype_addrs_def distinct_prop_map)
  apply (rule distinct_prop_distinct)
   apply simp
  apply (subgoal_tac  "of_nat y * (2::word32) ^ obj_bits_api tp us \<noteq> of_nat x * 2 ^ obj_bits_api tp us")
   apply (case_tac tp) defer
        apply (simp add:cap_range_def ptr_add_def)+
    apply (rename_tac aobject_type)
    apply (case_tac aobject_type)
          apply (simp add:ptr_add_def aobj_ref_def arch_default_cap_def)+
   apply (clarsimp simp: ptr_add_def word_unat_power[symmetric]
                      shiftl_t2n[simplified mult.commute, symmetric])
   apply (erule(2) of_nat_shift_distinct_helper[where 'a=32 and n = "obj_bits_api tp us"])
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


lemma copy_global_mappings_hoare_lift:
  assumes wp: "\<And>ptr val. \<lbrace>Q\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv. Q\<rbrace>"
  shows       "\<lbrace>Q\<rbrace> copy_global_mappings pd \<lbrace>\<lambda>rv. Q\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (wp mapM_x_wp' wp)
  done


lemma init_arch_objects_hoare_lift:
  assumes wp: "\<And>oper. \<lbrace>P\<rbrace> do_machine_op oper \<lbrace>\<lambda>rv :: unit. Q\<rbrace>"
              "\<And>ptr val. \<lbrace>P\<rbrace> store_pde ptr val \<lbrace>\<lambda>rv. P\<rbrace>"
  shows       "\<lbrace>P and Q\<rbrace> init_arch_objects tp ptr sz us adds \<lbrace>\<lambda>rv. Q\<rbrace>"
proof -
  have pres: "\<And>oper. \<lbrace>P and Q\<rbrace> do_machine_op oper \<lbrace>\<lambda>rv :: unit. Q\<rbrace>"
             "\<lbrace>P and Q\<rbrace> return () \<lbrace>\<lambda>rv. Q\<rbrace>"
    by (wp wp | simp)+
  show ?thesis
    apply (simp add: init_arch_objects_def create_word_objects_def
                  pres reserve_region_def
           split: Structures_A.apiobject_type.split
                  Arch_Structs_A.aobject_type.split)
    apply clarsimp
    apply (rule hoare_pre)
     apply (wp mapM_x_wp' copy_global_mappings_hoare_lift wp)
    apply simp
    done
qed


declare dmo_aligned [wp]


crunch pdistinct[wp]: do_machine_op "pspace_distinct"

crunch vmdb[wp]: do_machine_op "valid_mdb"

crunch mdb[wp]: do_machine_op "\<lambda>s. P (cdt s)"
crunch cte_wp_at[wp]: do_machine_op "\<lambda>s. P (cte_wp_at P' p s)"

lemmas dmo_valid_cap[wp] = valid_cap_typ [OF do_machine_op_obj_at]


lemma cap_refs_in_kernel_windowD2:
  "\<lbrakk> cte_wp_at P p s; cap_refs_in_kernel_window s \<rbrakk>
       \<Longrightarrow> \<exists>cap. P cap \<and> region_in_kernel_window (cap_range cap) s"
  apply (clarsimp simp: cte_wp_at_caps_of_state region_in_kernel_window_def)
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply fastforce
  done

(* FIXME: move *)
lemma delete_objects_pspace_no_overlap[wp]:
  "\<lbrace>valid_cap (cap.UntypedCap ptr bits idx) and pspace_aligned and valid_objs\<rbrace>
   delete_objects ptr bits
   \<lbrace>\<lambda>_. pspace_no_overlap ptr bits\<rbrace>"
  apply (unfold delete_objects_def)
  apply wp
  apply (simp add: do_machine_op_def split_def)
  apply wp
  apply (clarsimp simp: pspace_no_overlap_detype)
  done

lemma retype_region_descendants_range:
  "\<lbrace>\<lambda>s. descendants_range x cref s 
    \<and> pspace_no_overlap ptr sz s \<and> valid_pspace s 
    \<and> range_cover ptr sz (obj_bits_api ty us) n\<rbrace> retype_region ptr n us ty
          \<lbrace>\<lambda>rv s. descendants_range x cref s\<rbrace>"
  apply (simp add:descendants_range_def)
  apply (rule hoare_pre)
  apply (wps retype_region_mdb)
  apply (wp hoare_vcg_ball_lift retype_cte_wp_at)
  apply fastforce
  done

lemma init_arch_objects_descendants_range[wp]:
  "\<lbrace>\<lambda>s. descendants_range x cref s \<rbrace> init_arch_objects ty ptr n us y
          \<lbrace>\<lambda>rv s. descendants_range x cref s\<rbrace>"
  apply (simp add:descendants_range_def)
  apply (rule hoare_pre)
   apply (wp retype_region_mdb init_arch_objects_hoare_lift)
    apply (wps do_machine_op_mdb)
    apply (wp hoare_vcg_ball_lift)
   apply (rule hoare_pre)
    apply (wps store_pde_mdb_inv)
    apply wp
   apply simp
  apply fastforce
  done

lemma init_arch_objects_caps_overlap_reserved[wp]:
  "\<lbrace>\<lambda>s. caps_overlap_reserved S s\<rbrace>
   init_arch_objects ty ptr n us y
   \<lbrace>\<lambda>rv s. caps_overlap_reserved S s\<rbrace>"
  apply (simp add:caps_overlap_reserved_def)
  apply (rule hoare_pre)
   apply (wp retype_region_mdb init_arch_objects_hoare_lift)
  apply fastforce
  done


lemma retype_region_descendants_range_ret:
  "\<lbrace>\<lambda>s. (range_cover ptr sz (obj_bits_api ty us) n) 
    \<and> pspace_no_overlap ptr sz s 
    \<and> valid_pspace s 
    \<and> range_cover ptr sz (obj_bits_api ty us) n
    \<and> descendants_range_in {ptr..ptr + of_nat n * 2^(obj_bits_api ty us) - 1} cref s
  \<rbrace>
  retype_region ptr n us ty
          \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. descendants_range (default_cap ty y us) cref s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:valid_def)
  apply (frule retype_region_ret[unfolded valid_def,simplified,THEN spec,THEN bspec])
  apply clarsimp
  apply (erule use_valid[OF _ retype_region_descendants_range])
  apply (intro conjI,simp_all)
   apply (clarsimp simp:descendants_range_def descendants_range_in_def)
  apply (drule(1) bspec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (erule disjoint_subset2[rotated])
  apply (frule(1) range_cover_subset)
   apply simp
  apply (erule subset_trans[rotated])
  apply (subgoal_tac "ptr + of_nat p * 2 ^ obj_bits_api ty us 
          \<le> ptr + of_nat p * 2 ^ obj_bits_api ty us + 2 ^ obj_bits_api ty us - 1")
   prefer 2
   apply (rule is_aligned_no_overflow)
     apply (rule is_aligned_add_multI)
        apply (fastforce simp:range_cover_def)+
  apply (case_tac ty,simp_all add:cap_range_def ptr_add_def obj_bits_api_def)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type,
    simp_all add:cap_range_def aobj_ref_def arch_default_cap_def default_arch_object_def)
  done


lemma caps_overlap_reserved_def2: 
  "caps_overlap_reserved S =
   (\<lambda>s. (\<forall>cap \<in> ran (null_filter (caps_of_state s)).
           is_untyped_cap cap \<longrightarrow> usable_untyped_range cap \<inter> S = {}))"
  apply (rule ext)
  apply (clarsimp simp:caps_overlap_reserved_def)
  apply (intro iffI ballI impI)
    apply (elim ballE impE)
      apply simp
     apply simp
    apply (simp add:ran_def null_filter_def split:split_if_asm option.splits)    
  apply (elim ballE impE)
    apply simp
   apply simp
  apply (clarsimp simp:ran_def null_filter_def is_cap_simps 
    simp del:split_paired_All split_paired_Ex split:if_splits)
  apply (drule_tac x = "(a,b)" in spec)
  apply simp
  done


lemma set_cap_valid_mdb_simple:
  "\<lbrace>\<lambda>s. valid_objs s \<and> valid_mdb s \<and> descendants_range_in {ptr .. ptr+2^sz - 1} cref s 
   \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr) cref s\<rbrace>
  set_cap (cap.UntypedCap ptr sz idx) cref
 \<lbrace>\<lambda>rv s'. valid_mdb s'\<rbrace>"
  apply (simp add:valid_mdb_def)
  apply (rule hoare_pre)
  apply (wp set_cap_mdb_cte_at)
  apply (wps set_cap_rvk_cdt_ct_ms)
  apply wp
  apply (clarsimp simp:cte_wp_at_caps_of_state is_cap_simps 
    reply_master_revocable_def irq_revocable_def reply_mdb_def)
  unfolding fun_upd_def[symmetric]
  apply clarsimp
  proof(intro conjI impI)
  fix s r bits f
  assume obj:"valid_objs s"
  assume mdb:"untyped_mdb (cdt s) (caps_of_state s)"
  assume cstate:"caps_of_state s cref = Some (cap.UntypedCap r bits f)" (is "?m cref = Some ?srccap")
  show "untyped_mdb (cdt s) (caps_of_state s(cref \<mapsto> cap.UntypedCap r bits idx))"
  apply (rule untyped_mdb_update_free_index
     [where capa = ?srccap and m = "caps_of_state s" and src = cref,
       unfolded free_index_update_def,simplified,THEN iffD2])
   apply (simp add:cstate mdb)+
  done
  assume inc: "untyped_inc (cdt s) (caps_of_state s)"
  assume drange: "descendants_range_in {r..r + 2 ^ bits - 1} cref s"
  have untyped_range_simp: "untyped_range (cap.UntypedCap r bits f) = untyped_range (cap.UntypedCap r bits idx)"
    by simp
  note blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  show "untyped_inc (cdt s) (caps_of_state s(cref \<mapsto> cap.UntypedCap r bits idx))"
  using inc cstate drange
  apply (unfold untyped_inc_def)
   apply (intro allI impI)
   apply (drule_tac x = p in spec)
   apply (drule_tac x = p' in spec)
   apply (case_tac "p = cref")
    apply (simp)
    apply (case_tac "p' = cref")
     apply simp
    apply (simp add:untyped_range_simp)
    apply (intro conjI impI)
     apply (simp)
     apply (elim conjE)
     apply (thin_tac "Q \<longrightarrow> P" for P Q)+
     apply (frule(2) descendants_range_inD[rotated])
     apply (drule caps_of_state_valid_cap[OF _ obj])
     apply (drule sym)
     apply (rule disjoint_subset2[OF usable_range_subseteq])
     apply (simp add:valid_cap_def cap_aligned_def untyped_range.simps)+
    apply (elim disjE conjE)
     apply (frule(2) descendants_range_inD[rotated])
     apply (drule caps_of_state_valid_cap[OF _ obj])+
     apply (drule sym)
     apply (simp add:untyped_range.simps)
     apply (drule(1) untyped_range_non_empty[OF _ valid_cap_aligned])
     apply simp+
  apply (case_tac "p' = cref")
   apply simp
   apply (intro conjI)
      apply (elim conjE)
      apply (thin_tac "P\<longrightarrow>Q" for P Q)+
      apply (simp add:untyped_range_simp)+
     apply (intro impI)
     apply (elim conjE | simp)+
     apply (thin_tac "P\<longrightarrow>Q" for P Q)+
     apply (frule(2) descendants_range_inD[rotated])
     apply (drule caps_of_state_valid_cap[OF _ obj])
     apply (drule sym)
     apply (rule disjoint_subset2[OF usable_range_subseteq])
     apply ((clarsimp simp:valid_cap_def cap_aligned_def untyped_range.simps)+)[3]
    apply (intro impI)
    apply (elim conjE subset_splitE | simp)+
        apply (thin_tac "P\<longrightarrow>Q" for P Q)+
        apply (clarsimp simp:untyped_range.simps)
      apply simp
      apply (elim conjE)
      apply (thin_tac "P\<longrightarrow>Q" for P Q)+
      apply (clarsimp simp:untyped_range.simps)
     apply simp
     apply (erule disjE)
      apply (clarsimp simp:blah)
     apply (clarsimp simp:blah)
    apply (drule_tac t = c' in sym)
    apply (simp add:untyped_range.simps)
   apply (drule_tac t= c' in sym)
   apply (intro impI)
   apply (simp add:untyped_range.simps)
   apply (elim disjE conjE)
    apply simp
   apply (frule(2) descendants_range_inD[rotated])
   apply (drule caps_of_state_valid_cap[OF _ obj])+
   apply simp
   apply (drule(1) untyped_range_non_empty[OF _ valid_cap_aligned])
   apply simp+
  done
  assume "ut_revocable (is_original_cap s) (caps_of_state s)"
  thus "ut_revocable (is_original_cap s) (caps_of_state s(cref \<mapsto> cap.UntypedCap r bits idx))"
  using cstate
  by (fastforce simp:ut_revocable_def)
  assume "reply_caps_mdb (cdt s) (caps_of_state s)"
  thus "reply_caps_mdb (cdt s) (caps_of_state s(cref \<mapsto> cap.UntypedCap r bits idx))"
  using cstate
  apply (simp add:reply_caps_mdb_def del:split_paired_All split_paired_Ex)
  apply (intro allI impI conjI)
   apply (drule spec)+
   apply (erule(1) impE)
  apply (erule exE)
  apply (rule_tac x = ptr' in exI)
  apply simp+
  apply clarsimp
  done
  assume "reply_masters_mdb (cdt s) (caps_of_state s)"
  thus "reply_masters_mdb (cdt s) (caps_of_state s(cref \<mapsto> cap.UntypedCap r bits idx))"
   apply (simp add:reply_masters_mdb_def del:split_paired_All split_paired_Ex)
   apply (intro allI impI ballI)
   apply (erule exE)
   apply (elim allE impE)
    apply simp
   using cstate
   apply clarsimp
   done
  assume misc:
    "mdb_cte_at (swp (cte_wp_at (op \<noteq> cap.NullCap)) s) (cdt s)"
    "descendants_inc (cdt s) (caps_of_state s)"
    "caps_of_state s cref = Some (cap.UntypedCap r bits f)"
  thus "descendants_inc (cdt s) (caps_of_state s(cref \<mapsto> cap.UntypedCap r bits idx))"
   apply -
   apply (erule descendants_inc_minor)
    apply (clarsimp simp:swp_def cte_wp_at_caps_of_state)
   apply (clarsimp simp:untyped_range.simps)
   done
 qed

lemma set_free_index_valid_pspace_simple:
  "\<lbrace>\<lambda>s. valid_mdb s \<and> valid_pspace s \<and> pspace_no_overlap ptr sz s \<and> descendants_range_in {ptr .. ptr+2^sz - 1} cref s 
   \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr) cref s \<and> idx \<le> 2^ sz\<rbrace>
  set_cap (cap.UntypedCap ptr sz idx) cref
 \<lbrace>\<lambda>rv s'. valid_pspace s'\<rbrace>"
  apply (clarsimp simp:valid_pspace_def)
  apply (wp set_cap_valid_objs update_cap_iflive set_cap_zombies')
   apply (clarsimp simp:cte_wp_at_caps_of_state is_cap_simps)+
  apply (frule(1) caps_of_state_valid_cap)
  apply (clarsimp simp:valid_cap_def cap_aligned_def )
  apply (intro conjI)
  defer
  apply (clarsimp simp add:pred_tcb_at_def tcb_cap_valid_def obj_at_def is_tcb
          valid_ipc_buffer_cap_def split: option.split)
  apply (rule exI)
  apply (intro conjI)
    apply fastforce
   apply (drule caps_of_state_cteD)
   apply (clarsimp simp:cte_wp_at_cases)
   apply (erule(1) valid_objsE)
   apply (drule_tac m = "tcb_cap_cases" in ranI)
   apply (clarsimp simp:valid_obj_def valid_tcb_def)
   apply (drule(1) bspec)
   apply (auto simp:tcb_cap_cases_def is_cap_simps split:Structures_A.thread_state.splits)[1]
  apply (simp add:valid_untyped_def)
  apply (intro impI allI)
  apply (elim allE allE impE)
    apply simp+
  apply (drule(1) pspace_no_overlapD3)
   apply (drule(1) valid_cap_aligned[OF caps_of_state_valid_cap])
   apply (simp add:valid_cap_simps)
  apply simp
  done

lemma set_untyped_cap_invs_simple:
  "\<lbrace>\<lambda>s. descendants_range_in {ptr .. ptr+2^sz - 1} cref s \<and> pspace_no_overlap ptr sz s \<and> invs s 
  \<and> cte_wp_at (\<lambda>c. is_untyped_cap c \<and> cap_bits c = sz \<and> obj_ref_of c = ptr) cref s \<and> idx \<le> 2^ sz\<rbrace>
  set_cap (cap.UntypedCap ptr sz idx) cref
 \<lbrace>\<lambda>rv s. invs s\<rbrace>"
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_def valid_state_def)
  apply (rule hoare_pre)
  apply (wp set_free_index_valid_pspace_simple set_cap_valid_mdb_simple
    set_cap_idle update_cap_ifunsafe)
  apply (simp add:valid_irq_node_def)
  apply wps
  apply (wp hoare_vcg_all_lift set_cap_irq_handlers set_cap_arch_objs set_cap_valid_arch_caps
    set_cap.valid_global_objs set_cap_irq_handlers cap_table_at_lift_valid set_cap_typ_at )
  apply (clarsimp simp:cte_wp_at_caps_of_state is_cap_simps)
  apply (intro conjI,clarsimp)
        apply (rule ext,clarsimp simp:is_cap_simps)
       apply (clarsimp split:cap.splits simp:is_cap_simps appropriate_cte_cap_def)
      apply (drule(1) if_unsafe_then_capD[OF caps_of_state_cteD])
       apply clarsimp
      apply (clarsimp simp:is_cap_simps ex_cte_cap_wp_to_def appropriate_cte_cap_def cte_wp_at_caps_of_state)
     apply (clarsimp dest!:valid_global_refsD2 simp:cap_range_def)
    apply (simp add:valid_irq_node_def)
   apply (clarsimp simp:valid_irq_node_def)
  apply (clarsimp simp:no_cap_to_obj_with_diff_ref_def cte_wp_at_caps_of_state vs_cap_ref_def)
  apply (case_tac cap)
   apply (simp_all add:vs_cap_ref_def table_cap_ref_def)
  apply (rename_tac arch_cap)
  apply (case_tac arch_cap)
   apply simp_all
  apply (clarsimp simp:cap_refs_in_kernel_window_def
              valid_refs_def simp del:split_paired_All)
  apply (drule_tac x = cref in spec)
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply fastforce
  done

lemma set_untyped_cap_caps_overlap_reserved:
  "\<lbrace>\<lambda>s. invs s \<and> S \<subseteq> {ptr..ptr + 2 ^ sz - 1} \<and>
  usable_untyped_range (cap.UntypedCap ptr sz idx') \<inter> S = {} \<and> 
  descendants_range_in S cref s \<and> cte_wp_at (op = (cap.UntypedCap ptr sz idx)) cref s\<rbrace>
  set_cap (cap.UntypedCap ptr sz idx') cref
 \<lbrace>\<lambda>rv s. caps_overlap_reserved S s\<rbrace>"
  apply (unfold caps_overlap_reserved_def)
  apply wp
  apply (clarsimp simp: cte_wp_at_caps_of_state caps_overlap_reserved_def 
    simp del:usable_untyped_range.simps split:split_if_asm)
  apply (frule invs_mdb)
  apply (erule ranE)
  apply (simp split:split_if_asm del:usable_untyped_range.simps add:valid_mdb_def)
  apply (drule untyped_incD)
   apply ((simp add:is_cap_simps)+)[4]
  apply clarify
  apply (erule subset_splitE)
     apply (simp del:usable_untyped_range.simps)
     apply (thin_tac "P \<longrightarrow> Q" for P Q)+
     apply (elim conjE)
     apply blast
    apply (simp del:usable_untyped_range.simps)
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
  apply (simp add:caps_no_overlap_def)
  apply wp
  apply (clarsimp simp:cte_wp_at_caps_of_state caps_no_overlap_def
    simp del: atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff )
  apply (erule ranE)
  apply (simp split:if_splits
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
  apply (clarsimp simp:caps_of_state_detype caps_overlap_reserved_def )
  apply (erule ranE)
  apply (clarsimp split:if_splits)
  apply (drule bspec)
   apply fastforce
  apply simp
  done


lemma caps_no_overlap_detype:
  "caps_no_overlap ptr sz s \<Longrightarrow> caps_no_overlap ptr sz (detype H s)"
   apply (clarsimp simp:caps_of_state_detype caps_no_overlap_def)
   apply (erule ranE)
   apply (clarsimp split:if_splits)
   apply (drule bspec,fastforce)
   apply clarsimp
   apply (erule subsetD)
   apply simp
   done


lemma not_inD:"\<lbrakk>x \<notin> A; y \<in> A\<rbrakk> \<Longrightarrow>x \<noteq> y"
  by clarsimp


lemma caps_of_state_no_overlapD:
  "\<lbrakk>caps_of_state s slot = Some cap; valid_objs s; pspace_aligned s;
    pspace_no_overlap ptr sz s\<rbrakk> 
   \<Longrightarrow> (fst slot) \<notin> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}"
  apply (drule caps_of_state_cteD)
  apply (clarsimp simp:cte_wp_at_cases obj_at_def 
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
          del:atLeastAtMost_iff atLeastatMost_subset_iff 
          atLeastLessThan_iff Int_atLeastAtMost)
  apply clarify
  apply (frule(2) p_in_obj_range)
  apply (erule(1) pspace_no_overlapE)
  apply (drule(1) IntI)
  unfolding obj_range_def
  apply (drule notemptyI)+
  apply (simp add: Int_ac p_assoc_help add.commute
         del:atLeastAtMost_iff atLeastatMost_subset_iff 
         atLeastLessThan_iff Int_atLeastAtMost)
  done


lemma op_equal: "(\<lambda>x. x = c) = (op = c)" by (rule ext) auto


lemma mask_out_eq_0:
  "\<lbrakk>idx < 2^ sz;sz<word_bits\<rbrakk> \<Longrightarrow> ((of_nat idx)::word32) && ~~ mask sz = 0"
  apply (clarsimp simp:mask_out_sub_mask)
  apply (subst less_mask_eq[symmetric])
   apply (erule(1) of_nat_less_pow)
  apply simp
  done


lemma descendants_range_in_subseteq:
  "\<lbrakk>descendants_range_in A p ms ;B\<subseteq> A\<rbrakk> \<Longrightarrow> descendants_range_in B p ms"
  by (auto simp:descendants_range_in_def cte_wp_at_caps_of_state dest!:bspec)


lemma is_aligned_neg_mask_eq': 
  "is_aligned ptr sz = (ptr && ~~ mask sz = ptr)"
   apply (rule iffI)
    apply (erule is_aligned_neg_mask_eq)
   apply (simp add:is_aligned_mask)
   apply (drule sym)
   apply (subst (asm) word_plus_and_or_coroll2[symmetric,where w = "mask sz"])
   apply simp
   done


lemma neg_mask_mask_unat:
  "sz < word_bits \<Longrightarrow>
   unat ((ptr::word32) && ~~ mask sz)  + unat (ptr && mask sz) = unat ptr"
  apply (subst unat_plus_simple[THEN iffD1,symmetric])
  apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask[OF le_refl]])
  apply (rule and_mask_less')
    apply (simp add:word_bits_def)
  apply (simp add:word_plus_and_or_coroll2 field_simps)
  done


lemma cte_wp_at_pspace_no_overlapI:
  "\<lbrakk>invs s;
    cte_wp_at (\<lambda>c. c = cap.UntypedCap (ptr && ~~ mask sz) sz idx) cref s;
    idx \<le> unat (ptr && mask sz); sz < word_bits\<rbrakk>
   \<Longrightarrow> pspace_no_overlap ptr sz s"
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (frule caps_of_state_valid_cap)
    apply (simp add:invs_valid_objs)
  apply (clarsimp simp:valid_cap_def valid_untyped_def)
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
  "\<lbrakk>invs s; cte_wp_at (op = (cap.UntypedCap (ptr && ~~ mask sz) sz idx)) cref s;
  descendants_range_in {ptr .. (ptr && ~~ mask sz) +2^sz - 1} cref s\<rbrakk> \<Longrightarrow> caps_no_overlap ptr sz s"
  apply (frule invs_mdb)
  apply (clarsimp simp:valid_mdb_def cte_wp_at_caps_of_state)
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
   apply (clarsimp simp:word_and_le2)
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (drule disjoint_subset[rotated,
       where A' = "{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"])
  apply (clarsimp simp:word_and_le2 Int_ac)+
  done


lemma pbfs_atleast_pageBits':
  "pageBits \<le> pageBitsForSize sz"by (cases sz, simp_all add: pageBits_def)


lemma pbfs_less_wb':
  "pageBitsForSize sz < word_bits"by (cases sz, simp_all add: word_bits_conv pageBits_def)


lemma shiftr_then_mask_commute:
  "(x >> n) && mask m = (x && mask (m + n)) >> n"
  using test_bit_size[where w=x]
  by (auto intro: word_eqI simp add: word_size nth_shiftr)


lemma cte_wp_at_caps_no_overlapI:
  "\<lbrakk> invs s;cte_wp_at (\<lambda>c. c = cap.UntypedCap (ptr && ~~ mask sz) sz idx) cref s;
  idx \<le> unat (ptr && mask sz);sz < word_bits \<rbrakk> \<Longrightarrow> caps_no_overlap ptr sz s"
  apply (frule invs_mdb)
  apply (frule(1) le_mask_le_2p)
  apply (clarsimp simp:valid_mdb_def cte_wp_at_caps_of_state)
  apply (frule caps_of_state_valid_cap)
    apply (simp add:invs_valid_objs)
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
   apply (clarsimp simp:word_and_le2)
  apply (thin_tac "P\<longrightarrow>Q" for P Q)+
  apply (drule disjoint_subset[rotated,
       where A' = "{ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"])
  apply (clarsimp simp:word_and_le2 Int_ac)+
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
  apply (simp add:not_less)
  apply (subst add.assoc)
  apply (rule word_add_le_mono2)
    apply (rule order_trans[OF word_of_nat_le])
    apply simp
   apply (erule range_cover.range_cover_base_le)
  apply (subst unat_plus_simple[THEN iffD1])
   apply (erule range_cover.range_cover_base_le)
  apply (subst unat_add_lem[THEN iffD1,symmetric])
   apply (frule range_cover.unat_of_nat_shift[OF _ le_refl le_refl])
   apply (simp add:shiftl_t2n field_simps del:add.commute add.assoc)
   apply (rule le_less_trans)
    apply (subst add.commute)
    apply (erule range_cover.range_cover_compare_bound)
   apply (simp add:range_cover_def)
  apply (rule less_diff_conv[THEN iffD1])
  apply (rule less_le_trans)
   apply (simp add:shiftl_t2n field_simps)
  apply (subst le_diff_conv2)
   apply (rule less_imp_le[OF unat_lt2p])
  apply (subst add.commute)
  apply (subst unat_power_lower[where 'a='a, symmetric])
   apply (simp add:range_cover_def)
  apply (rule is_aligned_no_wrap_le[OF is_aligned_neg_mask[OF le_refl]])
  apply (simp add:range_cover_def)+
  done


locale invoke_untyped_proofs = 
 fixes s cref ptr tp us slots sz idx
  assumes cte_wp_at: "cte_wp_at (op = (cap.UntypedCap (ptr && ~~ mask sz) sz idx)) cref s"
  assumes  misc     : "distinct slots" "idx \<le> unat (ptr && mask sz) \<or> ptr = ptr && ~~ mask sz"
  "invs s" "slots \<noteq> []" "ct_active s"
  "\<forall>slot\<in>set slots. cte_wp_at (op = cap.NullCap) slot s"
  "\<forall>x\<in>set slots. ex_cte_cap_wp_to (\<lambda>_. True) x s"
  assumes cover     : "range_cover ptr sz (obj_bits_api tp us) (length slots)"
  assumes desc_range: "ptr = ptr && ~~ mask sz \<longrightarrow> descendants_range_in {ptr..ptr + 2 ^ sz - 1} (cref) s"
  notes blah[simp del] = untyped_range.simps usable_untyped_range.simps atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
begin

abbreviation(input)
  "retype_range == {ptr..ptr + of_nat (length slots) * 2 ^ (obj_bits_api tp us) - 1}"

abbreviation(input)
  "usable_range ==  {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}"

lemma not_0_ptr[simp]: "ptr\<noteq> 0"
  using misc cte_wp_at
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (drule(1) caps_of_state_valid)
  apply (clarsimp simp:valid_cap_def)
  done


lemma subset_stuff[simp]:
  "retype_range \<subseteq> usable_range"
  apply (rule range_cover_subset'[OF cover])
  apply (simp add:misc)
  done

lemma kernel_window_inv[simp]: "\<forall>x\<in>usable_range.
  arm_kernel_vspace (arch_state s) x = ArmVSpaceKernelWindow"
  using cte_wp_at misc
  apply (clarsimp simp:cte_wp_at_caps_of_state invs_def valid_state_def)
  apply (erule(1) cap_refs_in_kernel_windowD[THEN bspec])
  apply (simp add:blah cap_range_def)
  apply clarsimp
  apply (erule order_trans[OF word_and_le2])
  done

lemma descendants_range[simp]:
  "descendants_range_in usable_range cref s"
  "descendants_range_in retype_range cref s"
proof -
  have "descendants_range_in usable_range cref s"
    using misc cte_wp_at cover
    apply -
    apply (erule disjE)
    apply (erule cte_wp_at_caps_descendants_range_inI[OF _ _ _ range_cover.sz(1)
        [where 'a=32, folded word_bits_def]])
    apply (simp add:cte_wp_at_caps_of_state)+
    using desc_range
    apply simp
    done
  thus "descendants_range_in usable_range cref s"
    by simp
  thus "descendants_range_in retype_range cref s"
    by (rule descendants_range_in_subseteq[OF _ subset_stuff])
qed

lemma vc[simp] : "s \<turnstile>cap.UntypedCap (ptr && ~~ mask sz) sz idx"
  using misc cte_wp_at
  apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply (erule caps_of_state_valid)
  apply simp
  done

lemma ps_no_overlap[simp]: "ptr && ~~ mask sz \<noteq> ptr \<Longrightarrow> pspace_no_overlap ptr sz s"
  using misc cte_wp_at cover
  apply clarsimp
  apply (erule cte_wp_at_pspace_no_overlapI[OF  _ _ _
                 range_cover.sz(1)[where 'a=32, folded word_bits_def]])
    apply (simp add:cte_wp_at_caps_of_state)
   apply simp+
  done

    lemma caps_no_overlap[simp]: "caps_no_overlap ptr sz s"
      using cte_wp_at misc cover desc_range
      apply -
      apply (erule disjE)
       apply (erule cte_wp_at_caps_no_overlapI[OF  _ _ _ range_cover.sz(1)
           [where 'a=32, folded word_bits_def]])
        apply (simp add:cte_wp_at_caps_of_state)+
      apply (erule descendants_range_caps_no_overlapI)
       apply (simp add:cte_wp_at_caps_of_state)+
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
      using misc cte_wp_at
      apply -
      apply simp
      apply (drule(1) bspec)+
      apply (drule ex_cte_no_overlap)
       apply simp
      apply (clarsimp simp:cte_wp_at_caps_of_state)
      done

    lemma usable_range_disjoint:
      "usable_untyped_range (cap.UntypedCap (ptr && ~~ mask sz) sz
       (unat ((ptr && mask sz) + of_nat (length slots) * 2 ^ obj_bits_api tp us))) \<inter>
       {ptr..ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1} = {}"
      proof -
      have idx_compare''[simp]:
       "unat ((ptr && mask sz) + (of_nat (length slots) * (2::word32) ^ obj_bits_api tp us)) < 2 ^ sz
        \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1
        < ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us"
      apply (rule minus_one_helper,simp)
      apply (rule neq_0_no_wrap)
      apply (rule word32_plus_mono_right_split)
      apply (simp add:shiftl_t2n range_cover_unat[OF cover] field_simps)
      apply (simp add:range_cover.sz[where 'a=32, folded word_bits_def, OF cover])+
      done
      show ?thesis
       apply (clarsimp simp:mask_out_sub_mask blah)
       apply (drule idx_compare'')
       apply (simp add:not_le[symmetric])
       done
     qed

  lemma detype_locale:"ptr && ~~ mask sz = ptr \<Longrightarrow> detype_locale (cap.UntypedCap (ptr && ~~ mask sz) sz idx) cref s"
    using cte_wp_at descendants_range misc
    by (simp add:detype_locale_def descendants_range_def2 blah invs_untyped_children)

   lemma detype_descendants_range_in:
      "ptr && ~~ mask sz = ptr \<Longrightarrow> descendants_range_in usable_range cref (detype usable_range s)"
     using misc cte_wp_at
     apply -
     apply (frule detype_invariants)
         apply (simp)
        using descendants_range
        apply (clarsimp simp:blah descendants_range_def2)
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
    apply (frule detype_invariants)
    apply (simp)
    apply (clarsimp simp:blah descendants_range_def2)
    apply ((simp add: invs_untyped_children blah
      invs_valid_reply_caps invs_valid_reply_masters)+)[6]
    done

end

lemma aligned_after_mask:
  "is_aligned ptr a \<Longrightarrow> is_aligned (ptr && mask sz) a"
  apply (simp add:is_aligned_mask)
  apply (rule word_eqI)
  apply (drule_tac x = n in word_eqD)
  apply (simp add:word_ops_nth_size)
  done


lemma detype_clear_um_simps[simp]:
 "caps_no_overlap ptr sz (clear_um H s)
  = caps_no_overlap ptr sz s"
 "pspace_no_overlap ptr sz (clear_um H s)
  = pspace_no_overlap ptr sz s"
 "descendants_range_in S p (clear_um H s)
  = descendants_range_in S p s"
  apply (clarsimp simp:caps_no_overlap_def pspace_no_overlap_def
    clear_um.pspace descendants_range_in_def
    cong:if_cong)+
  apply (simp add:clear_um_def)
  done

crunch pred_tcb_at[wp]: set_cdt "pred_tcb_at proj P t"
  (simp: pred_tcb_at_def)

lemma pred_tcb_at_revokable[simp]:
  "pred_tcb_at proj P t (is_original_cap_update f s) = pred_tcb_at proj P t s"
  by (simp add: pred_tcb_at_def)

crunch pred_tcb_at[wp]: create_cap "pred_tcb_at proj P t"
  (simp: crunch_simps)

crunch pred_tcb_at[wp]: do_machine_op "pred_tcb_at proj P t"

crunch tcb[wp]: create_cap "tcb_at t"
  (simp: crunch_simps)


declare store_pde_pred_tcb_at [wp]

lemma valid_untyped_cap_inc:
  "\<lbrakk>s \<turnstile> cap.UntypedCap (ptr&&~~ mask sz) sz idx;
    idx \<le> unat (ptr && mask sz); range_cover ptr sz sb n\<rbrakk>
   \<Longrightarrow> s \<turnstile> cap.UntypedCap (ptr && ~~ mask sz) sz
                          (unat ((ptr && mask sz) + of_nat n * 2 ^ sb))"
 apply (clarsimp simp:valid_cap_def cap_aligned_def valid_untyped_def simp del:usable_untyped_range.simps)
 apply (intro conjI allI impI)
  apply (elim allE conjE impE)
    apply simp
   apply simp
   apply (erule disjoint_subset[rotated])
   apply (frule(1) le_mask_le_2p[OF _ 
                     range_cover.sz(1)[where 'a=32, folded word_bits_def]])
   apply clarsimp
   apply (rule word_plus_mono_right)
   apply (rule word_of_nat_le)
   apply (simp add:unat_of_nat32 range_cover_unat field_simps)
   apply (rule is_aligned_no_wrap'[OF is_aligned_neg_mask[OF le_refl]])
   apply (simp add: word_less_nat_alt
                    unat_power_lower[where 'a=32, folded word_bits_def])
  apply (simp add:range_cover_unat range_cover.unat_of_nat_shift shiftl_t2n field_simps)
  apply (subst add.commute)
  apply (simp add: range_cover.range_cover_compare_bound)
  done


(* FIXME: move *)
lemma tcb_cap_valid_untyped_cong:
  "\<lbrakk>a1 = a2; b1 = b2\<rbrakk> \<Longrightarrow>
   tcb_cap_valid (cap.UntypedCap a1 b1 c) =
   tcb_cap_valid (cap.UntypedCap a2 b2 d)"
  apply clarsimp
  apply (rule ext)+
  apply (clarsimp simp:tcb_cap_valid_def split:option.splits)
  apply (rule iffI)
   apply (clarsimp simp:pred_tcb_at_def obj_at_def valid_ipc_buffer_cap_def)
   apply (clarsimp simp:tcb_cap_cases_def is_cap_simps 
     split:if_splits Structures_A.thread_state.splits)
  apply (clarsimp simp:pred_tcb_at_def obj_at_def valid_ipc_buffer_cap_def)
  apply (clarsimp simp:tcb_cap_cases_def is_cap_simps 
     split:if_splits Structures_A.thread_state.splits)
  done


(* FIXME: move *)
lemma ex_nonz_cap_to_overlap:
  "\<lbrakk>ex_nonz_cap_to t s; cte_wp_at (op = cap) p s; is_untyped_cap cap; invs s;
    descendants_range cap p s \<rbrakk>
   \<Longrightarrow> \<not> t \<in> untyped_range cap"
   apply (rule ccontr)
   apply (clarsimp simp:ex_nonz_cap_to_def descendants_range_def2 
     cte_wp_at_caps_of_state caps_no_overlap_def zobj_refs_to_obj_refs)
   apply (frule invs_mdb)
   apply (clarsimp simp:valid_mdb_def)
   apply (frule_tac cap' = capa in untyped_mdbD)
      apply simp+
     apply blast
    apply simp
   apply (drule(2) descendants_range_inD) 
   apply (simp add:cap_range_def)
   apply blast
   done


lemma detype_valid_untyped:
  "\<lbrakk>invs s; detype S s \<turnstile> cap.UntypedCap ptr sz idx1;
    {ptr .. ptr + 2 ^ sz - 1} \<subseteq> S; idx2 \<le> 2 ^ sz\<rbrakk>
   \<Longrightarrow> detype S s \<turnstile> cap.UntypedCap ptr sz idx2"
  apply (clarsimp simp:detype_def valid_cap_def valid_untyped_def cap_aligned_def)
  apply (drule_tac x = p in spec)
  apply clarsimp
  apply (drule p_in_obj_range)
   apply (simp add:invs_psp_aligned invs_valid_objs)+
  apply (drule(1) subset_trans[rotated])
  apply blast
  done


lemma do_machine_op_pspace_no_overlap[wp]:
  "\<lbrace>pspace_no_overlap ptr sz\<rbrace> do_machine_op f \<lbrace>\<lambda>r. pspace_no_overlap ptr sz \<rbrace>"
  apply (clarsimp simp:pspace_no_overlap_def do_machine_op_def)
  apply (wp hoare_vcg_all_lift)
  apply (simp add:split_def)
  apply wp
  apply clarsimp
  done


lemma delete_objects_rewrite:
  "\<lbrakk>2\<le> sz; sz\<le> word_bits;ptr && ~~ mask sz = ptr\<rbrakk> \<Longrightarrow> delete_objects ptr sz = 
    do y \<leftarrow> modify (clear_um {ptr + of_nat k |k. k < 2 ^ sz});
    modify (detype {ptr && ~~ mask sz..ptr + 2 ^ sz - 1})
    od"
  apply (clarsimp simp:delete_objects_def freeMemory_def word_size_def)
  apply (subgoal_tac "is_aligned (ptr &&~~ mask sz) sz")
  apply (subst mapM_storeWord_clear_um)
  apply (simp)
  apply simp
  apply (simp add:range_cover_def)
  apply clarsimp
  apply (rule is_aligned_neg_mask)
  apply simp
  done


(*FIXME: move *)
lemma invoke_untyped_st_tcb_at:
  "\<lbrace>invs and st_tcb_at (P and (Not \<circ> inactive) and (Not \<circ> idle)) t
         and ct_active and valid_untyped_inv ui\<rbrace>
     invoke_untyped ui
   \<lbrace>\<lambda>rv. st_tcb_at P t\<rbrace>"
  apply (cases ui, simp add: mapM_x_def[symmetric]
                  split del: split_if)
  apply (rename_tac cslot_ptr word1 word2 apiobject_type nat list)
  apply (rule hoare_name_pre_state)
  apply (clarsimp)
  apply (wp mapM_x_wp[OF _ subset_refl] get_cap_wp
            retype_region_st_tcb_at set_cap_no_overlap
            init_arch_objects_hoare_lift set_cap_valid_objs
        | simp add:split_def)+
   apply (rule_tac P = "2\<le> sz \<and> sz \<le> word_bits" in hoare_gen_asm(1))
   apply (rule_tac P = "cap = cap.UntypedCap word2 sz idx" in hoare_gen_asm(1))
   apply (clarsimp simp:bits_of_def delete_objects_rewrite)
   apply (wp get_cap_wp)
  apply (clarsimp simp: conj_comms freeMemory_def invs_psp_aligned invs_valid_objs)
  apply (frule caps_of_state_valid)
   apply (simp add:cte_wp_at_caps_of_state)
  apply (intro conjI)
   apply (clarsimp)
   apply (subgoal_tac "cap = cap.UntypedCap (word2 && ~~ mask sz) sz idx")
   apply (intro conjI)
          apply (erule pred_tcb_weakenE,simp)
         apply (simp add:bits_of_def)
         apply (erule(3) cte_wp_at_pspace_no_overlapI[OF _ _ _ range_cover.sz(1)
             [where 'a=32, folded word_bits_def]])
        apply (clarsimp simp:cte_wp_at_caps_of_state bits_of_def shiftl_t2n add_minus_neg_mask)
       apply (simp add:bits_of_def)
       apply (erule(3) cte_wp_at_pspace_no_overlapI[OF _ _ _ range_cover.sz(1)
           [where 'a=32, folded word_bits_def]])
      apply (clarsimp simp:cte_wp_at_caps_of_state bits_of_def shiftl_t2n add_minus_neg_mask)
     apply (simp add: valid_untyped_cap_inc field_simps bits_of_def add_minus_neg_mask shiftl_t2n)
    apply (clarsimp simp:cte_wp_at_caps_of_state)
    apply (drule(1) tcb_cap_valid_caps_of_stateD[OF _ invs_valid_objs])
    apply (simp cong:tcb_cap_valid_untyped_cong add:bits_of_def)
   apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply clarsimp
  apply (rule conjI)
   apply (simp add:valid_cap_simps cap_aligned_def)
  apply (rule conjI)
   apply (erule pred_tcb_weakenE,simp)
  apply (rule conjI)
   apply (simp add:valid_cap_simps cap_aligned_def)
  apply (rule context_conjI)
   apply (simp add: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (frule(1) st_tcb_ex_cap[OF _ invs_iflive])
    apply (clarsimp split: Structures_A.thread_state.splits)
   apply (drule ex_nonz_cap_to_overlap)
    apply ((simp add:cte_wp_at_caps_of_state
            is_cap_simps descendants_range_def2)+)[5]
  apply (rule conjI)
   apply (simp add:bits_of_def)
  apply ((frule detype_invariants,(clarsimp
    simp: invs_psp_aligned bits_of_def invs_valid_objs
    cte_wp_at_caps_of_state descendants_range_def2)+)[1])+
  apply (cut_tac cap' = "cap.UntypedCap word2 sz idx" and cap = "cap.UntypedCap word2 sz idx"
    and ptr = "(a,b)" and s = sa in detype_locale.valid_cap)
     apply (simp add:detype_locale_def cte_wp_at_caps_of_state
       descendants_range_def2 invs_untyped_children)
    apply (erule(1) caps_of_state_valid[rotated])
   apply (simp add:obj_reply_refs_def)
  apply (subgoal_tac "{word2 + of_nat k |k. k < 2 ^ sz} = {word2 ..word2 + 2^sz - 1}")
   prefer 2
   apply (subst intvl_range_conv)
     apply (subgoal_tac "is_aligned (word2 && ~~ mask sz) sz")
      apply simp
     apply (rule is_aligned_neg_mask,simp)
    apply (simp add:valid_cap_simps cap_aligned_def word_bits_def)
   apply simp
  apply (clarsimp simp:invs_psp_aligned invs_valid_objs)
  apply (clarsimp simp:detype_clear_um_independent)
  apply (intro conjI)
    apply (rule detype_valid_untyped)
       apply simp
      apply simp
     apply simp
    apply (clarsimp simp:cte_wp_at_caps_of_state range_cover.unat_of_nat_n_shift)
    apply (subst mult.commute)
    apply (rule nat_le_power_trans[OF range_cover.range_cover_n_le(2)])
     apply assumption
    apply (erule range_cover.sz(2))
   apply (erule pspace_no_overlap_detype)
    apply (simp add:invs_psp_aligned invs_valid_objs)+
  apply (rule_tac c1 = idx in subst[OF tcb_cap_valid_untyped_cong])
    apply assumption
   apply simp
  apply (clarsimp simp:cte_wp_at_caps_of_state bits_of_def)
  apply (drule(1) tcb_cap_valid_caps_of_stateD[OF _ invs_valid_objs])
  apply (clarsimp simp:tcb_cap_valid_def)
 done

lemma invoked_untyp_tcb[wp]:
  "\<lbrace>invs and st_tcb_at active tptr
        and valid_untyped_inv ui and ct_active\<rbrace>
     invoke_untyped ui \<lbrace>\<lambda>rv. tcb_at tptr\<rbrace>"
  apply (simp add: tcb_at_st_tcb_at)
  apply (wp invoke_untyped_st_tcb_at)
  apply (clarsimp elim!: pred_tcb_weakenE)
  apply fastforce
  done

lemma create_cap_iflive[wp]:
  "\<lbrace>if_live_then_nonz_cap
     and cte_wp_at (op = cap.NullCap) cref\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv. if_live_then_nonz_cap\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp new_cap_iflive set_cdt_cte_wp_at | simp)+
  done

crunch cap_to_again[wp]: set_cdt "ex_cte_cap_wp_to P p"
  (simp: ex_cte_cap_wp_to_def)

lemma create_cap_ifunsafe[wp]:
  "\<lbrace>if_unsafe_then_cap
     and ex_cte_cap_wp_to (appropriate_cte_cap (default_cap tp oref sz)) cref
     and cte_wp_at (op = cap.NullCap) cref\<rbrace>
     create_cap tp sz p (cref, oref)
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

lemma state_refs_of_rvk[simp]:
  "state_refs_of (is_original_cap_update f s) = state_refs_of s"
  by (simp add: state_refs_of_def)


lemma create_cap_state_refs_of[wp]:
  "\<lbrace>\<lambda>s. P (state_refs_of s)\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv s. P (state_refs_of s)\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp | simp)+
  done

lemma create_cap_zombies[wp]:
  "\<lbrace>zombies_final and cte_wp_at (op = cap.NullCap) cref
     and (\<lambda>s. \<forall>r\<in>obj_refs (default_cap tp oref sz). \<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv. zombies_final\<rbrace>"
  apply (simp add: create_cap_def set_cdt_def)
  apply (wp new_cap_zombies | simp)+
  done

lemma create_cap_cur_tcb[wp]:
  "\<lbrace>cur_tcb\<rbrace> create_cap tp sz p tup \<lbrace>\<lambda>rv. cur_tcb\<rbrace>"
  apply (simp add: create_cap_def split_def set_cdt_def)
  apply (wp | simp)+
  done

lemma create_cap_valid_idle[wp]:
  "\<lbrace>valid_idle\<rbrace>
     create_cap tp sz p tup
   \<lbrace>\<lambda>rv. valid_idle\<rbrace>"
  apply (simp add: create_cap_def split_def set_cdt_def)
  apply (wp set_cap_idle | simp)+
  done


crunch it[wp]: create_cap "\<lambda>s. P (idle_thread s)"
  (simp: crunch_simps)


lemma default_cap_reply:
  "default_cap tp ptr sz \<noteq> cap.ReplyCap ptr' bool"
  by (cases tp, simp_all)


lemma create_cap_valid_reply_caps[wp]:
  "\<lbrace>valid_reply_caps\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv. valid_reply_caps\<rbrace>"
  apply (simp add: valid_reply_caps_def has_reply_cap_def
                   cte_wp_at_caps_of_state create_cap_def
                   set_cdt_def)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  apply (clarsimp simp: default_cap_reply)
  apply (erule conjI [OF allEI], clarsimp)
  apply (simp add: unique_reply_caps_def)
  done


lemma create_cap_valid_reply_masters[wp]:
  "\<lbrace>valid_reply_masters\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv. valid_reply_masters\<rbrace>"
  apply (simp add: valid_reply_masters_def cte_wp_at_caps_of_state
                   create_cap_def)
  apply (wp | simp add: default_cap_reply)+
  done


lemma create_cap_valid_global_refs[wp]:
  "\<lbrace>valid_global_refs
      and cte_wp_at (\<lambda>c. cap_range (default_cap tp oref sz) \<subseteq> cap_range c) p\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv. valid_global_refs\<rbrace>"
  apply (simp add: valid_global_refs_def valid_refs_def
                   cte_wp_at_caps_of_state create_cap_def pred_conj_def)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift
                | simp split del:split_if)+
  apply clarsimp
  apply (subgoal_tac "global_refs s \<inter> cap_range (default_cap tp oref sz) = {}")
   apply auto[1]
  apply (erule disjoint_subset2)
  apply (cases p, simp)
  done


crunch arch_state[wp]: create_cap "\<lambda>s. P (arch_state s)"
  (simp: crunch_simps)

crunch irq_node[wp]: create_cap "\<lambda>s. P (interrupt_irq_node s)"
  (simp: crunch_simps)


lemmas create_cap_valid_arch_state[wp]
    = valid_arch_state_lift [OF create_cap_typ_at create_cap_arch_state]

lemmas create_cap_valid_irq_node[wp]
    = valid_irq_node_typ [OF create_cap_typ_at create_cap_irq_node]


lemma default_cap_irqs[simp]:
  "cap_irqs (default_cap tp oref sz) = {}"
  by (cases tp, simp_all)


lemma create_cap_irq_handlers[wp]:
  "\<lbrace>valid_irq_handlers\<rbrace> create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. valid_irq_handlers\<rbrace>"
  apply (simp add: valid_irq_handlers_def irq_issued_def)
  apply (simp add: create_cap_def Ball_def)
  apply (simp only: imp_conv_disj)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift | simp)+
  apply (erule allEI)
  apply (auto simp: ran_def)
  done


crunch valid_arch_objs[wp]: create_cap "valid_arch_objs"
  (simp: crunch_simps)


definition
  nonempty_table :: "word32 set \<Rightarrow> Structures_A.kernel_object \<Rightarrow> bool"
where
 "nonempty_table S ko \<equiv>
    (a_type ko = AArch APageTable \<or> a_type ko = AArch APageDirectory)
       \<and> \<not> empty_table S ko"

lemma reachable_pg_cap_exst_update[simp]:
  "reachable_pg_cap x (trans_state f s) = reachable_pg_cap x s"
  by (simp add:reachable_pg_cap_def vs_lookup_pages_def
    vs_lookup_pages1_def obj_at_def)


lemma create_cap_valid_arch_caps[wp]:
  "\<lbrace>valid_arch_caps
      and valid_cap (default_cap tp oref sz)
      and (\<lambda>s. \<forall>r\<in>obj_refs (default_cap tp oref sz).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
      and cte_wp_at (op = cap.NullCap) cref
      and K (tp \<noteq> ArchObject ASIDPoolObj)\<rbrace>
     create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. valid_arch_caps\<rbrace>"
  apply (simp add: create_cap_def set_cdt_def)
  apply (wp set_cap_valid_arch_caps hoare_vcg_disj_lift
      hoare_vcg_conj_lift hoare_vcg_all_lift hoare_vcg_imp_lift
    | simp add: trans_state_update[symmetric] del: trans_state_update split_paired_All split_paired_Ex imp_disjL split del: split_if)+
  apply (clarsimp simp del: split_paired_All split_paired_Ex
                            imp_disjL
                      simp: cte_wp_at_caps_of_state)
  apply (rule conjI)
   apply (clarsimp simp: no_cap_to_obj_with_diff_ref_def
                         cte_wp_at_caps_of_state)
   apply (case_tac "\<exists>x. x \<in> obj_refs cap")
    apply (clarsimp dest!: obj_ref_elemD)
    apply (case_tac cref, fastforce)
   apply (simp add: obj_ref_none_no_asid)
  apply (rule conjI)
   apply (auto simp: is_cap_simps valid_cap_def
                     obj_at_def nonempty_table_def a_type_simps)[1]
  apply (clarsimp simp del: imp_disjL)
  apply (case_tac "\<exists>x. x \<in> obj_refs cap")
   apply (clarsimp dest!: obj_ref_elemD)
   apply fastforce
  apply (auto simp: is_cap_simps)[1]
  done


crunch valid_global_objs[wp]: create_cap "valid_global_objs"
  (simp: crunch_simps)


crunch v_ker_map[wp]: create_cap "valid_kernel_mappings"
  (simp: crunch_simps)


crunch eq_ker_map[wp]: create_cap "equal_kernel_mappings"
  (simp: crunch_simps)


lemma create_cap_asid_map[wp]:
  "\<lbrace>valid_asid_map\<rbrace>
     create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. valid_asid_map\<rbrace>"
  apply (simp add: create_cap_def set_cdt_def)
  apply (wp|simp)+
  done

crunch only_idle[wp]: create_cap only_idle
  (simp: crunch_simps)

crunch global_pd_mappings[wp]: create_cap "valid_global_pd_mappings"
  (simp: crunch_simps)

crunch pspace_in_kernel_window[wp]: create_cap "pspace_in_kernel_window"
  (simp: crunch_simps)

lemma create_cap_cap_refs_in_kernel_window[wp]:
  "\<lbrace>cap_refs_in_kernel_window and cte_wp_at (\<lambda>c. cap_range (default_cap tp oref sz) \<subseteq> cap_range c) p\<rbrace>
     create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. cap_refs_in_kernel_window\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp | simp)+
  apply (clarsimp simp: cte_wp_at_caps_of_state)
  apply (drule(1) cap_refs_in_kernel_windowD)
  apply blast
  done

lemma set_original_valid_ioc[wp]:
  "\<lbrace>valid_ioc\<rbrace> create_cap tp sz p slot \<lbrace>\<lambda>_. valid_ioc\<rbrace>"
  apply (cases slot)
  apply (simp add: create_cap_def set_original_set_cap_comm, wp)
  apply (simp add: cte_wp_at_caps_of_state)
  apply (wp set_cdt_cos_ioc set_cap_caps_of_state | simp)+
  apply (case_tac tp, simp_all)
  done

lemma create_cap_vms[wp]:
  "\<lbrace>\<lambda>s. valid_machine_state s\<rbrace>
   create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>_ s. valid_machine_state s\<rbrace>"
  apply (simp add: valid_machine_state_def in_user_frame_def)
  apply (wp hoare_vcg_all_lift hoare_vcg_disj_lift hoare_vcg_ex_lift)
  apply (wp|simp add: create_cap_def set_cdt_def bind_assoc)+
  done

crunch valid_irq_states[wp]: create_cap "valid_irq_states"

lemma create_cap_invs[wp]:
  "\<lbrace>invs 
      and cte_wp_at (\<lambda>c. is_untyped_cap c \<and> 
                         obj_refs (default_cap tp oref sz) \<subseteq> untyped_range c \<and>
                         untyped_range (default_cap tp oref sz) \<subseteq> untyped_range c
                         \<and> untyped_range (default_cap tp oref sz) \<inter> usable_untyped_range c = {}) p
      and descendants_range (default_cap tp oref sz) p
      and cte_wp_at (op = cap.NullCap) cref
      and valid_cap (default_cap tp oref sz)
      and ex_cte_cap_wp_to (appropriate_cte_cap (default_cap tp oref sz)) cref
      and real_cte_at cref
      and (\<lambda>s. \<forall>r\<in>obj_refs (default_cap tp oref sz).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
      and K (p \<noteq> cref \<and> tp \<noteq> ArchObject ASIDPoolObj)\<rbrace>
     create_cap tp sz p (cref, oref) \<lbrace>\<lambda>rv. invs\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add: invs_def valid_state_def valid_pspace_def)
   apply (wp | simp add: valid_cap_def)+
  apply clarsimp
  apply (clarsimp simp: cte_wp_at_caps_of_state valid_pspace_def)
  apply (frule_tac p1 = p in valid_cap_aligned[OF caps_of_state_valid])
    apply simp
  apply (simp add:invs_def valid_state_def valid_pspace_def )
  apply (simp add:cap_range_def)
  done

lemma create_cap_ex_cap_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p' and cte_wp_at (op = cap.NullCap) cref\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p'\<rbrace>"
  apply (simp add: create_cap_def)
  apply (wp set_cap_cte_cap_wp_to set_cdt_cte_wp_at
            | simp | wps set_cdt_irq_node)+
  apply (clarsimp elim!: cte_wp_at_weakenE)
  done

lemma create_cap_no_cap[wp]:
  "\<lbrace>\<lambda>s. (\<forall>p'. \<not> cte_wp_at P p' s) \<and> \<not> P (default_cap tp oref sz)\<rbrace>
     create_cap tp sz p (cref, oref)
   \<lbrace>\<lambda>rv s. \<forall>oref' cref'. \<not> cte_wp_at P (oref', cref') s\<rbrace>"
  apply (simp add: create_cap_def cte_wp_at_caps_of_state)
  apply (wp | simp)+
  done

lemma nonempty_table_caps_of:
  "nonempty_table S ko \<Longrightarrow> caps_of ko = {}"
  by (auto simp: caps_of_def cap_of_def nonempty_table_def a_type_def
          split: Structures_A.kernel_object.split split_if_asm)

lemma create_cap_nonempty_tables[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) p s)\<rbrace>
     create_cap tp sz p' (cref, oref)
   \<lbrace>\<lambda>rv s. P (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) p s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=arch_state, OF create_cap_arch_state])
   apply (simp add: create_cap_def set_cdt_def)
   apply (wp set_cap_obj_at_impossible|simp)+
  apply (clarsimp simp: nonempty_table_caps_of)
  done

lemma cap_range_not_untyped: 
  "\<not> is_untyped_cap c \<Longrightarrow> cap_range c = obj_refs c"
  apply (case_tac c)
  apply (simp_all add:is_cap_simps cap_range_def)
  done

lemma cap_range_inter_emptyI:
  "\<lbrakk>is_untyped_cap a = is_untyped_cap b; untyped_range a \<inter> untyped_range b ={};
    obj_refs a \<inter> obj_refs b = {}\<rbrakk>
   \<Longrightarrow> cap_range a \<inter> cap_range b = {}"
  apply (case_tac "is_untyped_cap a")
   apply (simp_all add:cap_range_not_untyped)
  done

lemma create_caps_invs_inv:
  assumes create_cap_Q[wp]: "\<lbrace>invs and Q and cte_wp_at (\<lambda>c. is_untyped_cap c) p and cte_wp_at (op = NullCap) cref\<rbrace>
         create_cap tp sz p (cref,oref) \<lbrace>\<lambda>_. Q \<rbrace>"
  shows
  "\<lbrace>(\<lambda>s. 

         invs s \<and> Q s 
       \<and> cte_wp_at is_untyped_cap p s
       \<and> (\<forall>tup \<in> set ((cref,oref)#list). 
           cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz) \<subseteq> untyped_range c
           \<and> (untyped_range (default_cap tp (snd tup) sz) \<inter> usable_untyped_range c = {})) p s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
           descendants_range (default_cap tp (snd tup) sz) p s)    
       \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz)) ((cref,oref)#list)) 
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
           cte_wp_at (op = cap.NullCap) (fst tup) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
              valid_cap (default_cap tp (snd tup) sz) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
              ex_cte_cap_wp_to is_cnode_cap (fst tup) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list).
              real_cte_at (fst tup) s)
       \<and> (\<forall>tup \<in> set ((cref,oref)#list). \<forall>r \<in> obj_refs (default_cap tp (snd tup) sz).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
       \<and> distinct (p # (map fst ((cref,oref)#list)))
       \<and> tp \<noteq> ArchObject ASIDPoolObj) \<rbrace>
     create_cap tp sz p (cref,oref)
   \<lbrace>(\<lambda>r s. 

         invs s \<and> Q s 
       \<and> cte_wp_at is_untyped_cap p s
       \<and> (\<forall>tup \<in> set list. 
           cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz) \<subseteq> untyped_range c
           \<and> (untyped_range (default_cap tp (snd tup) sz) \<inter> usable_untyped_range c = {})) p s)
       \<and> (\<forall>tup \<in> set list.
           descendants_range (default_cap tp (snd tup) sz) p s)    
       \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz)) list) 
       \<and> (\<forall>tup \<in> set list.
           cte_wp_at (op = cap.NullCap) (fst tup) s)
       \<and> (\<forall>tup \<in> set list.
              valid_cap (default_cap tp (snd tup) sz) s)
       \<and> (\<forall>tup \<in> set list.
              ex_cte_cap_wp_to is_cnode_cap (fst tup) s)
       \<and> (\<forall>tup \<in> set list.
              real_cte_at (fst tup) s)
       \<and> (\<forall>tup \<in> set list. \<forall>r \<in> obj_refs (default_cap tp (snd tup) sz).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
       \<and> distinct (p # (map fst list))
       \<and> tp \<noteq> ArchObject ASIDPoolObj) \<rbrace>"
  apply (rule hoare_pre)
  apply (wp hoare_vcg_const_Ball_lift | clarsimp)+
  apply (clarsimp simp: conj_comms invs_mdb distinct_sets_prop distinct_prop_map
                        ex_cte_cap_to_cnode_always_appropriate_strg)
  apply (simp add: cte_wp_at_caps_of_state[where p=p])
  apply (intro conjI)
     apply (clarsimp simp:image_def)
     apply (drule(1) bspec)+
     apply simp
    apply (fastforce simp:cap_range_def)
   apply (clarsimp simp:is_cap_simps)
   apply fastforce
  apply (clarsimp simp: cap_range_def)
  done


lemma create_caps_invs:
  assumes create_cap_Q[wp]: "\<And>tp sz p cref oref.\<lbrace>invs and Q and cte_wp_at (\<lambda>c. is_untyped_cap c) p and cte_wp_at (op = NullCap) cref\<rbrace>
         create_cap tp sz p (cref,oref) \<lbrace>\<lambda>_. Q \<rbrace>"
  (*defines "Ptup s tup \<equiv> 
     cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz) \<subseteq> untyped_range c \<and>
     (untyped_range (default_cap tp (snd tup) sz) \<inter> usable_untyped_range c = {})) p s) \<and>
     descendants_range (default_cap tp (snd tup) sz) p s) \<and>
     cte_wp_at (op = cap.NullCap) (fst tup) s) \<and>
     valid_cap (default_cap tp (snd tup) sz) s) \<and>
     ex_cte_cap_wp_to is_cnode_cap (fst tup) s) \<and>
     real_cte_at (fst tup) s) \<and>
     "*)
  shows
  "\<lbrace>\<lambda>s. invs s \<and> Q s
       \<and> cte_wp_at is_untyped_cap p s
       \<and> (\<forall>tup \<in> set (zip crefs orefs). 
           cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz) \<subseteq> untyped_range c
           \<and> (untyped_range (default_cap tp (snd tup) sz) \<inter> usable_untyped_range c = {})) p s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
           descendants_range (default_cap tp (snd tup) sz) p s)    
       \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz)) (zip crefs orefs)) 
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
           cte_wp_at (op = cap.NullCap) (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              valid_cap (default_cap tp (snd tup) sz) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              ex_cte_cap_wp_to is_cnode_cap (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              real_cte_at (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs). \<forall>r \<in> obj_refs (default_cap tp (snd tup) sz).
                (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
       \<and> distinct (p # (map fst (zip crefs orefs)))
       \<and> tp \<noteq> ArchObject ASIDPoolObj \<rbrace>
     mapM_x (create_cap tp sz p) (zip crefs orefs)
   \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  apply (induct ("zip crefs orefs"))
   apply (simp add: mapM_x_def sequence_x_def)
   apply wp
   apply simp
  apply (clarsimp simp add: mapM_x_def sequence_x_def) 
  apply (rule hoare_seq_ext)
   apply assumption
  apply (thin_tac "valid a b c" for a b c)
  apply (rule hoare_pre)
  apply (rule hoare_strengthen_post)
  apply (rule_tac list=list in create_caps_invs_inv[OF create_cap_Q],clarsimp+)
  done

lemma create_caps_invs_empty_descendants:
  assumes create_cap_Q[wp]: "\<And>tp sz p cref oref.\<lbrace>invs and Q and cte_wp_at (\<lambda>c. is_untyped_cap c) p and cte_wp_at (op = NullCap) cref\<rbrace>
         create_cap tp sz p (cref,oref) \<lbrace>\<lambda>_. Q \<rbrace>"
  shows
  "\<lbrace>\<lambda>s. invs s \<and> Q s
       \<and> descendants_of p (cdt s) = {}
       \<and> cte_wp_at is_untyped_cap p s
       \<and> (\<forall>tup \<in> set (zip crefs orefs). 
           cte_wp_at (\<lambda>c. cap_range (default_cap tp (snd tup) sz) \<subseteq> untyped_range c
           \<and> (untyped_range (default_cap tp (snd tup) sz) \<inter> usable_untyped_range c = {})) p s)
       \<and> distinct_sets (map (\<lambda>tup. cap_range (default_cap tp (snd tup) sz)) (zip crefs orefs)) 
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
           cte_wp_at (op = cap.NullCap) (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              valid_cap (default_cap tp (snd tup) sz) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs).
              ex_cte_cap_wp_to is_cnode_cap (fst tup) s \<and> real_cte_at (fst tup) s)
       \<and> (\<forall>tup \<in> set (zip crefs orefs). \<forall>r \<in> obj_refs (default_cap tp (snd tup) sz).
            (\<forall>p'. \<not> cte_wp_at (\<lambda>cap. r \<in> obj_refs cap) p' s)
              \<and> \<not> obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
       \<and> distinct (p # (map fst (zip crefs orefs)))
       \<and> tp \<noteq> ArchObject ASIDPoolObj\<rbrace>
     mapM_x (create_cap tp sz p) (zip crefs orefs)
   \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  apply (rule hoare_pre, rule create_caps_invs, rule create_cap_Q)
  apply (clarsimp simp: descendants_range_def)
  done


lemma retype_region_cte_at_other':
  "\<lbrace>pspace_no_overlap ptr sz and cte_wp_at P p
     and valid_pspace and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty
   \<lbrace>\<lambda>rv. cte_wp_at P p\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (wp retype_region_cte_at_other)
   apply assumption
  apply clarsimp
  done

lemma retype_region_ex_cte_cap_to:
  "\<lbrace>pspace_no_overlap ptr sz and ex_cte_cap_wp_to P p
     and valid_pspace and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  apply (simp add: ex_cte_cap_wp_to_def)
  apply (wp hoare_vcg_ex_lift retype_region_cte_at_other'
               | wps retype_region_irq_node)+
  apply auto
  done

lemma retype_region_obj_ref_range:
  "\<lbrakk> \<And>r. \<lbrace>P r\<rbrace> retype_region ptr n us ty \<lbrace>\<lambda>rv. Q r\<rbrace> \<rbrakk>
  \<Longrightarrow>
   \<lbrace>(\<lambda>s. \<forall>r \<in> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}. P r s) and K (range_cover ptr sz (obj_bits_api ty us) n)\<rbrace>
     retype_region ptr n us ty
   \<lbrace>\<lambda>rv s. \<forall>x \<in> set rv. \<forall>r \<in> obj_refs (default_cap tp x us). Q r s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift [OF retype_region_ret, simplified])
   apply (rule hoare_vcg_const_Ball_lift)
   apply assumption
  apply (clarsimp)
  apply (drule subsetD[OF obj_refs_default_cap])
  apply (drule_tac x = ra in  bspec)
   apply (simp add: ptr_add_def)
   apply (drule(1) range_cover_mem)
   apply simp
  apply simp
  done

lemma retype_region_not_cte_wp_at:
  "\<lbrace>(\<lambda>s. \<not> cte_wp_at P p s) and valid_pspace and 
     caps_overlap_reserved {ptr..ptr + of_nat n * 2 ^ obj_bits_api tp us - 1} and
     valid_mdb and pspace_no_overlap ptr sz and caps_no_overlap ptr sz and
     K (\<not> P cap.NullCap \<and> (tp = CapTableObject \<longrightarrow> 0 < us) \<and> range_cover ptr sz (obj_bits_api tp us) n)\<rbrace>
     retype_region ptr n us tp
   \<lbrace>\<lambda>rv s. \<not> cte_wp_at P p s\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (clarsimp simp: P_null_filter_caps_of_cte_wp_at[symmetric])
  apply (wp retype_region_caps_of)
    apply simp+
  apply auto
  done


lemma retype_region_refs_distinct[wp]:
  "\<lbrace>K (range_cover ptr sz (obj_bits_api tp us) n)\<rbrace> retype_region ptr n us tp
   \<lbrace>\<lambda>rv s. distinct_prop
             (\<lambda>x y. obj_refs (default_cap tp (snd x) us)
                  \<inter> obj_refs (default_cap tp (snd y) us) = {})
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
   apply (simp add:range_cover_def word_bits_def)
  apply (erule range_cover.range_cover_n_le[where 'a=32, folded word_bits_def])
  done


lemma unsafe_protected:
  "\<lbrakk> cte_wp_at P p s; cte_wp_at (op = (cap.UntypedCap ptr bits idx)) p' s;
     descendants_range_in S p' s; invs s; S \<subseteq> untyped_range (cap.UntypedCap ptr bits idx);
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
  "\<lbrakk> ex_cte_cap_wp_to P p s; cte_wp_at (op = (cap.UntypedCap ptr bits idx)) p' s;
     descendants_range (cap.UntypedCap ptr bits idx) p' s; invs s \<rbrakk>
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
    apply (clarsimp simp:cte_wp_at_caps_of_state)
  apply auto
  done

lemma valid_cap_aligned:
  "valid_cap cap s \<Longrightarrow> cap_aligned cap"
  by (simp add: valid_cap_def)

crunch irq_node[wp]: do_machine_op "\<lambda>s. P (interrupt_irq_node s)"
crunch irq_node[wp]: store_pde "\<lambda>s. P (interrupt_irq_node s)"
  (wp: crunch_wps)

lemma init_arch_objects_irq_node[wp]:
  "\<lbrace>\<lambda>s. P (interrupt_irq_node s)\<rbrace> init_arch_objects tp ptr bits us refs \<lbrace>\<lambda>rv s. P (interrupt_irq_node s)\<rbrace>"
  by (wp init_arch_objects_hoare_lift, simp)

lemma init_arch_objects_excap[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace> init_arch_objects tp ptr bits us refs \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  by (wp ex_cte_cap_to_pres init_arch_objects_irq_node init_arch_objects_cte_wp_at)

crunch nonempty_table[wp]: do_machine_op
  "\<lambda>s. P' (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)"

lemma store_pde_weaken:
  "\<lbrace>\<lambda>s. page_directory_at (p && ~~ mask pd_bits) s \<longrightarrow> P s\<rbrace> store_pde p e \<lbrace>Q\<rbrace> =
   \<lbrace>P\<rbrace> store_pde p e \<lbrace>Q\<rbrace>"
  apply (rule iffI)
   apply (simp add: valid_def)
   apply (erule allEI)
   apply clarsimp
  apply (simp add: valid_def)
  apply (erule allEI)
  apply clarsimp
  apply (rule use_valid, assumption)
   apply (simp add: store_pde_def set_pd_def set_object_def)
   apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def a_type_simps)
  apply (drule bspec, assumption)
  apply (simp add: simpler_store_pde_def obj_at_def fun_upd_def
            split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  done

(* FIXME: move *)
lemma ge_mask_eq: "len_of TYPE('a) \<le> n \<Longrightarrow> (x::'a::len word) && mask n = x"
  by (simp add: mask_def p2_eq_0[THEN iffD2])

lemma store_pde_nonempty_table:
  "\<lbrace>\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
           \<and> (\<forall>rf. pde_ref pde = Some rf \<longrightarrow>
                   rf \<in> set (arm_global_pts (arch_state s)))
           \<and> ucast (pde_ptr && mask pd_bits >> 2) \<in> kernel_mapping_slots
           \<and> valid_pde_mappings pde\<rbrace>
     store_pde pde_ptr pde
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def nonempty_table_def a_type_def)
  apply (clarsimp simp add: empty_table_def)
  done

crunch valid_global_objs[wp]: do_machine_op "valid_global_objs"

lemma store_pde_global_global_objs:
  "\<lbrace>\<lambda>s. valid_global_objs s
           \<and> (\<forall>rf. pde_ref pde = Some rf \<longrightarrow>
                   rf \<in> set (arm_global_pts (arch_state s)))
           \<and> ucast (pde_ptr && mask pd_bits >> 2) \<in> kernel_mapping_slots
           \<and> valid_pde_mappings pde\<rbrace>
   store_pde pde_ptr pde
   \<lbrace>\<lambda>rv s. valid_global_objs s\<rbrace>"
  apply (simp add: store_pde_def set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def fun_upd_def[symmetric])
proof -
  fix s pd
  assume vg: "valid_global_objs s"
     and gr: "\<forall>rf. pde_ref pde = Some rf \<longrightarrow>
                   rf \<in> set (arm_global_pts (arch_state s))"
     and uc: "ucast (pde_ptr && mask pd_bits >> 2) \<in> kernel_mapping_slots"
     and vp: "valid_pde_mappings pde"
     and pd: "kheap s (pde_ptr && ~~ mask pd_bits) =
              Some (ArchObj (PageDirectory pd))"
  let ?ko' = "ArchObj (PageDirectory
                         (pd(ucast (pde_ptr && mask pd_bits >> 2) := pde)))"
  let ?s' = "s\<lparr>kheap := kheap s(pde_ptr && ~~ mask pd_bits \<mapsto> ?ko')\<rparr>"
  have typ_at: "\<And>T p. typ_at T p s \<Longrightarrow> typ_at T p ?s'"
    using pd
    by (clarsimp simp: obj_at_def a_type_def)
  have valid_pde: "\<And>pde. valid_pde pde s \<Longrightarrow> valid_pde pde ?s'"
    by (case_tac pdea, simp_all add: typ_at)
  have valid_pte: "\<And>pte. valid_pte pte s \<Longrightarrow> valid_pte pte ?s'"
    by (case_tac pte, simp_all add: typ_at)
  have valid_ao_at: "\<And>p. valid_ao_at p s \<Longrightarrow> valid_ao_at p ?s'"
    using pd uc
    apply (clarsimp simp: valid_ao_at_def obj_at_def)
    apply (intro conjI impI allI)
      apply (clarsimp simp: valid_pde vp)
    apply (case_tac ao, simp_all add: typ_at valid_pde valid_pte)
    done
  have empty:
    "\<And>p. obj_at (empty_table (set (arm_global_pts (arch_state s)))) p s
          \<Longrightarrow> obj_at (empty_table (set (arm_global_pts (arch_state s)))) p ?s'"
    using pd gr vp uc
    by (clarsimp simp: obj_at_def empty_table_def)
  show "valid_global_objs ?s'"
    using vg pd
    apply (clarsimp simp add: valid_global_objs_def valid_ao_at empty)
    apply (fastforce simp add: obj_at_def)
    done
qed

lemma valid_arch_state_global_pd:
  "\<lbrakk> valid_arch_state s; pspace_aligned s \<rbrakk>
    \<Longrightarrow> obj_at (\<lambda>ko. \<exists>pd. ko = ArchObj (PageDirectory pd)) (arm_global_pd (arch_state s)) s
           \<and> is_aligned (arm_global_pd (arch_state s)) pd_bits"
  apply (clarsimp simp: valid_arch_state_def a_type_def
                        pd_aligned pd_bits_def pageBits_def
                 elim!: obj_at_weakenE)
  apply (clarsimp split: Structures_A.kernel_object.split_asm
                         arch_kernel_obj.split_asm split_if_asm)
  done


lemma pd_shifting':
  "is_aligned (pd :: word32) pd_bits \<Longrightarrow> pd + (vptr >> 20 << 2) && ~~ mask pd_bits = pd"
  by (rule pd_shifting, simp add: pd_bits_def pageBits_def)


lemma copy_global_mappings_nonempty_table:
  "is_aligned pd pd_bits \<Longrightarrow>
   \<lbrace>\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s) \<and>
        valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s\<rbrace>
   copy_global_mappings pd
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table
                        (set (arm_global_pts (arch_state s)))) r s) \<and>
           valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s\<rbrace>"
  apply (simp add: copy_global_mappings_def)
  apply (rule hoare_seq_ext [OF _ gets_sp])
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp[where S="{x. kernel_base >> 20 \<le> x \<and>
                                      x < 2 ^ (pd_bits - 2)}"])
    apply (wp get_pde_wp hoare_vcg_ball_lift
              store_pde_weaken[THEN iffD2,OF store_pde_nonempty_table]
              store_pde_weaken[THEN iffD2,OF store_pde_global_global_objs]
           | simp)+
    apply clarsimp
    apply (subst (asm) is_aligned_add_helper[THEN conjunct2])
      apply (clarsimp simp: valid_arch_state_def pspace_aligned_def dom_def
                            obj_at_def)
      apply (drule_tac x="arm_global_pd (arch_state s)" in spec, erule impE,
             fastforce)
      apply (simp add: pd_bits_def pageBits_def)
     apply (erule shiftl_less_t2n)
     apply (simp add: pd_bits_def pageBits_def)
    apply (clarsimp simp: valid_arch_state_def valid_global_objs_def obj_at_def
                          empty_table_def)
    apply (simp add: kernel_mapping_slots_def)
    apply (subst is_aligned_add_helper[THEN conjunct1], assumption)
     apply (erule shiftl_less_t2n)
     apply (simp add: pd_bits_def pageBits_def)
    apply (simp add: kernel_base_shift_cast_le[symmetric] ucast_ucast_mask)
    apply (subst shiftl_shiftr_id)
      apply simp
     apply (simp add: word_less_nat_alt pd_bits_def pageBits_def)
    apply (subst less_mask_eq)
     apply (simp add: pd_bits_def pageBits_def)
    apply assumption
   apply (clarsimp simp: pd_bits_def)
  apply simp
  done


lemma mapM_copy_global_mappings_nonempty_table[wp]:
  "\<lbrace>(\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
        \<and> valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s) and
    K (\<forall>pd\<in>set pds. is_aligned pd pd_bits)\<rbrace>
   mapM_x copy_global_mappings pds
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (rule hoare_strengthen_post)
   apply (rule mapM_x_wp', rule copy_global_mappings_nonempty_table)
   apply simp_all
  done

(* FIXME: replace do_machine_op_obj_at in KHeap_R by the lemma below *)
lemma do_machine_op_obj_at_arch_state[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (Q (arch_state s)) p s)\<rbrace>
   do_machine_op f
   \<lbrace>\<lambda>_ s. P (obj_at (Q (arch_state s)) p s)\<rbrace>"
  by (clarsimp simp: do_machine_op_def split_def | wp)+


lemma init_arch_objects_nonempty_table[wp]:
  "\<lbrace>(\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)
         \<and> valid_global_objs s \<and> valid_arch_state s \<and> pspace_aligned s) and
    K (tp = ArchObject PageDirectoryObj \<longrightarrow>
         (\<forall>pd\<in>set refs. is_aligned pd pd_bits))\<rbrace>
        init_arch_objects tp ptr bits us refs
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>"
  apply (rule hoare_gen_asm)
  apply (simp add: init_arch_objects_def)
  apply (rule hoare_pre)
   apply (wp | wpc | simp add: create_word_objects_def reserve_region_def)+
  done


lemma nonempty_default[simp]:
  "tp \<noteq> Untyped \<Longrightarrow> \<not> nonempty_table S (default_object tp us)"
  apply (case_tac tp, simp_all add: default_object_def nonempty_table_def
                                    a_type_def)
  apply (rename_tac aobject_type)
  apply (case_tac aobject_type, simp_all add: default_arch_object_def)
   apply (simp_all add: empty_table_def pde_ref_def valid_pde_mappings_def)
  done


lemma retype_nonempty_table[wp]:
  "\<lbrace>\<lambda>s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>
     retype_region ptr sz us tp
   \<lbrace>\<lambda>rv s. \<not> (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) r s)\<rbrace>"
  apply (simp add: retype_region_def split del: split_if)
  apply (rule hoare_pre)
   apply (wp|simp del: fun_upd_apply)+
  apply (clarsimp simp del:fun_upd_apply)
  apply (simp add: foldr_upd_app_if)
  apply (clarsimp simp: obj_at_def split: split_if_asm)
  done


lemma invs_valid_global_objs_strg:
  "invs s \<longrightarrow> valid_global_objs s"
  by (clarsimp simp: invs_def valid_state_def)


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

lemma set_cap_nonempty_tables[wp]:
  "\<lbrace>\<lambda>s. P (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) p s)\<rbrace>
     set_cap cap cref
   \<lbrace>\<lambda>rv s. P (obj_at (nonempty_table (set (arm_global_pts (arch_state s)))) p s)\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_use_eq [where f=arch_state, OF set_cap_arch])
   apply (wp set_cap_obj_at_impossible)
  apply (clarsimp simp: nonempty_table_caps_of)
  done


lemma ex_cte_cap_wp_to_def_msu[simp]:
  "ex_cte_cap_wp_to P x (machine_state_update f s)  = ex_cte_cap_wp_to P x s"
  by (simp add: ex_cte_cap_wp_to_def)


lemma retype_region_caps_reserved:
  "\<lbrace>cte_wp_at (is_untyped_cap) p and caps_overlap_reserved {ptr..ptr + of_nat (n * 2 ^ obj_bits_api tp us) - 1} 
  and K (range_cover ptr sz (obj_bits_api tp us) n) and pspace_no_overlap ptr sz and valid_pspace \<rbrace>
  retype_region ptr n us tp 
 \<lbrace>\<lambda>rv s. \<forall>y\<in>set rv. cte_wp_at (\<lambda>a. untyped_range (default_cap tp y us ) \<inter> usable_untyped_range a = {}) p s\<rbrace>"
  apply (clarsimp simp:valid_def cte_wp_at_caps_of_state)
  apply (frule use_valid[OF _ retype_region_ranges'])
   apply fastforce
  apply (drule(1) bspec)
  apply (frule_tac P1 = "op = cap" in use_valid[OF _ retype_region_cte_at_other])
    apply simp+
   apply (fastforce simp:cte_wp_at_caps_of_state)
  apply (clarsimp simp:cte_wp_at_caps_of_state caps_overlap_reserved_def)
  apply (drule bspec)
   apply fastforce
  apply (clarsimp simp:cap_range_def)
  apply blast
  done


lemma untyped_mdb_descendants_range:
  "\<lbrakk>caps_of_state s p = Some ucap; is_untyped_cap ucap; valid_mdb s; descendants_range_in S p s; S \<subseteq> untyped_range ucap;
   caps_of_state s slot = Some cap; x\<in> obj_refs cap \<rbrakk>\<Longrightarrow> x\<notin> S"
  apply (clarsimp simp:valid_mdb_def)
  apply (drule untyped_mdbD)
     apply simp+
    apply (rule ccontr)
    apply (clarsimp)
    apply blast
   apply simp
   apply (drule(2) descendants_range_inD)
  apply (simp add:cap_range_def,blast)
  done


lemma global_refs_detype[simp]: "global_refs (detype S s) = global_refs s"
  by (simp add: detype_def)


lemma ex_cte_cap_wp_to_clear_um[simp]:
  "ex_cte_cap_wp_to P p (clear_um T s) = ex_cte_cap_wp_to P p s"
  by (clarsimp simp:ex_cte_cap_wp_to_def clear_um_def)


lemma set_pd_cte_wp_at_iin[wp]:
  "\<lbrace>\<lambda>s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)\<rbrace>
   set_pd q pd
   \<lbrace>\<lambda>_ s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)\<rbrace>"
  apply (simp add: set_pd_def set_object_def)
  apply (wp get_object_wp)
  apply (clarsimp simp: obj_at_def cte_wp_at_caps_of_state
           split: Structures_A.kernel_object.splits arch_kernel_obj.splits)
  apply (subst caps_of_state_after_update)
   apply (simp add: obj_at_def)+
  done


crunch cte_wp_at_iin[wp]: init_arch_objects
  "\<lambda>s. P (cte_wp_at (P' (interrupt_irq_node s)) p s)"
  (ignore: clearMemory wp: crunch_wps)


lemma init_arch_objects_ex_cte_cap_wp_to[wp]:
  "\<lbrace>ex_cte_cap_wp_to P p\<rbrace>
   init_arch_objects tp ptr no us orefs
   \<lbrace>\<lambda>rv. ex_cte_cap_wp_to P p\<rbrace>"
  by (simp add: ex_cte_cap_wp_to_def) (wp hoare_vcg_ex_lift)

lemma invoke_untyp_invs':
 assumes create_cap_Q[wp]: "\<And>tp sz p cref oref.\<lbrace>invs and Q and cte_wp_at (\<lambda>c. is_untyped_cap c) p and cte_wp_at (op = NullCap) cref\<rbrace>
         create_cap tp sz p (cref,oref) \<lbrace>\<lambda>_. Q \<rbrace>"
 assumes init_arch_Q[wp]: "\<And>a b c d e. \<lbrace>Q\<rbrace> init_arch_objects a b c d e \<lbrace>\<lambda>_.Q\<rbrace>"
 assumes retype_region_Q[wp]: "\<And>a b c d. \<lbrace>invs and Q\<rbrace> retype_region a b c d \<lbrace>\<lambda>_.Q\<rbrace>"
 assumes set_cap_Q[wp]: "\<And>cap dest. \<lbrace>invs and Q\<rbrace> set_cap cap dest \<lbrace>\<lambda>_.Q\<rbrace>"
 assumes detype_Q: "\<And>cap s. invs s \<Longrightarrow> Q s \<Longrightarrow> Q
    (detype (untyped_range cap) (clear_um (untyped_range cap) s))"
 shows
  "\<lbrace>(invs ::'a::state_ext state \<Rightarrow> bool) and Q and valid_untyped_inv ui and ct_active\<rbrace> invoke_untyped ui \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
  apply (cases ui, simp split del: split_if del:invoke_untyped.simps)
  apply (rule hoare_name_pre_state)
  apply (clarsimp simp del:split_paired_All split_paired_Ex split_paired_Ball invoke_untyped.simps)
  apply (rename_tac cref oref ptr tp us slots s sz idx)
  proof -
    fix cref oref ptr tp us slots s sz idx
    assume cte_wp_at : "cte_wp_at (\<lambda>c. c = cap.UntypedCap (ptr && ~~ mask sz) sz idx) (cref,oref) (s::'a::state_ext state)"
     have cte_at: "cte_wp_at (op = (cap.UntypedCap (ptr && ~~ mask sz) sz idx)) (cref,oref) s" (is "?cte_cond s")
       using cte_wp_at by (simp add:cte_wp_at_caps_of_state)
    assume desc_range: "ptr = ptr && ~~ mask sz \<longrightarrow> descendants_range_in {ptr..ptr + 2 ^ sz - 1} (cref,oref) s"
    assume  misc     : "distinct slots" "tp = CapTableObject \<longrightarrow> 0 < (us::nat)"
      " tp = Untyped \<longrightarrow> 4 \<le> (us::nat)"
      " idx \<le> unat (ptr && mask sz) \<or> ptr = ptr && ~~ mask sz"
      " invs s" "Q s" "tp \<noteq> ArchObject ASIDPoolObj"
      " \<forall>slot\<in>set slots. cte_wp_at (op = cap.NullCap) slot s \<and> ex_cte_cap_wp_to is_cnode_cap slot s \<and> real_cte_at slot s"
      " ct_active s"
    assume cover     : "range_cover ptr sz (obj_bits_api tp us) (length slots)"
    assume vslot : "slots\<noteq> []"

    have pf : "invoke_untyped_proofs s (cref,oref) ptr tp us slots sz idx"
      using  cte_wp_at desc_range misc cover vslot 
      apply (clarsimp simp:invoke_untyped_proofs_def cte_wp_at_caps_of_state)
      apply (drule(1) bspec)
      apply (clarsimp elim!:ex_cte_cap_wp_to_weakenE)
      done
      
    have of_nat_length: "(of_nat (length slots)::word32) - (1::word32) < (of_nat (length slots)::word32)"
       using vslot
       using range_cover.range_cover_le_n_less(1)[OF cover,where p = "length slots"]
       apply -
       apply (case_tac slots)
        apply clarsimp
       apply clarsimp
       apply (subst add.commute)
       apply (subst word_le_make_less[symmetric])
       apply (rule less_imp_neq)
       apply (simp add:minus_one_norm)
       apply (rule word_of_nat_less)
       apply auto
       done
    have subset_stuff[simp]:
      "{ptr..ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1}
      \<subseteq> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}" (is "?retype_range \<subseteq> ?usable_range")
      apply (rule range_cover_subset'[OF cover])
      apply (simp add:vslot)
      done

    note blah[simp del] = untyped_range.simps usable_untyped_range.simps
          atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
    note descendants_range[simp] = invoke_untyped_proofs.descendants_range[OF pf]
    note caps_no_overlap[simp] = invoke_untyped_proofs.caps_no_overlap[OF pf]

    -- "pspace_no_overlap :"
    have ps_no_overlap[simp]: "ptr && ~~ mask sz \<noteq> ptr \<Longrightarrow> pspace_no_overlap ptr sz s"
      using misc cte_wp_at cover
      apply clarsimp
      apply (erule(3) cte_wp_at_pspace_no_overlapI
        [OF _ _ _ range_cover.sz(1)[where 'a=32, folded word_bits_def]])
      done

    note ex_cte_no_overlap = invoke_untyped_proofs.ex_cte_no_overlap[OF pf]
    note cref_inv = invoke_untyped_proofs.cref_inv[OF pf]

    have slots_invD: "\<And>x. x \<in> set slots
      \<Longrightarrow> fst x \<notin> ?usable_range \<and> caps_of_state s x = Some cap.NullCap
          \<and> ex_cte_cap_wp_to is_cnode_cap x s
          \<and> real_cte_at x s"
      using cte_at misc
      apply -
      apply (drule(1) bspec)+
      apply (clarsimp simp: cte_wp_at_caps_of_state)+
      apply (drule ex_cte_no_overlap)
       apply simp
      done

    note kernel_window_inv[simp] = invoke_untyped_proofs.kernel_window_inv[OF pf]

    have nidx[simp]: "\<And>m. ptr + m - (ptr && ~~ mask sz)
      = (ptr && mask sz) + m"
       apply (subst word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr])
       apply simp
       done

    have non_detype_idx_le[simp]: "ptr \<noteq>  ptr && ~~ mask sz \<Longrightarrow> idx < 2^sz"
       using misc cover
       apply clarsimp
       apply (frule le_mask_le_2p)
       apply (simp add:range_cover_def word_bits_def)+
       done
       
    have idx_compare:
      "\<lbrakk>unat ((ptr && mask sz) + of_nat (length slots) * 2 ^ obj_bits_api tp us) < 2^ sz;
        ptr \<noteq> ptr && ~~ mask sz \<rbrakk>
      \<Longrightarrow> (ptr && ~~ mask sz) + of_nat idx 
      \<le> ptr + (of_nat (length slots) << obj_bits_api tp us)"
       apply (rule range_cover_idx_compare[OF cover ])
         apply assumption+
       apply (frule non_detype_idx_le)
       apply (erule less_imp_le)
       using misc
       apply simp
      done

    have idx_compare'[simp]:"unat ((ptr && mask sz) + (of_nat (length slots)<< obj_bits_api tp us)) \<le> 2 ^ sz"
      apply (rule le_trans[OF unat_plus_gt])
      apply (simp add:range_cover.unat_of_nat_n_shift[OF cover] range_cover_unat)
      apply (insert range_cover.range_cover_compare_bound[OF cover])
      apply simp
      done

    note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]

    have usable_range_subset:
      "ptr && ~~ mask sz \<noteq> ptr
      \<Longrightarrow>usable_untyped_range
                     (cap.UntypedCap (ptr && ~~ mask sz) sz
                       (unat (ptr + (of_nat (length slots) << obj_bits_api tp us) - (ptr && ~~ mask sz))))
                    \<subseteq> usable_untyped_range (cap.UntypedCap (ptr && ~~ mask sz) sz idx)"
      apply (simp_all add:blah field_simps)
      apply (clarsimp simp:shiftl_t2n  add.assoc[symmetric] neg_mask_add_mask )
      apply (simp add:field_simps)
      apply (subst add.commute)
      apply (erule order_trans[OF idx_compare])
      apply (simp add:shiftl_t2n field_simps)+
      done

    have [simp]:"ptr \<noteq> 0"
      using cte_wp_at misc
      apply (clarsimp simp:cte_wp_at_caps_of_state)
      apply (drule(1) caps_of_state_valid)+
      apply (simp add:valid_cap_def)
      done

    have idx_compare''[simp]:
       "unat ((ptr && mask sz) + (of_nat (length slots) * (2::word32) ^ obj_bits_api tp us)) < 2 ^ sz
        \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1
        < ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us"
      apply (rule minus_one_helper,simp)
      apply (rule neq_0_no_wrap)
      apply (rule word32_plus_mono_right_split)
      apply (simp add:shiftl_t2n range_cover_unat[OF cover] field_simps)
      apply (simp add:range_cover.sz
        [where 'a=32, folded word_bits_def, OF cover])+
      done

    note neg_mask_add_mask = word_plus_and_or_coroll2[symmetric,where w = "mask sz" and t = ptr,symmetric]

    have idx_compare'''[simp]:
      "\<lbrakk>unat (of_nat (length slots) * (2::word32) ^ obj_bits_api tp us) < 2 ^ sz;
       ptr && ~~ mask sz = ptr\<rbrakk>
      \<Longrightarrow> ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us - 1
      < ptr + of_nat (length slots) * 2 ^ obj_bits_api tp us "
      apply (rule minus_one_helper,simp)
      apply (simp add:is_aligned_neg_mask_eq'[symmetric])
      apply (rule neq_0_no_wrap)
      apply (rule word32_plus_mono_right_split[where sz = sz])
       apply (simp add:is_aligned_mask)+
      apply (simp add:range_cover.sz[where 'a=32, folded word_bits_def, OF cover])+
      done

    have detype_locale:"ptr && ~~ mask sz = ptr \<Longrightarrow> detype_locale (cap.UntypedCap (ptr && ~~ mask sz) sz idx) (cref,oref) s"
      using cte_at descendants_range misc
      by (simp add:detype_locale_def cte_at descendants_range_def2 blah invs_untyped_children)

    have detype_descendants_range_in:
      "ptr && ~~ mask sz = ptr \<Longrightarrow> descendants_range_in ?usable_range (cref,oref) (detype ?usable_range s)"
      using misc cte_at
      apply -
      apply (frule detype_invariants)
          apply simp
         using descendants_range
         apply (clarsimp simp:blah descendants_range_def2)
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

    have detype_invs:
      "ptr && ~~ mask sz = ptr \<Longrightarrow> invs (detype ?usable_range (clear_um ?usable_range s))"
      apply (insert misc cte_at descendants_range)
      apply clarsimp
      apply (frule detype_invariants)
         apply simp
        apply (clarsimp simp:blah descendants_range_def2)
       apply ((simp add: invs_untyped_children blah
               invs_valid_reply_caps invs_valid_reply_masters)+)[6]
      done
    have detype_Q:
       "ptr && ~~ mask sz = ptr \<Longrightarrow> Q (detype ?usable_range (clear_um ?usable_range s))"
      apply (insert misc cte_at descendants_range)
      apply (frule_tac cap="(UntypedCap ptr sz idx)" in detype_Q)
      apply (simp add: blah)+
      done

    note set_cap_free_index_invs_spec = set_free_index_invs[where cap = "cap.UntypedCap (ptr && ~~ mask sz) sz idx"
      ,unfolded free_index_update_def free_index_of_def,simplified]

    have gen_pd_align[simp]:
      "\<And>pd. tp = ArchObject PageDirectoryObj \<Longrightarrow>
             is_aligned pd pd_bits = is_aligned pd (obj_bits_api tp us)"
      by (simp add: obj_bits_api_def default_arch_object_def
                    pd_bits_def pageBits_def)

    from cover
    have range_cover_pd[simp]:
      "(tp = ArchObject PageDirectoryObj \<longrightarrow>
        range_cover ptr sz (obj_bits_api (ArchObject PageDirectoryObj) us)
                    (length slots))"
      by clarsimp

    note msimp[simp] = misc neg_mask_add_mask
    show "\<lbrace>op = s\<rbrace> invoke_untyped 
        (Invocations_A.untyped_invocation.Retype (cref, oref) (ptr && ~~ mask sz) ptr tp us slots) 
        \<lbrace>\<lambda>rv s. invs s \<and> Q s\<rbrace>"
      using misc cover
      apply (simp add:mapM_x_def[symmetric])
      apply (case_tac "ptr && ~~ mask sz \<noteq> ptr")
       apply (simp add: cte_wp_at_conj ball_conj_distrib
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
                   retype_region_caps_reserved [where sz = sz]
                   retype_region_distinct_sets [where sz = sz]
                   create_caps_invs
                   retype_region_descendants_range_ret[where sz = sz]
                   retype_region_obj_at_other2
                     [where P="is_cap_table n" for n]
                   distinct_tuple_helper)+
         apply ((wp hoare_vcg_const_imp_lift hoare_drop_imp
                    retype_region_invs_extras[where sz = sz]
                    retype_region_aligned_for_init[where sz = sz] | simp)+)[1]
        apply (clarsimp simp:conj_comms,simp cong:conj_cong)
        apply (simp add:ball_conj_distrib conj_comms)
        apply (strengthen imp_consequent invs_mdb invs_valid_pspace
               | clarsimp simp:conj_comms)+
        apply (rule_tac P = "cap = cap.UntypedCap (ptr && ~~ mask sz) sz idx"
                     in hoare_gen_asm)
        apply (simp add:bits_of_def region_in_kernel_window_def)
        apply (wp set_cap_no_overlap hoare_vcg_ball_lift
                  set_cap_free_index_invs_spec
                  set_cap_cte_wp_at set_cap_descendants_range_in
                  set_cap_caps_no_overlap
                  set_untyped_cap_caps_overlap_reserved set_cap_cte_cap_wp_to)
        apply (wp set_cap_cte_wp_at_neg hoare_vcg_all_lift get_cap_wp)
       apply (insert cte_wp_at)
       apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
       apply (insert misc)
       apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
       apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
       apply (intro conjI)
                  apply (clarsimp simp:field_simps range_cover_unat shiftl_t2n)
                 apply (fastforce)+
             apply (clarsimp dest!:retype_addrs_subset_ptr_bits slots_invD)
             apply (drule(1) subsetD)
             apply (simp add:p_assoc_help)
            apply (erule subset_trans[OF range_cover_subset'])
             apply (simp add:vslot)
            apply (clarsimp simp:blah word_and_le2)
           apply (clarsimp simp: blah field_simps add.assoc[symmetric]
                                 add.commute shiftl_t2n
                          dest!: idx_compare'')
           apply simp+
          apply (simp add:Int_ac)
          apply (erule disjoint_subset2[rotated])
          apply (clarsimp simp:blah word_and_le2)
         apply (rule refl)
        apply (clarsimp simp:obj_at_def)
        apply (drule(1) pspace_no_overlap_obj_range
                        [OF ps_no_overlap _ subset_refl])
        apply (drule p_in_obj_range)
          apply (simp add:misc invs_psp_aligned invs_valid_objs)+
        apply blast
       apply clarsimp
       apply (drule untyped_mdb_descendants_range)
             apply (simp add:misc invs_mdb)+
           apply (rule descendants_range)
          apply (clarsimp simp:blah word_and_le2)
         apply assumption+
       apply simp
      apply (simp add: cte_wp_at_conj ball_conj_distrib
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
                  retype_region_caps_reserved [where sz = sz]
                  retype_region_distinct_sets [where sz = sz]
                  create_caps_invs
                  retype_region_descendants_range_ret[where sz = sz]
                  retype_region_obj_at_other2
                    [where P="is_cap_table n" for n]
                  distinct_tuple_helper)+
         apply ((wp hoare_vcg_const_imp_lift hoare_drop_imp
                    retype_region_invs_extras[where sz = sz]
                    retype_region_aligned_for_init[where sz = sz] | simp)+)[1]
        apply (clarsimp simp:conj_comms,simp cong:conj_cong)
        apply (simp add:ball_conj_distrib conj_comms)
        apply (strengthen imp_consequent invs_mdb invs_valid_pspace
               | clarsimp simp:conj_comms)+
        apply (rule_tac P = "cap = cap.UntypedCap ptr sz idx" in hoare_gen_asm)
        apply (simp add:bits_of_def region_in_kernel_window_def)
        apply (wp set_cap_no_overlap hoare_vcg_ball_lift
                  set_untyped_cap_invs_simple
                  set_cap_cte_wp_at set_cap_descendants_range_in
                  set_cap_caps_no_overlap set_untyped_cap_caps_overlap_reserved
                  set_cap_cte_cap_wp_to)
        apply (wp set_cap_cte_wp_at_neg hoare_vcg_all_lift)
       apply (rule_tac P = "cap = cap.UntypedCap ptr sz idx \<and> sz \<le> word_bits 
                            \<and> 2 \<le> sz" in hoare_gen_asm)
       apply (clarsimp simp:delete_objects_rewrite bits_of_def)
       apply (wp get_cap_wp)
      apply (insert cte_wp_at)
      apply (clarsimp simp:cte_wp_at_caps_of_state untyped_range.simps)
      apply (insert misc descendants_range cref_inv cte_at subset_stuff
        detype_locale detype_descendants_range_in detype_invs kernel_window_inv)
      apply (frule(1) valid_global_refsD2[OF _ invs_valid_global_refs])
      apply (clarsimp simp:cte_wp_at_caps_of_state invs_valid_objs
        untyped_range.simps bits_of_def conj_comms)
      apply (frule caps_of_state_valid[rotated])
       apply simp
      apply (frule valid_cap_aligned)
      apply (clarsimp simp:cap_aligned_def detype_clear_um_independent
        intvl_range_conv Int_ac valid_cap_simps)
      apply (intro conjI)
                     apply (clarsimp simp:field_simps range_cover_unat shiftl_t2n)
                    apply ((fastforce)+)[3]
                   apply (clarsimp dest!:retype_addrs_subset_ptr_bits slots_invD)
                   apply (drule(1) subsetD)
                   apply (simp add:p_assoc_help)
                  apply (clarsimp simp: intvl_range_conv[where 'a=32, folded word_bits_def] 
                             dest!:slots_invD)+
                 apply (subst detype_clear_um_independent[symmetric])
                 apply (simp add:detype_Q[simplified])
                apply (rule pspace_no_overlap_detype)
               apply (rule caps_of_state_valid)
                apply simp+
              apply (simp add:invs_psp_aligned invs_valid_objs)+
            apply (rule caps_no_overlap_detype[OF caps_no_overlap])
           apply (frule is_aligned_neg_mask_eq'[THEN iffD2])
           apply (clarsimp simp:blah field_simps add.commute shiftl_t2n is_aligned_mask)
           apply (drule idx_compare'''[rotated])
            apply (clarsimp simp:is_aligned_mask)
           apply (simp add:not_less[symmetric])
          apply (clarsimp dest!:slots_invD)+
          apply (erule cap_to_protected[OF _ _ ])
            apply (fastforce simp:cte_wp_at_caps_of_state)
           apply (simp add:descendants_range_def2 blah)
          apply simp
         apply (clarsimp dest!:slots_invD)+
        apply (simp add:detype_def Int_ac clear_um_def)
       apply (erule descendants_range_in_subseteq)
       apply (simp add:subset_stuff)
      apply (frule is_aligned_neg_mask_eq'[THEN iffD2])
      apply clarsimp
      apply (drule untyped_mdb_descendants_range)
            apply (simp add:misc invs_mdb)+
         apply (clarsimp simp:blah)
        apply assumption+
    apply simp
    done
qed

lemmas invoke_untyp_invs[wp] = 
  invoke_untyp_invs'[where Q=\<top>,simplified hoare_post_taut, OF TrueI TrueI TrueI TrueI TrueI, simplified]

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
  apply (cases ui, simp add:descendants_range_in_def)
  apply (rule hoare_pre)
  apply (wp hoare_vcg_const_Ball_lift hoare_vcg_ex_lift hoare_vcg_imp_lift | wps)+
  apply clarsimp
  done

(* FIXME: move *)
lemma snd_set_zip_in_set:
  "x\<in> snd ` set (zip a b) \<Longrightarrow> x\<in> set b"
  apply (clarsimp)
  apply (erule in_set_zipE)
  apply simp
  done

end
