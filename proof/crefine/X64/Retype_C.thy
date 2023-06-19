(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Retype_C
imports
  Detype_C
  CSpace_All
  StoreWord_C
begin

declare word_neq_0_conv [simp del]

instance cte_C :: array_outer_max_size
  by intro_classes simp

lemma sint_eq_uint:
  "unat (a::machine_word) < 2 ^ 63 \<Longrightarrow> sint a = uint a"
  by (fastforce simp: unat_ucast_less_no_overflow_simp sint_eq_uint not_msb_from_less)

lemma sle_positive: "\<lbrakk> b < 0x8000000000000000; (a :: machine_word) \<le> b \<rbrakk> \<Longrightarrow> a <=s b"
  apply (simp add:word_sle_def)
  apply (subst sint_eq_uint)
   apply (rule unat_less_helper)
   apply simp
  apply (subst sint_eq_uint)
   apply (rule unat_less_helper)
   apply simp
  apply (clarsimp simp:word_le_def)
  done

lemma sless_positive: "\<lbrakk> b < 0x8000000000000000; (a :: machine_word) < b \<rbrakk> \<Longrightarrow> a <s b"
  apply (clarsimp simp: word_sless_def)
  apply (rule conjI)
   apply (erule sle_positive)
   apply simp
  apply simp
  done

lemma zero_le_sint: "\<lbrakk> 0 \<le> (a :: machine_word); a < 0x8000000000000000 \<rbrakk> \<Longrightarrow> 0 \<le> sint a"
  apply (subst sint_eq_uint)
   apply (simp add:unat_less_helper)
  apply simp
  done

context begin interpretation Arch . (*FIXME: arch_split*)

lemma map_option_byte_to_word_heap:
  assumes disj: "\<And>(off :: 9 word) x. x<8 \<Longrightarrow> p + ucast off * 8 + x \<notin> S " (*9=page table index*)
  shows "byte_to_word_heap (\<lambda>x. if x \<in> S then 0 else mem x) p
        = byte_to_word_heap mem p"
  by (clarsimp simp: option_map_def  byte_to_word_heap_def[abs_def]
                     Let_def disj disj[where x = 0,simplified]
              split: option.splits)

text \<open>Generalise the different kinds of retypes to allow more general proofs
about what they might change.\<close>
definition
  ptr_retyps_gen :: "nat \<Rightarrow> ('a :: c_type) ptr \<Rightarrow> bool \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"
where
  "ptr_retyps_gen n p mk_array
    = (if mk_array then ptr_arr_retyps n p else ptr_retyps n p)"

end

context kernel_m
begin

(* Ensure that the given region of memory does not contain any typed memory. *)
definition
  region_is_typeless :: "machine_word \<Rightarrow> nat \<Rightarrow> ('a globals_scheme, 'b) StateSpace.state_scheme \<Rightarrow> bool"
where
  "region_is_typeless ptr sz s \<equiv>
      \<forall>z\<in>{ptr ..+ sz}. snd (snd (t_hrs_' (globals s)) z) = Map.empty"

lemma c_guard_word8:
  "c_guard (p :: word8 ptr) = (ptr_val p \<noteq> 0)"
  unfolding c_guard_def ptr_aligned_def c_null_guard_def
  apply simp
  apply (rule iffI)
   apply (drule intvlD)
   apply clarsimp
  apply simp
  apply (rule intvl_self)
  apply simp
  done

lemma
  "(x \<in> {x ..+ n}) = (n \<noteq> 0)"
  apply (rule iffI)
   apply (drule intvlD)
   apply clarsimp
  apply (rule intvl_self)
  apply simp
  done

lemma heap_update_list_append3:
    "\<lbrakk> s' = s + of_nat (length xs) \<rbrakk> \<Longrightarrow> heap_update_list s (xs @ ys) H = heap_update_list s' ys (heap_update_list s xs H)"
  apply simp
  apply (subst heap_update_list_append [symmetric])
  apply clarsimp
  done

lemma ptr_aligned_machine_word:
  "\<lbrakk> is_aligned p 3  \<rbrakk> \<Longrightarrow> ptr_aligned ((Ptr p) :: machine_word ptr)"
  apply (clarsimp simp: is_aligned_def ptr_aligned_def)
  done

lemma c_guard_machine_word:
  "\<lbrakk> is_aligned (ptr_val p) 3; p \<noteq> NULL  \<rbrakk> \<Longrightarrow> c_guard (p :: (machine_word ptr))"
  apply (clarsimp simp: c_guard_def)
  apply (rule conjI)
   apply (case_tac p, clarsimp simp: ptr_aligned_machine_word)
  apply (case_tac p, simp add: c_null_guard_def)
  apply (subst intvl_aligned_bottom_eq [where n=3 and bits=3], auto simp: word_bits_def)
  done

lemma is_aligned_and_not_zero: "\<lbrakk> is_aligned n k; n \<noteq> 0 \<rbrakk> \<Longrightarrow> 2^k \<le> n"
  apply (metis aligned_small_is_0 word_not_le)
  done

lemma replicate_append [rule_format]: "\<forall>xs. replicate n x @ (x # xs) = replicate (n + 1) x @ xs"
  apply (induct n)
   apply clarsimp
  apply clarsimp
  done

lemmas unat_add_simple =
       iffD1 [OF unat_add_lem [where 'a = 32, folded word_bits_def]]

lemma replicate_append_list [rule_format]:
  "\<forall>n. set L \<subseteq> {0::word8} \<longrightarrow> (replicate n 0 @ L = replicate (n + length L) 0)"
  apply (rule rev_induct)
   apply clarsimp
  apply (rule allI)
  apply (erule_tac x="n+1" in allE)
  apply clarsimp
  apply (subst append_assoc[symmetric])
  apply clarsimp
  apply (subgoal_tac "\<And>n. (replicate n 0 @ [0]) = (0 # replicate n (0 :: word8))")
   apply clarsimp
  apply (induct_tac na)
   apply clarsimp
  apply clarsimp
  done

lemma heap_update_list_replicate:
  "\<lbrakk> set L = {0}; n' = n + length L \<rbrakk> \<Longrightarrow>  heap_update_list s ((replicate n 0) @ L) H = heap_update_list s (replicate n' 0) H"
  apply (subst replicate_append_list)
   apply clarsimp
  apply clarsimp
  done

lemma heap_update_machine_word_is_heap_update_list:
  "heap_update p (x :: machine_word) = heap_update_list (ptr_val p) (to_bytes x a)"
  apply (rule ext)+
  apply (clarsimp simp: heap_update_def)
  apply (clarsimp simp: to_bytes_def typ_info_word)
  done

lemma to_bytes_machine_word_0:
  "to_bytes (0 :: machine_word) xs = [0, 0, 0, 0,0,0,0,0 :: word8]"
  apply (simp add: to_bytes_def typ_info_word word_rsplit_same word_rsplit_0 word_bits_def)
  done

lemma globals_list_distinct_subset:
  "\<lbrakk> globals_list_distinct D symtab xs; D' \<subseteq> D \<rbrakk>
    \<Longrightarrow> globals_list_distinct D' symtab xs"
  by (simp add: globals_list_distinct_def disjoint_subset)

lemma fst_s_footprint:
  "(fst ` s_footprint p) = {ptr_val (p :: 'a ptr)
        ..+ size_of TYPE('a :: c_type)}"
  apply (simp add: s_footprint_def s_footprint_untyped_def)
  apply (auto simp: intvl_def size_of_def image_def)
  done

lemma memzero_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. ptr_val \<acute>s \<noteq> 0 \<and> ptr_val \<acute>s \<le> ptr_val \<acute>s + (\<acute>n - 1)
         \<and> (is_aligned (ptr_val \<acute>s) 3) \<and> (is_aligned (\<acute>n) 3)
         \<and> {ptr_val \<acute>s ..+ unat \<acute>n} \<times> {SIndexVal, SIndexTyp 0} \<subseteq> dom_s (hrs_htd \<acute>t_hrs)
         \<and> gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state \<in> insert 0 {\<acute>n ..}\<rbrace>
    Call memzero_'proc {t.
     t_hrs_' (globals t) = hrs_mem_update (heap_update_list (ptr_val (s_' s))
                                            (replicate (unat (n_' s)) (ucast (0)))) (t_hrs_' (globals s))}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (clarsimp simp: whileAnno_def)
  apply (rule_tac I1="{t. (ptr_val (s_' s) \<le> ptr_val (s_' s) + ((n_' s) - 1) \<and> ptr_val (s_' s) \<noteq> 0) \<and>
                             ptr_val (s_' s) + (n_' s - n_' t) = ptr_val (p___ptr_to_unsigned_char_' t) \<and>
                             n_' t \<le> n_' s \<and>
                             (is_aligned (n_' t) 3) \<and>
                             (is_aligned (n_' s) 3) \<and>
                             (is_aligned (ptr_val (s_' t)) 3) \<and>
                             (is_aligned (ptr_val (s_' s)) 3) \<and>
                             (is_aligned (ptr_val (p___ptr_to_unsigned_char_' t)) 3) \<and>
                             {ptr_val (p___ptr_to_unsigned_char_' t) ..+ unat (n_' t)} \<times> {SIndexVal, SIndexTyp 0}
                                 \<subseteq> dom_s (hrs_htd (t_hrs_' (globals t))) \<and>
                             globals t = (globals s)\<lparr> t_hrs_' :=
                             hrs_mem_update (heap_update_list (ptr_val (s_' s))
                                               (replicate (unat (n_' s - n_' t)) 0))
                                                      (t_hrs_' (globals s))\<rparr> }"
            and V1=undefined in subst [OF whileAnno_def])
  apply vcg
    apply (clarsimp simp add: hrs_mem_update_def)

   apply clarsimp
   apply (case_tac s, case_tac p___ptr_to_unsigned_char)

   apply (subgoal_tac "8 \<le> unat na")
    apply (intro conjI)
           apply (simp add: ptr_safe_def s_footprint_def s_footprint_untyped_def
                            typ_uinfo_t_def typ_info_word)
           apply (erule order_trans[rotated])
            apply (auto intro!: intvlI)[1]
          apply (subst c_guard_machine_word, simp_all)[1]
          apply (clarsimp simp: field_simps)
          apply (metis le_minus' word_leq_minus_one_le olen_add_eqv diff_self word_le_0_iff word_le_less_eq)
         apply (clarsimp simp: field_simps)
        apply (frule is_aligned_and_not_zero)
         apply clarsimp
        apply (rule word_le_imp_diff_le, auto)[1]
       apply clarsimp
       apply (rule aligned_sub_aligned [where n=3], simp_all add: is_aligned_def word_bits_def)[1]
      apply clarsimp
      apply (rule is_aligned_add, simp_all add: is_aligned_def word_bits_def)[1]
     apply (erule order_trans[rotated])
     apply (clarsimp simp: subset_iff)
     apply (erule subsetD[OF intvl_sub_offset, rotated])
     apply (simp add: unat_sub word_le_nat_alt)
    apply (clarsimp simp: word_bits_def hrs_mem_update_def)
    apply (subst heap_update_machine_word_is_heap_update_list [where a="[]"])
    apply (subst heap_update_list_append3[symmetric])
     apply clarsimp
    apply (subst to_bytes_machine_word_0)
    apply (rule heap_update_list_replicate)
     apply clarsimp
    apply (rule_tac s="unat ((n - na) + 8)" in trans)
     apply (simp add: field_simps)
    apply (subst Word.unat_plus_simple[THEN iffD1])
     apply (rule is_aligned_no_overflow''[where n=3, simplified])
      apply (erule(1) aligned_sub_aligned, simp)
     apply (clarsimp simp: field_simps)
     apply (frule_tac x=n in is_aligned_no_overflow'', simp)
     apply simp
    apply simp
   apply (rule dvd_imp_le)
    apply (simp add: is_aligned_def)
   apply (simp add: unat_eq_0[symmetric])
  apply clarsimp
  done

lemma is_aligned_and_2_to_k:
  assumes  mask_2_k: "(n && 2 ^ k - 1) = 0"
  shows "is_aligned (n :: machine_word) k"
proof (subst is_aligned_mask)
  have "mask k = (2 :: machine_word) ^ k - 1"
   by (clarsimp simp: mask_def)
  thus "n && mask k = 0" using mask_2_k
   by simp
qed

lemma memset_spec:
  "\<forall>s. \<Gamma> \<turnstile> \<lbrace>s. ptr_val \<acute>s \<noteq> 0 \<and> ptr_val \<acute>s \<le> ptr_val \<acute>s + (\<acute>n - 1)
         \<and> {ptr_val \<acute>s ..+ unat \<acute>n} \<times> {SIndexVal, SIndexTyp 0} \<subseteq> dom_s (hrs_htd \<acute>t_hrs)
         \<and> gs_get_assn cap_get_capSizeBits_'proc \<acute>ghost'state \<in> insert 0 {\<acute>n ..}\<rbrace>
    Call memset_'proc
   {t. t_hrs_' (globals t) = hrs_mem_update (heap_update_list (ptr_val (s_' s))
                                            (replicate (unat (n_' s)) (ucast (c_' s)))) (t_hrs_' (globals s))}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (clarsimp simp: whileAnno_def)
  apply (rule_tac I1="{t. (ptr_val (s_' s) \<le> ptr_val (s_' s) + ((n_' s) - 1) \<and> ptr_val (s_' s) \<noteq> 0) \<and>
                             c_' t = c_' s \<and>
                             ptr_val (s_' s) + (n_' s - n_' t) = ptr_val (p___ptr_to_unsigned_char_' t) \<and>
                             n_' t \<le> n_' s \<and>
                             {ptr_val (p___ptr_to_unsigned_char_' t) ..+ unat (n_' t)} \<times> {SIndexVal, SIndexTyp 0}
                                \<subseteq> dom_s (hrs_htd (t_hrs_' (globals t))) \<and>
                             globals t = (globals s)\<lparr> t_hrs_' :=
                             hrs_mem_update (heap_update_list (ptr_val (s_' s))
                                               (replicate (unat (n_' s - n_' t)) (ucast (c_' t))))
                                                      (t_hrs_' (globals s))\<rparr>}"
            and V1=undefined in subst [OF whileAnno_def])
  apply vcg
    apply (clarsimp simp add: hrs_mem_update_def del: mod_0_imp_dvd split: if_split_asm)
    apply (subst (asm) word_mod_2p_is_mask [where n=3, simplified], simp)
    apply (subst (asm) word_mod_2p_is_mask [where n=3, simplified], simp)
    apply (rule conjI)
     apply (rule is_aligned_and_2_to_k, clarsimp simp: mask_def)
    apply (rule is_aligned_and_2_to_k, clarsimp simp: mask_def)
   apply clarsimp
   apply (intro conjI)
        apply (simp add: ptr_safe_def s_footprint_def s_footprint_untyped_def
                         typ_uinfo_t_def typ_info_word)
        apply (erule order_trans[rotated])
        apply (auto simp: intvl_self unat_gt_0 intro!: intvlI)[1]
       apply (simp add: c_guard_word8)
       apply (erule subst)
       apply (subst lt1_neq0 [symmetric])
       apply (rule order_trans)
        apply (subst lt1_neq0, assumption)
       apply (erule word_random)
       apply (rule word_le_minus_mono_right)
         apply (simp add: lt1_neq0)
        apply assumption
       apply (erule order_trans [rotated])
       apply (simp add: lt1_neq0)
      apply (case_tac p___ptr_to_unsigned_char, simp add: CTypesDefs.ptr_add_def unat_minus_one field_simps)
     apply (metis word_must_wrap word_not_simps(1) linear)
    apply (erule order_trans[rotated])
    apply (clarsimp simp: ptr_val_case split: ptr.splits)
    apply (erule subsetD[OF intvl_sub_offset, rotated])
    apply (simp add: unat_sub word_le_nat_alt word_less_nat_alt)
   apply (clarsimp simp: ptr_val_case unat_minus_one hrs_mem_update_def split: ptr.splits)
   apply (subgoal_tac "unat (n - (na - 1)) = Suc (unat (n - na))")
    apply (erule ssubst, subst replicate_Suc_append)
    apply (subst heap_update_list_append)
    apply (simp add: heap_update_word8)
   apply (subst unatSuc [symmetric])
    apply (subst add.commute)
    apply (metis word_neq_0_conv word_sub_plus_one_nonzero)
   apply (simp add: field_simps)
  apply (clarsimp)
  apply (metis diff_0_right word_gt_0)
  done

declare snd_get[simp]

declare snd_gets[simp]

lemma snd_when_aligneError[simp]:
  shows "(snd ((when P (alignError sz)) s)) = P"
  by (simp add: when_def alignError_def fail_def split: if_split)

lemma snd_unless_aligneError[simp]:
  shows "(snd ((unless P (alignError sz)) s)) = (\<not> P)"
  by (simp add: unless_def)

lemma lift_t_retyp_heap_same:
  fixes p :: "'a :: mem_type ptr"
  assumes gp: "g p"
  shows "lift_t g (hp, ptr_retyp p td) p = Some (from_bytes (heap_list hp (size_of TYPE('a)) (ptr_val p)))"
  apply (simp add: lift_t_def lift_typ_heap_if s_valid_def hrs_htd_def)
  apply (subst ptr_retyp_h_t_valid)
   apply (rule gp)
  apply simp
  apply (subst heap_list_s_heap_list_dom)
  apply (clarsimp simp: s_footprint_intvl)
  apply simp
  done

lemma lift_t_retyp_heap_same_rep0:
  fixes p :: "'a :: mem_type ptr"
  assumes gp: "g p"
  shows "lift_t g (heap_update_list (ptr_val p) (replicate (size_of TYPE('a)) 0) hp, ptr_retyp p td) p =
  Some (from_bytes (replicate (size_of TYPE('a)) 0))"
  apply (subst lift_t_retyp_heap_same)
   apply (rule gp)
  apply (subst heap_list_update [where v = "replicate (size_of TYPE('a)) 0", simplified])
  apply (rule order_less_imp_le)
  apply simp
  apply simp
  done

lemma lift_t_retyp_heap_other2:
  fixes p :: "'a :: mem_type ptr" and p' :: "'b :: mem_type ptr"
  assumes orth: "{ptr_val p..+size_of TYPE('a)} \<inter> {ptr_val p'..+size_of TYPE('b)} = {}"
  shows "lift_t g (hp, ptr_retyp p td) p' = lift_t g (hp, td) p'"
  apply (simp add: lift_t_def lift_typ_heap_if s_valid_def hrs_htd_def ptr_retyp_disjoint_iff [OF orth])
  apply (cases "td, g \<Turnstile>\<^sub>t p'")
   apply simp
   apply (simp add: h_t_valid_taut heap_list_s_heap_list heap_list_update_disjoint_same
     ptr_retyp_disjoint_iff orth)
  apply (simp add: h_t_valid_taut heap_list_s_heap_list heap_list_update_disjoint_same
    ptr_retyp_disjoint_iff orth)
  done

lemma dom_s_SindexValD:
  "(x, SIndexVal) \<in> dom_s td \<Longrightarrow> fst (td x)"
  unfolding dom_s_def by clarsimp

lemma typ_slice_t_self_nth:
  "\<exists>n < length (typ_slice_t td m). \<exists>b. typ_slice_t td m ! n = (td, b)"
  using typ_slice_t_self [where td = td and m = m]
  by (fastforce simp add: in_set_conv_nth)

lemma ptr_retyp_other_cleared_region:
  fixes p :: "'a :: mem_type ptr" and p' :: "'b :: mem_type ptr"
  assumes  ht: "ptr_retyp p td, g \<Turnstile>\<^sub>t p'"
  and   tdisj: "typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b :: mem_type)"
  and   clear: "\<forall>x \<in> {ptr_val p ..+ size_of TYPE('a)}. \<forall>n b. snd (td x) n \<noteq> Some (typ_uinfo_t TYPE('b), b)"
  shows "{ptr_val p'..+ size_of TYPE('b)} \<inter> {ptr_val p ..+ size_of TYPE('a)} = {}"
proof (rule classical)
  assume asm: "{ptr_val p'..+ size_of TYPE('b)} \<inter> {ptr_val p ..+ size_of TYPE('a)} \<noteq> {}"
  then obtain mv where mvp: "mv \<in> {ptr_val p..+size_of TYPE('a)}"
    and mvp': "mv \<in> {ptr_val p'..+size_of TYPE('b)}"
      by blast

  then obtain k' where mv: "mv = ptr_val p' + of_nat k'" and klt: "k' < size_td (typ_info_t TYPE('b))"
    by (clarsimp dest!: intvlD simp: size_of_def typ_uinfo_size)

  let ?mv = "ptr_val p' + of_nat k'"

  obtain n b where nl: "n < length (typ_slice_t (typ_uinfo_t TYPE('b)) k')"
    and tseq: "typ_slice_t (typ_uinfo_t TYPE('b)) k' ! n = (typ_uinfo_t TYPE('b), b)"
    using typ_slice_t_self_nth [where td = "typ_uinfo_t TYPE('b)" and m = k']
    by clarsimp

  with ht have "snd (ptr_retyp p td ?mv) n = Some (typ_uinfo_t TYPE('b), b)"
    unfolding h_t_valid_def
    apply -
    apply (clarsimp simp: valid_footprint_def Let_def)
    apply (drule spec, drule mp [OF _ klt])
    apply (clarsimp simp: map_le_def)
    apply (drule bspec)
    apply simp
    apply simp
    done

  moreover {
    assume "snd (ptr_retyp p empty_htd ?mv) n = Some (typ_uinfo_t TYPE('b), b)"
    hence "(typ_uinfo_t TYPE('b)) \<in> fst ` set (typ_slice_t (typ_uinfo_t TYPE('a))
                                                 (unat (ptr_val p' + of_nat k' - ptr_val p)))"
      using asm mv mvp
      apply -
      apply (rule_tac x = "(typ_uinfo_t TYPE('b), b)" in image_eqI)
       apply simp
      apply (fastforce simp add: ptr_retyp_footprint list_map_eq in_set_conv_nth split: if_split_asm)
      done

    with typ_slice_set have "(typ_uinfo_t TYPE('b)) \<in> fst ` td_set (typ_uinfo_t TYPE('a)) 0"
      by (rule subsetD)

    hence False using tdisj by (clarsimp simp: tag_disj_def typ_tag_le_def)
  } ultimately show ?thesis using mvp mvp' mv unfolding h_t_valid_def valid_footprint_def
    apply -
    apply (subst (asm) ptr_retyp_d_eq_snd)
    apply (auto simp add: map_add_Some_iff clear)
    done
qed

lemma h_t_valid_not_empty:
  fixes p :: "'a :: c_type ptr"
  shows "\<lbrakk> d,g \<Turnstile>\<^sub>t p; x \<in> {ptr_val p..+size_of TYPE('a)} \<rbrakk> \<Longrightarrow> snd (d x) \<noteq> Map.empty"
  apply (drule intvlD)
  apply (clarsimp simp: h_t_valid_def size_of_def)
  apply (drule valid_footprintD)
   apply (simp add: typ_uinfo_size)
  apply clarsimp
  done

lemma ptr_retyps_out:
  fixes p :: "'a :: mem_type ptr"
  shows "x \<notin> {ptr_val p..+n * size_of TYPE('a)} \<Longrightarrow> ptr_retyps n p td x = td x"
proof (induct n arbitrary: p)
  case 0 thus ?case by simp
next
  case (Suc m)

  have ih: "ptr_retyps m (CTypesDefs.ptr_add p 1) td x = td x"
  proof (rule Suc.hyps)
    from Suc.prems show "x \<notin> {ptr_val (CTypesDefs.ptr_add p 1)..+m * size_of TYPE('a)}"
      apply (rule contrapos_nn)
      apply (erule subsetD [rotated])
      apply (simp add: CTypesDefs.ptr_add_def)
      apply (rule intvl_sub_offset)
      apply (simp add: unat_of_nat)
      done
  qed

  from Suc.prems have "x \<notin> {ptr_val p..+size_of TYPE('a)}"
    apply (rule contrapos_nn)
    apply (erule subsetD [rotated])
    apply (rule intvl_start_le)
    apply simp
    done

  thus ?case
    by (simp add: ptr_retyp_d ih)
qed

lemma image_add_intvl:
  "((+) x) ` {p ..+ n} = {p + x ..+ n}"
  by (auto simp add: intvl_def)

lemma intvl_sum:
  "{p..+ i + j}
    = {p ..+ i} \<union> {(p :: ('a :: len) word) + of_nat i ..+ j}"
  apply (simp add: intvl_def, safe)
    apply clarsimp
    apply (case_tac "k < i")
     apply auto[1]
    apply (drule_tac x="k - i" in spec)
    apply simp
   apply fastforce
  apply (rule_tac x="k + i" in exI)
  apply simp
  done

lemma intvl_Suc_right:
  "{p ..+ Suc n} = {p} \<union> {(p :: ('a :: len) word) + 1 ..+ n}"
  apply (simp add: intvl_sum[where p=p and i=1 and j=n, simplified])
  apply (auto dest: intvl_Suc simp: intvl_self)
  done

lemma htd_update_list_same2:
  "x \<notin> {p ..+ length xs} \<Longrightarrow>
    htd_update_list p xs htd x = htd x"
  by (induct xs arbitrary: p htd, simp_all add: intvl_Suc_right)

lemma ptr_retyps_gen_out:
  fixes p :: "'a :: mem_type ptr"
  shows "x \<notin> {ptr_val p..+n * size_of TYPE('a)} \<Longrightarrow> ptr_retyps_gen n p arr td x = td x"
  apply (simp add: ptr_retyps_gen_def ptr_retyps_out split: if_split)
  apply (clarsimp simp: ptr_arr_retyps_def htd_update_list_same2)
  done

lemma h_t_valid_intvl_htd_contains_uinfo_t:
  "h_t_valid d g (p :: ('a :: c_type) ptr) \<Longrightarrow> x \<in> {ptr_val p ..+ size_of TYPE('a)} \<Longrightarrow>
    (\<exists>n. snd (d x) n \<noteq> None \<and> fst (the (snd (d x) n)) = typ_uinfo_t TYPE ('a))"
  apply (clarsimp simp: h_t_valid_def valid_footprint_def Let_def intvl_def size_of_def)
  apply (drule spec, drule(1) mp)
  apply (cut_tac m=k in typ_slice_t_self[where td="typ_uinfo_t TYPE ('a)"])
  apply (clarsimp simp: in_set_conv_nth)
  apply (drule_tac x=i in map_leD)
   apply simp
  apply fastforce
  done

lemma list_map_override_comono:
  "list_map xs  \<subseteq>\<^sub>m m ++ list_map ys
    \<Longrightarrow> xs \<le> ys \<or> ys \<le> xs"
  apply (simp add: map_le_def list_map_eq map_add_def)
  apply (cases "length xs \<le> length ys")
   apply (simp add: prefix_eq_nth)
  apply (simp split: if_split_asm add: prefix_eq_nth)
  done

lemma list_map_plus_le_not_tag_disj:
  "list_map (typ_slice_t td y) \<subseteq>\<^sub>m m ++ list_map (typ_slice_t td' y')
    \<Longrightarrow> \<not> td \<bottom>\<^sub>t td'"
  apply (drule list_map_override_comono)
  apply (auto dest: typ_slice_sub)
  done

lemma htd_update_list_not_tag_disj:
  "list_map (typ_slice_t td y)
        \<subseteq>\<^sub>m snd (htd_update_list p xs htd x)
    \<Longrightarrow> x \<in> {p ..+ length xs}
    \<Longrightarrow> y < size_td td
    \<Longrightarrow> length xs < addr_card
    \<Longrightarrow> set xs \<subseteq> list_map ` typ_slice_t td' ` {..< size_td td'}
    \<Longrightarrow> \<not> td \<bottom>\<^sub>t td'"
  apply (induct xs arbitrary: p htd)
   apply simp
  apply (clarsimp simp: intvl_Suc_right)
  apply (erule disjE)
   apply clarsimp
   apply (subst(asm) htd_update_list_same2,
     rule intvl_Suc_nmem'[where n="Suc m" for m, simplified])
    apply (simp add: addr_card_def card_word)
   apply (simp add: list_map_plus_le_not_tag_disj)
  apply blast
  done

(* Sigh *)
lemma td_set_offset_ind:
  "\<forall>j. td_set t (Suc j) = (apsnd Suc :: ('a typ_desc \<times> nat) \<Rightarrow> _) ` td_set t j"
  "\<forall>j. td_set_struct ts (Suc j) = (apsnd Suc :: ('a typ_desc \<times> nat) \<Rightarrow> _) ` td_set_struct ts j"
  "\<forall>j. td_set_list xs (Suc j) = (apsnd Suc :: ('a typ_desc \<times> nat) \<Rightarrow> _) ` td_set_list xs j"
  "\<forall>j. td_set_pair x (Suc j) = (apsnd Suc :: ('a typ_desc \<times> nat) \<Rightarrow> _) ` td_set_pair x j"
  apply (induct t and ts and xs and x)
  apply (simp_all add: image_Un)
  done

lemma td_set_offset:
  "(td, i) \<in> td_set td' j \<Longrightarrow> (td, i - j) \<in> td_set td' 0"
  by (induct j arbitrary: i, auto simp: td_set_offset_ind)

lemma typ_le_uinfo_array_tag_n_m:
  "0 < n \<Longrightarrow> td \<le> uinfo_array_tag_n_m TYPE('a :: c_type) n m
    = (td \<le> typ_uinfo_t TYPE('a) \<or> td = uinfo_array_tag_n_m TYPE('a) n m)"
proof -
  have ind: "\<And>xs cs. \<forall>n'. td_set_list (map (\<lambda>i. DTPair (typ_uinfo_t TYPE('a)) (cs i)) xs) n'
    \<subseteq> (fst ` (\<Union>i. td_set (typ_uinfo_t TYPE('a)) i)) \<times> UNIV"
    apply (induct_tac xs)
     apply clarsimp
    apply clarsimp
    apply (fastforce intro: image_eqI[rotated])
    done
  assume "0 < n"
  thus ?thesis
    apply (simp add: uinfo_array_tag_n_m_def typ_tag_le_def upt_conv_Cons)
    apply (auto dest!: ind[rule_format, THEN subsetD], (blast dest: td_set_offset)+)
    done
qed

lemma h_t_array_valid_retyp:
  "0 < n \<Longrightarrow> n * size_of TYPE('a) < addr_card
    \<Longrightarrow> h_t_array_valid (ptr_arr_retyps n p htd) (p :: ('a :: wf_type) ptr) n"
  apply (clarsimp simp: ptr_arr_retyps_def h_t_array_valid_def
                        valid_footprint_def)
  apply (simp add: htd_update_list_index intvlI mult.commute)
  apply (simp add: addr_card_wb unat_of_nat64)
  done

lemma valid_call_Spec_eq_subset:
"\<Gamma>' procname = Some (Spec R)
\<Longrightarrow> (\<forall>x. \<Gamma>'\<Turnstile>\<^bsub>/NF\<^esub> (P x) Call procname (Q x),(A x))
  = ((\<forall>x. P x \<subseteq> fst ` R) \<and> (R \<subseteq> (\<Inter>x. (- P x) \<times> UNIV \<union> UNIV \<times> Q x)))"
  supply image_cong_simp [cong del]
  apply (safe, simp_all)
    apply (clarsimp simp: HoarePartialDef.valid_def)
    apply (rule ccontr)
    apply (elim allE, subst(asm) imageI, assumption)
    apply (drule mp, erule exec.Call, rule exec.SpecStuck)
     apply (auto simp: image_def)[2]
   apply (clarsimp simp: HoarePartialDef.valid_def)
   apply (elim allE, drule mp, erule exec.Call, erule exec.Spec)
   apply auto[1]
  apply (clarsimp simp: HoarePartialDef.valid_def)
  apply (erule exec_Normal_elim_cases, simp_all)
  apply (erule exec_Normal_elim_cases, auto simp: image_def)
   apply blast
  apply (thin_tac "R \<subseteq> _", fastforce)
  done

lemma field_of_t_refl:
  "field_of_t p p' = (p = p')"
  apply (safe, simp_all add: field_of_t_def field_of_self)
  apply (simp add: field_of_def)
  apply (drule td_set_size_lte)
  apply (simp add: unat_eq_0)
  done

lemma h_t_valid_ptr_retyps_gen:
  assumes sz: "nptrs * size_of TYPE('a :: mem_type) < addr_card"
    and gd: "gd p'"
  shows
  "(p' \<in> ((+\<^sub>p) (Ptr p :: 'a ptr) \<circ> int) ` {k. k < nptrs})
    \<Longrightarrow> h_t_valid (ptr_retyps_gen nptrs (Ptr p :: 'a ptr) arr htd) gd p'"
  using gd sz
  apply (cases arr, simp_all add: ptr_retyps_gen_def)
   apply (cases "nptrs = 0")
    apply simp
   apply (cut_tac h_t_array_valid_retyp[where p="Ptr p" and htd=htd, OF _ sz], simp_all)
   apply clarsimp
   apply (drule_tac k=x in h_t_array_valid_field, simp_all)
  apply (induct nptrs arbitrary: p htd)
   apply simp
  apply clarsimp
  apply (case_tac x, simp_all add: ptr_retyp_h_t_valid)
  apply (rule ptr_retyp_disjoint)
   apply (elim meta_allE, erule meta_mp, rule image_eqI[rotated], simp)
   apply (simp add: field_simps)
  apply simp
  apply (cut_tac p=p and z="size_of TYPE('a)"
    and k="Suc nat * size_of TYPE('a)" in init_intvl_disj)
   apply (erule order_le_less_trans[rotated])
   apply (simp del: mult_Suc)
  apply (simp add: field_simps Int_ac)
  apply (erule disjoint_subset[rotated] disjoint_subset2[rotated])
  apply (rule intvl_start_le, simp)
  done

lemma ptr_retyps_gen_not_tag_disj:
  "x \<in> {p ..+ n * size_of TYPE('a :: mem_type)}
    \<Longrightarrow> list_map (typ_slice_t td y)
        \<subseteq>\<^sub>m snd (ptr_retyps_gen n (Ptr p :: 'a ptr) arr htd x)
    \<Longrightarrow> y < size_td td
    \<Longrightarrow> n * size_of TYPE('a) < addr_card
    \<Longrightarrow> 0 < n
    \<Longrightarrow> \<not> td \<bottom>\<^sub>t typ_uinfo_t TYPE('a)"
  apply (simp add: ptr_retyps_gen_def ptr_arr_retyps_def
            split: if_split_asm)
   apply (drule_tac td'="uinfo_array_tag_n_m TYPE('a) n n"
     in htd_update_list_not_tag_disj, simp+)
    apply (clarsimp simp: mult.commute)
   apply (clarsimp simp: tag_disj_def)
   apply (erule disjE)
    apply (metis order_refl typ_le_uinfo_array_tag_n_m)
   apply (erule notE, erule order_trans[rotated])
   apply (simp add: typ_le_uinfo_array_tag_n_m)
  apply clarsimp
  apply (induct n arbitrary: p htd, simp_all)
  apply (case_tac "x \<in> {p ..+ size_of TYPE('a)}")
   apply (simp add: intvl_sum ptr_retyp_def)
   apply (drule_tac td'="typ_uinfo_t TYPE('a)"
     in htd_update_list_not_tag_disj, simp+)
    apply (clarsimp simp add: typ_slices_def size_of_def)
   apply simp
  apply (simp add: intvl_sum)
  apply (case_tac "n = 0")
   apply simp
  apply (simp add: ptr_retyps_out[where n=1, simplified])
  apply blast
  done

lemma ptr_retyps_gen_valid_footprint:
  assumes cleared: "region_is_bytes' p (n * size_of TYPE('a)) htd"
    and distinct: "td \<bottom>\<^sub>t typ_uinfo_t TYPE('a)"
    and not_byte: "td \<noteq> typ_uinfo_t TYPE(word8)"
    and sz: "n * size_of TYPE('a) < addr_card"
  shows
  "valid_footprint (ptr_retyps_gen n (Ptr p :: 'a :: mem_type ptr) arr htd) p' td
    = (valid_footprint htd p' td)"
  apply (cases "n = 0")
   apply (simp add: ptr_retyps_gen_def ptr_arr_retyps_def split: if_split)
  apply (simp add: valid_footprint_def Let_def)
  apply (intro conj_cong refl, rule all_cong)
  apply (case_tac "p' + of_nat y \<in> {p ..+ n * size_of TYPE('a)}")
   apply (simp_all add: ptr_retyps_gen_out)
  apply (rule iffI; clarsimp)
   apply (frule(1) ptr_retyps_gen_not_tag_disj, (simp add: sz)+)
   apply (simp add: distinct)
  apply (cut_tac m=y in typ_slice_t_self[where td=td])
  apply (clarsimp simp: in_set_conv_nth)
  apply (drule_tac x=i in map_leD)
   apply simp
  apply (simp add: cleared[unfolded region_is_bytes'_def] not_byte)
  done

lemma list_map_length_is_None [simp]:
  "list_map xs (length xs) = None"
  apply (induct xs)
   apply (simp add: list_map_def)
  apply (simp add: list_map_def)
  done

lemma list_map_append_one:
  "list_map (xs @ [x]) = [length xs \<mapsto> x] ++ list_map xs"
  by (simp add: list_map_def)

lemma ptr_retyp_same_cleared_region:
  fixes p :: "'a :: mem_type ptr" and p' :: "'a :: mem_type ptr"
  assumes  ht: "ptr_retyp p td, g \<Turnstile>\<^sub>t p'"
  shows "p = p' \<or> {ptr_val p..+ size_of TYPE('a)} \<inter> {ptr_val p' ..+ size_of TYPE('a)} = {}"
  using ht
  by (simp add: h_t_valid_ptr_retyp_eq[where p=p and p'=p'] field_of_t_refl
         split: if_split_asm)

lemma h_t_valid_ptr_retyp_inside_eq:
  fixes p :: "'a :: mem_type ptr" and p' :: "'a :: mem_type ptr"
  assumes inside: "ptr_val p' \<in> {ptr_val p ..+ size_of TYPE('a)}"
  and         ht: "ptr_retyp p td, g \<Turnstile>\<^sub>t p'"
  shows   "p = p'"
  using ptr_retyp_same_cleared_region[OF ht] inside mem_type_self[where p=p']
  by blast

lemma ptr_add_orth:
  fixes p :: "'a :: mem_type ptr"
  assumes lt: "Suc n * size_of TYPE('a) < 2 ^ word_bits"
  shows "{ptr_val p..+size_of TYPE('a)} \<inter> {ptr_val (CTypesDefs.ptr_add p 1)..+n * size_of TYPE('a)} = {}"
  using lt
  apply -
  apply (rule disjointI)
  apply clarsimp
  apply (drule intvlD)+
  apply (clarsimp simp: CTypesDefs.ptr_add_def)
  apply (simp only: Abs_fnat_hom_add)
  apply (drule unat_cong)
  apply (simp only: unat_of_nat)
  apply (unfold word_bits_len_of)
   apply (simp add: addr_card_wb [symmetric])
  done

lemma h_t_valid_ptr_retyps_gen_same:
  assumes guard: "\<forall>n' < nptrs. gd (CTypesDefs.ptr_add (Ptr p :: 'a ptr) (of_nat n'))"
  assumes cleared: "region_is_bytes' p (nptrs * size_of TYPE('a :: mem_type)) htd"
  and not_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(word8)"
  assumes sz: "nptrs * size_of TYPE('a) < addr_card"
  shows
  "h_t_valid (ptr_retyps_gen nptrs (Ptr p :: 'a ptr) arr htd) gd p'
    = ((p' \<in> ((+\<^sub>p) (Ptr p :: 'a ptr) \<circ> int) ` {k. k < nptrs}) \<or> h_t_valid htd gd p')"
  (is "h_t_valid ?htd' gd p' = (p' \<in> ?S \<or> h_t_valid htd gd p')")
proof (cases "{ptr_val p' ..+ size_of TYPE('a)} \<inter> {p ..+ nptrs * size_of TYPE('a)} = {}")
  case True

  from True have notin:
    "p' \<notin> ?S"
    apply clarsimp
    apply (drule_tac x="p + of_nat (x * size_of TYPE('a))" in eqset_imp_iff)
    apply (simp only: Int_iff empty_iff simp_thms)
    apply (subst(asm) intvlI, simp)
    apply (simp add: intvl_self)
    done

  from True have same: "\<forall>y < size_of TYPE('a). ?htd' (ptr_val p' + of_nat y)
        = htd (ptr_val p' + of_nat y)"
    apply clarsimp
    apply (rule ptr_retyps_gen_out)
    apply simp
    apply (blast intro: intvlI)
    done

  show ?thesis
    by (clarsimp simp: h_t_valid_def valid_footprint_def Let_def
                       notin same size_of_def[symmetric, where t="TYPE('a)"]
             cong del: image_cong_simp)
next
  case False

  from False have nvalid: "\<not> h_t_valid htd gd p'"
    apply (clarsimp simp: h_t_valid_def valid_footprint_def set_eq_iff
                          Let_def size_of_def[symmetric, where t="TYPE('a)"]
                          intvl_def[where x="(ptr_val p', a)" for a])
    apply (drule cleared[unfolded region_is_bytes'_def, THEN bspec])
    apply (drule spec, drule(1) mp, clarsimp)
    apply (cut_tac m=k in typ_slice_t_self[where td="typ_uinfo_t TYPE ('a)"])
    apply (clarsimp simp: in_set_conv_nth)
    apply (drule_tac x=i in map_leD, simp_all)
    apply (simp add: not_byte)
    done

  have mod_split: "\<And>k. k < nptrs * size_of TYPE('a)
    \<Longrightarrow> \<exists>quot rem. k = quot * size_of TYPE('a) + rem \<and> rem < size_of TYPE('a) \<and> quot < nptrs"
    apply (intro exI conjI, rule div_mult_mod_eq[symmetric])
     apply simp
    apply (simp add: More_Divides.td_gal_lt)
    done

  have gd: "\<And>p'. p' \<in> ?S \<Longrightarrow> gd p'"
    using guard by auto

  note htv = h_t_valid_ptr_retyps_gen[where gd=gd, OF sz gd]

  show ?thesis using False
    apply (simp add: nvalid)
    apply (rule iffI, simp_all add: htv)
    apply (clarsimp simp: set_eq_iff intvl_def[where x="(p, a)" for a])
    apply (drule mod_split, clarsimp)
    apply (frule_tac htv[OF imageI, simplified])
     apply fastforce
    apply (rule ccontr)
    apply (drule(1) h_t_valid_neq_disjoint)
      apply simp
     apply (clarsimp simp: field_of_t_refl)
    apply (simp add: set_eq_iff)
    apply (drule spec, drule(1) mp)
    apply (subst(asm) add.assoc[symmetric], subst(asm) intvlI, assumption)
    apply simp
    done
qed

lemma clift_ptr_retyps_gen_memset_same:
  assumes guard: "\<forall>n' < n. c_guard (CTypesDefs.ptr_add (Ptr p :: 'a :: mem_type ptr) (of_nat n'))"
  assumes cleared: "region_is_bytes' p (n * size_of TYPE('a :: mem_type)) (hrs_htd hrs)"
    and not_byte: "typ_uinfo_t TYPE('a :: mem_type) \<noteq> typ_uinfo_t TYPE(word8)"
  and nb: "nb = n * size_of TYPE ('a)"
  and sz: "n * size_of TYPE('a) < 2 ^ word_bits"
  shows "(clift (hrs_htd_update (ptr_retyps_gen n (Ptr p :: 'a :: mem_type ptr) arr)
              (hrs_mem_update (heap_update_list p (replicate nb 0))
               hrs)) :: 'a :: mem_type typ_heap)
         = (\<lambda>y. if y \<in> (CTypesDefs.ptr_add (Ptr p :: 'a :: mem_type ptr) o of_nat) ` {k. k < n}
                then Some (from_bytes (replicate (size_of TYPE('a  :: mem_type)) 0)) else clift hrs y)"
  supply if_cong[cong]
  using sz
  apply (simp add: nb liftt_if[folded hrs_mem_def hrs_htd_def]
                   hrs_htd_update hrs_mem_update
                   h_t_valid_ptr_retyps_gen_same[OF guard cleared not_byte]
                   addr_card_wb)
  apply (rule ext, rename_tac p')
  apply (case_tac "p' \<in> ((+\<^sub>p) (Ptr p) \<circ> int) ` {k. k < n}")
   apply (clarsimp simp: h_val_def)
   apply (simp only: Word.Abs_fnat_hom_mult hrs_mem_update)
   apply (frule_tac k="size_of TYPE('a)" in mult_le_mono1[where j=n, OF Suc_leI])
   apply (subst heap_list_update_list; simp?)
   apply (simp add: addr_card_def card_word word_bits_def)
  apply (clarsimp split: if_split)
  apply (simp add: h_val_def)
  apply (subst heap_list_update_disjoint_same, simp_all)
  apply (simp add: region_is_bytes_disjoint[OF cleared not_byte])
  done

lemma clift_ptr_retyps_gen_prev_memset_same:
  assumes guard: "\<forall>n' < n. c_guard (CTypesDefs.ptr_add (Ptr p :: 'a :: mem_type ptr) (of_nat n'))"
  assumes cleared: "region_is_bytes' p (n * size_of TYPE('a :: mem_type)) (hrs_htd hrs)"
    and not_byte: "typ_uinfo_t TYPE('a :: mem_type) \<noteq> typ_uinfo_t TYPE(word8)"
  and nb: "nb = n * size_of TYPE ('a)"
  and sz: "n * size_of TYPE('a) < 2 ^ word_bits"
  and rep0:  "heap_list (hrs_mem hrs) nb p = replicate nb 0"
  shows "(clift (hrs_htd_update (ptr_retyps_gen n (Ptr p :: 'a :: mem_type ptr) arr) hrs) :: 'a :: mem_type typ_heap)
         = (\<lambda>y. if y \<in> (CTypesDefs.ptr_add (Ptr p :: 'a :: mem_type ptr) o of_nat) ` {k. k < n}
                then Some (from_bytes (replicate (size_of TYPE('a  :: mem_type)) 0)) else clift hrs y)"
  using rep0
  apply (subst clift_ptr_retyps_gen_memset_same[symmetric, OF guard cleared not_byte nb sz])
  apply (rule arg_cong[where f=clift])
  apply (rule_tac f="hrs_htd_update f" for f in arg_cong)
  apply (cases hrs, simp add: hrs_mem_update_def)
  apply (simp add: heap_update_list_id hrs_mem_def)
  done

lemma clift_ptr_retyps_gen_other:
  assumes cleared: "region_is_bytes' (ptr_val p) (nptrs * size_of TYPE('a :: mem_type)) (hrs_htd hrs)"
  and sz: "nptrs * size_of TYPE('a) < 2 ^ word_bits"
  and other: "typ_uinfo_t TYPE('b)  \<bottom>\<^sub>t typ_uinfo_t TYPE('a)"
  and not_byte: "typ_uinfo_t TYPE('b :: mem_type) \<noteq> typ_uinfo_t TYPE(word8)"
  shows "(clift (hrs_htd_update (ptr_retyps_gen nptrs (p :: 'a ptr) arr) hrs) :: 'b :: mem_type typ_heap)
         = clift hrs"
  using sz cleared
  apply (cases p)
  apply (simp add: liftt_if[folded hrs_mem_def hrs_htd_def]
                   h_t_valid_def hrs_htd_update
                   ptr_retyps_gen_valid_footprint[simplified addr_card_wb, OF _ other not_byte sz]
              cong: if_cong)
  done

lemma clift_heap_list_update_no_heap_other:
  assumes cleared: "region_is_bytes' p (length xs) (hrs_htd hrs)"
  and not_byte: "typ_uinfo_t TYPE('a :: c_type) \<noteq> typ_uinfo_t TYPE(word8)"
  shows "clift (hrs_mem_update (heap_update_list p xs) hrs) = (clift hrs :: 'a typ_heap)"
  apply (clarsimp simp: liftt_if[folded hrs_mem_def hrs_htd_def] hrs_mem_update
                        fun_eq_iff h_val_def split: if_split)
  apply (subst heap_list_update_disjoint_same, simp_all)
  apply (clarsimp simp: set_eq_iff h_t_valid_def valid_footprint_def Let_def
                 dest!: intvlD[where n="size_of TYPE('a)"])
  apply (drule_tac x="of_nat k" in spec, clarsimp simp: size_of_def)
  apply (cut_tac m=k in typ_slice_t_self[where td="typ_uinfo_t TYPE('a)"])
  apply (clarsimp simp: in_set_conv_nth)
  apply (drule_tac x=i in map_leD, simp)
  apply (simp add: cleared[unfolded region_is_bytes'_def] not_byte size_of_def)
  done

lemma add_is_injective_ring:
  "inj ((+) (x :: 'a :: ring))"
  by (rule inj_onI, clarsimp)

(* assumes that y & elements are n-aligned but not that the compound
   interval is aligned to a higher power of two. needed for cte arrays. *)
lemma ptr_span_disjoint_ptr_set_span:
  fixes y :: "('a :: mem_type) ptr"
  assumes align: "is_aligned p n"
  and size_of: "size_of TYPE('a) = 2 ^ n"
  and al: "is_aligned (ptr_val y) n"
  and card: "b * 2 ^ n < addr_card"
  and b: "b \<noteq> 0"
  shows "y \<notin> ((+\<^sub>p) (Ptr p) \<circ> int) ` {k. k < b}
    \<longrightarrow> ptr_span y \<inter> {p ..+ b * 2 ^ n} = {}"
proof -
  from card b have word_bits: "n < word_bits"
    using power_increasing[where n=word_bits and N=n and a=2]
    apply (simp add: word_bits_def addr_card)
    apply (rule ccontr, simp)
    apply (cases b, simp_all)
    apply (drule(1) order_less_le_trans)
    apply simp
    done

  note al_sub = aligned_sub_aligned_simple[OF al align]

  have yuck: "of_nat b * 2 ^ n \<noteq> (0 :: machine_word)"
    using of_nat_neq_0[where k="b * 2 ^ n" and 'a=machine_word_len] b card
    by (clarsimp simp: addr_card_def card_word)

  show ?thesis
    supply image_cong_simp [cong del]
    apply (clarsimp simp add: size_of)
    apply (rule inj_image_eq_iff[OF add_is_injective_ring[where x="- p"], THEN iffD1])
    apply (subst image_Int[OF add_is_injective_ring])
    apply (simp add: image_add_intvl upto_intvl_eq al_sub)
    apply (subst upto_intvl_eq', simp, simp add: b)
     apply (cut_tac card, simp add: addr_card_def card_word)
    apply safe
    apply (simp only: mask_in_range[symmetric] al_sub)
    apply simp
    apply (drule_tac f="(+) p" in arg_cong, simp)
    apply (erule notE, rule_tac x="unat (x >> n)" in image_eqI)
     apply (simp add: size_of)
     apply (cases y, clarsimp simp: and_not_mask shiftl_t2n)
    apply (simp add: shiftr_div_2n')
    apply (rule More_Divides.td_gal_lt[THEN iffD1], simp)
    apply (drule word_leq_minus_one_le[OF yuck])
    apply (rule unat_less_helper, simp)
    done
qed

lemma ptr_retyp_to_array:
  "ptr_retyps_gen 1 (p :: (('a :: wf_type)['b :: finite]) ptr) False
    = ptr_retyps_gen CARD('b) (ptr_coerce p :: 'a ptr) True"
  by (intro ext, simp add: ptr_retyps_gen_def ptr_arr_retyps_to_retyp)

lemma projectKO_opt_retyp_other:
  assumes cover: "range_cover ptr sz (objBitsKO ko) n"
  assumes pal: "pspace_aligned' \<sigma>"
  assumes pno: "pspace_no_overlap' ptr sz \<sigma>"
  and  ko_def: "ko \<equiv> x"
  and  pko: "\<forall>v. (projectKO_opt x :: ('a :: pre_storable) option) \<noteq> Some v"
  shows "projectKO_opt \<circ>\<^sub>m
    (\<lambda>x. if x \<in> set (new_cap_addrs n ptr ko) then Some ko else ksPSpace \<sigma> x)
  = (projectKO_opt \<circ>\<^sub>m (ksPSpace \<sigma>) :: machine_word \<Rightarrow> ('a :: pre_storable) option)" (is "?LHS = ?RHS")
proof (rule ext)
  fix x
  show "?LHS x = ?RHS x"
  proof (cases "x \<in> set (new_cap_addrs n ptr ko)")
    case False
      thus ?thesis by (simp add: map_comp_def)
  next
    case True
      hence "ksPSpace \<sigma> x = None"
        apply -
        apply (cut_tac no_overlap_new_cap_addrs_disjoint [OF cover pal pno])
          apply (rule ccontr)
          apply (clarsimp,drule domI[where a = x])
          apply blast
        done
      thus ?thesis using True pko ko_def by simp
  qed
qed

lemma pspace_aligned_to_C:
  fixes v :: "'a :: pre_storable"
  assumes pal: "pspace_aligned' s"
  and    cmap: "cmap_relation (projectKO_opt \<circ>\<^sub>m (ksPSpace s) :: machine_word \<rightharpoonup> 'a)
                              (cslift x :: 'b :: mem_type typ_heap) Ptr rel"
  and     pko: "projectKO_opt ko = Some v"
  and   pkorl: "\<And>ko' (v' :: 'a).  projectKO_opt ko' = Some v' \<Longrightarrow> objBitsKO ko = objBitsKO ko'"
  shows  "\<forall>x\<in>dom (cslift x :: 'b :: mem_type typ_heap). is_aligned (ptr_val x) (objBitsKO ko)"
  (is "\<forall>x\<in>dom ?CS. is_aligned (ptr_val x) (objBitsKO ko)")
proof
  fix z
  assume "z \<in> dom ?CS"
  hence "z \<in> Ptr ` dom (projectKO_opt \<circ>\<^sub>m (ksPSpace s) :: machine_word \<rightharpoonup> 'a)" using cmap
    by (simp add: cmap_relation_def)
  hence pvz: "ptr_val z \<in> dom (projectKO_opt \<circ>\<^sub>m (ksPSpace s) :: machine_word \<rightharpoonup> 'a)"
    by clarsimp
  then obtain v' :: 'a where "projectKO_opt (the (ksPSpace s (ptr_val z))) = Some v'"
    and pvz: "ptr_val z \<in> dom (ksPSpace s)"
    apply -
    apply (frule map_comp_subset_domD)
    apply (clarsimp simp: dom_def)
    done

  thus "is_aligned (ptr_val z) (objBitsKO ko)" using pal
    unfolding pspace_aligned'_def
    apply -
    apply (drule (1) bspec)
    apply (simp add: pkorl)
    done
qed

lemma pspace_aligned_to_C_cte:
  fixes v :: "cte"
  assumes pal: "pspace_aligned' s"
  and    cmap: "cmap_relation (ctes_of s) (cslift x :: cte_C typ_heap) Ptr ccte_relation"
  and     pko: "projectKO_opt ko = Some v"
  shows  "\<forall>x\<in>dom (cslift x :: cte_C typ_heap). is_aligned (ptr_val x) (objBitsKO ko)"
  (is "\<forall>x\<in>dom ?CS. is_aligned (ptr_val x) (objBitsKO ko)")
proof
  fix z
  assume "z \<in> dom ?CS"
  hence "z \<in> Ptr ` dom (ctes_of s)" using cmap
    by (simp add: cmap_relation_def)
  hence pvz: "ptr_val z \<in> dom (ctes_of s)"
    by clarsimp
  thus "is_aligned (ptr_val z) (objBitsKO ko)" using pal pko
    unfolding pspace_aligned'_def
    apply -
    apply clarsimp
    apply (drule ctes_of_is_aligned)
    apply (cases ko, simp_all add: projectKOs)
    apply (simp add: objBits_simps)
    done
qed

lemma pspace_aligned_to_C_tcb:
  fixes v :: "tcb"
  assumes pal: "pspace_aligned' s"
  and    cmap: "cpspace_tcb_relation (ksPSpace s) (t_hrs_' (globals x))"
  shows  "\<forall>x\<in>dom (cslift x :: tcb_C typ_heap). is_aligned (ptr_val x) ctcb_size_bits"
  (is "\<forall>x\<in>dom ?CS. is_aligned (ptr_val x) ctcb_size_bits")
proof
  fix z
  assume "z \<in> dom ?CS"
  hence "z \<in> tcb_ptr_to_ctcb_ptr ` dom (map_to_tcbs (ksPSpace s))" using cmap
    by (simp add: cmap_relation_def)
  hence pvz: "ctcb_ptr_to_tcb_ptr z \<in> dom (map_to_tcbs (ksPSpace s))"
    by clarsimp
  then obtain v' :: tcb where "projectKO_opt (the (ksPSpace s (ctcb_ptr_to_tcb_ptr z))) = Some v'"
    and pvz: "ctcb_ptr_to_tcb_ptr z \<in> dom (ksPSpace s)"
    apply -
    apply (frule map_comp_subset_domD)
    apply (clarsimp simp: dom_def)
    done

  thus "is_aligned (ptr_val z) ctcb_size_bits" using pal
    unfolding pspace_aligned'_def
    apply -
    apply (drule (1) bspec)
    apply (clarsimp simp add: projectKOs objBits_simps)
    apply (erule ctcb_ptr_to_tcb_ptr_aligned)
    done
qed

lemma ptr_add_to_new_cap_addrs:
  assumes size_of_m: "size_of TYPE('a :: mem_type) = 2 ^ objBitsKO ko"
  shows "(CTypesDefs.ptr_add (Ptr ptr :: 'a :: mem_type ptr) \<circ> of_nat) ` {k. k < n}
   = Ptr ` set (new_cap_addrs n ptr ko)"
  unfolding new_cap_addrs_def
  apply (simp add: image_image shiftl_t2n size_of_m field_simps)
  apply (clarsimp simp: atLeastLessThan_def lessThan_def)
  done

lemma cmap_relation_retype:
  assumes cm: "cmap_relation mp mp' Ptr rel"
  and   rel: "rel (makeObject :: 'a :: pspace_storable) ko'"
  shows "cmap_relation
        (\<lambda>x. if x \<in> addrs then Some (makeObject :: 'a :: pspace_storable) else mp x)
        (\<lambda>y. if y \<in> Ptr ` addrs then Some ko' else mp' y)
        Ptr rel"
  using cm rel
  apply -
  apply (rule cmap_relationI)
   apply (simp add: dom_if cmap_relation_def image_Un)
  apply (case_tac "x \<in> addrs")
   apply simp
  apply simp
  apply (subst (asm) if_not_P)
   apply clarsimp
  apply (erule (2) cmap_relation_relI)
  done

lemma word_rcat_single[simp]:
  "word_rcat [x] = x"
  by (simp add: word_rcat_def bin_rcat_def)

lemma update_ti_t_machine_word_0s:
  "update_ti_t (typ_info_t TYPE(machine_word)) [0,0,0,0,0,0,0,0] X = 0"
  "word_rcat [0, 0, 0, 0,0,0,0,(0 :: word8)] = (0 :: machine_word)"
  by (simp_all add: typ_info_word word_rcat_def bin_rcat_def)

lemma retype_guard_helper:
  assumes cover: "range_cover p sz (objBitsKO ko) n"
  and ptr0: "p \<noteq> 0"
  and szo: "size_of TYPE('a :: c_type) = 2 ^ objBitsKO ko"
  and lt2: "m \<le> objBitsKO ko"
  and ala: "align_of TYPE('a :: c_type) = 2 ^ m"
  shows "\<forall>b < n. c_guard (CTypesDefs.ptr_add (Ptr p :: 'a ptr) (of_nat b))"
proof (rule allI, rule impI)
  fix b :: nat
  assume nv: "b < n"
  let ?p = "(Ptr p :: 'a ptr)"

  have "of_nat b * of_nat (size_of TYPE('a)) = (of_nat (b * 2 ^ objBitsKO ko) :: machine_word)"
    by (simp add: szo)

  also have "\<dots> < (2 :: machine_word) ^ sz" using nv cover
    apply simp
    apply (rule word_less_power_trans_ofnat)
      apply (erule less_le_trans)
      apply (erule range_cover.range_cover_n_le(2))
    apply (erule range_cover.sz)+
    done

  finally have ofn: "of_nat b * of_nat (size_of TYPE('a)) < (2 :: machine_word) ^ sz" .

  have le: "p \<le> p + of_nat b * 2 ^ objBitsKO ko"
    using ofn szo nv
    apply -
    apply (cases b,clarsimp+)
    apply (cut_tac n = nat in range_cover_ptr_le)
     apply (rule range_cover_le[OF cover])
      apply simp
     apply (simp add:ptr0)
    apply (simp add:shiftl_t2n field_simps)
    done

  show "c_guard (CTypesDefs.ptr_add ?p (of_nat b))"
    apply (rule is_aligned_c_guard[OF _ _ ala _ lt2])
      apply (simp add: szo)
      apply (rule is_aligned_add)
       apply (rule range_cover.aligned, rule cover)
      apply (rule is_aligned_mult_triv2)
     apply (simp add: szo neq_0_no_wrap[OF le ptr0])
    apply (simp add: szo)
    done
qed

lemma retype_guard_helper2:
  assumes cover: "range_cover p sz (objBitsKO ko) n"
  and ptr0: "p \<noteq> 0"
  and szo: "size_of TYPE('a :: c_type) = 2 ^ objBitsKO ko"
  and ala: "align_of TYPE('a :: c_type) \<in> set (map (\<lambda>x. 2 ^ x) [0 ..< Suc (objBitsKO ko)])"
  shows "\<forall>b < n. c_guard (CTypesDefs.ptr_add (Ptr p :: 'a ptr) (of_nat b))"
  using ala retype_guard_helper[OF cover ptr0 szo]
  by (clarsimp simp del: upt.simps)

(* When we are retyping, CTEs in the system do not change,
 * unless we happen to be retyping into a CNode or a TCB,
 * in which case new CTEs only pop up in the new object. *)
lemma retype_ctes_helper:
  assumes pal: "pspace_aligned' s"
  and    pdst: "pspace_distinct' s"
  and     pno: "pspace_no_overlap' ptr sz s"
  and      al: "is_aligned ptr (objBitsKO ko)"
  and      sz: "objBitsKO ko \<le> sz"
  and     szb: "sz < word_bits"
  and     mko: "makeObjectKO dev tp = Some ko"
  and      rc: "range_cover ptr sz (objBitsKO ko) n"
  shows  "map_to_ctes (\<lambda>xa. if xa \<in> set (new_cap_addrs n ptr ko) then Some ko else ksPSpace s xa) =
   (\<lambda>x. if tp = Inr (APIObjectType ArchTypes_H.apiobject_type.CapTableObject) \<and> x \<in> set (new_cap_addrs n ptr ko) \<or>
           tp = Inr (APIObjectType ArchTypes_H.apiobject_type.TCBObject) \<and>
           x && ~~ mask tcbBlockSizeBits \<in> set (new_cap_addrs n ptr ko) \<and> x && mask tcbBlockSizeBits \<in> dom tcb_cte_cases
        then Some (CTE capability.NullCap nullMDBNode) else ctes_of s x)"
  using mko pal pdst
proof (rule ctes_of_retype)
  show "pspace_aligned' (s\<lparr>ksPSpace := \<lambda>xa. if xa \<in> set (new_cap_addrs n ptr ko) then Some ko else ksPSpace s xa\<rparr>)"
    using pal pdst pno szb al sz rc
    apply -
    apply (rule retype_aligned_distinct'', simp_all)
    done

  show "pspace_distinct' (s\<lparr>ksPSpace := \<lambda>xa. if xa \<in> set (new_cap_addrs n ptr ko) then Some ko else ksPSpace s xa\<rparr>)"
    using pal pdst pno szb al sz rc
    apply -
    apply (rule retype_aligned_distinct'', simp_all)
    done

  show "\<forall>x\<in>set (new_cap_addrs n ptr ko). is_aligned x (objBitsKO ko)"
    using al szb
    apply -
    apply (rule new_cap_addrs_aligned, simp_all)
    done

  show "\<forall>x\<in>set (new_cap_addrs n ptr ko). ksPSpace s x = None"
    using al szb pno pal rc sz
    apply -
    apply (drule(1) pspace_no_overlap_disjoint')
    apply (frule new_cap_addrs_subset)
    apply (clarsimp simp: More_Word_Operations.ptr_add_def field_simps)
    apply fastforce
    done
qed

lemma ptr_retyps_htd_safe:
  "\<lbrakk> htd_safe D htd;
    {ptr_val ptr ..+ n * size_of TYPE('a :: mem_type)}
        \<subseteq> D \<rbrakk>
   \<Longrightarrow> htd_safe D (ptr_retyps_gen n (ptr :: 'a ptr) arr htd)"
  apply (clarsimp simp: htd_safe_def)
  apply (case_tac "a \<in> {ptr_val ptr..+n * size_of TYPE('a)}")
   apply blast
  apply (case_tac "(a, b) \<in> dom_s htd")
   apply blast
  apply (clarsimp simp: dom_s_def ptr_retyps_gen_out)
  done

lemma ptr_retyps_htd_safe_neg:
  "\<lbrakk> htd_safe D htd; {ptr_val ptr ..+ n * size_of TYPE('a :: mem_type)} \<inter> D' = {}; -D \<subseteq> D' \<rbrakk>
   \<Longrightarrow> htd_safe D (ptr_retyps_gen n (ptr :: 'a ptr) arr htd)"
  using ptr_retyps_htd_safe by blast

lemmas ptr_retyps_htd_safe_neg' = ptr_retyps_htd_safe_neg[OF _ _ subset_refl]

lemma region_is_bytes_subset:
  "region_is_bytes' ptr sz htd
    \<Longrightarrow> {ptr' ..+ sz'} \<subseteq> {ptr ..+ sz}
    \<Longrightarrow> region_is_bytes' ptr' sz' htd"
  by (auto simp: region_is_bytes'_def)

lemma (in range_cover) strong_times_64:
  "len_of TYPE('a) = len_of TYPE(64) \<Longrightarrow> n * 2 ^ sbit < 2 ^ word_bits"
  apply (simp add: nat_mult_power_less_eq)
  apply (rule order_less_le_trans, rule string)
  apply (simp add: word_bits_def)
  done

(* Helper for use in the many proofs below. *)
lemma cslift_ptr_retyp_other_inst:
  assumes   bytes: "region_is_bytes' p (n * (2 ^ bits)) (hrs_htd hp)"
  and       cover: "range_cover p sz bits n"
  and          sz: "region_sz = n * size_of TYPE('a :: mem_type)"
  and         sz2: "size_of TYPE('a :: mem_type) = 2 ^ bits"
  and       tdisj: "typ_uinfo_t TYPE('b) \<bottom>\<^sub>t typ_uinfo_t TYPE('a)"
  and    not_byte: "typ_uinfo_t TYPE('b :: mem_type) \<noteq> typ_uinfo_t TYPE(word8)"
  shows "(clift (hrs_htd_update (ptr_retyps_gen n (Ptr p :: 'a :: mem_type ptr) arr)
               hp) :: 'b :: mem_type typ_heap)
         = clift hp"
  using bytes
  apply (subst clift_ptr_retyps_gen_other[OF _ _ tdisj not_byte], simp_all)
   apply (simp add: sz2)
  apply (simp add: sz2 range_cover.strong_times_64[OF cover])
  done

(* Helper for use in the many proofs below. *)
lemma cslift_ptr_retyp_memset_other_inst:
  assumes   bytes: "region_is_bytes p (n * (2 ^ bits)) x"
  and       cover: "range_cover p sz bits n"
  and          sz: "region_sz = n * size_of TYPE('a :: mem_type)"
  and         sz2: "size_of TYPE('a :: mem_type) = 2 ^ bits"
  and       tdisj: "typ_uinfo_t TYPE('b) \<bottom>\<^sub>t typ_uinfo_t TYPE('a)"
  and    not_byte: "typ_uinfo_t TYPE('b :: mem_type) \<noteq> typ_uinfo_t TYPE(word8)"
  shows "(clift (hrs_htd_update (ptr_retyps_gen n (Ptr p :: 'a :: mem_type ptr) arr)
              (hrs_mem_update (heap_update_list p (replicate (region_sz) 0))
               (t_hrs_' (globals x)))) :: 'b :: mem_type typ_heap)
         = cslift x"
  using bytes
  apply (subst cslift_ptr_retyp_other_inst[OF _ cover sz sz2 tdisj not_byte])
   apply simp
  apply (rule clift_heap_list_update_no_heap_other[OF _ not_byte])
  apply (simp add: hrs_htd_def sz sz2)
  done

lemma ptr_retyps_one:
  "ptr_retyps (Suc 0) = ptr_retyp"
  apply (rule ext)+
  apply simp
  done

lemma uinfo_array_tag_n_m_not_le_typ_name:
  "typ_name (typ_info_t TYPE('b)) @ ''_array_'' @ nat_to_bin_string m
      \<notin> td_names (typ_info_t TYPE('a))
    \<Longrightarrow> \<not> uinfo_array_tag_n_m TYPE('b :: c_type) n m \<le> typ_uinfo_t TYPE('a :: c_type)"
  apply (clarsimp simp: typ_tag_le_def typ_uinfo_t_def)
  apply (drule td_set_td_names)
   apply (clarsimp simp: uinfo_array_tag_n_m_def typ_uinfo_t_def)
   apply (drule arg_cong[where f="\<lambda>xs. set ''r'' \<subseteq> set xs"], simp)
  apply (simp add: uinfo_array_tag_n_m_def typ_uinfo_t_def)
  done

lemma tag_not_le_via_td_name:
  "typ_name (typ_info_t TYPE('a)) \<notin> td_names (typ_info_t TYPE('b))
    \<Longrightarrow> typ_name (typ_info_t TYPE('a)) \<noteq> pad_typ_name
    \<Longrightarrow> \<not> typ_uinfo_t TYPE('a :: c_type) \<le> typ_uinfo_t TYPE ('b :: c_type)"
  apply (clarsimp simp: typ_tag_le_def typ_uinfo_t_def)
  apply (drule td_set_td_names, simp+)
  done

lemma in_set_list_map:
  "x \<in> set xs \<Longrightarrow> \<exists>n. [n \<mapsto> x] \<subseteq>\<^sub>m list_map xs"
  apply (clarsimp simp: in_set_conv_nth)
  apply (rule_tac x=i in exI)
  apply (simp add: map_le_def)
  done

lemma h_t_valid_eq_array_valid:
  "h_t_valid htd gd (p :: (('a :: wf_type)['b :: finite]) ptr)
    = (gd p \<and> h_t_array_valid htd (ptr_coerce p :: 'a ptr) CARD('b))"
  by (auto simp: h_t_array_valid_def h_t_valid_def
                 typ_uinfo_array_tag_n_m_eq)

lemma h_t_array_valid_ptr_retyps_gen:
  assumes sz2: "size_of TYPE('a :: mem_type) = sz"
  assumes bytes: "region_is_bytes' (ptr_val p) (n * sz) htd"
  shows "h_t_array_valid htd p' n'
    \<Longrightarrow> h_t_array_valid (ptr_retyps_gen n (p :: 'a :: mem_type ptr) arr htd) p' n'"
  apply (clarsimp simp: h_t_array_valid_def valid_footprint_def)
  apply (drule spec, drule(1) mp, clarsimp)
  apply (case_tac "ptr_val p' + of_nat y \<in> {ptr_val p ..+ n * size_of TYPE('a)}")
   apply (cut_tac s="uinfo_array_tag_n_m TYPE('b) n' n'" and n=y in ladder_set_self)
   apply (clarsimp dest!: in_set_list_map)
   apply (drule(1) map_le_trans)
   apply (simp add: map_le_def)
   apply (subst(asm) bytes[unfolded region_is_bytes'_def, rule_format, symmetric])
     apply (simp add: sz2)
    apply (simp add: uinfo_array_tag_n_m_def typ_uinfo_t_def typ_info_word)
   apply simp
  apply (simp add: ptr_retyps_gen_out)
  done

lemma cvariable_array_ptr_retyps:
  assumes sz2: "size_of TYPE('a :: mem_type) = sz"
  assumes bytes: "region_is_bytes' (ptr_val p) (n * sz) htd"
  shows "cvariable_array_map_relation m ns ptrfun htd
    \<Longrightarrow> cvariable_array_map_relation m ns (ptrfun :: _ \<Rightarrow> ('b :: mem_type) ptr)
            (ptr_retyps_gen n (p :: 'a :: mem_type ptr) arr htd)"
  by (clarsimp simp: cvariable_array_map_relation_def
                     h_t_array_valid_ptr_retyps_gen[OF sz2 bytes])

lemma cvariable_array_ptr_upd:
  assumes at: "h_t_array_valid htd (ptrfun x) (ns y)"
  shows "cvariable_array_map_relation m ns ptrfun htd
    \<Longrightarrow> cvariable_array_map_relation (m(x \<mapsto> y))
        ns (ptrfun :: _ \<Rightarrow> ('b :: mem_type) ptr) htd"
  by (clarsimp simp: cvariable_array_map_relation_def at
              split: if_split)

lemma clift_eq_h_t_valid_eq:
  "clift hp = (clift hp' :: ('a :: c_type) ptr \<Rightarrow> _)
    \<Longrightarrow> (h_t_valid (hrs_htd hp) c_guard :: 'a ptr \<Rightarrow> _)
        = h_t_valid (hrs_htd hp') c_guard"
  by (rule ext, simp add: h_t_valid_clift_Some_iff)

lemma region_is_bytes_typ_region_bytes:
  "{ptr ..+ len} \<le> {ptr' ..+ 2 ^ bits}
    \<Longrightarrow> region_is_bytes' ptr len (typ_region_bytes ptr' bits htd)"
  apply (clarsimp simp: region_is_bytes'_def typ_region_bytes_def hrs_htd_update)
  apply (simp add: subsetD split: if_split_asm)
  done

lemma region_actually_is_bytes_retyp_disjoint:
  "{ptr ..+ sz} \<inter> {ptr_val (p :: 'a ptr)..+n * size_of TYPE('a :: mem_type)} = {}
    \<Longrightarrow> region_actually_is_bytes' ptr sz htd
    \<Longrightarrow> region_actually_is_bytes' ptr sz (ptr_retyps_gen n p arr htd)"
  apply (clarsimp simp: region_actually_is_bytes'_def del: impI)
  apply (subst ptr_retyps_gen_out)
   apply blast
  apply simp
  done

lemma intvl_plus_unat_eq:
  "p \<le> p + x - 1 \<Longrightarrow> x \<noteq> 0
    \<Longrightarrow> {p ..+ unat x} = {p .. p + x - 1}"
  apply (subst upto_intvl_eq', simp_all add: unat_eq_0 field_simps)
  apply (rule order_less_imp_le, simp)
  done

lemma zero_ranges_ptr_retyps:
  "zero_ranges_are_zero (gsUntypedZeroRanges s) hrs
    \<Longrightarrow> caps_overlap_reserved' {ptr_val (p :: 'a ptr) ..+ n * size_of TYPE ('a :: mem_type)} s
    \<Longrightarrow> untyped_ranges_zero' s
    \<Longrightarrow> valid_objs' s
    \<Longrightarrow> zero_ranges_are_zero (gsUntypedZeroRanges s)
       (hrs_htd_update (ptr_retyps_gen n p arr) hrs)"
  apply (clarsimp simp: zero_ranges_are_zero_def untyped_ranges_zero_inv_def
                        hrs_htd_update)
  apply (drule(1) bspec, clarsimp)
  apply (rule region_actually_is_bytes_retyp_disjoint, simp_all)
  apply (clarsimp simp: map_comp_Some_iff cteCaps_of_def
                 elim!: ranE)
  apply (frule(1) ctes_of_valid')
  apply (simp add: caps_overlap_reserved'_def,
      drule bspec, erule ranI)
  apply (frule(1) untypedZeroRange_to_usableCapRange)
  apply (clarsimp simp: isCap_simps untypedZeroRange_def
                        getFreeRef_def max_free_index_def
                 split: if_split_asm)
  apply (erule disjoint_subset[rotated])
  apply (subst intvl_plus_unat_eq)
    apply clarsimp
   apply clarsimp
   apply (clarsimp simp: word_unat.Rep_inject[symmetric]
                         valid_cap_simps' capAligned_def
                         unat_of_nat
               simp del: word_unat.Rep_inject)
  apply clarsimp
  done

abbreviation
  "ret_zero ptr sz
    \<equiv> valid_objs' and untyped_ranges_zero' and caps_overlap_reserved' {ptr ..+ sz}"

lemma createObjects_ccorres_ep:
  defines "ko \<equiv> (KOEndpoint (makeObject :: endpoint))"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr
  \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (n * (2 ^ objBitsKO ko)) \<sigma>
  \<and> region_is_zero_bytes ptr (n * (2 ^ objBitsKO ko)) x
  \<and> range_cover ptr sz (objBitsKO ko) n
  \<and> {ptr ..+ n * (2 ^ objBitsKO ko)} \<inter> kernel_data_refs = {}
  \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs n ptr ko) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen n (Ptr ptr :: endpoint_C ptr) False)
                   (t_hrs_' (globals x))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "Ptr ptr :: endpoint_C ptr"

  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr"
    and cover: "range_cover ptr sz (objBitsKO ko) n"
    and al: "is_aligned ptr (objBitsKO ko)" and ptr0: "ptr \<noteq> 0"
    and sz: "objBitsKO ko \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (n * (2 ^ objBitsKO ko)) \<sigma>"
    and empty: "region_is_bytes ptr (n * (2 ^ objBitsKO ko)) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (n * (2 ^ objBitsKO ko))"
    and rc: "range_cover ptr sz (objBitsKO ko) n"
    and kdr: "{ptr..+n * (2 ^ objBitsKO ko)} \<inter> kernel_data_refs = {}"
    by (clarsimp simp:range_cover_def[where 'a=machine_word_len, folded word_bits_def])+

  (* obj specific *)
  have mko: "\<And>dev. makeObjectKO dev (Inr (APIObjectType ArchTypes_H.apiobject_type.EndpointObject)) = Some ko"
    by (simp add: ko_def makeObjectKO_def)

  have relrl:
    "cendpoint_relation (cslift x) makeObject (from_bytes (replicate (size_of TYPE(endpoint_C)) 0))"
    unfolding cendpoint_relation_def
    apply (simp add: Let_def makeObject_endpoint size_of_def endpoint_lift_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps endpoint_C_tag_def endpoint_lift_def
      size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine Let_def
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: typ_info_array array_tag_def eval_nat_numeral)
    apply (simp add: array_tag_n_eq)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: EPState_Idle_def update_ti_t_machine_word_0s)
    done

  (* /obj specific *)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(endpoint_C) = 2 ^ objBitsKO ko" by (simp add: size_of_def objBits_simps' ko_def)
  have szo': "n * (2 ^ objBitsKO ko) = n * size_of TYPE(endpoint_C)"
    by (metis szo)

  note rl' = cslift_ptr_retyp_other_inst[OF empty cover[simplified] szo' szo]

  note rl = projectKO_opt_retyp_other [OF rc pal pno ko_def]
  note cterl = retype_ctes_helper [OF pal pdst pno al sz szb mko rc, simplified]
  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

 have guard:
    "\<forall>b < n. c_guard (CTypesDefs.ptr_add ?ptr (of_nat b))"
    apply (rule retype_guard_helper [where m = 3, OF cover ptr0 szo])
    apply (simp add: ko_def objBits_simps')
    apply (simp add: align_of_def)
    done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks  (underlying_memory (ksMachineState \<sigma>)) ?ks'"
    unfolding cpspace_relation_def
    apply -
    supply image_cong_simp[cong del]
    apply (clarsimp simp: rl' cterl tag_disj_via_td_name foldr_upd_app_if [folded data_map_insert_def]
      heap_to_user_data_def cte_C_size heap_to_device_data_def)
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard _ _ szo' _ zero],
      simp_all only: szo empty, simp_all)
     apply (rule range_cover.strong_times_64[OF cover refl])
    apply (simp add: ptr_add_to_new_cap_addrs [OF szo] ht_rl)
    apply (simp add: rl projectKO_opt_retyp_same projectKOs)
    apply (simp add: ko_def projectKO_opt_retyp_same projectKOs cong: if_cong)
    apply (erule cmap_relation_retype)
    apply (rule relrl[simplified szo ko_def])
    done

  thus ?thesis using rf empty kdr rzo
  apply (simp add: rf_sr_def cstate_relation_def Let_def rl'
                   tag_disj_via_td_name)
  apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
  apply (simp add: rl' cterl tag_disj_via_td_name h_t_valid_clift_Some_iff)
  apply (clarsimp simp: hrs_htd_update ptr_retyps_htd_safe_neg szo
                        kernel_data_refs_domain_eq_rotate
                        ht_rl foldr_upd_app_if [folded data_map_insert_def]
                        rl projectKOs cvariable_array_ptr_retyps[OF szo]
                        zero_ranges_ptr_retyps
              simp del: endpoint_C_size)
  done
qed

lemma createObjects_ccorres_ntfn:
  defines "ko \<equiv> (KONotification (makeObject :: Structures_H.notification))"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (n * (2 ^ objBitsKO ko)) \<sigma>
  \<and> region_is_zero_bytes ptr (n * 2 ^ objBitsKO ko) x
  \<and> range_cover ptr sz (objBitsKO ko) n
  \<and> {ptr ..+ n * (2 ^ objBitsKO ko)} \<inter> kernel_data_refs = {}
  \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs n ptr ko) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen n (Ptr ptr :: notification_C ptr) False)
                      (t_hrs_' (globals x))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")

proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "Ptr ptr :: notification_C ptr"

  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr"
    and cover: "range_cover ptr sz (objBitsKO ko) n"
    and al: "is_aligned ptr (objBitsKO ko)" and ptr0: "ptr \<noteq> 0"
    and sz: "objBitsKO ko \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (n * (2 ^ objBitsKO ko)) \<sigma>"
    and empty: "region_is_bytes ptr (n * (2 ^ objBitsKO ko)) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (n * (2 ^ objBitsKO ko))"
    and rc: "range_cover ptr sz (objBitsKO ko) n"
    and kdr: "{ptr..+n * 2 ^ objBitsKO ko} \<inter> kernel_data_refs = {}"
    by (clarsimp simp:range_cover_def[where 'a=machine_word_len, folded word_bits_def])+

  (* obj specific *)
  have mko: "\<And> dev. makeObjectKO dev (Inr (APIObjectType ArchTypes_H.apiobject_type.NotificationObject)) = Some ko" by (simp add: ko_def makeObjectKO_def)

  have relrl:
    "cnotification_relation (cslift x) makeObject (from_bytes (replicate (size_of TYPE(notification_C)) 0))"
    unfolding cnotification_relation_def
    apply (simp add: Let_def makeObject_notification size_of_def notification_lift_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps notification_C_tag_def notification_lift_def
      size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine Let_def
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: typ_info_array array_tag_def eval_nat_numeral)
    apply (simp add: array_tag_n.simps)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine Let_def
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: update_ti_t_machine_word_0s NtfnState_Idle_def option_to_ctcb_ptr_def)
    done

  (* /obj specific *)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(notification_C) = 2 ^ objBitsKO ko" by (simp add: size_of_def objBits_simps' ko_def)
  have szo': "n * (2 ^ objBitsKO ko) = n * size_of TYPE(notification_C)" using sz
    apply (subst szo)
    apply (simp add: power_add [symmetric])
    done

  note rl' = cslift_ptr_retyp_other_inst[OF empty cover[simplified] szo' szo]

  (* rest is generic *)
  note rl = projectKO_opt_retyp_other [OF rc pal pno ko_def]
  note cterl = retype_ctes_helper [OF pal pdst pno al sz szb mko rc, simplified]
  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have guard:
    "\<forall>b<n. c_guard (CTypesDefs.ptr_add ?ptr (of_nat b))"
    apply (rule retype_guard_helper[where m=3, OF cover ptr0 szo])
    apply (simp add: ko_def objBits_simps' align_of_def)+
    done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks  (underlying_memory (ksMachineState \<sigma>)) ?ks'"
    unfolding cpspace_relation_def
    apply -
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' cterl tag_disj_via_td_name foldr_upd_app_if [folded data_map_insert_def]
      heap_to_user_data_def cte_C_size)
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard _ _ szo' _ zero],
      simp_all only: szo empty, simp_all)
     apply (rule range_cover.strong_times_64[OF cover refl])
    apply (simp add: ptr_add_to_new_cap_addrs [OF szo] ht_rl)
    apply (simp add: rl projectKO_opt_retyp_same projectKOs)
    apply (simp add: ko_def projectKO_opt_retyp_same projectKOs cong: if_cong)
    apply (erule cmap_relation_retype)
    apply (rule relrl[simplified szo ko_def])
    done

  thus ?thesis using rf empty kdr rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (simp add: rl' cterl tag_disj_via_td_name h_t_valid_clift_Some_iff )
    apply (clarsimp simp: hrs_htd_update ptr_retyps_htd_safe_neg szo
                          kernel_data_refs_domain_eq_rotate
                          ht_rl foldr_upd_app_if [folded data_map_insert_def]
                          rl projectKOs cvariable_array_ptr_retyps[OF szo]
                          zero_ranges_ptr_retyps
                simp del: notification_C_size)
    done
qed


lemma ccte_relation_makeObject:
  notes option.case_cong_weak [cong]
  shows "ccte_relation makeObject (from_bytes (replicate (size_of TYPE(cte_C)) 0))"
  apply (simp add: Let_def makeObject_cte size_of_def ccte_relation_def map_option_Some_eq2)
  apply (simp add: from_bytes_def)
  apply (simp add: typ_info_simps cte_C_tag_def  cte_lift_def
    size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
  apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine
    size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
    ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def align_of_def
    typ_info_simps cap_C_tag_def mdb_node_C_tag_def split: option.splits)
  apply (simp add: typ_info_array array_tag_def eval_nat_numeral array_tag_n.simps)
  apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine
    size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
    ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def update_ti_t_machine_word_0s)
  apply (simp add: cap_lift_def Let_def cap_get_tag_def cap_tag_defs cte_to_H_def cap_to_H_def mdb_node_to_H_def
    mdb_node_lift_def nullMDBNode_def c_valid_cte_def)
  done

lemma ccte_relation_nullCap:
  notes option.case_cong_weak [cong]
  shows "ccte_relation (CTE NullCap (MDB 0 0 False False)) (from_bytes (replicate (size_of TYPE(cte_C)) 0))"
  apply (simp add: Let_def makeObject_cte size_of_def ccte_relation_def map_option_Some_eq2)
  apply (simp add: from_bytes_def)
  apply (simp add: typ_info_simps cte_C_tag_def  cte_lift_def
    size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
  apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine
    size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
    ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def align_of_def
    typ_info_simps cap_C_tag_def mdb_node_C_tag_def split: option.splits)
  apply (simp add: typ_info_array array_tag_def eval_nat_numeral array_tag_n.simps)
  apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine
    size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
    ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def update_ti_t_machine_word_0s)
  apply (simp add: cap_lift_def Let_def cap_get_tag_def cap_tag_defs cte_to_H_def cap_to_H_def mdb_node_to_H_def
    mdb_node_lift_def nullMDBNode_def c_valid_cte_def)
  done

lemma createObjects_ccorres_cte:
  defines "ko \<equiv> (KOCTE (makeObject :: cte))"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr  \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (n * 2 ^ objBitsKO ko) \<sigma>
  \<and> region_is_zero_bytes ptr (n * 2 ^ objBitsKO ko) x
  \<and> range_cover ptr sz (objBitsKO ko) n
  \<and> {ptr ..+ n * (2 ^ objBitsKO ko)} \<inter> kernel_data_refs = {}
   \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs n ptr ko) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen n (Ptr ptr :: cte_C ptr) True)
                       (t_hrs_' (globals x))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "Ptr ptr :: cte_C ptr"

  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr"
    and cover: "range_cover ptr sz (objBitsKO ko) n"
    and al: "is_aligned ptr (objBitsKO ko)" and ptr0: "ptr \<noteq> 0"
    and sz: "objBitsKO ko \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (n * 2 ^ objBitsKO ko) \<sigma>"
    and empty: "region_is_bytes ptr (n * (2 ^ objBitsKO ko)) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (n * (2 ^ objBitsKO ko))"
    and rc: "range_cover ptr sz (objBitsKO ko) n"
    and kdr: "{ptr..+n * 2 ^ objBitsKO ko} \<inter> kernel_data_refs = {}"
    by (clarsimp simp:range_cover_def[where 'a=machine_word_len, folded word_bits_def])+

  (* obj specific *)
  have mko: "\<And>dev. makeObjectKO dev (Inr (APIObjectType  ArchTypes_H.apiobject_type.CapTableObject)) = Some ko"
    by (simp add: ko_def makeObjectKO_def)

  note relrl = ccte_relation_makeObject

  (* /obj specific *)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(cte_C) = 2 ^ objBitsKO ko" by (simp add: size_of_def objBits_simps' ko_def)
  have szo': "n * 2 ^ objBitsKO ko = n * size_of TYPE(cte_C)" using sz
    apply (subst szo)
    apply (simp add: power_add [symmetric])
    done

  note rl' = cslift_ptr_retyp_other_inst[OF empty cover szo' szo]

  (* rest is generic *)
  note rl = projectKO_opt_retyp_other [OF rc pal pno ko_def]
  note cterl = retype_ctes_helper [OF pal pdst pno al sz szb mko rc, simplified]
  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have guard:
    "\<forall>b< n. c_guard (CTypesDefs.ptr_add ?ptr (of_nat b))"
    apply (rule retype_guard_helper[where m=3, OF cover ptr0 szo])
    apply (simp add: ko_def objBits_simps' align_of_def)+
    done

  note irq = h_t_valid_eq_array_valid[where 'a=cte_C]
    h_t_array_valid_ptr_retyps_gen[where p="Ptr ptr", simplified, OF szo empty]

  with rf have irq: "h_t_valid (hrs_htd ?ks') c_guard intStateIRQNode_array_Ptr"
    apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
    apply (simp add: hrs_htd_update h_t_valid_eq_array_valid)
    apply (simp add: h_t_array_valid_ptr_retyps_gen[OF szo] empty)
    done

  note if_cong[cong] (* needed by some of the [simplified]'s below. *)
  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>)) ?ks'"
    unfolding cpspace_relation_def
    apply -
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' cterl tag_disj_via_td_name foldr_upd_app_if [folded data_map_insert_def])
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard _ _ szo' _ zero],
      simp_all only: szo empty, simp_all)
     apply (rule range_cover.strong_times_64[OF cover refl])
    apply (simp add: ptr_add_to_new_cap_addrs [OF szo] ht_rl)
    apply (simp add: rl projectKO_opt_retyp_same projectKOs)
    apply (simp add: ko_def projectKO_opt_retyp_same projectKOs cong: if_cong)
    apply (subst makeObject_cte[symmetric])
    apply (erule cmap_relation_retype)
    apply (rule relrl[simplified szo ko_def])
    done

  thus ?thesis using rf empty kdr irq rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (simp add: rl' cterl tag_disj_via_td_name h_t_valid_clift_Some_iff)
    apply (clarsimp simp: hrs_htd_update ptr_retyps_htd_safe_neg szo
                          kernel_data_refs_domain_eq_rotate
                          rl foldr_upd_app_if [folded data_map_insert_def] projectKOs
                          zero_ranges_ptr_retyps
                          ht_rl cvariable_array_ptr_retyps[OF szo])
    done
qed

lemma h_t_valid_ptr_retyps_gen_disjoint_iff:
  "\<lbrakk> {ptr_val p..+ size_of TYPE('b)} \<inter> {ptr_val ptr..+n * size_of TYPE('a)} = {} \<rbrakk> \<Longrightarrow>
  ptr_retyps_gen n (ptr::'a::mem_type ptr) arr d \<Turnstile>\<^sub>t (p::'b::c_type ptr) = d \<Turnstile>\<^sub>t p"
  apply (cases "0 < size_td (typ_info_t TYPE('b))"; cases "c_guard p";
         clarsimp simp: h_t_valid_def valid_footprint_def Let_def)
  apply (rule forall_eq[rule_format], rule iff_impI)
  apply (subgoal_tac "ptr_val p + of_nat y \<notin> {ptr_val ptr..+n * size_of TYPE('a)}")
   apply (simp add: ptr_retyps_gen_out)
  apply clarsimp
  apply (drule intvlD)
  apply (clarsimp simp: disjoint_iff_not_equal )
  apply (drule_tac x = "ptr_val p + of_nat y" in bspec)
   apply (rule intvlI)
   apply (simp add: size_of_def)
  apply (drule_tac x = "ptr_val ptr + of_nat k" in bspec)
   apply (erule intvlI)
  apply simp
  done

lemma h_t_valid_ptr_retyps_gen_disjoint:
  "\<lbrakk> d \<Turnstile>\<^sub>t p; {ptr_val p..+ size_of TYPE('b)} \<inter> {ptr_val ptr..+n * size_of TYPE('a)} = {} \<rbrakk> \<Longrightarrow>
  ptr_retyps_gen n (ptr::'a::mem_type ptr) arr d \<Turnstile>\<^sub>t (p::'b::mem_type ptr)"
  using h_t_valid_ptr_retyps_gen_disjoint_iff[where arr=arr and d=d] by auto

lemma range_cover_intvl:
assumes cover: "range_cover (ptr :: 'a :: len word) sz us n"
assumes not0 : "n \<noteq> 0"
shows "{ptr..+n * 2 ^ us} = {ptr..ptr + (of_nat n * 2 ^ us - 1)}"
  proof
    have not0' : "(0 :: 'a word) < of_nat n * (2 :: 'a word) ^ us"
      using range_cover_not_zero_shift[OF _ cover,where gbits = "us"]
     apply (simp add:not0 shiftl_t2n field_simps)
     apply unat_arith
     done

    show "{ptr..+n * 2 ^ us} \<subseteq> {ptr..ptr + (of_nat n* 2 ^ us - 1)}"
     using not0 not0'
     apply (clarsimp simp:intvl_def)
     apply (intro conjI)
      apply (rule word_plus_mono_right2[rotated,where b = "of_nat n * 2^us - 1"])
       apply (subst le_m1_iff_lt[THEN iffD1])
        apply (simp add:not0')
       apply (rule word_of_nat_less)
       apply (clarsimp simp: range_cover.unat_of_nat_shift[OF cover] field_simps)
      apply (clarsimp simp: field_simps)
      apply (erule range_cover_bound[OF cover])
     apply (rule word_plus_mono_right)
      apply (subst le_m1_iff_lt[THEN iffD1])
       apply (simp add:not0')
      apply (rule word_of_nat_less)
      apply (clarsimp simp: range_cover.unat_of_nat_shift[OF cover] field_simps)
     apply (clarsimp simp: field_simps)
      apply (erule range_cover_bound[OF cover])
     done
   show "{ptr..ptr + (of_nat n * 2 ^ us - 1)} \<subseteq> {ptr..+n * 2 ^ us}"
     using not0 not0'
     apply (clarsimp simp:intvl_def)
     apply (rule_tac x = "unat (x - ptr)" in exI)
      apply simp
      apply (simp add:field_simps)
      apply (rule unat_less_helper)
      apply (subst le_m1_iff_lt[THEN iffD1,symmetric])
      apply (simp add:field_simps not0 range_cover_not_zero_shift[unfolded shiftl_t2n,OF _ _ le_refl])
     apply (rule word_diff_ls')
      apply (simp add:field_simps)
     apply simp
    done
  qed

lemma aligned_new_cap_addrs_eq_base:
  "is_aligned p bits \<Longrightarrow> is_aligned ptr bits
    \<Longrightarrow> n = 2 ^ (bits - objBitsKO ko)
    \<Longrightarrow> objBitsKO ko = shft
    \<Longrightarrow> y < of_nat n
    \<Longrightarrow> (p + (y << shft) \<in> set (new_cap_addrs n ptr ko)) = (p = ptr)"
  apply (erule is_aligned_get_word_bits)
   apply (rule iffI)
    apply (clarsimp simp: new_cap_addrs_def)
    apply (rule ccontr, drule(2) aligned_neq_into_no_overlap)
    apply (simp only: field_simps upto_intvl_eq[symmetric])
    apply (drule equals0D, erule notE, rule_tac c="p + (y << shft)" in IntI)
     apply (simp(no_asm) add: offs_in_intvl_iff)
     apply (rule unat_less_helper, simp, rule shiftl_less_t2n; simp)
    apply (simp add: offs_in_intvl_iff)
    apply (rule unat_less_helper, simp, rule shiftl_less_t2n; simp add: word_of_nat_less)
   apply (simp add: new_cap_addrs_def)
   apply (rule_tac x="unat y" in image_eqI; simp add: unat_less_helper)
  apply (erule is_aligned_get_word_bits; simp)
  apply (simp add: new_cap_addrs_def)
  apply (rule_tac x="unat y" in image_eqI; simp add: unat_less_helper)
  done

lemma cmap_relation_array_add_array[OF refl]:
  "ptrf = Ptr \<Longrightarrow> carray_map_relation n ahp chp ptrf
    \<Longrightarrow> is_aligned p n
    \<Longrightarrow> ahp' = (\<lambda>x. if x \<in> set (new_cap_addrs sz p ko) then Some v else ahp x)
    \<Longrightarrow> (\<forall>x. chp x \<longrightarrow> is_aligned (ptr_val x) n \<Longrightarrow> \<forall>y. chp' y = (y = ptrf p | chp y))
    \<Longrightarrow> sz = 2 ^ (n - objBits v)
    \<Longrightarrow> objBitsKO ko = objBitsKO (injectKOS v)
    \<Longrightarrow> objBits v \<le> n \<Longrightarrow> n < word_bits
    \<Longrightarrow> carray_map_relation n ahp' chp' ptrf"
  apply (clarsimp simp: carray_map_relation_def objBits_koTypeOf
                        objBitsT_koTypeOf[symmetric]
                        koTypeOf_injectKO
              simp del: objBitsT_koTypeOf)
  apply (drule meta_mp)
   apply auto[1]
  apply (case_tac "pa = p"; clarsimp)
   apply (subst if_P; simp add: new_cap_addrs_def)
   apply (rule_tac x="unat ((p' && mask n) >> objBitsKO ko)" in image_eqI)
    apply (simp add: shiftr_shiftl1 is_aligned_andI1 add.commute
                     word_plus_and_or_coroll2)
   apply (simp, rule unat_less_helper, simp, rule shiftr_less_t2n)
   apply (simp add: and_mask_less_size word_size word_bits_def)
  apply (case_tac "chp (ptrf pa)", simp_all)
   apply (drule spec, drule(1) iffD2)
   apply (auto split: if_split)[1]
  apply (drule_tac x=pa in spec, clarsimp)
  apply (drule_tac x=p' in spec, clarsimp split: if_split_asm)
  apply (clarsimp simp: new_cap_addrs_def)
  apply (subst(asm) is_aligned_add_helper, simp_all)
  apply (rule shiftl_less_t2n, rule word_of_nat_less, simp_all add: word_bits_def)
  done

lemma createObjects_ccorres_pte:
  defines "ko \<equiv> (KOArch (KOPTE (makeObject :: pte)))"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (2 ^ ptBits) \<sigma>
  \<and> region_is_zero_bytes ptr (2 ^ ptBits) x
  \<and> range_cover ptr sz ptBits 1
  \<and> valid_global_refs' s
  \<and> kernel_data_refs \<inter> {ptr..+ 2 ^ ptBits} = {} \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs 512 ptr ko) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen 1 (pt_Ptr ptr) False)
                       (t_hrs_' (globals x))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "Ptr ptr :: (pte_C[512]) ptr"
  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr"
    and cover: "range_cover ptr sz ptBits 1"
    and al: "is_aligned ptr ptBits"
    and ptr0: "ptr \<noteq> 0"
    and sz: "ptBits \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>"
    and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (2 ^ ptBits) \<sigma>"
    and empty: "region_is_bytes ptr (2 ^ ptBits) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (2 ^ ptBits)"
    and kernel_data_refs_disj : "kernel_data_refs \<inter> {ptr..+ 2 ^ ptBits} = {}"
    by (clarsimp simp:range_cover_def[where 'a=machine_word_len, folded word_bits_def])+

    note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  (* obj specific *)
  have mko: "\<And>dev. makeObjectKO dev (Inr X64_H.PageTableObject) = Some ko" by (simp add: ko_def makeObjectKO_def)

  have relrl:
    "cpte_relation makeObject (from_bytes (replicate (size_of TYPE(pte_C)) 0))"
    unfolding cpte_relation_def
    apply (simp add: Let_def makeObject_pte size_of_def pte_lift_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps pte_C_tag_def pte_lift_def
      size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine Let_def
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: typ_info_array array_tag_def eval_nat_numeral)
    apply (simp add: array_tag_n.simps)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine Let_def
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: update_ti_t_machine_word_0s )
    done

  (* /obj specific *)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(pte_C[512]) = 2 ^ ptBits"
    by (simp add: size_of_def size_td_array bit_simps)
  have szo2: "512 * size_of TYPE(pte_C) = 2 ^ ptBits"
    by (simp add: szo[symmetric] bit_simps)
  have szo': "size_of TYPE(pte_C) = 2 ^ objBitsKO ko"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)

  note rl' = cslift_ptr_retyp_other_inst[where n=1,
    simplified, OF empty, simplified, OF cover[simplified]
    szo[symmetric] szo[simplified bit_simps_corres]]

  have sz_weaken: "objBitsKO ko \<le> ptBits"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)
  have cover': "range_cover ptr sz (objBitsKO ko) 512"
    apply (rule range_cover_rel[OF cover sz_weaken])
    apply (simp add: ptBits_def objBits_simps ko_def archObjSize_def bit_simps)
    done
  from sz sz_weaken have sz': "objBitsKO ko \<le> sz" by simp
  note al' = is_aligned_weaken[OF al sz_weaken]

  have koT: "koTypeOf ko = ArchT PTET"
    by (simp add: ko_def)

  (* rest used to be generic, but PT arrays are complicating everything *)

  note rl = projectKO_opt_retyp_other [OF cover' pal pno ko_def]
  note cterl = retype_ctes_helper [OF pal pdst pno al' sz' szb mko cover']

  have guard: "c_guard ?ptr"
    using al[simplified bit_simps]
    apply -
    apply (rule is_aligned_c_guard[where n=ptBits and m=3])
    apply (simp_all add:  align_td_array align_of_def bit_simps ptr0)
    done

  have guard': "\<forall>n < 512. c_guard (pte_Ptr ptr +\<^sub>p int n)"
    using al[simplified bit_simps]
    apply -
    apply (rule retype_guard_helper [OF cover' ptr0 szo', where m=3])
     apply (simp_all add: objBits_simps ko_def archObjSize_def align_of_def bit_simps)
    done

  note ptr_retyps.simps[simp del]

  from rf have pterl: "cmap_relation (map_to_ptes (ksPSpace \<sigma>)) (cslift x) Ptr cpte_relation"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def cpspace_relation_def)

  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have pte_arr: "cpspace_pte_array_relation (ksPSpace \<sigma>) (t_hrs_' (globals x))
    \<Longrightarrow> cpspace_pte_array_relation ?ks ?ks'"
   apply (erule cmap_relation_array_add_array[OF _ al])
        apply (simp add: foldr_upd_app_if[folded data_map_insert_def])
        apply (rule projectKO_opt_retyp_same, simp add: ko_def projectKOs)
       apply (simp add: h_t_valid_clift_Some_iff dom_def split: if_split)
       apply (subst clift_ptr_retyps_gen_prev_memset_same[where n=1, simplified, OF guard],
         simp_all only: szo refl empty, simp_all add: zero[simplified])[1]
        apply (simp add: bit_simps word_bits_def)
       apply (auto split: if_split)[1]
      apply (simp_all add: objBits_simps archObjSize_def bit_simps
                           ko_def word_bits_def)
   done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>))  ?ks'"
    unfolding cpspace_relation_def
    using pte_arr
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' cterl cte_C_size tag_disj_via_td_name
                          foldr_upd_app_if [folded data_map_insert_def])
    apply (simp add: ht_rl)
    apply (simp add: ptr_retyp_to_array[simplified])
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard'], simp_all only: szo2 empty)
       apply simp
      apply (simp(no_asm) add: bit_simps word_bits_def)
     apply (simp add: zero[simplified])
    apply (simp add: rl projectKOs del: pte_C_size)
    apply (simp add: rl projectKO_opt_retyp_same ko_def projectKOs Let_def
                     ptr_add_to_new_cap_addrs [OF szo']
                cong: if_cong del: pte_C_size)
    apply (erule cmap_relation_retype)
    apply (insert relrl, auto)
    done

  moreover
  from rf szb al
  have "ptr_span (pml4_Ptr (symbol_table ''x64KSSKIMPML4'')) \<inter> {ptr ..+ 2 ^ ptBits} = {}"
    apply (clarsimp simp: valid_global_refs'_def  Let_def
                          valid_refs'_def ran_def rf_sr_def cstate_relation_def)
    apply (erule disjoint_subset)
    apply (simp add:kernel_data_refs_disj[simplified bit_simps_corres])
    done

  ultimately
  show ?thesis using rf empty kernel_data_refs_disj rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (clarsimp simp add: rl' cterl tag_disj_via_td_name
      hrs_htd_update ht_rl foldr_upd_app_if [folded data_map_insert_def] rl projectKOs
      cvariable_array_ptr_retyps[OF szo]
      zero_ranges_ptr_retyps[where p="pt_Ptr ptr", simplified szo])
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    by (simp add:szo ptr_retyps_htd_safe_neg hrs_htd_def
      kernel_data_refs_domain_eq_rotate bit_simps
      Int_ac del: replicate_numeral)

qed

lemma createObjects_ccorres_pde:
  defines "ko \<equiv> (KOArch (KOPDE (makeObject :: pde)))"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (2 ^ pdBits) \<sigma>
  \<and> region_is_zero_bytes ptr (2 ^ pdBits) x
  \<and> range_cover ptr sz pdBits 1
  \<and> valid_global_refs' s
  \<and> kernel_data_refs \<inter> {ptr..+ 2 ^ pdBits} = {} \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs 512 ptr ko) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen 1 (pd_Ptr ptr) False)
                       (t_hrs_' (globals x))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "pd_Ptr ptr"
  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr"
    and cover: "range_cover ptr sz pdBits 1"
    and al: "is_aligned ptr pdBits"
    and ptr0: "ptr \<noteq> 0"
    and sz: "pdBits \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>"
    and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (2 ^ pdBits) \<sigma>"
    and empty: "region_is_bytes ptr (2 ^ pdBits) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (2 ^ pdBits)"
    and kernel_data_refs_disj : "kernel_data_refs \<inter> {ptr..+ 2 ^ pdBits} = {}"
    by (clarsimp simp:range_cover_def[where 'a=machine_word_len, folded word_bits_def])+

    note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  (* obj specific *)
  have mko: "\<And>dev. makeObjectKO dev (Inr X64_H.PageDirectoryObject) = Some ko" by (simp add: ko_def makeObjectKO_def)

  have relrl:
    "cpde_relation makeObject (from_bytes (replicate (size_of TYPE(pde_C)) 0))"
    unfolding cpde_relation_def
    supply if_cong[cong]
    apply (simp add: Let_def makeObject_pde size_of_def pde_lift_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps pde_C_tag_def pde_lift_def size_td_lt_final_pad
                     size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def
                     padup_def align_td_array' size_td_array update_ti_adjust_ti
                     ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: typ_info_array array_tag_def eval_nat_numeral)
    apply (simp add: array_tag_n.simps)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine size_of_def
                     padup_def align_td_array' size_td_array update_ti_adjust_ti
                     ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: update_ti_t_machine_word_0s pde_get_tag_def pde_pde_pt_def)
    done

  (* /obj specific *)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(pde_C[512]) = 2 ^ pdBits"
    by (simp add: size_of_def size_td_array bit_simps)
  have szo2: "512 * size_of TYPE(pde_C) = 2 ^ pdBits"
    by (simp add: szo[symmetric] bit_simps)
  have szo': "size_of TYPE(pde_C) = 2 ^ objBitsKO ko"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)

  note rl' = cslift_ptr_retyp_other_inst[where n=1,
    simplified, OF empty, simplified, OF cover[simplified]
    szo[symmetric] szo[simplified bit_simps_corres]]

  have sz_weaken: "objBitsKO ko \<le> pdBits"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)
  have cover': "range_cover ptr sz (objBitsKO ko) 512"
    apply (rule range_cover_rel[OF cover sz_weaken])
    apply (simp add: ptBits_def objBits_simps ko_def archObjSize_def bit_simps)
    done
  from sz sz_weaken have sz': "objBitsKO ko \<le> sz" by simp
  note al' = is_aligned_weaken[OF al sz_weaken]

  have koT: "koTypeOf ko = ArchT PDET"
    by (simp add: ko_def)

  (* rest used to be generic, but PT arrays are complicating everything *)

  note rl = projectKO_opt_retyp_other [OF cover' pal pno ko_def]
  note cterl = retype_ctes_helper [OF pal pdst pno al' sz' szb mko cover']

  have guard: "c_guard ?ptr"
    using al[simplified bit_simps]
    apply -
    apply (rule is_aligned_c_guard[where n=pdBits and m=3])
    apply (simp_all add:  align_td_array align_of_def bit_simps ptr0)
    done

  have guard': "\<forall>n < 512. c_guard (pde_Ptr ptr +\<^sub>p int n)"
    using al[simplified bit_simps]
    apply -
    apply (rule retype_guard_helper [OF cover' ptr0 szo', where m=3])
     apply (simp_all add: objBits_simps ko_def archObjSize_def align_of_def bit_simps)
    done

  note ptr_retyps.simps[simp del]

  from rf have pderl: "cmap_relation (map_to_pdes (ksPSpace \<sigma>)) (cslift x) Ptr cpde_relation"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def cpspace_relation_def)

  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have pde_arr: "cpspace_pde_array_relation (ksPSpace \<sigma>) (t_hrs_' (globals x))
    \<Longrightarrow> cpspace_pde_array_relation ?ks ?ks'"
   apply (erule cmap_relation_array_add_array[OF _ al])
        apply (simp add: foldr_upd_app_if[folded data_map_insert_def])
        apply (rule projectKO_opt_retyp_same, simp add: ko_def projectKOs)
       apply (simp add: h_t_valid_clift_Some_iff dom_def split: if_split)
       apply (subst clift_ptr_retyps_gen_prev_memset_same[where n=1, simplified, OF guard],
         simp_all only: szo refl empty, simp_all add: zero[simplified])[1]
        apply (simp add: bit_simps word_bits_def)
       apply (auto split: if_split)[1]
      apply (simp_all add: objBits_simps archObjSize_def bit_simps
                           ko_def word_bits_def)
   done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>))  ?ks'"
    unfolding cpspace_relation_def
    using pde_arr
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' cterl cte_C_size tag_disj_via_td_name
                          foldr_upd_app_if [folded data_map_insert_def])
    apply (simp add: ht_rl)
    apply (simp add: ptr_retyp_to_array[simplified])
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard'], simp_all only: szo2 empty)
       apply simp
      apply (simp(no_asm) add: bit_simps word_bits_def)
     apply (simp add: zero[simplified])
    apply (simp add: rl projectKOs del: pde_C_size)
    apply (simp add: rl projectKO_opt_retyp_same ko_def projectKOs Let_def
                     ptr_add_to_new_cap_addrs [OF szo']
                cong: if_cong del: pde_C_size)
    apply (erule cmap_relation_retype)
    apply (insert relrl, auto)
    done

  moreover
  from rf szb al
  have "ptr_span (pml4_Ptr (symbol_table ''x64KSSKIMPML4'')) \<inter> {ptr ..+ 2 ^ pdBits} = {}"
    apply (clarsimp simp: valid_global_refs'_def  Let_def
                          valid_refs'_def ran_def rf_sr_def cstate_relation_def)
    apply (erule disjoint_subset)
    apply (simp add:kernel_data_refs_disj[simplified bit_simps_corres])
    done

  ultimately
  show ?thesis using rf empty kernel_data_refs_disj rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (clarsimp simp add: rl' cterl tag_disj_via_td_name
      hrs_htd_update ht_rl foldr_upd_app_if [folded data_map_insert_def] rl projectKOs
      cvariable_array_ptr_retyps[OF szo]
      zero_ranges_ptr_retyps[where p="pd_Ptr ptr", simplified szo])
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    by (simp add: szo ptr_retyps_htd_safe_neg hrs_htd_def kernel_data_refs_domain_eq_rotate
                  bit_simps Int_ac)
qed

lemma createObjects_ccorres_pdpte:
  defines "ko \<equiv> (KOArch (KOPDPTE (makeObject :: pdpte)))"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (2 ^ pdptBits) \<sigma>
  \<and> region_is_zero_bytes ptr (2 ^ pdptBits) x
  \<and> range_cover ptr sz pdptBits 1
  \<and> valid_global_refs' s
  \<and> kernel_data_refs \<inter> {ptr..+ 2 ^ pdptBits} = {} \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs 512 ptr ko) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen 1 (pdpt_Ptr ptr) False)
                       (t_hrs_' (globals x))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "pdpt_Ptr ptr"
  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr"
    and cover: "range_cover ptr sz pdptBits 1"
    and al: "is_aligned ptr pdptBits"
    and ptr0: "ptr \<noteq> 0"
    and sz: "pdptBits \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>"
    and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (2 ^ pdptBits) \<sigma>"
    and empty: "region_is_bytes ptr (2 ^ pdptBits) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (2 ^ pdptBits)"
    and kernel_data_refs_disj : "kernel_data_refs \<inter> {ptr..+ 2 ^ pdptBits} = {}"
    by (clarsimp simp:range_cover_def[where 'a=machine_word_len, folded word_bits_def])+

    note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  (* obj specific *)
  have mko: "\<And>dev. makeObjectKO dev (Inr X64_H.PDPointerTableObject) = Some ko" by (simp add: ko_def makeObjectKO_def)

  have relrl:
    "cpdpte_relation makeObject (from_bytes (replicate (size_of TYPE(pdpte_C)) 0))"
    unfolding cpdpte_relation_def
    supply if_cong[cong]
    apply (simp add: Let_def makeObject_pdpte size_of_def pdpte_lift_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps pdpte_C_tag_def pdpte_lift_def size_td_lt_final_pad
                     size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def size_td_lt_ti_typ_pad_combine size_of_def
                     padup_def align_td_array' size_td_array update_ti_adjust_ti
                     ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: typ_info_array array_tag_def eval_nat_numeral)
    apply (simp add: array_tag_n.simps)
    apply (simp add: final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def
                     padup_def align_td_array' size_td_array update_ti_adjust_ti
                     ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: update_ti_t_machine_word_0s pdpte_get_tag_def pdpte_pdpte_1g_def
                     pdpte_pdpte_pd_def)
    done
  (* /obj specific *)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(pdpte_C[512]) = 2 ^ pdptBits"
    by (simp add: size_of_def size_td_array bit_simps)
  have szo2: "512 * size_of TYPE(pdpte_C) = 2 ^ pdptBits"
    by (simp add: szo[symmetric] bit_simps)
  have szo': "size_of TYPE(pdpte_C) = 2 ^ objBitsKO ko"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)

  note rl' = cslift_ptr_retyp_other_inst[where n=1,
    simplified, OF empty, simplified, OF cover[simplified]
    szo[symmetric] szo[simplified bit_simps_corres]]

  have sz_weaken: "objBitsKO ko \<le> pdptBits"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)
  have cover': "range_cover ptr sz (objBitsKO ko) 512"
    apply (rule range_cover_rel[OF cover sz_weaken])
    apply (simp add: ptBits_def objBits_simps ko_def archObjSize_def bit_simps)
    done
  from sz sz_weaken have sz': "objBitsKO ko \<le> sz" by simp
  note al' = is_aligned_weaken[OF al sz_weaken]

  have koT: "koTypeOf ko = ArchT PDPTET"
    by (simp add: ko_def)

  (* rest used to be generic, but PT arrays are complicating everything *)

  note rl = projectKO_opt_retyp_other [OF cover' pal pno ko_def]
  note cterl = retype_ctes_helper [OF pal pdst pno al' sz' szb mko cover']

  have guard: "c_guard ?ptr"
    using al[simplified bit_simps]
    apply -
    apply (rule is_aligned_c_guard[where n=pdptBits and m=3])
    apply (simp_all add:  align_td_array align_of_def bit_simps ptr0)
    done

  have guard': "\<forall>n < 512. c_guard (pdpte_Ptr ptr +\<^sub>p int n)"
    using al[simplified bit_simps]
    apply -
    apply (rule retype_guard_helper [OF cover' ptr0 szo', where m=3])
     apply (simp_all add: objBits_simps ko_def archObjSize_def align_of_def bit_simps)
    done

  note ptr_retyps.simps[simp del]

  from rf have pdpterl: "cmap_relation (map_to_pdptes (ksPSpace \<sigma>)) (cslift x) Ptr cpdpte_relation"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def cpspace_relation_def)

  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have pdpte_arr: "cpspace_pdpte_array_relation (ksPSpace \<sigma>) (t_hrs_' (globals x))
    \<Longrightarrow> cpspace_pdpte_array_relation ?ks ?ks'"
   apply (erule cmap_relation_array_add_array[OF _ al])
        apply (simp add: foldr_upd_app_if[folded data_map_insert_def])
        apply (rule projectKO_opt_retyp_same, simp add: ko_def projectKOs)
       apply (simp add: h_t_valid_clift_Some_iff dom_def split: if_split)
       apply (subst clift_ptr_retyps_gen_prev_memset_same[where n=1, simplified, OF guard],
         simp_all only: szo refl empty, simp_all add: zero[simplified])[1]
        apply (simp add: bit_simps word_bits_def)
       apply (auto split: if_split)[1]
      apply (simp_all add: objBits_simps archObjSize_def bit_simps
                           ko_def word_bits_def)
   done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>))  ?ks'"
    unfolding cpspace_relation_def
    using pdpte_arr
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' cterl cte_C_size tag_disj_via_td_name
                          foldr_upd_app_if [folded data_map_insert_def])
    apply (simp add: ht_rl)
    apply (simp add: ptr_retyp_to_array[simplified])
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard'], simp_all only: szo2 empty)
       apply simp
      apply (simp(no_asm) add: bit_simps word_bits_def)
     apply (simp add: zero[simplified])
    apply (simp add: rl projectKOs del: pdpte_C_size)
    apply (simp add: rl projectKO_opt_retyp_same ko_def projectKOs Let_def
                     ptr_add_to_new_cap_addrs [OF szo']
                cong: if_cong del: pdpte_C_size)
    apply (erule cmap_relation_retype)
    apply (insert relrl, auto)
    done

  moreover
  from rf szb al
  have "ptr_span (pml4_Ptr (symbol_table ''x64KSSKIMPML4'')) \<inter> {ptr ..+ 2 ^ pdptBits} = {}"
    apply (clarsimp simp: valid_global_refs'_def  Let_def
                          valid_refs'_def ran_def rf_sr_def cstate_relation_def)
    apply (erule disjoint_subset)
    apply (simp add:kernel_data_refs_disj[simplified bit_simps_corres])
    done

  ultimately
  show ?thesis using rf empty kernel_data_refs_disj rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (clarsimp simp add: rl' cterl tag_disj_via_td_name
      hrs_htd_update ht_rl foldr_upd_app_if [folded data_map_insert_def] rl projectKOs
      cvariable_array_ptr_retyps[OF szo]
      zero_ranges_ptr_retyps[where p="pdpt_Ptr ptr", simplified szo])
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    by (simp add:szo ptr_retyps_htd_safe_neg hrs_htd_def
      kernel_data_refs_domain_eq_rotate bit_simps
      Int_ac del: replicate_numeral)
qed

lemma createObjects_ccorres_pml4e:
  defines "ko \<equiv> (KOArch (KOPML4E (makeObject :: pml4e)))"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (2 ^ pml4Bits) \<sigma>
  \<and> region_is_zero_bytes ptr (2 ^ pml4Bits) x
  \<and> range_cover ptr sz pml4Bits 1
  \<and> valid_global_refs' s
  \<and> kernel_data_refs \<inter> {ptr..+ 2 ^ pml4Bits} = {} \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs 512 ptr ko) (ksPSpace \<sigma>)\<rparr>,
   x\<lparr>globals := globals x
                 \<lparr>t_hrs_' := hrs_htd_update (ptr_retyps_gen 1 (Ptr ptr :: (pml4e_C[512]) ptr) False)
                       (t_hrs_' (globals x))\<rparr>\<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "pml4_Ptr ptr"
  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr"
    and cover: "range_cover ptr sz pml4Bits 1"
    and al: "is_aligned ptr pml4Bits"
    and ptr0: "ptr \<noteq> 0"
    and sz: "pml4Bits \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>"
    and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (2 ^ pml4Bits) \<sigma>"
    and empty: "region_is_bytes ptr (2 ^ pml4Bits) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (2 ^ pml4Bits)"
    and kernel_data_refs_disj : "kernel_data_refs \<inter> {ptr..+ 2 ^ pml4Bits} = {}"
    by (clarsimp simp:range_cover_def[where 'a=machine_word_len, folded word_bits_def])+

    note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  (* obj specific *)
  have mko: "\<And>dev. makeObjectKO dev (Inr X64_H.PML4Object) = Some ko" by (simp add: ko_def makeObjectKO_def)

  have relrl:
    "cpml4e_relation makeObject (from_bytes (replicate (size_of TYPE(pml4e_C)) 0))"
    unfolding cpml4e_relation_def
    apply (simp add: Let_def makeObject_pml4e size_of_def pml4e_lift_def)
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps pml4e_C_tag_def pml4e_lift_def
      size_td_lt_final_pad size_td_lt_ti_typ_pad_combine Let_def size_of_def)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine Let_def
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: typ_info_array array_tag_def eval_nat_numeral)
    apply (simp add: array_tag_n.simps)
    apply (simp add: final_pad_def Let_def size_td_lt_ti_typ_pad_combine Let_def
      size_of_def padup_def align_td_array' size_td_array update_ti_adjust_ti
      ti_typ_pad_combine_def Let_def ti_typ_combine_def empty_typ_info_def)
    apply (simp add: update_ti_t_machine_word_0s)
    done

  (* /obj specific *)

  (* s/obj/obj'/ *)
  have szo: "size_of TYPE(pml4e_C[512]) = 2 ^ pml4Bits"
    by (simp add: size_of_def size_td_array bit_simps)
  have szo2: "512 * size_of TYPE(pml4e_C) = 2 ^ pml4Bits"
    by (simp add: szo[symmetric] bit_simps)
  have szo': "size_of TYPE(pml4e_C) = 2 ^ objBitsKO ko"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)

  note rl' = cslift_ptr_retyp_other_inst[where n=1,
    simplified, OF empty, simplified, OF cover[simplified]
    szo[symmetric] szo[simplified bit_simps_corres]]

  have sz_weaken: "objBitsKO ko \<le> pml4Bits"
    by (simp add: objBits_simps ko_def archObjSize_def bit_simps)
  have cover': "range_cover ptr sz (objBitsKO ko) 512"
    apply (rule range_cover_rel[OF cover sz_weaken])
    apply (simp add: ptBits_def objBits_simps ko_def archObjSize_def bit_simps)
    done
  from sz sz_weaken have sz': "objBitsKO ko \<le> sz" by simp
  note al' = is_aligned_weaken[OF al sz_weaken]

  have koT: "koTypeOf ko = ArchT PML4ET"
    by (simp add: ko_def)

  (* rest used to be generic, but PT arrays are complicating everything *)

  note rl = projectKO_opt_retyp_other [OF cover' pal pno ko_def]
  note cterl = retype_ctes_helper [OF pal pdst pno al' sz' szb mko cover']

  have guard: "c_guard ?ptr"
    using al[simplified bit_simps]
    apply -
    apply (rule is_aligned_c_guard[where n=pml4Bits and m=3])
    apply (simp_all add:  align_td_array align_of_def bit_simps ptr0)
    done

  have guard': "\<forall>n < 512. c_guard (pml4e_Ptr ptr +\<^sub>p int n)"
    using al[simplified bit_simps]
    apply -
    apply (rule retype_guard_helper [OF cover' ptr0 szo', where m=3])
     apply (simp_all add: objBits_simps ko_def archObjSize_def align_of_def bit_simps)
    done

  note ptr_retyps.simps[simp del]

  from rf have pml4erl: "cmap_relation (map_to_pml4es (ksPSpace \<sigma>)) (cslift x) Ptr cpml4e_relation"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def cpspace_relation_def)

  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]
    uinfo_array_tag_n_m_not_le_typ_name

  have pml4e_arr: "cpspace_pml4e_array_relation (ksPSpace \<sigma>) (t_hrs_' (globals x))
    \<Longrightarrow> cpspace_pml4e_array_relation ?ks ?ks'"
   apply (erule cmap_relation_array_add_array[OF _ al])
        apply (simp add: foldr_upd_app_if[folded data_map_insert_def])
        apply (rule projectKO_opt_retyp_same, simp add: ko_def projectKOs)
       apply (simp add: h_t_valid_clift_Some_iff dom_def split: if_split)
       apply (subst clift_ptr_retyps_gen_prev_memset_same[where n=1, simplified, OF guard],
         simp_all only: szo refl empty, simp_all add: zero[simplified])[1]
        apply (simp add: bit_simps word_bits_def)
       apply (auto split: if_split)[1]
      apply (simp_all add: objBits_simps archObjSize_def bit_simps
                           ko_def word_bits_def)
   done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>))  ?ks'"
    unfolding cpspace_relation_def
    using pml4e_arr
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' cterl cte_C_size tag_disj_via_td_name
                          foldr_upd_app_if [folded data_map_insert_def])
    apply (simp add: ht_rl)
    apply (simp add: ptr_retyp_to_array[simplified])
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard'], simp_all only: szo2 empty)
       apply simp
      apply (simp(no_asm) add: bit_simps word_bits_def)
     apply (simp add: zero[simplified])
    apply (simp add: rl projectKOs del: pml4e_C_size)
    apply (simp add: rl projectKO_opt_retyp_same ko_def projectKOs Let_def
                     ptr_add_to_new_cap_addrs [OF szo']
                cong: if_cong del: pml4e_C_size)
    apply (erule cmap_relation_retype)
    apply (insert relrl, auto)
    done

  moreover
  from rf szb al
  have "ptr_span (pml4_Ptr (symbol_table ''x64KSSKIMPML4'')) \<inter> {ptr ..+ 2 ^ pml4Bits} = {}"
    apply (clarsimp simp: valid_global_refs'_def  Let_def
                          valid_refs'_def ran_def rf_sr_def cstate_relation_def)
    apply (erule disjoint_subset)
    apply (simp add:kernel_data_refs_disj[simplified bit_simps_corres])
    done

  ultimately
  show ?thesis using rf empty kernel_data_refs_disj rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name)
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (clarsimp simp add: rl' cterl tag_disj_via_td_name
      hrs_htd_update ht_rl foldr_upd_app_if [folded data_map_insert_def] rl projectKOs
      cvariable_array_ptr_retyps[OF szo]
      zero_ranges_ptr_retyps[where p="pml4_Ptr ptr", simplified szo])
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    apply (subst h_t_valid_ptr_retyps_gen_disjoint, assumption)
     apply (simp add:szo cte_C_size cte_level_bits_def)
     apply (erule disjoint_subset)
     apply (simp add: bit_simps del: replicate_numeral)
    by (simp add:szo ptr_retyps_htd_safe_neg hrs_htd_def
      kernel_data_refs_domain_eq_rotate bit_simps
      Int_ac del: replicate_numeral)
qed

definition
  object_type_from_H :: "object_type \<Rightarrow> machine_word"
  where
  "object_type_from_H tp \<equiv> case tp of
                              APIObjectType x \<Rightarrow>
                                     (case x of ArchTypes_H.apiobject_type.Untyped \<Rightarrow> scast seL4_UntypedObject
                                              | ArchTypes_H.apiobject_type.TCBObject \<Rightarrow> scast seL4_TCBObject
                                              | ArchTypes_H.apiobject_type.EndpointObject \<Rightarrow> scast seL4_EndpointObject
                                              | ArchTypes_H.apiobject_type.NotificationObject \<Rightarrow> scast seL4_NotificationObject
                                              | ArchTypes_H.apiobject_type.CapTableObject \<Rightarrow> scast seL4_CapTableObject)
                            | X64_H.SmallPageObject \<Rightarrow> scast seL4_X86_4K
                            | X64_H.LargePageObject \<Rightarrow> scast seL4_X86_LargePageObject
                            | X64_H.HugePageObject \<Rightarrow> scast seL4_X64_HugePageObject
                            | X64_H.PageTableObject \<Rightarrow> scast seL4_X86_PageTableObject
                            | X64_H.PageDirectoryObject \<Rightarrow> scast seL4_X86_PageDirectoryObject
                            | X64_H.PDPointerTableObject \<Rightarrow> scast seL4_X86_PDPTObject
                            | X64_H.PML4Object \<Rightarrow> scast seL4_X64_PML4Object"

lemmas nAPIObjects_def = seL4_NonArchObjectTypeCount_def

(* FIXME x64: find aggregator lemma for mode objects *)
lemma nAPIOBjects_object_type_from_H:
  "(scast nAPIObjects <=s object_type_from_H tp) = (toAPIType tp = None)"
  by (simp add: toAPIType_def nAPIObjects_def
    object_type_from_H_def word_sle_def api_object_defs "StrictC'_object_defs"
    seL4_X64_HugePageObject_def seL4_X86_PDPTObject_def seL4_X64_PML4Object_def
    split: X64_H.object_type.splits ArchTypes_H.apiobject_type.splits)

definition
  object_type_to_H :: "machine_word \<Rightarrow> object_type"
  where
  "object_type_to_H x \<equiv>
     (if (x = scast seL4_UntypedObject) then APIObjectType ArchTypes_H.apiobject_type.Untyped else (
      if (x = scast seL4_TCBObject) then APIObjectType ArchTypes_H.apiobject_type.TCBObject else (
       if (x = scast seL4_EndpointObject) then APIObjectType ArchTypes_H.apiobject_type.EndpointObject else (
        if (x = scast seL4_NotificationObject) then APIObjectType ArchTypes_H.apiobject_type.NotificationObject else (
         if (x = scast seL4_CapTableObject) then APIObjectType ArchTypes_H.apiobject_type.CapTableObject else (
          if (x = scast seL4_X86_4K) then X64_H.SmallPageObject else (
           if (x = scast seL4_X86_LargePageObject) then X64_H.LargePageObject else (
            if (x = scast seL4_X64_HugePageObject) then X64_H.HugePageObject else (
              if (x = scast seL4_X86_PageTableObject) then X64_H.PageTableObject else (
               if (x = scast seL4_X86_PageDirectoryObject) then X64_H.PageDirectoryObject else (
                if (x = scast seL4_X86_PDPTObject) then X64_H.PDPointerTableObject else (
                 if (x = scast seL4_X64_PML4Object) then X64_H.PML4Object else
                undefined))))))))))))"

lemmas Kernel_C_defs =
  seL4_UntypedObject_def
  seL4_TCBObject_def
  seL4_EndpointObject_def
  seL4_NotificationObject_def
  seL4_CapTableObject_def
  seL4_X86_4K_def
  seL4_X86_LargePageObject_def
  seL4_X86_PageTableObject_def
  seL4_X86_PageDirectoryObject_def
  seL4_X64_HugePageObject_def
  seL4_X86_PDPTObject_def
  seL4_X64_PML4Object_def
  Kernel_C.asidLowBits_def
  Kernel_C.asidHighBits_def

abbreviation(input)
  "Basic_htd_update f ==
     (Basic (globals_update (t_hrs_'_update (hrs_htd_update f))))"

lemma object_type_to_from_H [simp]: "object_type_to_H (object_type_from_H x) = x"
  apply (clarsimp simp: object_type_from_H_def object_type_to_H_def Kernel_C_defs)
  by (clarsimp split: object_type.splits apiobject_type.splits simp: Kernel_C_defs)

declare ptr_retyps_one[simp]

(* FIXME: move *)
lemma ccorres_return_C_Seq:
  "ccorres_underlying sr \<Gamma> r rvxf arrel xf P P' hs X (return_C xfu v) \<Longrightarrow>
      ccorres_underlying sr \<Gamma> r rvxf arrel xf P P' hs X (return_C xfu v ;; Z)"
  apply (clarsimp simp: return_C_def)
  apply (erule ccorres_semantic_equiv0[rotated])
  apply (rule semantic_equivI)
  apply (clarsimp simp: exec_assoc[symmetric])
  apply (rule exec_Seq_cong, simp)
  apply (clarsimp simp: exec_assoc[symmetric])
  apply (rule exec_Seq_cong, simp)
  apply (rule iffI)
   apply (auto elim!:exec_Normal_elim_cases intro: exec.Throw exec.Seq)[1]
  apply (auto elim!:exec_Normal_elim_cases intro: exec.Throw)
 done

(* FIXME: move *)
lemma ccorres_rewrite_while_guard:
  assumes rl: "\<And>s. s \<in> R \<Longrightarrow> (s \<in> P) = (s \<in> P')"
  and     cc: "ccorres r xf G G' hs a (While P' b)"
  shows   "ccorres r xf G (G' \<inter> R) hs a (While P' b)"
proof (rule iffD1 [OF ccorres_semantic_equiv])
  show "ccorres r xf G (G' \<inter> R) hs a (While P' b)"
    by (rule ccorres_guard_imp2 [OF cc]) simp
next
  fix s s'
  assume "s \<in> G' \<inter> R"
  hence sin: "(s \<in> P) = (s \<in> P')" using rl by simp

  show "semantic_equiv \<Gamma> s s' (While P' b) (While P' b)"
    apply (rule semantic_equivI)
    apply (simp add: sin)
    done
qed

(* FIXME: move *)
lemma ccorres_to_vcg_nf:
  "\<lbrakk>ccorres rrel xf P P' [] a c; no_fail Q a; \<And>s. P s \<Longrightarrow> Q s\<rbrakk>
   \<Longrightarrow> \<Gamma>\<turnstile> {s. P \<sigma> \<and> s \<in> P' \<and> (\<sigma>, s) \<in> rf_sr} c
          {s. \<exists>(rv, \<sigma>')\<in>fst (a \<sigma>). (\<sigma>', s) \<in> rf_sr \<and> rrel rv (xf s)}"
  apply (rule HoarePartial.conseq_exploit_pre)
  apply clarsimp
  apply (rule conseqPre)
  apply (drule ccorres_to_vcg')
    prefer 2
    apply simp
   apply (simp add: no_fail_def)
  apply clarsimp
  done

lemma mdb_node_get_mdbNext_heap_ccorres:
  "ccorres (=) ret__unsigned_longlong_' \<top> UNIV hs
  (liftM (mdbNext \<circ> cteMDBNode) (getCTE parent))
  (\<acute>ret__unsigned_longlong :== CALL mdb_node_get_mdbNext(h_val
                           (hrs_mem \<acute>t_hrs)
                           (Ptr &((Ptr parent :: cte_C ptr) \<rightarrow>[''cteMDBNode_C'']))))"
  apply (simp add: ccorres_liftM_simp)
  apply (rule ccorres_add_return2)
  apply (rule ccorres_guard_imp2)
  apply (rule ccorres_getCTE)
   apply (rule_tac  P = "\<lambda>s. ctes_of s parent = Some x" in ccorres_from_vcg [where P' = UNIV])
   apply (rule allI, rule conseqPre)
    apply vcg
   apply (clarsimp simp: return_def)
   apply (drule cmap_relation_cte)
   apply (erule (1) cmap_relationE1)
   apply (simp add: typ_heap_simps)
   apply (drule ccte_relation_cmdbnode_relation)
   apply (erule mdbNext_CL_mdb_node_lift_eq_mdbNext [symmetric])
   apply simp
   done

lemma getCTE_pre_cte_at:
  "\<lbrace>\<lambda>s. \<not> cte_at' p s \<rbrace> getCTE p \<lbrace> \<lambda>_ _. False \<rbrace>"
  apply (wp getCTE_wp)
  apply clarsimp
  done

lemmas ccorres_getCTE_cte_at = ccorres_guard_from_wp [OF getCTE_pre_cte_at empty_fail_getCTE]
  ccorres_guard_from_wp_bind [OF getCTE_pre_cte_at empty_fail_getCTE]

lemmas ccorres_guard_from_wp_liftM = ccorres_guard_from_wp [OF liftM_pre empty_fail_liftM]
lemmas ccorres_guard_from_wp_bind_liftM = ccorres_guard_from_wp_bind [OF liftM_pre empty_fail_liftM]

lemmas ccorres_liftM_getCTE_cte_at = ccorres_guard_from_wp_liftM [OF getCTE_pre_cte_at empty_fail_getCTE]
  ccorres_guard_from_wp_bind_liftM [OF getCTE_pre_cte_at empty_fail_getCTE]

lemma insertNewCap_ccorres_helper:
  notes option.case_cong_weak [cong]
  shows "ccap_relation cap rv'b
       \<Longrightarrow> ccorres dc xfdc (cte_at' slot and K (is_aligned next cteSizeBits \<and> canonical_address next \<and> is_aligned parent cteSizeBits))
           UNIV hs (setCTE slot (CTE cap (MDB next parent True True)))
           (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update (heap_update
                                    (Ptr &(Ptr slot :: cte_C ptr\<rightarrow>[''cap_C'']) :: cap_C ptr) rv'b))) s);;
            \<acute>ret__struct_mdb_node_C :== CALL mdb_node_new(ptr_val (Ptr next),scast true,scast true,ptr_val (Ptr parent));;
            Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t (Ptr slot :: cte_C ptr)\<rbrace>
             (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update (heap_update
                                                                  (Ptr &(Ptr slot :: cte_C ptr\<rightarrow>[''cteMDBNode_C'']) :: mdb_node_C ptr)
                                                                  (ret__struct_mdb_node_C_' s)))) s)))"
  apply simp
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre)
   apply vcg
  apply (clarsimp simp: Collect_const_mem cte_wp_at_ctes_of)
  apply (frule (1) rf_sr_ctes_of_clift)
  apply (clarsimp simp: typ_heap_simps)
  apply (rule fst_setCTE [OF ctes_of_cte_at], assumption)
  apply (erule bexI [rotated])
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (clarsimp simp add: rf_sr_def cstate_relation_def typ_heap_simps Let_def cpspace_relation_def)
  apply (rule conjI)
   apply (erule (2) cmap_relation_updI)
   apply (simp add: ccap_relation_def ccte_relation_def cte_lift_def)
    subgoal by (simp add: cte_to_H_def map_option_Some_eq2 mdb_node_to_H_def to_bool_mask_to_bool_bf
                          is_aligned_neg_mask_weaken c_valid_cte_def canonical_address_sign_extended
                          sign_extended_iff_sign_extend cteSizeBits_def
                   split: option.splits)
   subgoal by simp
  apply (erule_tac t = s' in ssubst)
  apply (simp cong: lifth_update)
  apply (rule conjI)
   apply (erule (1) setCTE_tcb_case)
  apply (simp add: carch_state_relation_def cmachine_state_relation_def
                   fpu_null_state_heap_update_tag_disj_simps typ_heap_simps
                   cvariable_array_map_const_add_map_option[where f="tcb_no_ctes_proj"])
  done

definition
   byte_regions_unmodified :: "heap_raw_state \<Rightarrow> heap_raw_state \<Rightarrow> bool"
where
  "byte_regions_unmodified hrs hrs' \<equiv> \<forall>x. (\<forall>n td b. snd (hrs_htd hrs x) n = Some (td, b)
        \<longrightarrow> td = typ_uinfo_t TYPE (word8))
    \<longrightarrow> snd (hrs_htd hrs x) 0 \<noteq> None
    \<longrightarrow> hrs_mem hrs' x = hrs_mem hrs x"

abbreviation
  byte_regions_unmodified' :: "globals myvars \<Rightarrow> globals myvars \<Rightarrow> bool"
where
  "byte_regions_unmodified' s t \<equiv> byte_regions_unmodified (t_hrs_' (globals s))
    (t_hrs_' (globals t))"

lemma byte_regions_unmodified_refl[iff]:
  "byte_regions_unmodified hrs hrs"
  by (simp add: byte_regions_unmodified_def)

lemma byte_regions_unmodified_trans:
  "byte_regions_unmodified hrs hrs'
    \<Longrightarrow> byte_regions_unmodified hrs' hrs''
    \<Longrightarrow> hrs_htd hrs' = hrs_htd hrs
    \<Longrightarrow> byte_regions_unmodified hrs hrs''"
  by (simp add: byte_regions_unmodified_def)

lemma byte_regions_unmodified_hrs_mem_update1:
  "byte_regions_unmodified hrs hrs'
    \<Longrightarrow> hrs_htd hrs \<Turnstile>\<^sub>t (p :: ('a :: wf_type) ptr)
    \<Longrightarrow> hrs_htd hrs' = hrs_htd hrs
    \<Longrightarrow> typ_uinfo_t TYPE ('a) \<noteq> typ_uinfo_t TYPE (word8)
    \<Longrightarrow> byte_regions_unmodified hrs
      (hrs_mem_update (heap_update p v) hrs')"
  apply (erule byte_regions_unmodified_trans, simp_all)
  apply (clarsimp simp: byte_regions_unmodified_def hrs_mem_update
                        heap_update_def h_t_valid_def
                        valid_footprint_def Let_def)
  apply (rule heap_update_nmem_same)
  apply (clarsimp simp: size_of_def intvl_def)
  apply (drule spec, drule(1) mp, clarsimp)
  apply (cut_tac s="(typ_uinfo_t TYPE('a))" and n=k in ladder_set_self)
  apply (clarsimp dest!: in_set_list_map)
  apply (drule(1) map_le_trans)
  apply (simp add: map_le_def)
  apply metis
  done

lemma byte_regions_unmodified_hrs_mem_update2:
  "byte_regions_unmodified hrs hrs'
    \<Longrightarrow> hrs_htd hrs \<Turnstile>\<^sub>t (p :: ('a :: wf_type) ptr)
    \<Longrightarrow> typ_uinfo_t TYPE ('a) \<noteq> typ_uinfo_t TYPE (word8)
    \<Longrightarrow> byte_regions_unmodified (hrs_mem_update (heap_update p v) hrs) hrs'"
  apply (erule byte_regions_unmodified_trans[rotated], simp_all)
  apply (clarsimp simp: byte_regions_unmodified_def hrs_mem_update
                        heap_update_def h_t_valid_def
                        valid_footprint_def Let_def)
  apply (rule sym, rule heap_update_nmem_same)
  apply (clarsimp simp: size_of_def intvl_def)
  apply (drule spec, drule(1) mp, clarsimp)
  apply (cut_tac s="(typ_uinfo_t TYPE('a))" and n=k in ladder_set_self)
  apply (clarsimp dest!: in_set_list_map)
  apply (drule(1) map_le_trans)
  apply (simp add: map_le_def)
  apply metis
  done

lemmas byte_regions_unmodified_hrs_mem_update
  = byte_regions_unmodified_hrs_mem_update1
    byte_regions_unmodified_hrs_mem_update2

lemma byte_regions_unmodified_hrs_htd_update[iff]:
  "byte_regions_unmodified
      (hrs_htd_update h hrs) hrs"
  by (clarsimp simp: byte_regions_unmodified_def)

lemma byte_regions_unmodified_flip:
  "byte_regions_unmodified (hrs_htd_update (\<lambda>_. hrs_htd hrs) hrs') hrs
    \<Longrightarrow> byte_regions_unmodified hrs hrs'"
  by (simp add: byte_regions_unmodified_def hrs_htd_update)

lemma mdb_node_ptr_set_mdbPrev_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call mdb_node_ptr_set_mdbPrev_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
         \<and> byte_regions_unmodified' s t}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: )
  apply (intro byte_regions_unmodified_hrs_mem_update byte_regions_unmodified_refl,
    simp_all add: typ_heap_simps)
  done

lemma mdb_node_ptr_set_mdbNext_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call mdb_node_ptr_set_mdbNext_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
         \<and> byte_regions_unmodified' s t}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: )
  apply (intro byte_regions_unmodified_hrs_mem_update byte_regions_unmodified_refl,
    simp_all add: typ_heap_simps)
  done

lemma updateNewFreeIndex_noop_ccorres:
  "ccorres dc xfdc (valid_objs' and cte_wp_at' (\<lambda>cte. cteCap cte = cap) slot)
      {s. (case untypedZeroRange cap of None \<Rightarrow> True
          | Some (a, b) \<Rightarrow> region_actually_is_zero_bytes a (unat ((b + 1) - a)) s)} hs
      (updateNewFreeIndex slot) Skip"
  (is "ccorres _ _ ?P ?P' hs _ _")
  apply (simp add: updateNewFreeIndex_def getSlotCap_def)
  apply (rule ccorres_guard_imp)
    apply (rule ccorres_pre_getCTE[where P="\<lambda>rv. cte_wp_at' ((=) rv) slot and ?P"
        and P'="K ?P'"])
    apply (case_tac "cteCap cte", simp_all add: ccorres_guard_imp[OF ccorres_return_Skip])[1]
    defer
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply simp
  apply (simp add: updateTrackedFreeIndex_def getSlotCap_def)
  apply (rule ccorres_guard_imp)
    apply (rule_tac P="\<lambda>rv. cte_wp_at' ((=) rv) slot and K (rv = cte) and ?P"
        in ccorres_pre_getCTE[where P'="K ?P'"])
    defer
    apply (clarsimp simp: cte_wp_at_ctes_of)
   apply simp
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: bind_def simpler_modify_def)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: zero_ranges_are_zero_def
                        cte_wp_at_ctes_of
                 split: option.split)
  done

lemma byte_regions_unmodified_region_is_bytes:
  "byte_regions_unmodified hrs hrs'
    \<Longrightarrow> region_actually_is_bytes' y n (hrs_htd hrs)
    \<Longrightarrow> x \<in> {y ..+ n}
    \<Longrightarrow> hrs_mem hrs' x = hrs_mem hrs x"
  apply (clarsimp simp: byte_regions_unmodified_def imp_conjL[symmetric])
  apply (drule spec, erule mp)
  apply (clarsimp simp: region_actually_is_bytes'_def)
  apply (drule(1) bspec, simp split: if_split_asm)
  done


lemma insertNewCap_ccorres1:
  "ccorres dc xfdc (pspace_aligned' and pspace_canonical' and valid_mdb' and valid_objs' and valid_cap' cap)
     ({s. (case untypedZeroRange cap of None \<Rightarrow> True
          | Some (a, b) \<Rightarrow> region_actually_is_zero_bytes a (unat ((b + 1) - a)) s)}
       \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. parent_' s = Ptr parent}
       \<inter> {s. slot_' s = Ptr slot}) []
     (insertNewCap parent slot cap)
     (Call insertNewCap_'proc)"
  supply if_cong[cong] option.case_cong[cong]
  apply (cinit (no_ignore_call) lift: cap_' parent_' slot_')
  apply (rule ccorres_liftM_getCTE_cte_at)
   apply (rule ccorres_move_c_guard_cte)
   apply (simp only: )
   apply (rule ccorres_split_nothrow [OF mdb_node_get_mdbNext_heap_ccorres])
      apply ceqv
     apply (erule_tac s = "next" in subst)
     apply csymbr
     apply (ctac (c_lines 3) pre: ccorres_pre_getCTE ccorres_assert add: insertNewCap_ccorres_helper)
       apply (simp only: Ptr_not_null_pointer_not_zero)
       apply (ctac add: updateMDB_set_mdbPrev)
         apply (rule ccorres_seq_skip'[THEN iffD1])
         apply (ctac add: updateMDB_set_mdbNext)
           apply (rule updateNewFreeIndex_noop_ccorres[where cap=cap])
          apply (wp updateMDB_weak_cte_wp_at)
         apply simp
         apply (vcg exspec=mdb_node_ptr_set_mdbNext_preserves_bytes)
        apply (wp updateMDB_weak_cte_wp_at)
       apply clarsimp
       apply (vcg exspec=mdb_node_ptr_set_mdbPrev_preserves_bytes)
      apply (wp setCTE_weak_cte_wp_at)
     apply (clarsimp simp: hrs_mem_update Collect_const_mem
                 simp del: imp_disjL)
     apply vcg
    apply simp
    apply (wp getCTE_wp')
   apply (clarsimp simp: hrs_mem_update)
   apply vcg
  apply (rule conjI)
   apply (clarsimp simp: cte_wp_at_ctes_of is_aligned_3_next ctes_of_aligned_bits
                         canonical_address_mdbNext ctes_of_canonical)
  apply (clarsimp split: option.split)
  apply (intro allI conjI impI; simp; clarsimp simp: region_actually_is_bytes)
   apply (erule trans[OF heap_list_h_eq2, rotated])
   apply (rule byte_regions_unmodified_region_is_bytes)
      apply (erule byte_regions_unmodified_trans[rotated]
         | simp
         | rule byte_regions_unmodified_hrs_mem_update
         | simp add: typ_heap_simps')+
  apply (erule trans[OF heap_list_h_eq2, rotated])
  apply (rule byte_regions_unmodified_region_is_bytes)
     apply (erule byte_regions_unmodified_trans[rotated]
        | simp
        | rule byte_regions_unmodified_hrs_mem_update
        | simp add: typ_heap_simps')+
  done

lemma insertNewCap_pre_cte_at:
  "\<lbrace>\<lambda>s. \<not> (cte_at' p s \<and> cte_at' p' s) \<rbrace> insertNewCap p p' cap \<lbrace> \<lambda>_ _. False \<rbrace>"
  unfolding insertNewCap_def
  apply simp
  apply (wp getCTE_wp)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  done

lemmas createNewCaps_guard_helper = createNewCaps_guard[where 'a=64, folded word_bits_def]

end

locale insertNewCap_i_locale = kernel
begin

lemma mdb_node_get_mdbNext_spec:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call mdb_node_get_mdbNext_'proc {t. i_' t = i_' s}"
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply simp
  done

lemma mdb_node_new_spec:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call mdb_node_new_'proc {t. i_' t = i_' s}"
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply simp
  done

lemma mdb_node_ptr_set_mdbPrev_spec:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call mdb_node_ptr_set_mdbPrev_'proc {t. i_' t = i_' s}"
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply simp
  done

lemma mdb_node_ptr_set_mdbNext_spec:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call mdb_node_ptr_set_mdbNext_'proc {t. i_' t = i_' s}"
  apply (rule allI)
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply vcg
  apply simp
  done

lemma insertNewCap_spec:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call insertNewCap_'proc {t. i_' t = i_' s}"
  apply vcg
  apply clarsimp
  done
end

context kernel_m
begin

lemma insertNewCap_spec:
  "\<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} Call insertNewCap_'proc {t. i_' t = i_' s}"
  apply (rule insertNewCap_i_locale.insertNewCap_spec)
  apply (intro_locales)
  done

lemma ccorres_fail:
  "ccorres r xf \<top> UNIV hs fail c"
  apply (rule ccorresI')
  apply (simp add: fail_def)
  done

lemma hoarep_Cond_UNIV:
  "\<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> P c P', A \<Longrightarrow>
  \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> P (Cond UNIV c d)  P', A"
  apply (rule HoarePartial.Cond [where P\<^sub>1 = P and P\<^sub>2 = "{}"])
    apply simp
   apply assumption
  apply (rule HoarePartial.conseq_exploit_pre)
  apply simp
  done

(* FIXME x64: mode object defs *)
lemma object_type_from_H_toAPIType_simps:
  "(object_type_from_H tp = scast seL4_UntypedObject) = (toAPIType tp = Some ArchTypes_H.apiobject_type.Untyped)"
  "(object_type_from_H tp = scast seL4_TCBObject) = (toAPIType tp = Some ArchTypes_H.apiobject_type.TCBObject)"
  "(object_type_from_H tp = scast seL4_EndpointObject) = (toAPIType tp = Some ArchTypes_H.apiobject_type.EndpointObject)"
  "(object_type_from_H tp = scast seL4_NotificationObject) = (toAPIType tp = Some ArchTypes_H.apiobject_type.NotificationObject)"
  "(object_type_from_H tp = scast seL4_CapTableObject) = (toAPIType tp = Some ArchTypes_H.apiobject_type.CapTableObject)"
  "(object_type_from_H tp = scast seL4_X86_4K) = (tp = X64_H.SmallPageObject)"
  "(object_type_from_H tp = scast seL4_X86_LargePageObject) = (tp = X64_H.LargePageObject)"
  "(object_type_from_H tp = scast seL4_X64_HugePageObject) = (tp = X64_H.HugePageObject)"
  "(object_type_from_H tp = scast seL4_X86_PageTableObject) = (tp = X64_H.PageTableObject)"
  "(object_type_from_H tp = scast seL4_X86_PageDirectoryObject) = (tp = X64_H.PageDirectoryObject)"
  "(object_type_from_H tp = scast seL4_X86_PDPTObject) = (tp = X64_H.PDPointerTableObject)"
  "(object_type_from_H tp = scast seL4_X64_PML4Object) = (tp = X64_H.PML4Object)"
  by (auto simp: toAPIType_def seL4_X86_PDPTObject_def seL4_X64_PML4Object_def seL4_X64_HugePageObject_def
                 object_type_from_H_def "StrictC'_object_defs" api_object_defs
          split: object_type.splits ArchTypes_H.apiobject_type.splits)

declare Collect_const_mem [simp]

lemma createNewCaps_untyped_if_helper:
  "\<forall>s s'. (s, s') \<in> rf_sr \<and> (sz < word_bits \<and> gbits < word_bits) \<and> True  \<longrightarrow>
             (\<not> gbits \<le> sz) = (s' \<in> \<lbrace>of_nat sz < (of_nat gbits :: machine_word)\<rbrace>)"
  by (clarsimp simp: not_le unat_of_nat64 word_less_nat_alt lt_word_bits_lt_pow)

lemma heap_list_update':
  "\<lbrakk> n = length v; length v \<le> 2 ^ word_bits \<rbrakk> \<Longrightarrow> heap_list (heap_update_list p v h) n p = v"
  by (simp add: heap_list_update addr_card_wb)

lemma h_t_valid_clift_Some_iff':
  "td \<Turnstile>\<^sub>t p = (clift (hp, td) p = Some (h_val hp p))"
  by (simp add: lift_t_if split: if_split)

lemma option_noneI: "\<lbrakk> \<And>x. a = Some x \<Longrightarrow> False \<rbrakk> \<Longrightarrow> a = None"
  apply (case_tac a)
   apply clarsimp
  apply atomize
  apply clarsimp
  done

lemma projectKO_opt_retyp_other':
  assumes pko: "\<forall>v. (projectKO_opt ko :: 'a :: pre_storable option) \<noteq> Some v"
  and pno: "pspace_no_overlap' ptr (objBitsKO ko) (\<sigma> :: kernel_state)"
  and pal: "pspace_aligned' (\<sigma> :: kernel_state)"
  and al: "is_aligned ptr (objBitsKO ko)"
  shows "projectKO_opt \<circ>\<^sub>m ((ksPSpace \<sigma>)(ptr \<mapsto> ko))
  = (projectKO_opt \<circ>\<^sub>m (ksPSpace \<sigma>) :: machine_word \<Rightarrow> 'a :: pre_storable option)" (is "?LHS = ?RHS")
proof (rule ext)
  fix x
  show "?LHS x = ?RHS x"
  proof (cases "x = ptr")
    case True
    hence "x \<in> {ptr..(ptr && ~~ mask (objBitsKO ko)) + 2 ^ objBitsKO ko - 1}"
      apply (rule ssubst)
      apply (insert al)
      apply (clarsimp simp: is_aligned_def)
      done
    hence "ksPSpace \<sigma> x = None" using pno
      apply -
      apply (rule option_noneI)
      apply (frule pspace_no_overlap_disjoint'[rotated])
       apply (rule pal)
      apply (drule domI[where a = x])
      apply blast
      done
    thus ?thesis using True pko by simp
  next
    case False
    thus ?thesis by (simp add: map_comp_def)
  qed
qed

lemma dom_tcb_cte_cases_iff:
  "(x \<in> dom tcb_cte_cases) = (\<exists>y < 5. unat x = y * (2^cteSizeBits))"
  unfolding tcb_cte_cases_def
  by (auto simp: unat_arith_simps objBits_simps')

lemma cmap_relation_retype2:
  assumes cm: "cmap_relation mp mp' Ptr rel"
  and   rel: "rel (mobj :: 'a :: pre_storable) ko'"
  shows "cmap_relation
        (\<lambda>x. if x \<in> ptr_val ` addrs then Some (mobj :: 'a :: pre_storable) else mp x)
        (\<lambda>y. if y \<in> addrs then Some ko' else mp' y)
        Ptr rel"
  using cm rel
  apply -
  apply (rule cmap_relationI)
   apply (simp add: dom_if cmap_relation_def image_Un)
  apply (case_tac "x \<in> addrs")
   apply (simp add: image_image)
  apply (simp add: image_image)
  apply (clarsimp split: if_split_asm)
   apply (erule contrapos_np)
   apply (erule image_eqI [rotated])
   apply simp
  apply (erule (2) cmap_relation_relI)
  done

lemma ti_typ_pad_combine_empty_ti:
  fixes tp :: "'b :: c_type itself"
  shows "ti_typ_pad_combine tp lu upd fld (empty_typ_info n) =
  TypDesc (TypAggregate [DTPair (adjust_ti (typ_info_t TYPE('b)) lu upd) fld]) n"
  by (simp add: ti_typ_pad_combine_def ti_typ_combine_def empty_typ_info_def Let_def)

lemma ti_typ_combine_empty_ti:
  fixes tp :: "'b :: c_type itself"
  shows "ti_typ_combine tp lu upd fld (empty_typ_info n) =
  TypDesc (TypAggregate [DTPair (adjust_ti (typ_info_t TYPE('b)) lu upd) fld]) n"
  by (simp add: ti_typ_combine_def empty_typ_info_def Let_def)

lemma ti_typ_pad_combine_td:
  fixes tp :: "'b :: c_type itself"
  shows "padup (align_of TYPE('b)) (size_td_struct st) = 0 \<Longrightarrow>
  ti_typ_pad_combine tp lu upd fld (TypDesc st n) =
  TypDesc (extend_ti_struct st (adjust_ti (typ_info_t TYPE('b)) lu upd) fld) n"
  by (simp add: ti_typ_pad_combine_def ti_typ_combine_def Let_def)

lemma ti_typ_combine_td:
  fixes tp :: "'b :: c_type itself"
  shows "padup (align_of TYPE('b)) (size_td_struct st) = 0 \<Longrightarrow>
  ti_typ_combine tp lu upd fld (TypDesc st n) =
  TypDesc (extend_ti_struct st (adjust_ti (typ_info_t TYPE('b)) lu upd) fld) n"
  by (simp add: ti_typ_combine_def Let_def)

lemma update_ti_t_pad_combine:
  assumes std: "size_td td' mod 2 ^ align_td (typ_info_t TYPE('a :: c_type)) = 0"
  shows "update_ti_t (ti_typ_pad_combine TYPE('a :: c_type) lu upd fld td') bs v =
  update_ti_t (ti_typ_combine TYPE('a :: c_type) lu upd fld td') bs v"
  using std
  by (simp add: ti_typ_pad_combine_def size_td_simps Let_def)


lemma update_ti_t_ptr_0s:
  "update_ti_t (typ_info_t TYPE('a :: c_type ptr)) [0,0,0,0,0,0,0,0] X = NULL"
  apply (simp add: typ_info_ptr word_rcat_def bin_rcat_def)
  done

lemma size_td_map_list:
  "size_td_list (map (\<lambda>n. DTPair
                                 (adjust_ti (typ_info_t TYPE('a :: c_type))
                                   (\<lambda>x. index x n)
                                   (\<lambda>x f. Arrays.update f n x))
                                 (replicate n CHR ''1''))
                        [0..<n]) = (size_td (typ_info_t TYPE('a :: c_type)) * n)"
  apply (induct n)
   apply simp
  apply simp
  done

lemma update_ti_t_array_tag_n_rep:
  fixes x :: "'a :: c_type ['b :: finite]"
  shows "\<lbrakk> bs = replicate (n * size_td (typ_info_t TYPE('a))) v; n \<le> card (UNIV  :: 'b set) \<rbrakk> \<Longrightarrow>
  update_ti_t (array_tag_n n) bs x =
  foldr (\<lambda>n arr. Arrays.update arr n
        (update_ti_t (typ_info_t TYPE('a)) (replicate (size_td (typ_info_t TYPE('a))) v) (index arr n)))
        [0..<n] x"
  apply (induct n arbitrary: bs x)
   apply (simp add: array_tag_n_eq)
  apply (simp add: array_tag_n_eq size_td_map_list iffD2 [OF linorder_min_same1] field_simps
    cong: if_cong )
  apply (simp add: update_ti_adjust_ti)
  done

lemma update_ti_t_array_rep:
  "bs = replicate ((card (UNIV :: 'b :: finite set)) * size_td (typ_info_t TYPE('a))) v \<Longrightarrow>
  update_ti_t (typ_info_t TYPE('a :: c_type['b :: finite])) bs x =
  foldr (\<lambda>n arr. Arrays.update arr n
        (update_ti_t (typ_info_t TYPE('a)) (replicate (size_td (typ_info_t TYPE('a))) v) (index arr n)))
        [0..<(card (UNIV :: 'b :: finite set))] x"
  unfolding typ_info_array array_tag_def
  apply (rule update_ti_t_array_tag_n_rep)
    apply simp
   apply simp
   done

lemma update_ti_t_array_rep_word0:
  "bs = replicate ((card (UNIV :: 'b :: finite set)) * 8) 0 \<Longrightarrow>
  update_ti_t (typ_info_t TYPE(machine_word['b :: finite])) bs x =
  foldr (\<lambda>n arr. Arrays.update arr n 0)
        [0..<(card (UNIV :: 'b :: finite set))] x"
  apply (subst update_ti_t_array_rep)
   apply simp
  apply (simp add: update_ti_t_machine_word_0s)
  done

lemma update_ti_t_array_rep_byte0:
  "bs = replicate (CARD('b)) 0 \<Longrightarrow>
  update_ti_t (typ_info_t TYPE(8 word['b :: finite])) bs x =
  foldr (\<lambda>n arr. Arrays.update arr n 0)
        [0..<CARD('b)] x"
  apply (subst update_ti_t_array_rep)
   apply simp
  apply (simp add: typ_info_word)
  done

lemma selCS3_eq:
  "selCS3 = 0x2B"
  by (simp add: selCS3_def gdtToSel_masked_def gdtToSel_def fromEnum_def enum_gdtslot)

lemma selDS3_eq:
  "selDS3 = 0x33"
  by (simp add: selDS3_def gdtToSel_masked_def gdtToSel_def fromEnum_def enum_gdtslot)

lemma FLAGS_default_eq:
  "(((1 << 9) || bit 1) :: machine_word) = 0x202"
  by (word_bitwise, clarsimp)

lemma newContext_def2:
  "newContext \<equiv> UserContext FPUNullState (\<lambda>x. if x = CS then 0x2B
                                              else if x = SS then 0x33
                                              else if x = FLAGS then 0x202
                                              else 0)"
  (is "_ \<equiv> ?UC")
proof -
  have "newContext = ?UC"
    apply (simp add: newContext_def initContext_def selCS3_eq selDS3_eq fun_upd_def)
    apply (rule ext, simp split: if_splits)
    done
  thus "newContext \<equiv> ?UC" by simp
qed

lemma tcb_queue_update_other:
  "\<lbrakk> ctcb_ptr_to_tcb_ptr p \<notin> set tcbs \<rbrakk> \<Longrightarrow>
  tcb_queue_relation next prev (mp(p \<mapsto> v)) tcbs qe qh =
  tcb_queue_relation next prev mp tcbs qe qh"
  apply (induct tcbs arbitrary: qh qe)
   apply simp
  apply (rename_tac a tcbs qh qe)
  apply simp
  apply (subgoal_tac "p \<noteq> tcb_ptr_to_ctcb_ptr a")
   apply (simp cong: conj_cong)
  apply clarsimp
  done

lemma cmap_relation_cong':
  "\<lbrakk>am = am'; cm = cm';
   \<And>p a a' b b'.
      \<lbrakk>am p = Some a; am' p = Some a'; cm (f p) = Some b; cm' (f p) = Some b'\<rbrakk>
      \<Longrightarrow> rel a b = rel' a' b'\<rbrakk>
    \<Longrightarrow> cmap_relation am cm f rel = cmap_relation am' cm' f rel'"
  by (rule cmap_relation_cong, simp_all)

lemma tcb_queue_update_other':
  "\<lbrakk> ctcb_ptr_to_tcb_ptr p \<notin> set tcbs \<rbrakk> \<Longrightarrow>
  tcb_queue_relation' next prev (mp(p \<mapsto> v)) tcbs qe qh =
  tcb_queue_relation' next prev mp tcbs qe qh"
  unfolding tcb_queue_relation'_def
  by (simp add: tcb_queue_update_other)

lemma c_guard_tcb:
  assumes al: "is_aligned (ctcb_ptr_to_tcb_ptr p) tcbBlockSizeBits"
  and   ptr0: "ctcb_ptr_to_tcb_ptr p \<noteq> 0"
  shows "c_guard p"
  unfolding c_guard_def
proof (rule conjI)
  show "ptr_aligned p" using al
    apply -
    apply (rule is_aligned_ptr_aligned [where n = word_size_bits])
    apply (rule is_aligned_weaken)
    apply (erule ctcb_ptr_to_tcb_ptr_aligned)
     apply (simp add: ctcb_size_bits_def word_size_bits_def)
    apply (simp add: align_of_def word_size_bits_def)
    done

  show "c_null_guard p" using ptr0 al
    unfolding c_null_guard_def
    apply -
    apply (rule intvl_nowrap [where x = 0, simplified])
    apply (clarsimp simp: ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs tcbBlockSizeBits_def is_aligned_def)
    apply (drule ctcb_ptr_to_tcb_ptr_aligned)
    apply (erule is_aligned_no_wrap_le)
     apply (simp add: word_bits_conv ctcb_size_bits_def)
    apply (simp add: size_of_def ctcb_size_bits_def)
    done
qed

lemma tcb_ptr_orth_cte_ptrs:
  "{ptr_val p..+size_of TYPE(tcb_C)} \<inter> {ctcb_ptr_to_tcb_ptr p..+5 * size_of TYPE(cte_C)} = {}"
  apply (rule disjointI)
  apply (clarsimp simp: ctcb_ptr_to_tcb_ptr_def intvl_def field_simps size_of_def ctcb_offset_defs)
  apply unat_arith
   apply (simp add: unat_of_nat64 word_bits_conv)
  apply (simp add: unat_of_nat64 word_bits_conv)
  done

lemma tcb_ptr_orth_cte_ptrs':
  "ptr_span (tcb_Ptr (regionBase + 0x400)) \<inter> ptr_span (Ptr regionBase :: (cte_C[5]) ptr) = {}"
  apply (rule disjointI)
  apply (clarsimp simp: ctcb_ptr_to_tcb_ptr_def size_td_array
                        intvl_def field_simps size_of_def ctcb_offset_def)
  apply (simp add: unat_arith_simps unat_of_nat)
  done

lemma region_is_typeless_weaken:
  "\<lbrakk> region_is_typeless a b s'; (t_hrs_' (globals s)) = (t_hrs_' (globals s')); a \<le> x; unat x + y \<le> unat a + b \<rbrakk> \<Longrightarrow> region_is_typeless x y s"
  by (clarsimp simp: region_is_typeless_def subsetD[OF intvl_both_le])

lemmas ptr_retyp_htd_safe_neg
  = ptr_retyps_htd_safe_neg[where n="Suc 0" and arr=False, unfolded ptr_retyps_gen_def, simplified]

lemmas ptr_retyp_htd_safe_neg' = ptr_retyp_htd_safe_neg[OF _ _ subset_refl]

abbreviation
  tcbContext_of_tcb_Ptr :: "tcb_C ptr \<Rightarrow> user_context_C ptr"
where
  "tcbContext_of_tcb_Ptr p \<equiv> Ptr &(atcb_Ptr &(p\<rightarrow>[''tcbArch_C''])\<rightarrow>[''tcbContext_C''])"

abbreviation
  registers_of_tcb_Ptr :: "tcb_C ptr \<Rightarrow> (machine_word[24]) ptr"
where
  "registers_of_tcb_Ptr p \<equiv> Ptr &(tcbContext_of_tcb_Ptr p \<rightarrow>[''registers_C''])"

abbreviation
  fpu_state_of_tcb_Ptr :: "tcb_C ptr \<Rightarrow> user_fpu_state_C ptr"
where
  "fpu_state_of_tcb_Ptr p \<equiv> fpu_state_Ptr &(tcbContext_of_tcb_Ptr p\<rightarrow>[''fpuState_C''])"

definition
  array_updates :: "'a::c_type['b::finite] \<Rightarrow> (nat \<times> 'a) list \<Rightarrow> 'a['b]"
where
  "array_updates \<equiv> foldl (\<lambda>a (i,v). Arrays.update a i v)"

definition
  heap_updates :: "heap_raw_state \<Rightarrow> (heap_mem \<Rightarrow> heap_mem) list \<Rightarrow> heap_raw_state"
where
  "heap_updates \<equiv> foldl (\<lambda>h upd. hrs_mem_update upd h)"

lemmas heap_updates_defs =
  heap_updates_def heap_modify_def array_updates_def

(* FIXME: move up to TypHeapLib? *)
lemma clift_heap_update_same':
  fixes p :: "'a :: mem_type ptr"
  shows "\<lbrakk> hrs_htd hp \<Turnstile>\<^sub>t p; typ_uinfo_t TYPE('a) \<bottom>\<^sub>t typ_uinfo_t TYPE('b) \<rbrakk>
  \<Longrightarrow> clift (hrs_mem_update (\<lambda>h. heap_update p (v h) h) hp) = (clift hp :: 'b :: mem_type typ_heap)"
  unfolding hrs_mem_update_def
  apply (cases hp)
  apply (simp add: split_def hrs_htd_def)
  apply (erule lift_t_heap_update_same)
  apply simp
  done

(* FIXME: move up to TypHeapLib? *)
lemmas clift_heap_update_same_td_name' =
  clift_heap_update_same'[OF _  tag_disj_via_td_name, unfolded pad_typ_name_def]

definition
  initContext_registers :: "(nat \<times> machine_word) list"
where
  "initContext_registers \<equiv>
    [(unat Kernel_C.RAX, 0), (unat Kernel_C.RBX, 0), (unat Kernel_C.RCX, 0), (unat Kernel_C.RDX, 0),
     (unat Kernel_C.RSI, 0), (unat Kernel_C.RDI, 0), (unat Kernel_C.RBP, 0), (unat Kernel_C.R8 , 0),
     (unat Kernel_C.R9 , 0), (unat Kernel_C.R10, 0), (unat Kernel_C.R11, 0), (unat Kernel_C.R12, 0),
     (unat Kernel_C.R13, 0), (unat Kernel_C.R14, 0), (unat Kernel_C.R15, 0), (unat Kernel_C.RSP, 0),
     (unat Kernel_C.FS_BASE, 0), (unat Kernel_C.GS_BASE, 0), (unat Kernel_C.Error, 0),
     (unat Kernel_C.FaultIP, 0), (unat Kernel_C.NextIP, 0), (unat Kernel_C.CS, 0x2B),
     (unat Kernel_C.FLAGS, 0x202), (unat Kernel_C.SS, 0x33)]"

(* FIXME: move *)
lemma field_tag_sub':
  fixes p :: "'a::mem_type ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t,n)"
  assumes sz: "size_of TYPE('b) = size_td t"
  shows "ptr_span (Ptr &(p\<rightarrow>f)::'b::mem_type ptr) \<subseteq> ptr_span p"
  by (clarsimp simp: sz field_tag_sub[OF fl])

lemmas field_tag_sub_trans =
  subset_trans[OF field_tag_sub', rotated -1]

lemmas field_tag_subs =
  field_tag_sub_trans[OF field_tag_sub_trans[OF field_tag_sub_trans[OF field_tag_sub']]]
  field_tag_sub_trans[OF field_tag_sub_trans[OF field_tag_sub']]
  field_tag_sub_trans[OF field_tag_sub']
  field_tag_sub'

lemmas fpu_null_state_heap_update_field =
  field_tag_subs[THEN disjoint_subset[where B=kernel_data_refs],
                 THEN fpu_null_state_heap_update_span_disjoint]

context
  fixes p:: "'a::mem_type ptr" and n :: nat
  assumes nkr: "{ptr_val p ..+ n * size_of TYPE('a)} \<inter> kernel_data_refs = {}"
begin

lemma retyp_non_kernel_data_ref:
  fixes q :: "'b::mem_type ptr"
  assumes "ptr_span q \<subseteq> kernel_data_refs"
  shows "ptr_retyps_gen n p foo (hrs_htd h) \<Turnstile>\<^sub>t q \<longleftrightarrow> hrs_htd h \<Turnstile>\<^sub>t q"
  apply (rule h_t_valid_ptr_retyps_gen_disjoint_iff)
  apply (subst Int_commute)
  apply (rule disjoint_subset2[OF assms nkr])
  done

lemma fpu_null_state_retyp_disjoint:
  "fpu_null_state_relation (hrs_htd_update (ptr_retyps_gen n p foo) h) = fpu_null_state_relation h"
  by (cases "ptr_span (fpu_state_Ptr (symbol_table ''x86KSnullFpuState'')) \<subseteq> kernel_data_refs";
      clarsimp simp: fpu_null_state_relation_def lift_t_Some_iff hrs_htd_update
                     retyp_non_kernel_data_ref)

end

lemma cnc_tcb_helper:
  fixes p :: "tcb_C ptr"
  defines "kotcb \<equiv> (KOTCB (makeObject :: tcb))"
  assumes rfsr: "(\<sigma>\<lparr>ksPSpace := ks\<rparr>, x) \<in> rf_sr"
  assumes al: "is_aligned (ctcb_ptr_to_tcb_ptr p) (objBitsKO kotcb)"
  assumes ptr0: "ctcb_ptr_to_tcb_ptr p \<noteq> 0"
  assumes vq: "valid_queues \<sigma>"
  assumes pal: "pspace_aligned' (\<sigma>\<lparr>ksPSpace := ks\<rparr>)"
  assumes pno: "pspace_no_overlap' (ctcb_ptr_to_tcb_ptr p) (objBitsKO kotcb) (\<sigma>\<lparr>ksPSpace := ks\<rparr>)"
  assumes pds: "pspace_distinct' (\<sigma>\<lparr>ksPSpace := ks\<rparr>)"
  assumes symref: "sym_refs (state_refs_of' (\<sigma>\<lparr>ksPSpace := ks\<rparr>))"
  assumes kssub: "dom (ksPSpace \<sigma>) \<subseteq> dom ks"
  assumes rzo: "ret_zero (ctcb_ptr_to_tcb_ptr p) (2 ^ objBitsKO kotcb) \<sigma>"
  assumes empty: "region_is_bytes (ctcb_ptr_to_tcb_ptr p) (2 ^ tcbBlockSizeBits) x"
  assumes rep0: "heap_list (fst (t_hrs_' (globals x))) (2 ^ tcbBlockSizeBits) (ctcb_ptr_to_tcb_ptr p) = replicate (2 ^ tcbBlockSizeBits) 0"
  assumes kdr: "{ctcb_ptr_to_tcb_ptr p..+2 ^ tcbBlockSizeBits} \<inter> kernel_data_refs = {}"
  shows "(\<sigma>\<lparr>ksPSpace := ks(ctcb_ptr_to_tcb_ptr p \<mapsto> kotcb)\<rparr>,
            globals_update
              (t_hrs_'_update
                (\<lambda>hrs. (heap_updates (hrs_htd_update (\<lambda>htd. ptr_retyps_gen 1 (tcb_cnode_Ptr (ctcb_ptr_to_tcb_ptr p)) False
                                                                           (ptr_retyps_gen 1 p False htd)) hrs)
                                     [heap_update (registers_of_tcb_Ptr p)
                                                  (array_updates (h_val (hrs_mem hrs) (registers_of_tcb_Ptr p))
                                                                 initContext_registers),
                                      heap_update (fpu_state_of_tcb_Ptr p)
                                                  (user_fpu_state_C (ARRAY i. FPUNullState (finite_index i))),
                                      heap_update (machine_word_Ptr &(p\<rightarrow>[''tcbTimeSlice_C''])) 5])
                       )) x)
           \<in> rf_sr"
  (is "(\<sigma>\<lparr>ksPSpace := ?ks\<rparr>, globals_update ?gs' x) \<in> rf_sr")
proof -
  define ko where "ko \<equiv> (KOCTE (makeObject :: cte))"
  let ?ptr = "cte_Ptr (ctcb_ptr_to_tcb_ptr p)"
  let ?arr_ptr = "Ptr (ctcb_ptr_to_tcb_ptr p) :: (cte_C[5]) ptr"
  let ?sp = "\<sigma>\<lparr>ksPSpace := ks\<rparr>"
  let ?s = "\<sigma>\<lparr>ksPSpace := ?ks\<rparr>"
  let ?gs = "?gs' (globals x)"
  let ?hp = "(fst (t_hrs_' ?gs), (ptr_retyps_gen 1 p False (snd (t_hrs_' (globals x)))))"

  note tcb_C_size[simp del]

  from al have cover: "range_cover (ctcb_ptr_to_tcb_ptr p) (objBitsKO kotcb)
        (objBitsKO kotcb) (Suc 0)"
    by (rule range_cover_full, simp_all add: al)

  have "\<forall>n<2 ^ (objBitsKO kotcb - objBitsKO ko). c_guard (CTypesDefs.ptr_add ?ptr (of_nat n))"
    apply (rule retype_guard_helper [where m = 3])
        apply (rule range_cover_rel[OF cover, rotated])
         apply simp
        apply (simp add: ko_def objBits_simps' kotcb_def)
       apply (rule ptr0)
      apply (simp add: ko_def objBits_simps' size_of_def)
     apply (simp add: ko_def objBits_simps')
    apply (simp add: ko_def objBits_simps align_of_def)
    done
  hence guard: "\<forall>n<5. c_guard (CTypesDefs.ptr_add ?ptr (of_nat n))"
    by (simp add: ko_def kotcb_def objBits_simps' align_of_def)

  have arr_guard: "c_guard ?arr_ptr"
    apply (rule is_aligned_c_guard[where m=3], simp, rule al)
       apply (simp add: ptr0)
      apply (simp add: align_of_def align_td_array)
     apply (simp add: cte_C_size objBits_simps' kotcb_def)
    apply (simp add: kotcb_def objBits_simps')
    done

  have heap_update_to_hrs_mem_update:
    "\<And>p x hp ht. (heap_update p x hp, ht) = hrs_mem_update (heap_update p x) (hp, ht)"
    by (simp add: hrs_mem_update_def split_def)

  have empty_smaller:
    "region_is_bytes (ptr_val p) (size_of TYPE(tcb_C)) x"
    "region_is_bytes' (ctcb_ptr_to_tcb_ptr p) (5 * size_of TYPE(cte_C))
        (ptr_retyps_gen 1 p False (hrs_htd (t_hrs_' (globals x))))"
    using al region_is_bytes_subset[OF empty] tcb_ptr_to_ctcb_ptr_in_range'
    apply (simp add: objBits_simps kotcb_def)
    apply (clarsimp simp: region_is_bytes'_def)
    apply (subst(asm) ptr_retyps_gen_out)
     apply (clarsimp simp: ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs intvl_def)
     apply (simp add: unat_arith_simps unat_of_nat cte_C_size tcb_C_size
               split: if_split_asm)
    apply (subst(asm) empty[unfolded region_is_bytes'_def], simp_all)
    apply (erule subsetD[rotated], rule intvl_start_le)
    apply (simp add: cte_C_size objBits_simps')
    done

  note htd[simp] = hrs_htd_update_htd_update[unfolded o_def,
        where d="ptr_retyps_gen n p a" and d'="ptr_retyps_gen n' p' a'"
        for n p a n' p' a', symmetric]

  have cgp: "c_guard p" using al
    apply -
    apply (rule c_guard_tcb [OF _ ptr0])
    apply (simp add: kotcb_def objBits_simps)
    done

  from pal rfsr have "\<forall>x\<in>dom (cslift x :: cte_C typ_heap). is_aligned (ptr_val x) (objBitsKO ko)"
    apply (rule pspace_aligned_to_C_cte [OF _ cmap_relation_cte])
    apply (simp add: projectKOs ko_def)
    done

  have "ptr_val p = ctcb_ptr_to_tcb_ptr p + ctcb_offset"
    by (simp add: ctcb_ptr_to_tcb_ptr_def)

  have cte_tcb_disjoint: "\<And>y. y \<in> (CTypesDefs.ptr_add (cte_Ptr (ctcb_ptr_to_tcb_ptr p)) \<circ> of_nat) ` {k. k < 5}
    \<Longrightarrow> {ptr_val p..+size_of TYPE(tcb_C)} \<inter> {ptr_val y..+size_of TYPE(cte_C)} = {}"
    apply (rule disjoint_subset2 [OF _ tcb_ptr_orth_cte_ptrs])
    apply (clarsimp simp: intvl_def size_of_def)
    apply (rule_tac x = "x * (2^cteSizeBits) + k" in exI)
    apply (simp add: objBits_simps')
    done

  have cl_cte: "(cslift (x\<lparr>globals := ?gs\<rparr>) :: cte_C typ_heap) =
    (\<lambda>y. if y \<in> (CTypesDefs.ptr_add (cte_Ptr (ctcb_ptr_to_tcb_ptr p)) \<circ>
                 of_nat) `
                {k. k < 5}
         then Some (from_bytes (replicate (size_of TYPE(cte_C)) 0)) else cslift x y)"
    using cgp unfolding heap_updates_defs
    apply (simp add: ptr_retyp_to_array[simplified] hrs_comm[symmetric] Let_def)
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard],
           simp_all add: hrs_htd_update empty_smaller[simplified])
      apply (simp add: cte_C_size word_bits_def)
     apply (simp add: hrs_mem_update typ_heap_simps
                      packed_heap_update_collapse)
     apply (simp add: heap_update_def)
     apply (subst heap_list_update_disjoint_same)
      apply (clarsimp simp: ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs intvl_def
                            set_eq_iff)
      apply (simp add: unat_arith_simps unat_of_nat cte_C_size tcb_C_size)
     apply (subst take_heap_list_le[symmetric])
      prefer 2
      apply (simp add: hrs_mem_def, subst rep0)
      apply (simp only: take_replicate, simp add: cte_C_size objBits_simps')
     apply (simp add: cte_C_size objBits_simps')
    apply (simp add: fun_eq_iff split: if_split)
    apply (simp add: hrs_comm packed_heap_update_collapse
                     typ_heap_simps)
    apply (subst clift_heap_update_same_td_name', simp_all,
           simp add: hrs_htd_update ptr_retyps_gen_def ptr_retyp_h_t_valid)+
    apply (subst clift_ptr_retyps_gen_other,
           simp_all add: empty_smaller tag_disj_via_td_name)
    apply (simp add: tcb_C_size word_bits_def)
    done

  have tcb0: "heap_list (fst (t_hrs_' (globals x))) (size_of TYPE(tcb_C)) (ptr_val p) = replicate (size_of TYPE(tcb_C)) 0"
  proof -
    have "heap_list (fst (t_hrs_' (globals x))) (size_of TYPE(tcb_C)) (ptr_val p)
      = take (size_of TYPE(tcb_C)) (drop (unat (ptr_val p - ctcb_ptr_to_tcb_ptr p))
           (heap_list (fst (t_hrs_' (globals x))) (2 ^ tcbBlockSizeBits) (ctcb_ptr_to_tcb_ptr p)))"
      by (simp add: drop_heap_list_le take_heap_list_le size_of_def ctcb_ptr_to_tcb_ptr_def
                       ctcb_offset_defs objBits_simps')
    also have "\<dots> = replicate (size_of TYPE(tcb_C)) 0"
      apply (subst rep0)
      apply (simp only: take_replicate drop_replicate)
      apply (rule arg_cong [where f = "\<lambda>x. replicate x 0"])
      apply (clarsimp simp: ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs size_of_def objBits_simps')
      done
    finally show "heap_list (fst (t_hrs_' (globals x))) (size_of TYPE(tcb_C)) (ptr_val p) = replicate (size_of TYPE(tcb_C)) 0" .
  qed

  note alrl = pspace_aligned_to_C_tcb [OF pal cmap_relation_tcb [OF rfsr]]

  have tdisj:
    "\<forall>xa\<in>dom (cslift x) \<union> {p}. \<forall>y\<in>dom (cslift x). {ptr_val xa..+size_of TYPE(tcb_C)} \<inter> {ptr_val y..+size_of TYPE(tcb_C)} \<noteq> {}
           \<longrightarrow> xa = y"
    using al
    apply (intro ballI impI)
    apply (erule contrapos_np)
    apply (subgoal_tac "is_aligned (ptr_val xa) ctcb_size_bits")
     apply (subgoal_tac "is_aligned (ptr_val y) ctcb_size_bits")
      apply (subgoal_tac "ctcb_size_bits < word_bits")
       apply (rule_tac A = "{ptr_val xa..+2 ^ ctcb_size_bits}" in disjoint_subset)
        apply (rule intvl_start_le)
        apply (simp add: size_of_def ctcb_size_bits_def)
       apply (rule_tac B = "{ptr_val y..+2 ^ ctcb_size_bits}" in disjoint_subset2)
        apply (rule intvl_start_le)
        apply (simp add: size_of_def ctcb_size_bits_def)
       apply (simp only: upto_intvl_eq)
       apply (rule aligned_neq_into_no_overlap [simplified field_simps])
          apply simp
         apply assumption+
      apply (simp add: word_bits_conv ctcb_size_bits_def)
     apply (erule bspec [OF alrl])
    apply (clarsimp)
    apply (erule disjE)
     apply (simp add: objBits_simps kotcb_def)
     apply (erule ctcb_ptr_to_tcb_ptr_aligned)
    apply (erule bspec [OF alrl])
    done

  let ?tcbArch_C = "tcbArch_C (from_bytes (replicate (size_of TYPE(tcb_C)) 0))"

  let ?new_tcb =  "(from_bytes (replicate (size_of TYPE(tcb_C)) 0)
                     \<lparr>tcbArch_C := ?tcbArch_C
                       \<lparr>tcbContext_C := tcbContext_C ?tcbArch_C
                         \<lparr>registers_C := array_updates (registers_C (tcbContext_C ?tcbArch_C))
                                                       initContext_registers,
                          fpuState_C := fpuState_C (tcbContext_C ?tcbArch_C)
                            \<lparr>state_C := ARRAY i. FPUNullState (finite_index i)\<rparr>\<rparr>\<rparr>,
                        tcbTimeSlice_C := 5\<rparr>)"

  have tdisj':
    "\<And>y. hrs_htd (t_hrs_' (globals x)) \<Turnstile>\<^sub>t y \<Longrightarrow> ptr_span p \<inter> ptr_span y \<noteq> {} \<Longrightarrow> y = p"
    using tdisj by (auto simp: h_t_valid_clift_Some_iff)

  have state_C_udpate_const_user_fpu_state_C:
    "\<And>arr. state_C_update (\<lambda>_. arr) = (\<lambda>_. user_fpu_state_C arr)"
    by (metis state_C_update.simps user_fpu_state_C.exhaust)

  have "ptr_retyp p (snd (t_hrs_' (globals x))) \<Turnstile>\<^sub>t p" using cgp
    by (rule ptr_retyp_h_t_valid)
  hence "clift (hrs_mem (t_hrs_' (globals x)), ptr_retyp p (snd (t_hrs_' (globals x)))) p
    = Some (from_bytes (replicate (size_of TYPE(tcb_C)) 0))"
    by (simp add: lift_t_if h_val_def tcb0 hrs_mem_def)
  hence cl_tcb: "(cslift (x\<lparr>globals := ?gs\<rparr>) :: tcb_C typ_heap) = (cslift x)(p \<mapsto> ?new_tcb)"
    using cgp
    apply (clarsimp simp add: typ_heap_simps heap_updates_def
                              hrs_mem_update packed_heap_update_collapse_hrs)
    apply (simp add: hrs_comm[symmetric])
    apply (subst clift_ptr_retyps_gen_other,
           simp_all add: hrs_htd_update empty_smaller[simplified] tag_disj_via_td_name)
     apply (simp add: cte_C_size word_bits_def)
    apply (simp add: hrs_comm typ_heap_simps ptr_retyps_gen_def
                     hrs_htd_update ptr_retyp_h_t_valid
                     h_val_heap_update h_val_field_from_bytes')
    apply (simp add: h_val_def tcb0[folded hrs_mem_def]
                     state_C_udpate_const_user_fpu_state_C)
    apply (rule ext, rename_tac p')
    apply (case_tac "p' = p", simp_all)
    apply (cut_tac clift_ptr_retyps_gen_prev_memset_same
                     [where n=1 and arr=False, simplified, OF _ empty_smaller(1) _ refl])
        apply (simp_all add: tcb0[folded hrs_mem_def] ptr_retyps_gen_def)
    apply (simp add: tcb_C_size word_bits_def)
    done

  have cl_rest:
    "\<lbrakk>typ_uinfo_t TYPE(tcb_C) \<bottom>\<^sub>t typ_uinfo_t TYPE('a :: mem_type);
      typ_uinfo_t TYPE(cte_C[5]) \<bottom>\<^sub>t typ_uinfo_t TYPE('a :: mem_type);
      typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(word8) \<rbrakk> \<Longrightarrow>
    cslift (x\<lparr>globals := ?gs\<rparr>) = (cslift x :: 'a :: mem_type typ_heap)"
    using cgp
    apply (clarsimp simp: hrs_comm[symmetric] heap_updates_def)
    apply (subst clift_ptr_retyps_gen_other,
      simp_all add: hrs_htd_update empty_smaller[simplified],
      simp_all add: cte_C_size tcb_C_size word_bits_def)
    apply (simp add: hrs_comm ptr_retyps_gen_def)
    apply (simp add: clift_heap_update_same hrs_htd_update ptr_retyp_h_t_valid typ_heap_simps)
    apply (rule trans[OF _ clift_ptr_retyps_gen_other[where nptrs=1 and arr=False,
        simplified, OF empty_smaller(1)]], simp_all)
     apply (simp add: ptr_retyps_gen_def)
    apply (simp add: tcb_C_size word_bits_def)
    done

  have rl:
    "(\<forall>v :: 'a :: pre_storable. projectKO_opt kotcb \<noteq> Some v) \<Longrightarrow>
    (projectKO_opt \<circ>\<^sub>m (ks(ctcb_ptr_to_tcb_ptr p \<mapsto> KOTCB makeObject)) :: machine_word \<Rightarrow> 'a option)
    = projectKO_opt \<circ>\<^sub>m ks" using pno al
    apply -
    apply (drule(2) projectKO_opt_retyp_other'[OF _ _ pal])
    apply (simp add: kotcb_def)
    done

  have rl_tcb: "(projectKO_opt \<circ>\<^sub>m (ks(ctcb_ptr_to_tcb_ptr p \<mapsto> KOTCB makeObject)) :: machine_word \<Rightarrow> tcb option)
    = (projectKO_opt \<circ>\<^sub>m ks)(ctcb_ptr_to_tcb_ptr p \<mapsto> makeObject)"
    apply (rule ext)
    apply (clarsimp simp: projectKOs map_comp_def split: if_split)
    done

  have mko: "\<And>dev. makeObjectKO dev (Inr (APIObjectType ArchTypes_H.apiobject_type.TCBObject)) = Some kotcb"
    by (simp add: makeObjectKO_def kotcb_def)
  note hacky_cte = retype_ctes_helper [where sz = "objBitsKO kotcb" and ko = kotcb and ptr = "ctcb_ptr_to_tcb_ptr p",
    OF pal pds pno al _ _ mko, simplified new_cap_addrs_def, simplified]

  \<comment> \<open>Ugh\<close>
  moreover have
    "\<And>y. y \<in> ptr_val ` (CTypesDefs.ptr_add (cte_Ptr (ctcb_ptr_to_tcb_ptr p)) \<circ> of_nat) ` {k. k < 5}
    = (y && ~~ mask tcbBlockSizeBits = ctcb_ptr_to_tcb_ptr p \<and> y && mask tcbBlockSizeBits \<in> dom tcb_cte_cases)" (is "\<And>y. ?LHS y = ?RHS y")
  proof -
    fix y

    have al_rl: "\<And>k. k < 5 \<Longrightarrow>
      ctcb_ptr_to_tcb_ptr p + of_nat k * of_nat (size_of TYPE(cte_C)) && mask tcbBlockSizeBits = of_nat k * of_nat (size_of TYPE(cte_C))
      \<and> ctcb_ptr_to_tcb_ptr p + of_nat k * of_nat (size_of TYPE(cte_C)) && ~~ mask tcbBlockSizeBits = ctcb_ptr_to_tcb_ptr p" using al
      apply -
      apply (rule is_aligned_add_helper)
      apply (simp add: objBits_simps kotcb_def)
       apply (subst Abs_fnat_hom_mult)
       apply (subst word_less_nat_alt)
       apply (subst unat_of_nat64)
       apply (simp add: size_of_def word_bits_conv objBits_simps')+
      done

    have al_rl2: "\<And>k. k < 5 \<Longrightarrow> unat (of_nat k * of_nat (size_of TYPE(cte_C)) :: machine_word) = k * (2^cteSizeBits)"
       apply (subst Abs_fnat_hom_mult)
       apply (subst unat_of_nat64)
       apply (simp add: size_of_def word_bits_conv objBits_simps')+
       done

    show "?LHS y = ?RHS y" using al
      apply (simp add: image_image kotcb_def objBits_simps)
      apply rule
       apply (clarsimp simp: dom_tcb_cte_cases_iff al_rl al_rl2)
      apply (clarsimp simp: dom_tcb_cte_cases_iff al_rl al_rl2)
      apply (rule_tac x = ya in image_eqI)
      apply (rule mask_eqI [where n = tcbBlockSizeBits])
      apply (subst unat_arith_simps(3))
      apply (simp add: al_rl al_rl2)+
      done
  qed

  ultimately have rl_cte: "(map_to_ctes (ks(ctcb_ptr_to_tcb_ptr p \<mapsto> KOTCB makeObject)) :: machine_word \<Rightarrow> cte option)
    = (\<lambda>x. if x \<in> ptr_val ` (CTypesDefs.ptr_add (cte_Ptr (ctcb_ptr_to_tcb_ptr p)) \<circ> of_nat) ` {k. k < 5}
         then Some (CTE NullCap nullMDBNode)
         else map_to_ctes ks x)"
    apply simp
    apply (drule_tac x = "Suc 0" in meta_spec)
    apply clarsimp
    apply (erule impE[OF impI])
     apply (rule range_cover_full[OF al])
     apply (simp add: objBits_simps' word_bits_conv bit_simps archObjSize_def
       split:kernel_object.splits arch_kernel_object.splits)
    apply (simp add: fun_upd_def kotcb_def cong: if_cong)
    done

  let ?tcb = "(tcbArch_C_update
     (\<lambda>_. tcbContext_C_update
           (\<lambda>_. registers_C_update (\<lambda>_. foldr (\<lambda>n arr. Arrays.update arr n 0) [0..<24]
                     (registers_C (tcbContext_C (tcbArch_C undefined))))
                 (fpuState_C_update
                   (\<lambda>_. state_C_update (\<lambda>_. foldr (\<lambda>n arr. Arrays.update arr n 0) [0..<576]
                           (state_C (fpuState_C (tcbContext_C (tcbArch_C undefined)))))
                         (fpuState_C (tcbContext_C (tcbArch_C undefined))))
                   (tcbContext_C (tcbArch_C undefined))))
           (tcbArch_C undefined))
     undefined)\<lparr>
       tcbState_C :=
         thread_state_C.words_C_update
          (\<lambda>_. foldr (\<lambda>n arr. Arrays.update arr n 0) [0..<3]
                (thread_state_C.words_C (tcbState_C undefined)))
          (tcbState_C undefined),
       tcbFault_C :=
         seL4_Fault_C.words_C_update
          (\<lambda>_. foldr (\<lambda>n arr. Arrays.update arr n 0) [0..<2]
                (seL4_Fault_C.words_C (tcbFault_C undefined)))
          (tcbFault_C undefined),
       tcbLookupFailure_C :=
         lookup_fault_C.words_C_update
          (\<lambda>_. foldr (\<lambda>n arr. Arrays.update arr n 0) [0..<2]
                (lookup_fault_C.words_C (tcbLookupFailure_C undefined)))
          (tcbLookupFailure_C undefined),
       tcbPriority_C := 0, tcbMCP_C := 0, tcbDomain_C := 0, tcbTimeSlice_C := 0,
       tcbFaultHandler_C := 0, tcbIPCBuffer_C := 0,
       tcbSchedNext_C := tcb_Ptr 0, tcbSchedPrev_C := tcb_Ptr 0,
       tcbEPNext_C := tcb_Ptr 0, tcbEPPrev_C := tcb_Ptr 0,
       tcbBoundNotification_C := ntfn_Ptr 0\<rparr>"
  have fbtcb: "from_bytes (replicate (size_of TYPE(tcb_C)) 0) = ?tcb"
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps tcb_C_tag_def)
    apply (simp add: ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td align_of_def padup_def
      final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def)(* takes ages *)
    apply (simp add: update_ti_adjust_ti update_ti_t_machine_word_0s
      typ_info_simps thread_state_C_tag_def seL4_Fault_C_tag_def
      lookup_fault_C_tag_def update_ti_t_ptr_0s arch_tcb_C_tag_def
      ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td
      ti_typ_combine_empty_ti ti_typ_combine_td
      align_of_def padup_def user_fpu_state_C_tag_def user_context_C_tag_def
      final_pad_def size_td_lt_ti_typ_pad_combine Let_def size_of_def
      align_td_array' size_td_array)
    apply (simp add: update_ti_t_array_rep_word0  update_ti_t_array_rep_byte0)
    done

  have tcb_rel:
    "ctcb_relation makeObject ?new_tcb"
    unfolding ctcb_relation_def makeObject_tcb heap_updates_defs initContext_registers_def
    apply (simp add: fbtcb minBound_word)
    apply (intro conjI)
        apply (simp add: cthread_state_relation_def thread_state_lift_def
                         eval_nat_numeral ThreadState_Inactive_def)
       apply (clarsimp simp: ccontext_relation_def newContext_def2 carch_tcb_relation_def
                             newArchTCB_def cregs_relation_def atcbContextGet_def fpu_relation_def)
       apply (case_tac r; simp add: C_register_defs index_foldr_update
                                    atcbContext_def newArchTCB_def newContext_def
                                    initContext_def selCS3_eq selDS3_eq)
       apply (clarsimp simp: fpu_relation_def)
      apply (simp add: thread_state_lift_def index_foldr_update atcbContextGet_def)
     apply (simp add: Kernel_Config.timeSlice_def)
    apply (simp add: cfault_rel_def seL4_Fault_lift_def seL4_Fault_get_tag_def Let_def
                     lookup_fault_lift_def lookup_fault_get_tag_def lookup_fault_invalid_root_def
                     index_foldr_update seL4_Fault_NullFault_def option_to_ptr_def option_to_0_def
              split: if_split)+
    done

  have pks: "ks (ctcb_ptr_to_tcb_ptr p) = None"
    by (rule pspace_no_overlap_base' [OF pal pno al, simplified])

  have ep1 [simplified]: "\<And>p' list. map_to_eps (ksPSpace ?sp) p' = Some (Structures_H.endpoint.RecvEP list)
       \<Longrightarrow> ctcb_ptr_to_tcb_ptr p \<notin> set list"
    using symref pks pal pds
    apply -
    apply (frule map_to_ko_atI)
      apply simp
     apply simp
    apply (drule (1) sym_refs_ko_atD')
    apply clarsimp
    apply (drule (1) bspec)
    apply (simp add: ko_wp_at'_def)
    done

  have ep2 [simplified]: "\<And>p' list. map_to_eps (ksPSpace ?sp) p' = Some (Structures_H.endpoint.SendEP list)
       \<Longrightarrow> ctcb_ptr_to_tcb_ptr p \<notin> set list"
    using symref pks pal pds
    apply -
    apply (frule map_to_ko_atI)
      apply simp
     apply simp
    apply (drule (1) sym_refs_ko_atD')
    apply clarsimp
    apply (drule (1) bspec)
    apply (simp add: ko_wp_at'_def)
    done

  have ep3 [simplified]: "\<And>p' list boundTCB. map_to_ntfns (ksPSpace ?sp) p' = Some (Structures_H.notification.NTFN (Structures_H.ntfn.WaitingNtfn list) boundTCB)
       \<Longrightarrow> ctcb_ptr_to_tcb_ptr p \<notin> set list"
    using symref pks pal pds
    apply -
    apply (frule map_to_ko_atI)
      apply simp
     apply simp
    apply (drule (1) sym_refs_ko_atD')
    apply clarsimp
    apply (drule_tac x="(ctcb_ptr_to_tcb_ptr p, NTFNSignal)" in bspec, simp)
    apply (simp add: ko_wp_at'_def)
    done

  have pks': "ksPSpace \<sigma> (ctcb_ptr_to_tcb_ptr p) = None" using pks kssub
    apply -
    apply (erule contrapos_pp)
    apply (fastforce simp: dom_def)
    done

  hence kstcb: "\<And>qdom prio. ctcb_ptr_to_tcb_ptr p \<notin> set (ksReadyQueues \<sigma> (qdom, prio))" using vq
    apply (clarsimp simp add: valid_queues_def valid_queues_no_bitmap_def)
    apply (drule_tac x = qdom in spec)
    apply (drule_tac x = prio in spec)
    apply clarsimp
    apply (drule (1) bspec)
    apply (simp add: obj_at'_def)
    done

  have ball_subsetE:
    "\<And>P S R. \<lbrakk> \<forall>x \<in> S. P x; R \<subseteq> S \<rbrakk> \<Longrightarrow> \<forall>x \<in> R. P x"
    by blast

  have domain_kdr:
    "-domain \<subseteq> kernel_data_refs"
    using rfsr unfolding rf_sr_def cstate_relation_def Let_def by simp

  have htd_safe:
    "htd_safe domain (hrs_htd (t_hrs_' (globals x)))
        \<Longrightarrow> htd_safe domain (hrs_htd (t_hrs_' ?gs))"
    using kdr
    apply (simp add: hrs_htd_update heap_updates_def)
    apply (intro ptr_retyps_htd_safe_neg[OF _ _ domain_kdr], simp_all)
     apply (erule disjoint_subset[rotated])
     apply (simp add: ctcb_ptr_to_tcb_ptr_def size_of_def)
     apply (rule intvl_sub_offset[where k="ptr_val p - ctcb_offset" and x="ctcb_offset", simplified])
     apply (simp add: ctcb_offset_defs objBits_simps')
    apply (erule disjoint_subset[rotated])
    apply (rule intvl_start_le)
    apply (simp add: size_of_def objBits_simps')
    done

  have zro:
    "zero_ranges_are_zero (gsUntypedZeroRanges \<sigma>) (t_hrs_' (globals x))"
    using rfsr
    by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)

  have h_t_valid_p:
    "h_t_valid (hrs_htd (t_hrs_' ?gs)) c_guard p"
    using fun_cong[OF cl_tcb, where x=p]
    by (clarsimp dest!: h_t_valid_clift)

  have zro':
    "zero_ranges_are_zero (gsUntypedZeroRanges \<sigma>) (t_hrs_' ?gs)"
    using zro h_t_valid_p rzo al
    apply clarsimp
    apply (simp add: heap_updates_def hrs_htd_update typ_heap_simps')
    apply (intro zero_ranges_ptr_retyps, simp_all)
     apply (erule caps_overlap_reserved'_subseteq)
     apply (rule order_trans, rule tcb_ptr_to_ctcb_ptr_in_range')
      apply (simp add: objBits_simps kotcb_def)
     apply (simp add: objBits_simps kotcb_def)
    apply (erule caps_overlap_reserved'_subseteq)
    apply (rule intvl_start_le)
    apply (simp add: cte_C_size kotcb_def objBits_simps')
    done

  note al' = al[simplified objBits_simps kotcb_def, simplified]

  have p_nkr: "ptr_span p \<inter> kernel_data_refs = {}"
    apply (rule disjoint_subset[OF _ kdr])
    using ptr_span_ctcb_subset[OF al']
    apply (simp add: upto_intvl_eq[OF al'])
    done

  note ht_rest = clift_eq_h_t_valid_eq[OF cl_rest, simplified]

  note irq = h_t_valid_eq_array_valid[where p=intStateIRQNode_array_Ptr]
    h_t_array_valid_ptr_retyps_gen[where n=1, simplified, OF refl empty_smaller(1)]
    h_t_array_valid_ptr_retyps_gen[where p="Ptr x" for x, simplified, OF refl empty_smaller(2)]

  from rfsr have "cpspace_relation ks (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)
  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>))  (t_hrs_' ?gs)"
    unfolding cpspace_relation_def
    apply -
    apply (simp add: cl_cte [simplified] cl_tcb [simplified] cl_rest [simplified] tag_disj_via_td_name
                     ht_rest)
    apply (simp add: rl kotcb_def projectKOs rl_tcb rl_cte)
    apply (elim conjE)
    apply (intro conjI)
     \<comment> \<open>cte\<close>
     apply (erule cmap_relation_retype2)
     apply (simp add:ccte_relation_nullCap nullMDBNode_def nullPointer_def)
    \<comment> \<open>tcb\<close>
     apply (erule cmap_relation_updI2 [where dest = "ctcb_ptr_to_tcb_ptr p" and f = "tcb_ptr_to_ctcb_ptr", simplified])
     apply (rule map_comp_simps)
     apply (rule pks)
     apply (rule tcb_rel[simplified FLAGS_default_eq, simplified])
    \<comment> \<open>ep\<close>
     apply (erule iffD2 [OF cmap_relation_cong, OF refl refl, rotated -1])
     apply (simp add: cendpoint_relation_def Let_def)
     apply (subst endpoint.case_cong)
       apply (rule refl)
      apply (simp add: tcb_queue_update_other' ep1)
     apply (simp add: tcb_queue_update_other' del: tcb_queue_relation'_empty)
    apply (simp add: tcb_queue_update_other' ep2)
   apply clarsimp
  \<comment> \<open>ntfn\<close>
   apply (erule iffD2 [OF cmap_relation_cong, OF refl refl, rotated -1])
   apply (simp add: cnotification_relation_def Let_def)
     apply (subst ntfn.case_cong)
      apply (rule refl)
     apply (simp add: tcb_queue_update_other' del: tcb_queue_relation'_empty)
    apply (simp add: tcb_queue_update_other' del: tcb_queue_relation'_empty)
   apply (case_tac a, simp add: tcb_queue_update_other' ep3)
  apply (clarsimp simp: typ_heap_simps)
  done

  moreover have "cte_array_relation \<sigma> ?gs
    \<and> tcb_cte_array_relation ?s ?gs"
    using rfsr
    apply (clarsimp simp: heap_updates_def
                          rf_sr_def cstate_relation_def Let_def
                          hrs_htd_update map_comp_update
                          kotcb_def projectKO_opt_tcb)
    apply (intro cvariable_array_ptr_upd conjI
                 cvariable_array_ptr_retyps[OF refl, where n=1, simplified],
           simp_all add: empty_smaller[simplified])
    apply (simp add: ptr_retyps_gen_def)
    apply (rule ptr_retyp_h_t_valid[where g=c_guard, OF arr_guard,
        THEN h_t_array_valid, simplified])
    done

  ultimately show ?thesis
    using rfsr zro'
    apply (simp add: rf_sr_def cstate_relation_def Let_def h_t_valid_clift_Some_iff
                     tag_disj_via_td_name carch_state_relation_def
                     cmachine_state_relation_def irq)
    apply (simp add: cl_cte [simplified] cl_tcb [simplified] cl_rest [simplified] tag_disj_via_td_name)
    apply (clarsimp simp: cready_queues_relation_def Let_def
                          htd_safe[simplified] kernel_data_refs_domain_eq_rotate)
    apply (simp add: heap_updates_def kstcb tcb_queue_update_other' hrs_htd_update
                     ptr_retyp_to_array[simplified] irq[simplified])
    apply (match premises in H: \<open>fpu_null_state_relation _\<close> \<Rightarrow>
             \<open>match premises in _[thin]: _ (multi) \<Rightarrow> \<open>insert H\<close>\<close>)
    apply (simp add: fpu_null_state_heap_update_field p_nkr size_td_array
                     fpu_null_state_retyp_disjoint
                     disjoint_subset[OF _ kdr] disjoint_subset[OF _ p_nkr]
                     intvl_start_le cte_C_size tcbBlockSizeBits_def)
    done
qed

lemma cnc_foldl_foldr:
  defines "ko \<equiv> (KOTCB makeObject)"
  shows "foldl (\<lambda>v addr. v(addr \<mapsto> ko)) mp
  (map (\<lambda>n. ptr + (of_nat n << tcbBlockSizeBits)) [0..< n]) =
  foldr (\<lambda>addr. data_map_insert addr ko) (new_cap_addrs n ptr ko) mp"
  by (simp add: foldr_upd_app_if foldl_conv_foldr
                new_cap_addrs_def objBits_simps ko_def power_minus_is_div
          cong: foldr_cong)

lemma objBitsKO_gt_1:
  "(1 :: machine_word) < 2 ^ objBitsKO ko"
  by (simp add: objBits_simps' archObjSize_def bit_simps
         split: kernel_object.splits arch_kernel_object.splits)

lemma ps_clear_subset:
  assumes pd: "ps_clear x (objBitsKO ko) (s' \<lparr>ksPSpace := (\<lambda>x. if x \<in> as then Some (f x) else ksPSpace s' x) \<rparr>)"
  and    sub: "as' \<subseteq> as"
  and     al: "is_aligned x (objBitsKO ko)"
  shows  "ps_clear x (objBitsKO ko) (s' \<lparr>ksPSpace := (\<lambda>x. if x \<in> as' then Some (f x) else ksPSpace s' x) \<rparr>)"
  using al pd sub
  apply -
  apply (simp add: ps_clear_def3 [OF al objBitsKO_gt_0] dom_if_Some)
  apply (erule disjoint_subset2 [rotated])
  apply fastforce
  done

lemma pspace_distinct_subset:
  assumes pd: "pspace_distinct' (s' \<lparr>ksPSpace := (\<lambda>x. if x \<in> as then Some (f x) else ksPSpace s' x) \<rparr>)"
  and   pal: "pspace_aligned' (s' \<lparr>ksPSpace := (\<lambda>x. if x \<in> as then Some (f x) else ksPSpace s' x) \<rparr>)"
  and    sub: "as' \<subseteq> as"
  and  doms: "as \<inter> dom (ksPSpace s') = {}"
  shows  "pspace_distinct' (s' \<lparr>ksPSpace := (\<lambda>x. if x \<in> as' then Some (f x) else ksPSpace s' x) \<rparr>)"
  using pd sub doms pal
  unfolding pspace_distinct'_def pspace_aligned'_def
  apply -
  apply (rule ballI)
  apply (simp add: pspace_distinct'_def dom_if_Some)
  apply (drule_tac x = x in bspec)
   apply fastforce
  apply (drule_tac x = x in bspec)
   apply fastforce
  apply (erule disjE)
   apply (frule (1) subsetD)
   apply simp
   apply (erule (2) ps_clear_subset)
  apply (subgoal_tac "x \<notin> as")
   apply (frule (1) contra_subsetD)
   apply simp
   apply (erule (2) ps_clear_subset)
  apply fastforce
  done

lemma pspace_aligned_subset:
  assumes pal: "pspace_aligned' (s' \<lparr>ksPSpace := (\<lambda>x. if x \<in> as then Some (f x) else ksPSpace s' x) \<rparr>)"
  and     sub: "as' \<subseteq> as"
  and    doms: "as \<inter> dom (ksPSpace s') = {}"
  shows  "pspace_aligned' (s' \<lparr>ksPSpace := (\<lambda>x. if x \<in> as' then Some (f x) else ksPSpace s' x) \<rparr>)"
  using pal sub doms unfolding pspace_aligned'_def
  apply -
  apply (rule ballI)
  apply (simp add: dom_if_Some)
  apply (drule_tac x = x in bspec)
   apply fastforce
  apply (erule disjE)
   apply simp
   apply (frule (1) subsetD)
   apply simp
  apply (subgoal_tac "x \<notin> as")
   apply (frule (1) contra_subsetD)
   apply simp
  apply fastforce
  done


lemma cslift_empty_mem_update:
  fixes x :: cstate and sz and ptr
  defines "x' \<equiv> x\<lparr>globals := globals x
                       \<lparr>t_hrs_' := hrs_mem_update (heap_update_list ptr (replicate sz 0)) (t_hrs_' (globals x))\<rparr>\<rparr>"
  assumes empty: "region_is_typeless ptr sz x"
  shows "cslift x' = clift (fst (t_hrs_' (globals x)), snd (t_hrs_' (globals x)))"
  using empty
  apply -
  apply (unfold region_is_typeless_def)
  apply (rule ext)
  apply (simp only: lift_t_if hrs_mem_update_def split_def x'_def)
  apply (simp add: lift_t_if hrs_mem_update_def split_def)
  apply (clarsimp simp: h_val_def split: if_split)
  apply (subst heap_list_update_disjoint_same)
   apply simp
   apply (rule disjointI)
   apply clarsimp
   apply (drule (1) bspec)
   apply (frule (1) h_t_valid_not_empty)
   apply simp
  apply simp
  done

lemma cslift_bytes_mem_update:
  fixes x :: cstate and sz and ptr
  defines "x' \<equiv> x\<lparr>globals := globals x
                       \<lparr>t_hrs_' := hrs_mem_update (heap_update_list ptr (replicate sz 0)) (t_hrs_' (globals x))\<rparr>\<rparr>"
  assumes bytes: "region_is_bytes ptr sz x"
  assumes not_byte: "typ_uinfo_t TYPE ('a) \<noteq> typ_uinfo_t TYPE (word8)"
  shows "(cslift x' :: ('a :: mem_type) ptr \<Rightarrow> _)
     = clift (fst (t_hrs_' (globals x)), snd (t_hrs_' (globals x)))"
  using bytes
  apply (unfold region_is_bytes'_def)
  apply (rule ext)
  apply (simp only: lift_t_if hrs_mem_update_def split_def x'_def)
  apply (simp add: lift_t_if hrs_mem_update_def split_def)
  apply (clarsimp simp: h_val_def split: if_split)
  apply (subst heap_list_update_disjoint_same)
   apply simp
   apply (rule disjointI)
   apply clarsimp
   apply (drule (1) bspec)
   apply (frule (1) h_t_valid_intvl_htd_contains_uinfo_t)
   apply (clarsimp simp: hrs_htd_def not_byte)
  apply simp
  done

lemma heap_list_eq_replicate_eq_eq:
  "(heap_list hp n ptr = replicate n v)
    = (\<forall>p \<in> {ptr ..+ n}. hp p = v)"
  by (induct n arbitrary: ptr, simp_all add: intvl_Suc_right)

lemma heap_update_list_replicate_eq:
  "(heap_update_list x (replicate n v) hp y)
    = (if y \<in> {x ..+ n} then v else hp y)"
  apply (induct n arbitrary: x hp, simp_all add: intvl_Suc_right)
  apply (simp split: if_split)
  done

lemma zero_ranges_are_zero_update_zero[simp]:
  "zero_ranges_are_zero rs hrs
    \<Longrightarrow> zero_ranges_are_zero rs (hrs_mem_update (heap_update_list ptr (replicate n 0)) hrs)"
  supply if_cong[cong]
  apply (clarsimp simp: zero_ranges_are_zero_def hrs_mem_update)
  apply (drule(1) bspec)
  apply (clarsimp simp: heap_list_eq_replicate_eq_eq heap_update_list_replicate_eq)
  done

lemma rf_sr_rep0:
  assumes sr: "(\<sigma>, x) \<in> rf_sr"
  assumes empty: "region_is_bytes ptr sz x"
  shows "(\<sigma>, globals_update (t_hrs_'_update (hrs_mem_update (heap_update_list ptr (replicate sz 0)))) x) \<in> rf_sr"
  using sr
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def cpspace_relation_def
                     carch_state_relation_def fpu_null_state_relation_def
                     cmachine_state_relation_def hrs_mem_update
                     cslift_bytes_mem_update[OF empty, simplified] cte_C_size)

(* FIXME: generalise *)
lemma ccorres_already_have_rrel:
  "\<lbrakk> ccorres dc xfdc P P' hs a c; \<forall>s. \<Gamma> \<turnstile>\<^bsub>/UNIV\<^esub> {s} c {t. xf t = xf s} \<rbrakk>
  \<Longrightarrow>
  ccorres r xf P (P' \<inter> {s. r v (xf s)}) hs (a >>= (\<lambda>_.  return v)) c"
  apply (rule ccorres_return_into_rel)
  apply (rule ccorresI')
  apply (erule (2) ccorresE)
     apply simp
    apply assumption+
  apply (clarsimp elim!: rev_bexI)
  apply (simp add: unif_rrel_def)
  apply (drule_tac x = s' in spec)
  apply (drule (1) exec_handlers_use_hoare_nothrow)
   apply simp
  apply fastforce
  done

lemma mapM_x_storeWord:
  assumes al: "is_aligned ptr 3"
  shows "mapM_x (\<lambda>x. storeWord (ptr + of_nat x * 8) 0) [0..<n]
  = modify (underlying_memory_update (\<lambda>m x. if x \<in> {ptr..+ n * 8} then 0 else m x))"
proof (induct n)
  case 0
  thus ?case
    apply (rule ext)
    apply (simp add: mapM_x_mapM mapM_def sequence_def
      modify_def get_def put_def bind_def return_def)
    done
next
  case (Suc n')

  have funs_eq:
    "\<And>m x. (if x \<in> {ptr..+8 + n' * 8} then 0 else (m x :: word8)) =
           ((\<lambda>xa. if xa \<in> {ptr..+n' * 8} then 0 else m xa)
           (ptr + of_nat n' * 8 := word_rsplit (0 :: machine_word) ! 7,
            ptr + of_nat n' * 8 + 1 := word_rsplit (0 :: machine_word) ! 6,
            ptr + of_nat n' * 8 + 2 := word_rsplit (0 :: machine_word) ! 5,
            ptr + of_nat n' * 8 + 3 := word_rsplit (0 :: machine_word) ! 4,
            ptr + of_nat n' * 8 + 4:= word_rsplit (0 :: machine_word) ! 3,
            ptr + of_nat n' * 8 + 5 := word_rsplit (0 :: machine_word) ! 2,
            ptr + of_nat n' * 8 + 6 := word_rsplit (0 :: machine_word) ! Suc 0,
            ptr + of_nat n' * 8 + 7 := word_rsplit (0 :: machine_word) ! 0)) x"
  proof -
    fix m x

    have xin': "\<And>x. (x < 8 + n' * 8) = (x < n' * 8 \<or> x = n' * 8
                     \<or> x = (n' * 8) + 1 \<or> x = (n' * 8) + 2 \<or> x = (n' * 8) + 3
                      \<or> x = (n' * 8) + 4 \<or> x = (n' * 8) + 5 \<or> x = (n' * 8) + 6
                      \<or> x = (n' * 8) + 7)"
      by (safe, simp_all)

    have xin: "x \<in> {ptr..+8 + n' * 8} = (x \<in> {ptr..+n' * 8} \<or> x = ptr + of_nat n' * 8 \<or>
      x = ptr + of_nat n' * 8 + 1 \<or> x = ptr + of_nat n' * 8 + 2 \<or> x = ptr + of_nat n' * 8 + 3
      \<or> x = ptr + of_nat n' * 8 + 4 \<or> x = ptr + of_nat n' * 8 + 5 \<or> x = ptr + of_nat n' * 8 + 6
      \<or> x = ptr + of_nat n' * 8 + 7)"
      by (simp add: intvl_def xin' conj_disj_distribL
                    ex_disj_distrib field_simps)

    show "?thesis m x"
      apply (simp add: xin word_rsplit_0 word_bits_def cong: if_cong)
      apply (simp split: if_split)
      done
  qed

  from al have "is_aligned (ptr + of_nat n' * 8) 3"
    apply (rule aligned_add_aligned)
    apply (rule is_aligned_mult_triv2 [where n = 3, simplified])
    apply (simp add: word_bits_conv)+
    done

  thus ?case
    apply (simp add: mapM_x_append bind_assoc Suc.hyps mapM_x_singleton)
    apply (simp add: storeWord_def assert_def is_aligned_mask modify_modify comp_def)
    apply (simp only: funs_eq upto0_7_def)
    apply (rule arg_cong[where f=modify])
    apply (rule arg_cong[where f=underlying_memory_update])
    apply (simp add: fold_def del: fun_upd_apply)
    done
qed

lemma mapM_x_storeWord_step:
  assumes al: "is_aligned ptr sz"
  and    sz2: "3 \<le> sz"
  and     sz: "sz < word_bits"
  shows "mapM_x (\<lambda>p. storeWord p 0) [ptr , ptr + 8 .e. ptr + 2 ^ sz - 1] =
  modify (underlying_memory_update (\<lambda>m x. if x \<in> {ptr..+2 ^ (sz - 3) * 8} then 0 else m x))"
  using al sz
  apply (simp only: upto_enum_step_def field_simps cong: if_cong)
  apply (subst if_not_P)
   apply (subst not_less)
   apply (erule is_aligned_no_overflow)
   apply (simp add: mapM_x_map upto_enum_word del: upt.simps)
   apply (subst div_power_helper_64 [OF sz2, simplified])
    apply assumption
   apply (simp add: word_bits_def unat_minus_one del: upt.simps)
   apply (subst mapM_x_storeWord)
   apply (erule is_aligned_weaken [OF _ sz2])
   apply (simp add: field_simps)
   done


lemma pspace_aligned_to_C_user_data:
  fixes v :: "user_data"
  assumes pal: "pspace_aligned' s"
  and    cmap: "cpspace_user_data_relation (ksPSpace s) (underlying_memory (ksMachineState s)) (t_hrs_' (globals x))"
  shows  "\<forall>x\<in>dom (cslift x :: user_data_C typ_heap). is_aligned (ptr_val x) (objBitsKO KOUserData)"
  (is "\<forall>x\<in>dom ?CS. is_aligned (ptr_val x) (objBitsKO KOUserData)")
proof
  fix z
  assume "z \<in> dom ?CS"
  hence "z \<in> Ptr ` dom (map_to_user_data (ksPSpace s))" using cmap
    by (simp add: cmap_relation_def dom_heap_to_user_data)
  hence pvz: "ptr_val z \<in> dom (map_to_user_data (ksPSpace s))"
    by clarsimp
  hence "projectKO_opt (the (ksPSpace s (ptr_val z))) = Some UserData"
    apply -
    apply (frule map_comp_subset_domD)
    apply (clarsimp simp: dom_def)+
    done
  moreover have pvz: "ptr_val z \<in> dom (ksPSpace s)" using pvz
    by (rule map_comp_subset_domD)
  ultimately show "is_aligned (ptr_val z) (objBitsKO KOUserData)" using pal
    unfolding pspace_aligned'_def
    apply -
    apply (drule (1) bspec)
    apply (simp add: projectKOs)
    done
qed

lemma range_cover_bound_weak:
  "\<lbrakk> n \<noteq> 0; range_cover ptr sz us n \<rbrakk> \<Longrightarrow>
    ptr + (of_nat n * 2 ^ us - 1) \<le> (ptr && ~~ mask sz) + 2 ^ sz - 1"
  apply (frule range_cover_cell_subset[where x = "of_nat (n - 1)"])
   apply (simp add:range_cover_not_zero)
  apply (frule range_cover_subset_not_empty[rotated,where x = "of_nat (n - 1)"])
   apply (simp add:range_cover_not_zero)
  apply (clarsimp simp: field_simps)
  done

lemma pspace_no_overlap_underlying_zero:
  "pspace_no_overlap' ptr sz \<sigma>
    \<Longrightarrow> valid_machine_state' \<sigma>
    \<Longrightarrow> x \<in> {ptr .. (ptr && ~~ mask sz) + 2 ^ sz - 1}
    \<Longrightarrow> underlying_memory (ksMachineState \<sigma>) x = 0"
  using mask_in_range[where ptr'=x and bits=pageBits and ptr="x && ~~ mask pageBits"]
  apply (clarsimp simp: valid_machine_state'_def)
  apply (drule_tac x=x in spec, clarsimp simp: pointerInUserData_def)
  apply (clarsimp simp: typ_at'_def ko_wp_at'_def koTypeOf_eq_UserDataT)
  apply (case_tac "pointerInDeviceData x \<sigma>")
   apply (clarsimp simp: pointerInDeviceData_def
                         ko_wp_at'_def obj_at'_def projectKOs
                  dest!: device_data_at_ko)
   apply (drule(1) pspace_no_overlapD')
   apply (drule_tac x=x in eqset_imp_iff)
   apply (simp add: objBits_simps)
  apply clarsimp
  apply (drule(1) pspace_no_overlapD')
  apply (drule_tac x=x in eqset_imp_iff, simp)
  apply (simp add: objBits_simps)
  done

lemma range_cover_nca_neg: "\<And>x p (off :: 9 word).
  \<lbrakk>(x::machine_word) < 8; {p..+2 ^pageBits } \<inter> {ptr..ptr + (of_nat n * 2 ^ (gbits + pageBits) - 1)} = {};
    range_cover ptr sz (gbits + pageBits) n\<rbrakk>
  \<Longrightarrow> p + ucast off * 8 + x \<notin> {ptr..+n * 2 ^ (gbits + pageBits)}"
  apply (case_tac "n = 0")
   apply simp
  apply (subst range_cover_intvl,simp)
   apply simp
  apply (subgoal_tac "p + ucast off * 8 + x \<in>  {p..+2 ^ pageBits}")
   apply blast
  apply (clarsimp simp: intvl_def)
  apply (rule_tac x = "unat off * 8 + unat x" in exI)
  apply (simp add: ucast_nat_def)
  apply (rule nat_add_offset_less [where n = 3, simplified])
    apply (simp add: word_less_nat_alt)
   apply (rule unat_lt2p)
  apply (simp add: pageBits_def objBits_simps)
  done

lemma heap_to_device_data_disj_mdf:
  assumes rc: "range_cover ptr sz (gbits + pageBits) n"
  and ko_at: "ksPSpace \<sigma> a = Some obj"
  and obj_size: "objBitsKO obj = pageBits"
  and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
  and pno: "pspace_no_overlap' ptr sz \<sigma>"
  and sz: "gbits + pageBits \<le> sz"
  and szb: "sz < word_bits"
  shows "(heap_to_device_data (ksPSpace \<sigma>)
          (\<lambda>x. if x \<in> {ptr..+n * 2 ^ (gbits + pageBits)} then 0 else underlying_memory (ksMachineState \<sigma>) x) a)
          = (heap_to_device_data (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) a)"
  proof -
  from sz have "3 \<le> sz" by (simp add: objBits_simps pageBits_def)

  hence sz2: "2 ^ (sz - 3) * 8 = (2 :: nat) ^ sz"
    apply (subgoal_tac "(8 :: nat) = 2 ^ 3")
    apply (erule ssubst)
    apply (subst power_add [symmetric])
    apply (rule arg_cong [where f = "\<lambda>n. 2 ^ n"])
    apply simp
    apply simp
    done
  have p2dist: "n * (2::nat) ^ (gbits + pageBits) = n * 2 ^ gbits * 2 ^ pageBits" (is "?lhs = ?rhs")
    by (simp add: monoid_mult_class.power_add)
  show ?thesis
    apply (simp add: heap_to_device_data_def)
    apply (case_tac "n = 0")
     apply simp
    apply (subst map_option_byte_to_word_heap)
     apply (erule range_cover_nca_neg[OF _ _ rc])
     using range_cover_intvl[OF rc]
     apply (clarsimp simp add: heap_to_user_data_def Let_def
       byte_to_word_heap_def[abs_def] map_comp_Some_iff projectKOs)
     apply (cut_tac pspace_no_overlapD' [OF ko_at pno])
     apply (subst (asm) upto_intvl_eq [symmetric])
      apply (rule pspace_alignedD' [OF ko_at pal])
     apply (simp add: obj_size p2dist)
     apply (drule_tac B' = "{ptr..ptr + (of_nat n * 2 ^ (gbits + pageBits) - 1)}" in disjoint_subset2[rotated])
      apply (clarsimp simp: p2dist )
      apply (rule range_cover_bound_weak)
       apply simp
      apply (rule rc)
     apply simp
    apply simp
   done
qed

lemma pageBitsForSize_mess_multi:
  "8 * (2::nat) ^ (pageBitsForSize sz - 3) = 2^(pageBitsForSize sz)"
  apply (subgoal_tac "(8 :: nat) = 2 ^ 3")
  apply (erule ssubst)
  apply (subst power_add [symmetric])
  apply (rule arg_cong [where f = "\<lambda>n. 2 ^ n"])
  apply (case_tac sz,(simp add: bit_simps)+)
  done

lemma createObjects_ccorres_user_data:
  defines "ko \<equiv> KOUserData"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> range_cover ptr sz (gbits + pageBits) n
  \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> valid_machine_state' \<sigma>
  \<and> ret_zero ptr (n * 2 ^ (gbits + pageBits)) \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> region_is_zero_bytes ptr (n * 2 ^ (gbits + pageBits)) x
  \<and> {ptr ..+ n * (2 ^ (gbits + pageBits))} \<inter> kernel_data_refs = {}
  \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace :=
               foldr (\<lambda>addr. data_map_insert addr KOUserData)
                  (new_cap_addrs (n * 2^gbits) ptr KOUserData) (ksPSpace \<sigma>)\<rparr>,
           x\<lparr>globals := globals x\<lparr>t_hrs_' :=
                      hrs_htd_update
                       (ptr_retyps_gen (n * 2 ^ gbits) (Ptr ptr :: user_data_C ptr) arr)
                       ((t_hrs_' (globals x)))\<rparr> \<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "Ptr ptr :: user_data_C ptr"

  note Kernel_C.user_data_C_size [simp del]

  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr" and al: "is_aligned ptr (gbits + pageBits)"
    and ptr0: "ptr \<noteq> 0"
    and sz: "gbits + pageBits \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and vms: "valid_machine_state' \<sigma>"
    and rzo: "ret_zero ptr (n * 2 ^ (gbits + pageBits)) \<sigma>"
    and empty: "region_is_bytes ptr (n * 2 ^ (gbits + pageBits)) x"
    and zero: "heap_list_is_zero (hrs_mem (t_hrs_' (globals x))) ptr (n * 2 ^ (gbits + pageBits))"
    and rc: "range_cover ptr sz (gbits + pageBits) n"
    and rc': "range_cover ptr sz (objBitsKO ko) (n * 2^ gbits)"
    and kdr: "{ptr..+n * 2 ^ (gbits + pageBits)} \<inter> kernel_data_refs = {}"
    by (auto simp: range_cover.aligned objBits_simps  ko_def
                   range_cover_rel[where sbit' = pageBits]
                   range_cover.sz[where 'a=machine_word_len, folded word_bits_def])

  hence al': "is_aligned ptr (objBitsKO ko)"
    by (clarsimp dest!: is_aligned_weaken range_cover.aligned)

  (* This is a hack *)
  have mko: "\<And>dev. makeObjectKO False (Inr object_type.SmallPageObject) = Some ko"
    by (simp add: makeObjectKO_def ko_def)

  from sz have "3 \<le> sz" by (simp add: objBits_simps pageBits_def ko_def)

  hence sz2: "2 ^ (sz - 3) * 8 = (2 :: nat) ^ sz"
    apply (subgoal_tac "(8 :: nat) = 2 ^ 3")
    apply (erule ssubst)
    apply (subst power_add [symmetric])
    apply (rule arg_cong [where f = "\<lambda>n. 2 ^ n"])
    apply simp
    apply simp
    done

  define big_0s where "big_0s \<equiv> (replicate (2^pageBits) 0) :: word8 list"

  have "length big_0s = 4096" unfolding big_0s_def
    by simp (simp add: bit_simps)

  hence i1: "\<And>off :: 9 word. index (user_data_C.words_C (from_bytes big_0s)) (unat off) = 0"
    apply (simp add: from_bytes_def)
    apply (simp add: typ_info_simps user_data_C_tag_def)
    apply (simp add: ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td align_of_def padup_def
      final_pad_def size_td_lt_ti_typ_pad_combine Let_def align_td_array' size_td_array size_of_def
      cong: if_cong)
    apply (simp add: update_ti_adjust_ti update_ti_t_machine_word_0s
      typ_info_simps update_ti_t_ptr_0s
      ti_typ_pad_combine_empty_ti ti_typ_pad_combine_td
      ti_typ_combine_empty_ti ti_typ_combine_td
      align_of_def padup_def
      final_pad_def size_td_lt_ti_typ_pad_combine Let_def
      align_td_array' size_td_array cong: if_cong)
    apply (subst update_ti_t_array_rep_word0)
     apply (unfold big_0s_def)[1]
     apply (rule arg_cong [where f = "\<lambda>x. replicate x 0"])
     apply (simp (no_asm) add: size_of_def pageBits_def)
    apply (subst index_foldr_update)
      apply (rule order_less_le_trans [OF unat_lt2p])
      apply simp
     apply simp
    apply simp
    done

  have p2dist: "n * (2::nat) ^ (gbits + pageBits) = n * 2 ^ gbits * 2 ^ pageBits" (is "?lhs = ?rhs")
    by (simp add:monoid_mult_class.power_add)

  have nca: "\<And>x p (off :: 9 word). \<lbrakk> p \<in> set (new_cap_addrs (n*2^gbits) ptr KOUserData); x < 8 \<rbrakk>
    \<Longrightarrow> p + ucast off * 8 + x \<in> {ptr..+ n * 2 ^ (gbits + pageBits) }"
    using sz
    apply (clarsimp simp: new_cap_addrs_def objBits_simps shiftl_t2n intvl_def)
    apply (rename_tac x off pa)
    apply (rule_tac x = "2 ^ pageBits * pa + unat off * 8 + unat x" in exI)
    apply (simp add: ucast_nat_def power_add)
    apply (subst mult.commute, subst add.assoc)
    apply (rule_tac y = "(pa + 1) * 2 ^ pageBits " in less_le_trans)
     apply (simp add:word_less_nat_alt)
    apply (rule_tac y="unat off * 8 + 8" in less_le_trans)
      apply simp
     apply (simp add:pageBits_def)
     apply (cut_tac x = off in unat_lt2p)
     apply simp
    apply (subst mult.assoc[symmetric])
    apply (rule mult_right_mono)
     apply simp+
    done

  have nca_neg: "\<And>x p (off :: 9 word).
    \<lbrakk>x < 4; {p..+2 ^ objBitsKO KOUserData } \<inter> {ptr..ptr + (of_nat n * 2 ^ (gbits + pageBits) - 1)} = {}\<rbrakk>
     \<Longrightarrow> p + ucast off * 8 + x \<notin> {ptr..+n * 2 ^ (gbits + pageBits)}"
    apply (case_tac "n = 0")
     apply simp
    apply (subst range_cover_intvl[OF rc])
     apply simp
    apply (subgoal_tac " p + ucast off * 8 + x \<in>  {p..+2 ^ objBitsKO KOUserData}")
     apply blast
    apply (clarsimp simp:intvl_def)
    apply (rule_tac x = "unat off * 8 + unat x" in exI)
    apply (simp add: ucast_nat_def)
    apply (rule nat_add_offset_less [where n = 3, simplified])
      apply (simp add: word_less_nat_alt)
     apply (rule unat_lt2p)
    apply (simp add: pageBits_def objBits_simps)
    done

  have zero_app: "\<And>x. x \<in> {ptr..+ n * 2 ^ (gbits + pageBits) }
    \<Longrightarrow> underlying_memory (ksMachineState \<sigma>) x = 0"
    apply (cases "n = 0")
     apply simp
    apply (rule pspace_no_overlap_underlying_zero[OF pno vms])
    apply (erule subsetD[rotated])
    apply (cases "n = 0")
     apply simp
    apply (subst range_cover_intvl[OF rc], simp)
    apply (rule order_trans[rotated], erule range_cover_subset'[OF rc])
    apply (simp add: field_simps)
    done

  have cud: "\<And>p. p \<in> set (new_cap_addrs (n * 2^ gbits) ptr KOUserData) \<Longrightarrow>
              cuser_user_data_relation
                (byte_to_word_heap
                  (underlying_memory (ksMachineState \<sigma>)) p)
                (from_bytes big_0s)"
    unfolding cuser_user_data_relation_def
    apply -
    apply (rule allI)
    apply (subst i1)
    apply (simp add: byte_to_word_heap_def Let_def
                     zero_app nca nca [where x3 = 0, simplified])
    apply (simp add: word_rcat_bl)
    done

  note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
      Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  have cud2: "\<And>xa v y.
              \<lbrakk> heap_to_user_data
                     (\<lambda>x. if x \<in> set (new_cap_addrs (n*2^gbits) ptr KOUserData)
                           then Some KOUserData else ksPSpace \<sigma> x)
                     (underlying_memory (ksMachineState \<sigma>)) xa =
              Some v; xa \<notin> set (new_cap_addrs (n*2^gbits) ptr KOUserData);
              heap_to_user_data (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) xa = Some y \<rbrakk> \<Longrightarrow> y = v"
    using range_cover_intvl[OF rc]
    by (clarsimp simp add: heap_to_user_data_def Let_def sz2
      byte_to_word_heap_def[abs_def] map_comp_Some_iff projectKOs)

  have relrl: "cmap_relation (heap_to_user_data (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)))
                             (cslift x) Ptr cuser_user_data_relation
    \<Longrightarrow> cmap_relation
        (heap_to_user_data
          (\<lambda>x. if x \<in> set (new_cap_addrs (n * 2 ^ gbits) ptr KOUserData)
               then Some KOUserData else ksPSpace \<sigma> x)
          (underlying_memory (ksMachineState \<sigma>)))
        (\<lambda>y. if y \<in> Ptr ` set (new_cap_addrs (n*2^gbits) ptr KOUserData)
             then Some
                   (from_bytes (replicate (2 ^ pageBits) 0))
             else cslift x y)
        Ptr cuser_user_data_relation"
    apply (rule cmap_relationI)
    apply (clarsimp simp: dom_heap_to_user_data cmap_relation_def dom_if image_Un
      projectKO_opt_retyp_same projectKOs)
    apply (case_tac "xa \<in> set (new_cap_addrs (n*2^gbits) ptr KOUserData)")
    apply (clarsimp simp: heap_to_user_data_def sz2)
    apply (erule cud [unfolded big_0s_def])
    apply (subgoal_tac "(Ptr xa :: user_data_C ptr) \<notin> Ptr ` set (new_cap_addrs (n*2^gbits) ptr KOUserData)")
    apply simp
    apply (erule (1) cmap_relationE2)
    apply (drule (1) cud2)
    apply simp
   apply simp
   apply clarsimp
   done

  (* /obj specific *)

  (* s/obj/obj'/ *)

  have szo: "size_of TYPE(user_data_C) = 2 ^ objBitsKO ko" by (simp add: size_of_def objBits_simps archObjSize_def ko_def pageBits_def)
  have szo': "n * 2 ^ (gbits + pageBits) = n * 2 ^ gbits * size_of TYPE(user_data_C)" using sz
    apply (subst szo)
    apply (clarsimp simp: power_add[symmetric] objBits_simps ko_def)
    done

  have rb': "region_is_bytes ptr (n * 2 ^ gbits * 2 ^ objBitsKO ko) x"
    using empty
    by (simp add: mult.commute mult.left_commute power_add objBits_simps ko_def)

  note rl' = cslift_ptr_retyp_other_inst[OF rb' rc' szo' szo, simplified]

  (* rest is generic *)

  note rl = projectKO_opt_retyp_other [OF rc' pal pno,unfolded ko_def]
  note cterl = retype_ctes_helper[OF pal pdst pno al' range_cover.sz(2)[OF rc'] range_cover.sz(1)[OF rc', folded word_bits_def] mko rc']
  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]

  have guard:
    "\<forall>t<n * 2 ^ gbits. c_guard (CTypesDefs.ptr_add ?ptr (of_nat t))"
    apply (rule retype_guard_helper[OF rc' ptr0 szo,where m = 3])
    apply (clarsimp simp:align_of_def objBits_simps ko_def pageBits_def)+
    done

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)

  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>)) ?ks'"
    unfolding cpspace_relation_def
    using empty rc' szo
    apply -
    supply image_cong_simp [cong del]
    apply (clarsimp simp: rl' tag_disj_via_td_name cte_C_size ht_rl
                          foldr_upd_app_if [folded data_map_insert_def])
    apply (simp add: rl ko_def projectKOs p2dist
                     cterl[unfolded ko_def])
    apply (subst clift_ptr_retyps_gen_prev_memset_same[OF guard])
         apply (simp add: pageBits_def objBits_simps)
        apply simp
       apply (simp add: pageBits_def objBits_simps)
      apply (cut_tac range_cover.strong_times_64[OF rc], simp_all)[1]
      apply (simp add: p2dist objBits_simps)
     apply (cut_tac zero)
     apply (simp add: pageBits_def power_add field_simps)
    apply (simp add: objBits_simps ptr_add_to_new_cap_addrs[OF szo] ko_def
               cong: if_cong)
    apply (simp add: p2dist[symmetric])
    apply (erule relrl[simplified])
    done

  thus  ?thesis using rf empty kdr rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name )
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (simp add: tag_disj_via_td_name rl' tcb_C_size h_t_valid_clift_Some_iff)
    apply (clarsimp simp: hrs_htd_update szo'[symmetric])
    apply (simp add:szo hrs_htd_def p2dist objBits_simps ko_def ptr_retyps_htd_safe_neg
                    kernel_data_refs_domain_eq_rotate
                    rl foldr_upd_app_if [folded data_map_insert_def]
                    projectKOs cvariable_array_ptr_retyps
                    zero_ranges_ptr_retyps)
    done
qed

lemma t_hrs_update_hrs_htd_id:
  "t_hrs_'_update id = id"
  "hrs_htd_update id = id"
  by (simp_all add: fun_eq_iff hrs_htd_update_def)

lemmas clift_array_assertionE
    = clift_array_assertion_imp[where p="Ptr q" and p'="Ptr q" for q,
        OF _ refl _ exI[where x=0], simplified]

lemma copyGlobalMappings_ccorres:
  "ccorres dc xfdc (page_map_l4_at' pm) (UNIV \<inter> {s. new_vspace_' s = Ptr pm}) []
           (copyGlobalMappings pm) (Call copyGlobalMappings_'proc)"
  apply (cinit lift: new_vspace_' simp:)
   apply csymbr
   apply (rule ccorres_pre_gets_x64KSSKIMPML4_ksArchState, rename_tac skimPM)
   apply (rule ccorres_rel_imp[where r=dc, simplified])
   apply (clarsimp simp: whileAnno_def objBits_simps archObjSize_def
                         getPML4Index_def bit_simps X64.pptrBase_def mask_def)
    apply csymbr
    apply (rule_tac F="\<lambda>n s. skimPM = x64KSSKIMPML4 (ksArchState s) \<and> page_map_l4_at' pm s"
                and i="0x1FF"
             in ccorres_mapM_x_while';
           clarsimp simp: word_bits_def)
    apply (rule ccorres_guard_imp2)
     apply (rule ccorres_pre_getObject_pml4e, rename_tac pml4e)
     apply (simp add: storePML4E_def)
     apply (rule_tac P="\<lambda>s. ko_at' pml4e (x64KSSKIMPML4 (ksArchState s) + 0xFF8) s
                             \<and> page_map_l4_at' pm s" and P'="\<lbrace>\<acute>i = 0x1FF\<rbrace>"
              in setObject_ccorres_helper)
       apply (rule conseqPre, vcg, clarsimp)
       apply (strengthen array_assertion_shrink_right[where n'=511 and n=512, simplified])
       apply (frule (1) page_map_l4_at'_array_assertion; clarsimp simp: bit_simps)
       apply (frule page_map_l4_pml4e_atI'[where x="0x1FF"]; simp add: bit_simps c_guard_abs_pml4e)
       apply (rule conjI, clarsimp simp: rf_sr_def cstate_relation_def Let_def)
       apply (clarsimp simp: rf_sr_x64KSSKIMPML4)
       apply (rule cmap_relationE1[OF rf_sr_cpml4e_relation], assumption,
              erule_tac ko=ko' in ko_at_projectKO_opt)
       apply (rule cmap_relationE1[OF rf_sr_cpml4e_relation], assumption,
              erule_tac ko=pml4e in ko_at_projectKO_opt)
       apply (clarsimp simp: typ_heap_simps' heap_access_Array_element)
       apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
       apply (clarsimp simp: typ_heap_simps update_pml4e_map_tos)
       apply (rule conjI)
        apply (clarsimp simp: cpspace_relation_def typ_heap_simps
                              update_pml4e_map_tos update_pml4e_map_to_pml4es
                              carray_map_relation_upd_triv)
        subgoal by (erule (2) cmap_relation_updI; simp)
       subgoal by (clarsimp simp: carch_state_relation_def cmachine_state_relation_def
                                  global_ioport_bitmap_heap_update_tag_disj_simps
                                  fpu_null_state_heap_update_tag_disj_simps)
      apply simp
     apply (simp add: objBits_simps archObjSize_def)
    apply clarsimp
   apply (rule conseqPre, vcg, clarsimp)
  by clarsimp

lemma getObjectSize_symb:
  "\<forall>s. \<Gamma> \<turnstile> {s. t_' s = object_type_from_H newType \<and> userObjSize_' s = sz} Call getObjectSize_'proc
  {s'. ret__unsigned_long_' s' = of_nat (getObjectSize newType (unat sz))}"
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: nAPIObjects_def Kernel_C_defs framesize_to_H_def)
  apply (case_tac newType)
   apply (simp_all add: object_type_from_H_def Kernel_C_defs
                        X86_SmallPage_def X86_LargePage_def X64_HugePage_def
                        APIType_capBits_def objBits_simps')
   apply (rename_tac apiobject_type)
   apply (case_tac apiobject_type)
   apply (simp_all add: object_type_from_H_def Kernel_C_defs
                        X86_SmallPage_def X86_LargePage_def X64_HugePage_def
                        APIType_capBits_def objBits_simps' bit_simps)
  apply unat_arith
  done

(* If we only change local variables on the C side, nothing need be done on the abstract side. *)
lemma ccorres_only_change_locals:
  "\<lbrakk> \<And>s. \<Gamma> \<turnstile> {s} C {t. globals s = globals t} \<rbrakk> \<Longrightarrow> ccorresG rf_sr \<Gamma> dc xfdc \<top> UNIV hs (return x) C"
  apply (rule ccorres_from_vcg)
  apply (clarsimp simp: return_def)
  apply (clarsimp simp: rf_sr_def)
  apply (rule hoare_complete)
  apply (clarsimp simp: HoarePartialDef.valid_def)
  apply (erule_tac x=x in meta_allE)
  apply (drule hoare_sound)
  apply (clarsimp simp: cvalid_def HoarePartialDef.valid_def)
  apply auto
  done

lemmas upt_enum_offset_trivial = upt_enum_offset_trivial[where 'a=64, folded word_bits_def]

lemma getObjectSize_max_size:
  "\<lbrakk> newType =  APIObjectType apiobject_type.Untyped \<longrightarrow> x < 64;
         newType =  APIObjectType apiobject_type.CapTableObject \<longrightarrow> x < 59 \<rbrakk> \<Longrightarrow> getObjectSize newType x < word_bits"
  apply (clarsimp simp only: getObjectSize_def apiGetObjectSize_def word_bits_def
                  split: X64_H.object_type.splits apiobject_type.splits)
  apply (clarsimp simp: tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def cteSizeBits_def
                        bit_simps)
  done

lemma getObjectSize_min_size:
  "\<lbrakk> newType =  APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> x;
     newType =  APIObjectType apiobject_type.CapTableObject \<longrightarrow> 2 \<le> x \<rbrakk> \<Longrightarrow>
    4 \<le> getObjectSize newType x"
  apply (clarsimp simp only: getObjectSize_def apiGetObjectSize_def word_bits_def
                  split: X64_H.object_type.splits apiobject_type.splits)
  apply (clarsimp simp: tcbBlockSizeBits_def epSizeBits_def ntfnSizeBits_def cteSizeBits_def
                        bit_simps untypedBits_defs)
  done

(*
 * Assuming "placeNewObject" doesn't fail, it is equivalent
 * to placing a number of objects into the PSpace.
 *)
lemma placeNewObject_eq:
  notes option.case_cong_weak [cong]
  shows
  "\<lbrakk> groupSizeBits < word_bits; is_aligned ptr (groupSizeBits + objBitsKO (injectKOS object));
    no_fail ((=) s) (placeNewObject ptr object groupSizeBits) \<rbrakk> \<Longrightarrow>
  ((), (s\<lparr>ksPSpace := foldr (\<lambda>addr. data_map_insert addr (injectKOS object)) (new_cap_addrs (2 ^ groupSizeBits) ptr (injectKOS object)) (ksPSpace s)\<rparr>))
                \<in> fst (placeNewObject ptr object groupSizeBits s)"
  apply (clarsimp simp: placeNewObject_def placeNewObject'_def)
  apply (clarsimp simp: split_def field_simps split del: if_split)
  apply (clarsimp simp: no_fail_def)
  apply (subst lookupAround2_pspace_no)
   apply assumption
  apply (subst (asm) lookupAround2_pspace_no)
   apply assumption
  apply (clarsimp simp add: in_monad' split_def bind_assoc field_simps
    snd_bind ball_to_all unless_def  split: option.splits if_split_asm)
  apply (clarsimp simp: data_map_insert_def new_cap_addrs_def)
  apply (subst upto_enum_red2)
   apply (fold word_bits_def, assumption)
  apply (clarsimp simp: field_simps shiftl_t2n power_add mult.commute mult.left_commute
           cong: foldr_cong map_cong)
  done

lemma globals_list_distinct_rf_sr:
  "\<lbrakk> (s, s') \<in> rf_sr; S \<inter> kernel_data_refs = {} \<rbrakk>
    \<Longrightarrow> globals_list_distinct S symbol_table globals_list"
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (erule globals_list_distinct_subset)
  apply blast
  done

lemma rf_sr_htd_safe:
  "(s, s') \<in> rf_sr \<Longrightarrow> htd_safe domain (hrs_htd (t_hrs_' (globals s')))"
  by (simp add: rf_sr_def cstate_relation_def Let_def)

lemma region_actually_is_bytes_dom_s:
  "region_actually_is_bytes' ptr len htd
    \<Longrightarrow> S \<subseteq> {ptr ..+ len}
    \<Longrightarrow> S \<times> {SIndexVal, SIndexTyp 0} \<subseteq> dom_s htd"
  apply (clarsimp simp: region_actually_is_bytes'_def dom_s_def)
  apply fastforce
  done

lemma typ_region_bytes_actually_is_bytes:
  "htd = typ_region_bytes ptr bits htd'
    \<Longrightarrow> region_actually_is_bytes' ptr (2 ^ bits) htd"
  by (clarsimp simp: region_actually_is_bytes'_def typ_region_bytes_def)

(* FIXME: need a way to avoid overruling the parser on this, it's ugly *)
lemma memzero_modifies:
  "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {\<sigma>} Call memzero_'proc {t. t may_only_modify_globals \<sigma> in [t_hrs]}"
  apply (rule allI, rule conseqPre)
  apply (hoare_rule HoarePartial.ProcNoRec1)
   apply (tactic \<open>HoarePackage.vcg_tac "_modifies" "false" [] @{context} 1\<close>)
  apply (clarsimp simp: mex_def meq_def simp del: split_paired_Ex)
  apply (intro exI globals.equality, simp_all)
  done

lemma ghost_assertion_size_logic_no_unat:
  "sz \<le> gsMaxObjectSize s
    \<Longrightarrow> (s, \<sigma>) \<in> rf_sr
    \<Longrightarrow> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' (globals \<sigma>)) = 0 \<or>
            of_nat sz \<le> gs_get_assn cap_get_capSizeBits_'proc (ghost'state_' (globals \<sigma>))"
  apply (rule ghost_assertion_size_logic'[rotated])
   apply (simp add: rf_sr_def)
  apply (simp add: unat_of_nat)
  done

lemma ccorres_placeNewObject_endpoint:
  "ko = (makeObject :: endpoint)
   \<Longrightarrow> ccorresG rf_sr \<Gamma> dc xfdc
   (pspace_aligned' and pspace_distinct'
      and pspace_no_overlap' regionBase (objBits ko)
      and ret_zero regionBase (2 ^ objBits ko)
      and (\<lambda>s. 2 ^ (objBits ko) \<le> gsMaxObjectSize s)
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase (objBits ko) (objBits ko) 1
      \<and> {regionBase..+ 2 ^ (objBits ko)} \<inter> kernel_data_refs = {}))
   ({s. region_actually_is_zero_bytes regionBase (2 ^ objBits ko) s})
    hs
    (placeNewObject regionBase ko 0)
    (global_htd_update (\<lambda>_. (ptr_retyp (ep_Ptr regionBase))))"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         objBits_simps'
                         ptr_retyp_htd_safe_neg)
  apply (rule bexI [OF _ placeNewObject_eq])
     apply (clarsimp simp: split_def)
     apply (clarsimp simp: new_cap_addrs_def)
     apply (cut_tac createObjects_ccorres_ep [where ptr=regionBase and n="1" and sz="objBitsKO (KOEndpoint makeObject)"])
     apply (erule_tac x=\<sigma> in allE, erule_tac x=x in allE)
     apply (clarsimp elim!: is_aligned_weaken simp: objBitsKO_def word_bits_def)+
     apply (clarsimp simp: split_def Let_def rf_sr_def new_cap_addrs_def
                           region_actually_is_bytes ptr_retyps_gen_def objBits_simps
                    elim!: rsubst[where P="cstate_relation s'" for s'])
    apply (clarsimp simp: word_bits_conv)
   apply (clarsimp simp: range_cover.aligned objBits_simps)
  apply (clarsimp simp: no_fail_def)
  done

lemma ccorres_placeNewObject_notification:
  "ko = (makeObject :: notification)
   \<Longrightarrow> ccorresG rf_sr \<Gamma> dc xfdc
   (pspace_aligned' and pspace_distinct'
      and pspace_no_overlap' regionBase (objBits ko)
      and ret_zero regionBase (2 ^ objBits ko)
      and (\<lambda>s. 2 ^ (objBits ko) \<le> gsMaxObjectSize s)
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase (objBits ko) (objBits ko) 1
      \<and> {regionBase..+ 2 ^ (objBits ko)} \<inter> kernel_data_refs = {}))
   ({s. region_actually_is_zero_bytes regionBase (2 ^ objBits ko) s})
    hs
    (placeNewObject regionBase ko 0)
    (global_htd_update (\<lambda>_. (ptr_retyp (ntfn_Ptr regionBase))))"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate objBits_simps'
                         ptr_retyp_htd_safe_neg)
  apply (rule bexI [OF _ placeNewObject_eq])
     apply (clarsimp simp: split_def)
     apply (clarsimp simp: new_cap_addrs_def)
     apply (cut_tac createObjects_ccorres_ntfn [where ptr=regionBase and n="1" and sz="objBitsKO (KONotification makeObject)"])
     apply (erule_tac x=\<sigma> in allE, erule_tac x=x in allE)
     apply (clarsimp elim!: is_aligned_weaken simp: objBitsKO_def word_bits_def)+
     apply (clarsimp simp: split_def Let_def rf_sr_def new_cap_addrs_def
                           region_actually_is_bytes ptr_retyps_gen_def objBits_simps'
                    elim!: rsubst[where P="cstate_relation s'" for s'])
    apply (clarsimp simp: word_bits_conv)
   apply (clarsimp simp: range_cover.aligned objBits_simps)
  apply (clarsimp simp: no_fail_def)
  done


lemma htd_update_list_dom_better [rule_format]:
  "(\<forall>p d. dom_s (htd_update_list p xs d) =
          (dom_s d) \<union> dom_tll p xs)"
  apply(induct_tac xs)
   apply simp
  apply clarsimp
  apply(auto split: if_split_asm)
   apply(erule notE)
   apply(clarsimp simp: dom_s_def)
  apply(case_tac y)
   apply clarsimp+
  apply(clarsimp simp: dom_s_def)
  done

lemma ptr_array_retyps_htd_safe_neg:
  "\<lbrakk> htd_safe D htd; {ptr_val ptr ..+ n * size_of TYPE('a :: mem_type)} \<inter> D' = {}; -D \<subseteq> D' \<rbrakk>
   \<Longrightarrow> htd_safe D (ptr_arr_retyps n (ptr :: 'a ptr) htd)"
  apply (simp add: htd_safe_def ptr_arr_retyps_def htd_update_list_dom_better)
  apply (auto simp: dom_tll_def intvl_def)
  done

lemmas ptr_array_retyps_htd_safe_neg' = ptr_array_retyps_htd_safe_neg[OF _ _ subset_refl]

lemma ccorres_placeNewObject_captable:
  "ccorresG rf_sr \<Gamma> dc xfdc
   (pspace_aligned' and pspace_distinct' and pspace_no_overlap' regionBase (unat userSize + 5)
      and (\<lambda>s. 2 ^ (unat userSize + 5) \<le> gsMaxObjectSize s)
      and ret_zero regionBase (2 ^ (unat userSize + 5))
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase (unat userSize + 5) (unat userSize + 5) 1
      \<and> ({regionBase..+2 ^ (unat userSize + 5)} \<inter> kernel_data_refs = {})))
    ({s. region_actually_is_zero_bytes regionBase (2 ^ (unat userSize + 5)) s})
    hs
    (placeNewObject regionBase (makeObject :: cte) (unat (userSize::machine_word)))
    (global_htd_update (\<lambda>_. (ptr_arr_retyps (2 ^ (unat userSize)) (cte_Ptr regionBase))))"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         ptr_array_retyps_htd_safe_neg
                         size_of_def power_add)
  apply (frule range_cover_rel[where sbit' = 5])
    apply simp
   apply simp
  apply (frule range_cover.unat_of_nat_shift[where gbits = 5 , OF _ le_refl le_refl ])
   apply (subgoal_tac "region_is_bytes regionBase (2 ^ (unat userSize + 5)) x")
   apply (rule bexI [OF _ placeNewObject_eq])
      apply (clarsimp simp: split_def new_cap_addrs_def)
      apply (cut_tac createObjects_ccorres_cte [where ptr=regionBase and n="2 ^ unat userSize" and sz="unat userSize + objBitsKO (KOCTE makeObject)"])
      apply (erule_tac x=\<sigma> in allE, erule_tac x=x in allE)
      apply (clarsimp elim!: is_aligned_weaken simp: objBitsKO_def word_bits_def cteSizeBits_def)+
      apply (clarsimp simp: split_def objBitsKO_def rf_sr_def split_def Let_def cteSizeBits_def
                            new_cap_addrs_def field_simps power_add ptr_retyps_gen_def
                     elim!: rsubst[where P="cstate_relation s'" for s'])
     apply (clarsimp simp: word_bits_conv range_cover_def)
    apply (clarsimp simp: objBitsKO_def objBits_simps' range_cover.aligned)
   apply (clarsimp simp: no_fail_def)
  apply (simp add: region_actually_is_bytes)
 done

lemma rf_sr_helper:
  "\<And>a b P X. ((a, globals_update P (b\<lparr>tcb_' := X\<rparr>)) \<in> rf_sr) = ((a, globals_update P b) \<in> rf_sr)"
  apply (clarsimp simp: rf_sr_def)
  done

declare replicate_numeral [simp del]

definition
  array_updates_rev :: "(nat \<times> 'a) list \<Rightarrow> 'a::c_type['b::finite] \<Rightarrow> 'a['b]"
where
  "array_updates_rev \<equiv> foldr (\<lambda>(i,v) a. Arrays.update a i v)"

lemma array_updates_rev:
  "array_updates_rev upds arr = array_updates arr (fold (#) upds [])"
  by (auto simp: array_updates_rev_def array_updates_def rev_conv_fold[symmetric]
                 foldl_conv_foldr
          intro: foldr_cong[OF refl refl])

lemma array_updates_rev':
  "array_updates arr upds = array_updates_rev (fold (#) upds []) arr"
  by (auto simp: array_updates_rev_def array_updates_def rev_conv_fold[symmetric]
                 foldl_conv_foldr
          intro: foldr_cong[OF refl refl])

lemma Arrays_udpate_array_updates_rev:
  "Arrays.update a i v = array_updates_rev [(i,v)] a"
  by (simp add: array_updates_rev_def)

lemma array_updates_rev_app:
  "array_updates_rev upds1 (array_updates_rev upds2 a) = array_updates_rev (upds1 @ upds2) a"
  by (simp add: array_updates_rev_def)

lemma Mode_initContext_spec':
  defines
    "Mode_initContext_regs \<equiv>
      [(unat Kernel_C.RAX, 0), (unat Kernel_C.RBX, 0), (unat Kernel_C.RCX, 0), (unat Kernel_C.RDX, 0),
       (unat Kernel_C.RSI, 0), (unat Kernel_C.RDI, 0), (unat Kernel_C.RBP, 0), (unat Kernel_C.R8 , 0),
       (unat Kernel_C.R9 , 0), (unat Kernel_C.R10, 0), (unat Kernel_C.R11, 0), (unat Kernel_C.R12, 0),
       (unat Kernel_C.R13, 0), (unat Kernel_C.R14, 0), (unat Kernel_C.R15, 0), (unat Kernel_C.RSP, 0)]"
  shows
    "\<forall>s\<^sub>0. \<Gamma> \<turnstile>
      {t. t = s\<^sub>0 \<and> t \<Turnstile>\<^sub>c context_' t}
        Call Mode_initContext_'proc
      {t. t = globals_update
               (t_hrs_'_update
                (hrs_mem_update
                 (heap_update
                  (registers_Ptr &(context_' s\<^sub>0\<rightarrow>[''registers_C'']))
                  (array_updates (h_val (hrs_mem (t_hrs_' (globals s\<^sub>0)))
                                        (registers_Ptr &(context_' s\<^sub>0\<rightarrow>[''registers_C''])))
                                 Mode_initContext_regs)))) s\<^sub>0}"
  unfolding Mode_initContext_regs_def
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (simp add: C_register_defs Arrays_udpate_array_updates_rev)
  apply (rule allI, rule conseqPre)
  apply (rule hoarep.Catch[rotated], vcg)
  apply (rule conseqPost[where A'="{}" and Q'=Q and Q=Q for Q, simplified])
  apply (rule hoarep.Seq[rotated]
         | (vcg, clarsimp simp: hrs_mem_update_compose h_val_id packed_heap_update_collapse'
                                array_updates_rev_app))+
  by (simp add: array_updates_rev)

lemmas Mode_initContext_spec'' =
  Mode_initContext_spec'[simplified array_updates_rev' C_register_defs, simplified]

lemma Arch_initContext_spec':
  shows
    "\<forall>s\<^sub>0. \<Gamma> \<turnstile>
      {t. t = s\<^sub>0 \<and> t \<Turnstile>\<^sub>c context_' t \<and> s\<^sub>0 \<Turnstile>\<^sub>c fpu_state_Ptr (symbol_table ''x86KSnullFpuState'')}
        Call Arch_initContext_'proc
      {t. t = globals_update
               (t_hrs_'_update
                (hrs_mem_update
                 (heap_update (fpu_state_Ptr &(context_' s\<^sub>0\<rightarrow>[''fpuState_C'']))
                              (h_val (hrs_mem (t_hrs_' (globals s\<^sub>0)))
                                     (fpu_state_Ptr (symbol_table ''x86KSnullFpuState''))) \<circ>
                  heap_update (registers_Ptr &(context_' s\<^sub>0\<rightarrow>[''registers_C'']))
                              (array_updates (h_val (hrs_mem (t_hrs_' (globals s\<^sub>0)))
                                                    (registers_Ptr &(context_' s\<^sub>0\<rightarrow>[''registers_C''])))
                                             initContext_registers)))) s\<^sub>0}"
  unfolding initContext_registers_def
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (simp add: C_register_defs Arrays_udpate_array_updates_rev)
  apply (rule allI, rule conseqPre)
   apply (rule hoarep.Catch[rotated], vcg)
   apply (rule conseqPost[where A'="{}" and Q'=Q and Q=Q for Q, simplified])
   apply (rule hoarep.Seq[rotated], vcg)
   apply (rule hoarep.Seq[rotated]
          | (vcg exspec=Mode_initContext_spec'',
             clarsimp simp: hrs_mem_update_compose h_val_id packed_heap_update_collapse o_def
                            array_updates_rev_app))+
  apply (auto simp: h_val_heap_same_hrs_mem_update_typ_disj[OF h_t_valid_c_guard_field _ tag_disj_via_td_name]
                    export_tag_adjust_ti typ_uinfo_t_def array_updates_rev
              cong: Kernel_C.globals.unfold_congs StateSpace.state.unfold_congs)
  done

lemma rf_sr_fpu_null_relation:
  "(s,s') \<in> rf_sr \<Longrightarrow> fpu_null_state_relation (t_hrs_' (globals s'))"
  by (simp add: rf_sr_def cstate_relation_def Let_def carch_state_relation_def)

lemma ccorres_placeNewObject_tcb:
  "ccorresG rf_sr \<Gamma> dc xfdc
   (pspace_aligned' and pspace_distinct' and pspace_no_overlap' regionBase tcbBlockSizeBits and valid_queues and (\<lambda>s. sym_refs (state_refs_of' s))
      and (\<lambda>s. 2 ^ tcbBlockSizeBits \<le> gsMaxObjectSize s)
      and ret_zero regionBase (2 ^ tcbBlockSizeBits)
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase tcbBlockSizeBits tcbBlockSizeBits 1
      \<and>  {regionBase..+2^tcbBlockSizeBits} \<inter> kernel_data_refs = {}))
   ({s. region_actually_is_zero_bytes regionBase (2^tcbBlockSizeBits) s})
    hs
   (placeNewObject regionBase (makeObject :: tcb) 0)
   (\<acute>tcb :== tcb_Ptr (regionBase + 0x400);;
        (global_htd_update (\<lambda>s. ptr_retyp (Ptr (ptr_val (tcb_' s) - ctcb_offset) :: (cte_C[5]) ptr)
            \<circ> ptr_retyp (tcb_' s)));;
        (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>tcb\<rbrace>
           (call (\<lambda>s. s\<lparr>context_' := Ptr &((Ptr &(tcb_' s\<rightarrow>[''tcbArch_C'']) :: arch_tcb_C ptr)\<rightarrow>[''tcbContext_C''])\<rparr>) Arch_initContext_'proc (\<lambda>s t. s\<lparr>globals := globals t\<rparr>) (\<lambda>s' s''. Basic (\<lambda>s. s))));;
        (Guard C_Guard \<lbrace>hrs_htd \<acute>t_hrs \<Turnstile>\<^sub>t \<acute>tcb\<rbrace>
           (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update (heap_update (Ptr &((tcb_' s)\<rightarrow>[''tcbTimeSlice_C''])) (5::machine_word)))) s))))"
  apply (simp add: placeNewObject_eq)
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre, vcg exspec=Arch_initContext_spec')
  apply (clarsimp simp: rf_sr_htd_safe ctcb_offset_defs cong: conj_cong)
  apply (subgoal_tac "c_guard (tcb_Ptr (regionBase + 0x400))")
   prefer 2
   apply (rule c_guard_tcb;
          clarsimp simp: ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs range_cover.aligned)
  apply (subgoal_tac "hrs_htd (hrs_htd_update (ptr_retyp (Ptr regionBase :: (cte_C[5]) ptr)
                                \<circ> ptr_retyp (tcb_Ptr (regionBase + 0x400)))
                 (t_hrs_' (globals x))) \<Turnstile>\<^sub>t tcb_Ptr (regionBase + 0x400)")
   prefer 2
   apply (clarsimp simp: hrs_htd_update)
   apply (rule h_t_valid_ptr_retyps_gen_disjoint
                 [where n=1 and arr=False, unfolded ptr_retyps_gen_def, simplified])
    apply (rule ptr_retyp_h_t_valid)
    apply simp
   apply (rule tcb_ptr_orth_cte_ptrs')
  apply (simp add: o_def)
  apply (intro conjI allI impI)
     apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                           kernel_data_refs_domain_eq_rotate)
     apply (intro ptr_retyps_htd_safe_neg ptr_retyp_htd_safe_neg, simp_all add: size_of_def)[1]
      apply (erule disjoint_subset[rotated])
      apply (rule intvl_sub_offset, simp add: objBits_defs)
     apply (erule disjoint_subset[rotated],
            simp add: intvl_start_le size_td_array cte_C_size objBits_defs)
    apply (clarsimp simp: hrs_htd_update)
    apply (rule h_t_valid_field[rotated], simp+)+
   apply (clarsimp simp: hrs_htd_update)
   apply (subgoal_tac "{regionBase + 0x400 ..+ size_of TYPE(tcb_C)} \<subseteq> {regionBase ..+ 2 ^ tcbBlockSizeBits}")
    apply (subgoal_tac "{regionBase ..+ 5*size_of TYPE(cte_C)} \<subseteq> {regionBase ..+ 2 ^ tcbBlockSizeBits}")
     apply (intro h_t_valid_ptr_retyps_gen_disjoint
                    [where n=1 and arr=False, unfolded ptr_retyps_gen_def, simplified];
            clarsimp simp: rf_sr_def cstate_relation_def Let_def carch_state_relation_def
                           fpu_null_state_relation_def2 objBits_defs
                    elim!: disjoint_subset disjoint_subset2; blast)
    apply (rule intvl_sub_offset intvl_start_le; clarsimp simp: objBits_defs cte_C_size)+
  apply (rule bexI[OF _ placeNewObject_eq];
         clarsimp simp: hrs_htd_update word_bits_def no_fail_def objBitsKO_def
                        range_cover.aligned new_cap_addrs_def)
  apply (cut_tac \<sigma>=\<sigma> and x=x and ks="ksPSpace \<sigma>" and p="tcb_Ptr (regionBase + ctcb_offset)"
           in cnc_tcb_helper;
         clarsimp simp: ctcb_ptr_to_tcb_ptr_def objBitsKO_def range_cover.aligned)
    apply (frule region_actually_is_bytes; clarsimp simp: region_is_bytes'_def)
   apply (clarsimp simp: hrs_mem_def)
  apply (frule rf_sr_fpu_null_relation; simp add: fpu_null_state_relation_def2)
  by (clarsimp simp: ctcb_offset_defs rf_sr_def ptr_retyps_gen_def heap_updates_def
                     hrs_mem_update_compose
               cong: Kernel_C.globals.unfold_congs StateSpace.state.unfold_congs
                     kernel_state.unfold_congs)

lemma placeNewObject_pte:
  "ccorresG rf_sr \<Gamma> dc xfdc
   ( valid_global_refs' and pspace_aligned' and pspace_distinct' and pspace_no_overlap' regionBase pageBits
      and (\<lambda>s. 2 ^ pageBits \<le> gsMaxObjectSize s)
      and ret_zero regionBase (2 ^ pageBits)
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase pageBits pageBits 1
      \<and> ({regionBase..+2 ^ pageBits} \<inter> kernel_data_refs = {})
      ))
    ({s. region_actually_is_zero_bytes regionBase (2 ^ pageBits) s})
    hs
    (placeNewObject regionBase (makeObject :: pte) ptTranslationBits)
    (global_htd_update (\<lambda>_. (ptr_retyp (pt_Ptr regionBase))))"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         ptr_retyp_htd_safe_neg bit_simps)
  apply (frule range_cover_rel[where sbit' = 3])
    apply ((simp add: pageBits_def)+)[3]
  apply (frule range_cover.unat_of_nat_shift[where gbits = 3 ])
     apply (simp add: pageBits_def)+
    apply (rule le_refl)
  apply (subgoal_tac "region_is_bytes regionBase 4096 x")
   apply (rule bexI [OF _ placeNewObject_eq])
      apply (clarsimp simp: split_def new_cap_addrs_def)
      apply (cut_tac s=\<sigma> in createObjects_ccorres_pte [where ptr=regionBase and sz=pageBits])
      apply (erule_tac x=\<sigma> in allE, erule_tac x=x in allE)
      apply (clarsimp elim!: is_aligned_weaken simp: objBitsKO_def word_bits_def)+
      apply (clarsimp simp: split_def objBitsKO_def archObjSize_def
                            rf_sr_def split_def Let_def ptr_retyps_gen_def
                            new_cap_addrs_def field_simps power_add
                      cong: globals.unfold_congs)
      apply (simp add: Int_ac bit_simps)
     apply (clarsimp simp: word_bits_conv range_cover_def archObjSize_def bit_simps)
    apply (clarsimp simp: objBitsKO_def range_cover.aligned archObjSize_def bit_simps)
   apply (clarsimp simp: no_fail_def)
  apply (simp add: region_actually_is_bytes bit_simps)
 done

lemma placeNewObject_pde:
  "ccorresG rf_sr \<Gamma> dc xfdc
   ( valid_global_refs' and pspace_aligned' and pspace_distinct' and pspace_no_overlap' regionBase pdBits
      and (\<lambda>s. 2 ^ pdBits \<le> gsMaxObjectSize s)
      and ret_zero regionBase (2 ^ pdBits)
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase pdBits pdBits 1
      \<and> ({regionBase..+2 ^ pdBits} \<inter> kernel_data_refs = {})
      ))
    ({s. region_actually_is_zero_bytes regionBase (2 ^ pdBits) s})
    hs
    (placeNewObject regionBase (makeObject :: pde) ptTranslationBits)
    (global_htd_update (\<lambda>_. (ptr_retyp (pd_Ptr regionBase))))"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         ptr_retyp_htd_safe_neg bit_simps)
  apply (frule range_cover_rel[where sbit' = 3])
    apply ((simp add: bit_simps)+)[3]
  apply (frule range_cover.unat_of_nat_shift[where gbits = 3 ])
     apply (simp add: bit_simps)+
    apply (rule le_refl)
  apply (subgoal_tac "region_is_bytes regionBase 4096 x")
   apply (rule bexI [OF _ placeNewObject_eq])
      apply (clarsimp simp: split_def new_cap_addrs_def)
      apply (cut_tac s=\<sigma> in createObjects_ccorres_pde [where ptr=regionBase and sz=pdBits])
      apply (erule_tac x=\<sigma> in allE, erule_tac x=x in allE)
      apply (clarsimp elim!:is_aligned_weaken simp: objBitsKO_def word_bits_def)+
      apply (clarsimp simp: split_def objBitsKO_def archObjSize_def
          Fun.comp_def rf_sr_def split_def Let_def ptr_retyps_gen_def
          new_cap_addrs_def field_simps power_add
          cong: globals.unfold_congs)
      apply (simp add: Int_ac bit_simps)
     apply (clarsimp simp: word_bits_conv range_cover_def archObjSize_def bit_simps)
    apply (clarsimp simp: objBitsKO_def range_cover.aligned archObjSize_def bit_simps)
   apply (clarsimp simp: no_fail_def)
  apply (simp add: region_actually_is_bytes bit_simps)
  done

lemma placeNewObject_pdpte:
  "ccorresG rf_sr \<Gamma> dc xfdc
   ( valid_global_refs' and pspace_aligned' and pspace_distinct' and pspace_no_overlap' regionBase pdptBits
      and (\<lambda>s. 2 ^ pdptBits \<le> gsMaxObjectSize s)
      and ret_zero regionBase (2 ^ pdptBits)
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase pdptBits pdptBits 1
      \<and> ({regionBase..+2 ^ pdptBits} \<inter> kernel_data_refs = {})
      ))
    ({s. region_actually_is_zero_bytes regionBase (2 ^ pdptBits) s})
    hs
    (placeNewObject regionBase (makeObject :: pdpte) ptTranslationBits)
    (global_htd_update (\<lambda>_. (ptr_retyp (pdpt_Ptr regionBase))))"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         ptr_retyp_htd_safe_neg bit_simps)
  apply (frule range_cover_rel[where sbit' = 3])
    apply ((simp add: bit_simps)+)[3]
  apply (frule range_cover.unat_of_nat_shift[where gbits = 3 ])
     apply (simp add: bit_simps)+
    apply (rule le_refl)
  apply (subgoal_tac "region_is_bytes regionBase 4096 x")
   apply (rule bexI [OF _ placeNewObject_eq])
      apply (clarsimp simp: split_def new_cap_addrs_def)
      apply (cut_tac s=\<sigma> in createObjects_ccorres_pdpte [where ptr=regionBase and sz=pdptBits])
      apply (erule_tac x=\<sigma> in allE, erule_tac x=x in allE)
      apply (clarsimp elim!:is_aligned_weaken simp: objBitsKO_def word_bits_def)+
      apply (clarsimp simp: split_def objBitsKO_def archObjSize_def
          Fun.comp_def rf_sr_def split_def Let_def ptr_retyps_gen_def
          new_cap_addrs_def field_simps power_add
          cong: globals.unfold_congs)
      apply (simp add: Int_ac bit_simps)
     apply (clarsimp simp: word_bits_conv range_cover_def archObjSize_def bit_simps)
    apply (clarsimp simp: objBitsKO_def range_cover.aligned archObjSize_def bit_simps)
   apply (clarsimp simp: no_fail_def)
  apply (simp add: region_actually_is_bytes bit_simps)
  done

lemma placeNewObject_pml4e:
  "ccorresG rf_sr \<Gamma> dc xfdc
   (valid_global_refs' and pspace_aligned' and pspace_distinct' and pspace_no_overlap' regionBase pml4Bits
      and (\<lambda>s. 2 ^ pml4Bits \<le> gsMaxObjectSize s)
      and ret_zero regionBase (2 ^ pml4Bits)
      and K (regionBase \<noteq> 0 \<and> range_cover regionBase pml4Bits pml4Bits 1
      \<and> ({regionBase..+2 ^ pml4Bits}
          \<inter> kernel_data_refs = {})
      ))
    ({s. region_actually_is_zero_bytes regionBase (2 ^ pml4Bits) s})
    hs
    (placeNewObject regionBase (makeObject :: pml4e) ptTranslationBits)
    (global_htd_update (\<lambda>_. (ptr_retyp (pml4_Ptr regionBase))))"
  apply (rule ccorres_from_vcg_nofail)
  apply clarsimp
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         ptr_retyp_htd_safe_neg bit_simps)
  apply (frule range_cover_rel[where sbit' = 3])
    apply (simp add: bit_simps)+
  apply (frule range_cover.unat_of_nat_shift[where gbits = 3 ])
   apply simp+
   apply (rule le_refl)

   apply (subgoal_tac "region_is_bytes regionBase 4096 x")
   apply (rule bexI [OF _ placeNewObject_eq])
      apply (clarsimp simp: split_def new_cap_addrs_def)
      apply (cut_tac s=\<sigma> in createObjects_ccorres_pml4e [where ptr=regionBase and sz=pml4Bits])
      apply (erule_tac x=\<sigma> in allE, erule_tac x=x in allE)
      apply (clarsimp elim!:is_aligned_weaken simp: objBitsKO_def word_bits_def bit_simps)+
      apply (clarsimp simp: split_def objBitsKO_def archObjSize_def
          Fun.comp_def rf_sr_def Let_def ptr_retyps_gen_def
          new_cap_addrs_def field_simps power_add
          cong: globals.unfold_congs)
      apply (simp add: Int_ac bit_simps)
     apply (clarsimp simp: word_bits_conv range_cover_def archObjSize_def)
    apply (clarsimp simp: objBitsKO_def range_cover.aligned archObjSize_def bit_simps)
   apply (clarsimp simp: no_fail_def)
  apply (simp add: region_actually_is_bytes)
 done

end

lemma dom_disj_union:
  "dom (\<lambda>x. if P x \<or> Q x then Some (G x) else None) = dom (\<lambda>x. if P x then Some (G x) else None)
  \<union> dom (\<lambda>x. if Q x then Some (G x) else None)"
  by (auto split:if_splits)

context kernel_m begin

lemma createObjects_ccorres_user_data_device:
  defines "ko \<equiv> KOUserDataDevice"
  shows "\<forall>\<sigma> x. (\<sigma>, x) \<in> rf_sr \<and> range_cover ptr sz (gbits + pageBits) n
  \<and> ptr \<noteq> 0
  \<and> pspace_aligned' \<sigma> \<and> pspace_distinct' \<sigma>
  \<and> pspace_no_overlap' ptr sz \<sigma>
  \<and> ret_zero ptr (n * 2 ^ (gbits + pageBits)) \<sigma>
  \<and> region_is_bytes ptr (n * 2 ^ (gbits + pageBits)) x
  \<and> {ptr ..+ n * (2 ^ (gbits + pageBits))} \<inter> kernel_data_refs = {}
  \<longrightarrow>
  (\<sigma>\<lparr>ksPSpace :=
               foldr (\<lambda>addr. data_map_insert addr KOUserDataDevice) (new_cap_addrs (n * 2^gbits) ptr KOUserDataDevice) (ksPSpace \<sigma>)\<rparr>,
           x\<lparr>globals := globals x\<lparr>t_hrs_' :=
                      hrs_htd_update
                       (ptr_retyps_gen (n * 2 ^ gbits) (Ptr ptr :: user_data_device_C ptr) arr)
                       (t_hrs_' (globals x))\<rparr> \<rparr>) \<in> rf_sr"
  (is "\<forall>\<sigma> x. ?P \<sigma> x \<longrightarrow>
    (\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr")
proof (intro impI allI)
  fix \<sigma> x
  let ?thesis = "(\<sigma>\<lparr>ksPSpace := ?ks \<sigma>\<rparr>, x\<lparr>globals := globals x\<lparr>t_hrs_' := ?ks' x\<rparr>\<rparr>) \<in> rf_sr"
  let ?ks = "?ks \<sigma>"
  let ?ks' = "?ks' x"
  let ?ptr = "Ptr ptr :: user_data_device_C ptr"

  note Kernel_C.user_data_C_size [simp del]

  assume "?P \<sigma> x"
  hence rf: "(\<sigma>, x) \<in> rf_sr" and al: "is_aligned ptr (gbits + pageBits)"
    and ptr0: "ptr \<noteq> 0"
    and sz: "gbits + pageBits \<le> sz"
    and szb: "sz < word_bits"
    and pal: "pspace_aligned' \<sigma>" and pdst: "pspace_distinct' \<sigma>"
    and pno: "pspace_no_overlap' ptr sz \<sigma>"
    and rzo: "ret_zero ptr (n * 2 ^ (gbits + pageBits)) \<sigma>"
    and empty: "region_is_bytes ptr (n * 2 ^ (gbits + pageBits)) x"
    and rc: "range_cover ptr sz (gbits + pageBits) n"
    and rc': "range_cover ptr sz (objBitsKO ko) (n * 2^ gbits)"
    and kdr: "{ptr..+n * 2 ^ (gbits + pageBits)} \<inter> kernel_data_refs = {}"
    by (auto simp: range_cover.aligned objBits_simps  ko_def
                   range_cover_rel[where sbit' = pageBits]
                   range_cover.sz[where 'a=machine_word_len, folded word_bits_def])


  hence al': "is_aligned ptr (objBitsKO ko)"
    by (clarsimp dest!:is_aligned_weaken range_cover.aligned)

  note range_cover.no_overflow_n[OF rc']
  hence sz_word_bits:
    "n * 2 ^ gbits * size_of TYPE(user_data_device_C)  < 2 ^ word_bits"
      by (simp add:word_bits_def objBits_simps ko_def pageBits_def)

  (* This is a hack *)
  have mko: "\<And>dev. makeObjectKO True (Inr object_type.SmallPageObject) = Some ko"
    by (simp add: makeObjectKO_def ko_def)

  from sz have "3 \<le> sz" by (simp add: objBits_simps pageBits_def ko_def)

  hence sz2: "2 ^ (sz - 3) * 8 = (2 :: nat) ^ sz"
    apply (subgoal_tac "(8 :: nat) = 2 ^ 3")
    apply (erule ssubst)
    apply (subst power_add [symmetric])
    apply (rule arg_cong [where f = "\<lambda>n. 2 ^ n"])
    apply simp
    apply simp
    done

  have p2dist: "n * (2::nat) ^ (gbits + pageBits) = n * 2 ^ gbits * 2 ^ pageBits" (is "?lhs = ?rhs")
    by (simp add:monoid_mult_class.power_add)

  note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
      Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  (* /obj specific *)

  (* s/obj/obj'/ *)

  have szo: "size_of TYPE(user_data_device_C) = 2 ^ objBitsKO ko"
    by (simp add: size_of_def objBits_simps archObjSize_def ko_def pageBits_def)
  have szo': "n * 2 ^ (gbits + pageBits) = n * 2 ^ gbits * size_of TYPE(user_data_device_C)" using sz
    apply (subst szo)
    apply (clarsimp simp: power_add[symmetric] objBits_simps ko_def)
    done

  have rb': "region_is_bytes ptr (n * 2 ^ gbits * 2 ^ objBitsKO ko) x"
    using empty
    by (simp add: mult.commute mult.left_commute power_add objBits_simps ko_def)

  from rb' have rbu: "region_is_bytes ptr (n * 2 ^ gbits * size_of TYPE(user_data_device_C)) x"
    by (simp add:szo[symmetric])

  note rl' = clift_ptr_retyps_gen_other[where p = "Ptr ptr",simplified, OF rbu  sz_word_bits]

  (* rest is generic *)

  note rl = projectKO_opt_retyp_other [OF rc' pal pno,unfolded ko_def]
  note cterl = retype_ctes_helper[OF pal pdst pno al' range_cover.sz(2)[OF rc'] range_cover.sz(1)[OF rc', folded word_bits_def] mko rc']
  note ht_rl = clift_eq_h_t_valid_eq[OF rl', OF tag_disj_via_td_name, simplified]

  have guard:
    "\<forall>t<n * 2 ^ gbits. c_guard (CTypesDefs.ptr_add ?ptr (of_nat t))"
    apply (rule retype_guard_helper[OF rc' ptr0 szo,where m = 3])
    apply (clarsimp simp: align_of_def objBits_simps ko_def pageBits_def)+
    done

  have cud2: "\<And>xa v y.
              \<lbrakk> heap_to_device_data
                     (\<lambda>x. if x \<in> set (new_cap_addrs (n*2^gbits) ptr KOUserDataDevice)
                           then Some KOUserData else ksPSpace \<sigma> x)
                     (underlying_memory (ksMachineState \<sigma>)) xa =
              Some v; xa \<notin> set (new_cap_addrs (n*2^gbits) ptr KOUserDataDevice);
              heap_to_device_data (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) xa = Some y \<rbrakk> \<Longrightarrow> y = v"
    using range_cover_intvl[OF rc]
    by (clarsimp simp add: heap_to_device_data_def Let_def sz2
      byte_to_word_heap_def[abs_def] map_comp_Some_iff projectKOs)

  note ptr_retyps_valid = h_t_valid_ptr_retyps_gen_same[OF guard rbu,unfolded addr_card_wb,OF _ sz_word_bits,simplified]

  from rf have "cpspace_relation (ksPSpace \<sigma>) (underlying_memory (ksMachineState \<sigma>)) (t_hrs_' (globals x))"
    unfolding rf_sr_def cstate_relation_def by (simp add: Let_def)

  hence "cpspace_relation ?ks (underlying_memory (ksMachineState \<sigma>)) ?ks'"
    unfolding cpspace_relation_def
    using empty rc' szo
    supply if_cong[cong]
    apply -
    apply (clarsimp simp: rl' tag_disj_via_td_name cte_C_size ht_rl
                          clift_ptr_retyps_gen_other
                          foldr_upd_app_if [folded data_map_insert_def])
    apply (simp add: rl ko_def projectKOs p2dist
                     cterl[unfolded ko_def])
    apply (rule cmap_relationI)
     apply (clarsimp simp: dom_heap_to_device_data cmap_relation_def dom_if image_Un
                           projectKO_opt_retyp_same projectKOs liftt_if[folded hrs_mem_def hrs_htd_def]
                           hrs_htd_update hrs_mem_update ptr_retyps_valid dom_disj_union
                simp flip: ptr_add_to_new_cap_addrs)
     apply (simp add: heap_to_device_data_def cuser_user_data_device_relation_def)
    done (* dont need to track all the device memory *)

  thus  ?thesis using rf empty kdr rzo
    apply (simp add: rf_sr_def cstate_relation_def Let_def rl' tag_disj_via_td_name )
    apply (simp add: carch_state_relation_def fpu_null_state_relation_def cmachine_state_relation_def)
    apply (simp add: tag_disj_via_td_name rl' tcb_C_size h_t_valid_clift_Some_iff)
    apply (clarsimp simp: hrs_htd_update szo'[symmetric] cvariable_array_ptr_retyps[OF szo] rb')
    apply (subst zero_ranges_ptr_retyps, simp_all only: szo'[symmetric] power_add, simp)
    apply (simp add:szo  p2dist objBits_simps ko_def ptr_retyps_htd_safe_neg
                    kernel_data_refs_domain_eq_rotate
                    rl foldr_upd_app_if [folded data_map_insert_def]
                    projectKOs cvariable_array_ptr_retyps)
    apply (subst cvariable_array_ptr_retyps[OF szo])
    apply (simp add: rb' ptr_retyps_htd_safe_neg)+
    apply (erule ptr_retyps_htd_safe_neg; simp add:pageBits_def field_simps)
    done
qed

lemma placeNewObject_user_data:
  "ccorresG rf_sr \<Gamma> dc xfdc
  (pspace_aligned' and pspace_distinct' and pspace_no_overlap' regionBase (pageBits+us)
  and valid_queues and valid_machine_state'
  and ret_zero regionBase (2 ^ (pageBits+us))
  and (\<lambda>s. sym_refs (state_refs_of' s))
  and (\<lambda>s. 2^(pageBits +  us) \<le> gsMaxObjectSize s)
  and K (regionBase \<noteq> 0 \<and> range_cover regionBase (pageBits + us) (pageBits+us) (Suc 0)
  \<and> us < word_bits
  \<and>  {regionBase..+2^(pageBits +  us)} \<inter> kernel_data_refs = {}))
  ({s. region_actually_is_zero_bytes regionBase (2^(pageBits+us)) s})
  hs
  (placeNewObject regionBase UserData us)
  (global_htd_update (\<lambda>s. (ptr_retyps (2^us) (Ptr regionBase :: user_data_C ptr))))"
  apply (rule ccorres_from_vcg_nofail)
  apply (clarsimp simp:)
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         ptr_retyps_htd_safe_neg[where arr=False, unfolded ptr_retyps_gen_def, simplified]
                         size_of_def pageBits_def power_add mult.commute mult.left_commute)
  apply (frule range_cover.unat_of_nat_shift[where gbits = "pageBits + us"])
    apply simp
   apply (clarsimp simp:size_of_def power_add pageBits_def
     rf_sr_def cstate_relation_def Let_def field_simps)
   apply blast
  apply (frule range_cover.aligned)
  apply (rule bexI [OF _ placeNewObject_eq], simp_all)
    apply (cut_tac ptr=regionBase and sz="pageBits + us" and gbits=us and arr=False
                in createObjects_ccorres_user_data[rule_format])
     apply (rule conjI, assumption, clarsimp)
     apply (fastforce simp: pageBits_def field_simps region_actually_is_bytes)
    apply (clarsimp elim!: rsubst[where P="\<lambda>x. (\<sigma>, x) \<in> rf_sr" for \<sigma>]
                     simp: field_simps objBitsKO_def ptr_retyps_gen_def)
   apply (simp add: objBitsKO_def field_simps)
  apply (rule no_fail_pre, rule no_fail_placeNewObject)
  apply (clarsimp simp: objBitsKO_def)
  done

definition
  createObject_hs_preconds :: "machine_word \<Rightarrow> ArchTypes_H.object_type \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "createObject_hs_preconds regionBase newType userSize d \<equiv>
     (invs' and pspace_no_overlap' regionBase (getObjectSize newType userSize)
           and caps_overlap_reserved' {regionBase ..+ 2 ^ (getObjectSize newType userSize)}
           and (\<lambda>s. 2 ^ (getObjectSize newType userSize) \<le> gsMaxObjectSize s)
           and K(regionBase \<noteq> 0 \<and> canonical_address regionBase
                   \<and> ({regionBase..+2 ^ (getObjectSize newType userSize)} \<inter> kernel_data_refs = {})
                   \<and> range_cover regionBase (getObjectSize newType userSize) (getObjectSize newType userSize) (Suc 0)
                   \<and> (newType = APIObjectType apiobject_type.Untyped \<longrightarrow> userSize \<le> maxUntypedSizeBits)
                   \<and> (newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> userSize < 59)
                   \<and> (newType = APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> userSize)
                   \<and> (newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < userSize)
                   \<and> (d \<longrightarrow> newType = APIObjectType apiobject_type.Untyped \<or> isFrameType newType)
           ))"

abbreviation
  "region_actually_is_dev_bytes ptr len devMem s
    \<equiv> region_actually_is_bytes ptr len s
        \<and> (\<not> devMem \<longrightarrow> heap_list_is_zero (hrs_mem (t_hrs_' (globals s))) ptr len)"

(* these preconds actually used throughout the proof *)
abbreviation(input)
  createObject_c_preconds1 :: "machine_word \<Rightarrow> ArchTypes_H.object_type \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (globals myvars) set"
where
  "createObject_c_preconds1 regionBase newType userSize deviceMemory \<equiv>
    {s. region_actually_is_dev_bytes regionBase (2 ^ getObjectSize newType userSize) deviceMemory s}"

(* these preconds used at start of proof *)
definition
  createObject_c_preconds :: "machine_word \<Rightarrow> ArchTypes_H.object_type \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> (globals myvars) set"
where
  "createObject_c_preconds regionBase newType userSize deviceMemory \<equiv>
  (createObject_c_preconds1 regionBase newType userSize deviceMemory
           \<inter> {s. object_type_from_H newType = t_' s}
           \<inter> {s. Ptr regionBase = regionBase_' s}
           \<inter> {s. unat (scast (userSize_' s) :: machine_word) = userSize}
           \<inter> {s. deviceMemory_' s = from_bool deviceMemory}
     )"

lemma ccorres_apiType_split:
  "\<lbrakk> apiType = apiobject_type.Untyped \<Longrightarrow> ccorres rr xf P1 P1' hs X Y;
     apiType = apiobject_type.TCBObject \<Longrightarrow> ccorres rr xf P2 P2' hs X Y;
     apiType = apiobject_type.EndpointObject \<Longrightarrow> ccorres rr xf P3 P3' hs X Y;
     apiType = apiobject_type.NotificationObject \<Longrightarrow> ccorres rr xf P4 P4' hs X Y;
     apiType = apiobject_type.CapTableObject \<Longrightarrow> ccorres rr xf P5 P5' hs X Y
   \<rbrakk> \<Longrightarrow> ccorres rr xf
         ((\<lambda>s. apiType = apiobject_type.Untyped \<longrightarrow> P1 s)
         and (\<lambda>s. apiType = apiobject_type.TCBObject \<longrightarrow> P2 s)
         and (\<lambda>s. apiType = apiobject_type.EndpointObject \<longrightarrow> P3 s)
         and (\<lambda>s. apiType = apiobject_type.NotificationObject \<longrightarrow> P4 s)
         and (\<lambda>s. apiType = apiobject_type.CapTableObject \<longrightarrow> P5 s))
         ({s. apiType = apiobject_type.Untyped \<longrightarrow> s \<in> P1'}
         \<inter> {s. apiType = apiobject_type.TCBObject \<longrightarrow> s \<in> P2'}
         \<inter> {s. apiType = apiobject_type.EndpointObject \<longrightarrow> s \<in> P3'}
         \<inter> {s. apiType = apiobject_type.NotificationObject \<longrightarrow> s \<in> P4'}
         \<inter> {s. apiType = apiobject_type.CapTableObject \<longrightarrow> s \<in> P5'})
         hs X Y"
  apply (case_tac apiType, simp_all)
  done

lemma range_cover_simpleI:
  "\<lbrakk> is_aligned (ptr :: 'a :: len word) a; a < len_of TYPE('a); c = Suc 0 \<rbrakk>
  \<Longrightarrow> range_cover ptr a a c"
  apply (clarsimp simp: range_cover_def)
  apply (metis shiftr_0 is_aligned_mask unat_0)
  done

lemma range_coverI:
  "\<lbrakk>is_aligned (ptr :: 'a :: len word) a; b \<le> a; a < len_of TYPE('a);
    c \<le> 2 ^ (a - b)\<rbrakk>
  \<Longrightarrow> range_cover ptr a b c"
  apply (clarsimp simp: range_cover_def field_simps)
  apply (rule conjI)
   apply (erule(1) is_aligned_weaken)
  apply (subst mask_zero, simp)
  apply simp
  done

(* FIXME: with the current state of affairs, we could simplify gs_new_frames *)
lemma gsUserPages_update_ccorres:
  "ccorresG rf_sr G dc xf (\<lambda>_. sz = pageBitsForSize pgsz) UNIV hs
     (modify (gsUserPages_update (\<lambda>m a. if a = ptr then Some pgsz else m a)))
     (Basic (globals_update (ghost'state_'_update
                  (gs_new_frames pgsz ptr sz))))"
  apply (rule ccorres_from_vcg)
  apply vcg_step
  apply (clarsimp simp: split_def simpler_modify_def gs_new_frames_def)
  apply (case_tac "ghost'state_' (globals x)")
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def fun_upd_def
                        carch_state_relation_def cmachine_state_relation_def
                        ghost_size_rel_def ghost_assertion_data_get_def
                  cong: if_cong)
  done

lemma placeNewObject_user_data_device:
  "ccorresG rf_sr \<Gamma> dc xfdc
  (pspace_aligned' and pspace_distinct'
    and ret_zero regionBase (2 ^ (pageBits + us))
    and pspace_no_overlap' regionBase (pageBits+us) and valid_queues
    and (\<lambda>s. sym_refs (state_refs_of' s))
    and (\<lambda>s. 2^(pageBits +  us) \<le> gsMaxObjectSize s)
    and K (regionBase \<noteq> 0 \<and> range_cover regionBase (pageBits + us) (pageBits+us) (Suc 0)
    \<and>  {regionBase..+2^(pageBits +  us)} \<inter> kernel_data_refs = {}))
  ({s. region_actually_is_bytes regionBase (2^(pageBits+us)) s})
  hs
  (placeNewObject regionBase UserDataDevice us )
  (global_htd_update (\<lambda>s. (ptr_retyps (2^us) (Ptr regionBase :: user_data_device_C ptr))))"
  apply (rule ccorres_from_vcg_nofail)
  apply (clarsimp simp:)
  apply (rule conseqPre)
  apply vcg
  apply (clarsimp simp: rf_sr_htd_safe)
  apply (intro conjI allI impI)
   apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                         kernel_data_refs_domain_eq_rotate
                         ptr_retyps_htd_safe_neg[where arr=False, unfolded ptr_retyps_gen_def, simplified]
                         size_of_def pageBits_def power_add mult.commute mult.left_commute)
  apply (frule range_cover.unat_of_nat_shift[where gbits = "pageBits + us"])
    apply simp
   apply (clarsimp simp:size_of_def power_add pageBits_def
     rf_sr_def cstate_relation_def Let_def field_simps)
   apply blast
  apply (frule range_cover.aligned)
  apply (frule range_cover.sz(1), fold word_bits_def)
  apply (rule bexI [OF _ placeNewObject_eq], simp_all)
    apply (cut_tac ptr=regionBase and sz="pageBits + us" and gbits=us and arr=False
                in createObjects_ccorres_user_data_device[rule_format])
     apply (rule conjI, assumption, clarsimp)
     apply (fastforce simp: pageBits_def field_simps region_actually_is_bytes)
    apply (clarsimp elim!: rsubst[where P="\<lambda>x. (\<sigma>, x) \<in> rf_sr" for \<sigma>]
                     simp: field_simps objBitsKO_def ptr_retyps_gen_def)
   apply (simp add: objBitsKO_def field_simps)
  apply (rule no_fail_pre, rule no_fail_placeNewObject)
  apply (clarsimp simp: objBitsKO_def)
  done

lemma createObjects'_page_directory_at_global:
  "\<lbrace> \<lambda>s. n \<noteq> 0 \<and> range_cover ptr sz (objBitsKO val + gbits) n
      \<and> pspace_aligned' s \<and> pspace_distinct' s \<and> pspace_no_overlap' ptr sz s
      \<and> page_directory_at' (armKSGlobalPD (ksArchState s)) s \<rbrace>
    createObjects' ptr n val gbits
  \<lbrace> \<lambda>rv s. page_directory_at' (armKSGlobalPD (ksArchState s)) s \<rbrace>"
  apply (simp add: page_directory_at'_def)
  apply (rule hoare_pre, wp hoare_vcg_all_lift hoare_vcg_const_imp_lift)
   apply (wps createObjects'_ksArch)
   apply (wp createObjects'_typ_at[where sz=sz])
  apply simp
  done

lemma gsUserPages_update:
    "\<And>f. (\<lambda>s. s\<lparr>gsUserPages := f(gsUserPages s)\<rparr>) = gsUserPages_update f"
    by (rule ext) simp

lemma modify_gsUserPages_update:
  "modify (\<lambda>s. s\<lparr>gsUserPages := f(gsUserPages s)\<rparr>) = modify (gsUserPages_update f)"
  by (simp only: gsUserPages_update)

method arch_create_data_obj_corres_helper =
  (match conclusion in "ccorres ?rel ?var ?P ?P' ?hs
            (X64_H.createObject object_type.SmallPageObject ?regionBase sz ?deviceMemory)
            (Call Arch_createObject_'proc)
             " for sz \<Rightarrow> \<open>(simp add: toAPIType_def X64_H.createObject_def
                placeNewDataObject_def bind_assoc
               ),subst gsUserPages_update,((rule ccorres_gen_asm)+) \<close>)

lemma placeNewDataObject_ccorres:
  "ccorresG rf_sr \<Gamma> dc xfdc
  (createObject_hs_preconds regionBase newType us devMem
      and K (APIType_capBits newType us = pageBits + us))
  ({s. region_actually_is_bytes regionBase (2 ^ (pageBits + us)) s
      \<and> (\<not> devMem \<longrightarrow> heap_list_is_zero (hrs_mem (t_hrs_' (globals s))) regionBase
          (2 ^ (pageBits + us)))})
  hs
  (placeNewDataObject regionBase us devMem)
  (Cond {s. devMem}
    (global_htd_update (\<lambda>s. (ptr_retyps (2^us) (Ptr regionBase :: user_data_device_C ptr))))
    (global_htd_update (\<lambda>s. (ptr_retyps (2^us) (Ptr regionBase :: user_data_C ptr))))
  )"
  apply (cases devMem)
   apply (simp add: placeNewDataObject_def ccorres_cond_univ_iff)
   apply (rule ccorres_guard_imp, rule placeNewObject_user_data_device, simp_all)
   apply (clarsimp simp: createObject_hs_preconds_def invs'_def
                         valid_state'_def valid_pspace'_def)
  apply (simp add: placeNewDataObject_def ccorres_cond_empty_iff)
  apply (rule ccorres_guard_imp, rule placeNewObject_user_data, simp_all)
  apply (clarsimp simp: createObject_hs_preconds_def invs'_def
                        valid_state'_def valid_pspace'_def)
  apply (frule range_cover.sz(1), simp add: word_bits_def)
  done

lemma cond_second_eq_seq_ccorres:
  "ccorres_underlying sr Gamm r xf arrel axf G G' hs m
        (Cond P (a ;; c) (b ;; c) ;; d)
    = ccorres_underlying sr Gamm r xf arrel axf G G' hs m
        (Cond P a b ;; c ;; d)"
  apply (rule ccorres_semantic_equiv)
  apply (rule semantic_equivI)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.Seq exec.CondTrue exec.CondFalse)
  done

lemma cvariable_array_ptr_kill:
  "cvariable_array_map_relation m ns ptrfun htd
    \<Longrightarrow> cvariable_array_map_relation (m(x := None))
          ns (ptrfun :: _ \<Rightarrow> ('b :: mem_type) ptr) htd"
  by (clarsimp simp: cvariable_array_map_relation_def
              split: if_split)

lemma maptype_scast_mask_VMNoMap[simp]:
  "maptype_to_H (SCAST(32 signed \<rightarrow> 64) X86_MappingNone && 3) = VMNoMap"
  by (simp add: maptype_to_H_def X86_MappingNone_def)

lemma Mode_createObject_ccorres:
  assumes t: "toAPIType newType = None"
  shows "ccorres (\<lambda>a b. ccap_relation (ArchObjectCap a) b) ret__struct_cap_C_'
     (createObject_hs_preconds regionBase newType userSize deviceMemory)
     (createObject_c_preconds regionBase newType userSize deviceMemory)
     []
     (Arch.createObject newType regionBase userSize deviceMemory)
     (Call Mode_createObject_'proc)"
proof -
  note if_cong[cong]
  note sign_extend_canonical_address[simp]

  show ?thesis
    apply (clarsimp simp: createObject_c_preconds_def
                          createObject_hs_preconds_def)
    apply (rule ccorres_gen_asm)
    apply clarsimp
    apply (frule range_cover.aligned)
    apply (cut_tac t)
    apply (case_tac newType; simp add: toAPIType_def bind_assoc)
          apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
           apply (simp add: object_type_from_H_def Kernel_C_defs)
           apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff
                            asidInvalid_def
                            APIType_capBits_def shiftL_nat objBits_simps
                            ptBits_def archObjSize_def pageBits_def word_sle_def word_sless_def
                            fold_eq_0_to_bool)
           apply (clarsimp simp: hrs_htd_update ptBits_def objBits_simps archObjSize_def
                                 X64_H.createObject_def pageBits_def
                                 cond_second_eq_seq_ccorres modify_gsUserPages_update
                                 intro!: ccorres_rhs_assoc)
           apply ((rule ccorres_return_C | simp | wp | vcg
            | (rule match_ccorres, ctac add:
                    placeNewDataObject_ccorres[where us=0 and newType=newType, simplified]
                    gsUserPages_update_ccorres[folded modify_gsUserPages_update])
            | (rule match_ccorres, csymbr))+)[1]
          apply (intro conjI)
           apply (clarsimp simp: createObject_hs_preconds_def frameSizeConstants_defs
                                APIType_capBits_def pageBits_def)
          apply (clarsimp simp: pageBits_def ccap_relation_def APIType_capBits_def
                    framesize_to_H_def cap_to_H_simps cap_frame_cap_lift X86_SmallPage_def
                    vmrights_to_H_def mask_def vm_rights_defs c_valid_cap_def cl_valid_cap_def
                    vm_page_map_type_defs maptype_to_H_def)

        \<comment> \<open>Page objects: could possibly fix the duplication here\<close>
         apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
          apply (simp add: object_type_from_H_def Kernel_C_defs)
          apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff
                      asidInvalid_def
                       APIType_capBits_def shiftL_nat objBits_simps
                      ptBits_def archObjSize_def pageBits_def word_sle_def word_sless_def
                      fold_eq_0_to_bool)
          apply (clarsimp simp: hrs_htd_update ptBits_def objBits_simps archObjSize_def
            X64_H.createObject_def pageBits_def ptTranslationBits_def
            cond_second_eq_seq_ccorres modify_gsUserPages_update
            intro!: ccorres_rhs_assoc)
          apply ((rule ccorres_return_C | simp | wp | vcg
            | (rule match_ccorres, ctac add:
                    placeNewDataObject_ccorres[where us=9 and newType=newType, simplified]
                    gsUserPages_update_ccorres[folded modify_gsUserPages_update])
            | (rule match_ccorres, csymbr))+)[1]
         apply (intro conjI)
          apply (clarsimp simp: createObject_hs_preconds_def frameSizeConstants_defs ptTranslationBits_def
                                APIType_capBits_def pageBits_def)
         apply (clarsimp simp: pageBits_def ccap_relation_def APIType_capBits_def
                    framesize_to_H_def cap_to_H_simps cap_frame_cap_lift
                    X86_SmallPage_def X86_LargePage_def ptTranslationBits_def
                    vmrights_to_H_def mask_def vm_rights_defs c_valid_cap_def cl_valid_cap_def
                    vm_page_map_type_defs maptype_to_H_def)

        apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
         apply (simp add: object_type_from_H_def Kernel_C_defs)
         apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff
                      asidInvalid_def
                       APIType_capBits_def shiftL_nat objBits_simps
                      ptBits_def archObjSize_def pageBits_def word_sle_def word_sless_def
                      fold_eq_0_to_bool)
         apply (clarsimp simp: hrs_htd_update ptBits_def objBits_simps archObjSize_def
            X64_H.createObject_def pageBits_def ptTranslationBits_def
            cond_second_eq_seq_ccorres modify_gsUserPages_update
            intro!: ccorres_rhs_assoc)
         apply ((rule ccorres_return_C | simp | wp | vcg
            | (rule match_ccorres, ctac add:
                    placeNewDataObject_ccorres[where us=18 and newType=newType, simplified]
                    gsUserPages_update_ccorres[folded modify_gsUserPages_update])
            | (rule match_ccorres, csymbr))+)[1]
        apply (intro conjI)
         apply (clarsimp simp: createObject_hs_preconds_def frameSizeConstants_defs ptTranslationBits_def
                               APIType_capBits_def pageBits_def)
        apply (clarsimp simp: pageBits_def ccap_relation_def APIType_capBits_def
                    framesize_to_H_def cap_to_H_simps cap_frame_cap_lift
                    X86_SmallPage_def X86_LargePage_def X64_HugePage_def ptTranslationBits_def
                    vmrights_to_H_def mask_def vm_rights_defs c_valid_cap_def cl_valid_cap_def
                    vm_page_map_type_defs maptype_to_H_def)

       \<comment> \<open>PageTableObject\<close>
       apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
        apply (simp add: object_type_from_H_def Kernel_C_defs)
        apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff
                         asidInvalid_def
                         sle_positive APIType_capBits_def shiftL_nat objBits_simps
                         ptBits_def archObjSize_def pageBits_def word_sle_def word_sless_def)
        apply (rule ccorres_rhs_assoc)+
        apply (clarsimp simp: hrs_htd_update ptBits_def objBits_simps archObjSize_def
                              X64_H.createObject_def pageBits_def pt_bits_def table_size)
        apply (ctac pre only: add: placeNewObject_pte[simplified ptTranslationBits_def])
          apply csymbr
          apply (rule ccorres_return_C)
            apply simp
           apply simp
          apply simp
         apply wp
        apply vcg
       apply clarify
       apply (intro conjI)
        apply (clarsimp simp: invs_pspace_aligned' invs_pspace_distinct' invs_valid_global'
                              APIType_capBits_def invs_queues invs_valid_objs'
                              invs_urz pageBits_def)
       apply clarsimp
       apply (clarsimp simp: pageBits_def ccap_relation_def APIType_capBits_def
                             framesize_to_H_def cap_to_H_simps cap_page_table_cap_lift
                             vmrights_to_H_def)
       apply (clarsimp simp: isFrameType_def)

      \<comment> \<open>PageDirectoryObject\<close>
      apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
       apply (simp add: object_type_from_H_def Kernel_C_defs)
       apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff
                asidInvalid_def sle_positive APIType_capBits_def shiftL_nat
                objBits_simps archObjSize_def
                ptBits_def pageBits_def pdBits_def word_sle_def word_sless_def)
       apply (rule ccorres_rhs_assoc)+
       apply (clarsimp simp: hrs_htd_update ptBits_def objBits_simps archObjSize_def
                           X64_H.createObject_def bit_simps)
       apply (ctac pre only: add: placeNewObject_pde[simplified ptTranslationBits_def])
         apply csymbr
         apply (rule ccorres_return_C)
           apply simp
          apply simp
         apply simp
        apply wp
       apply vcg
      apply clarify
      apply (intro conjI)
       apply (clarsimp simp: invs_pspace_aligned' invs_pspace_distinct' invs_valid_global'
                             APIType_capBits_def invs_queues invs_valid_objs'
                             invs_urz bit_simps)
      apply clarsimp
      apply (clarsimp simp: ccap_relation_def APIType_capBits_def
                            framesize_to_H_def cap_to_H_simps cap_page_directory_cap_lift
                            vmrights_to_H_def bit_simps)
      apply (clarsimp simp: isFrameType_def)

     \<comment> \<open>PDPointerTableObject\<close>
     apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
      apply (simp add: object_type_from_H_def Kernel_C_defs)
      apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff
                asidInvalid_def sle_positive APIType_capBits_def shiftL_nat
                objBits_simps archObjSize_def
                ptBits_def pageBits_def pdBits_def word_sle_def word_sless_def)
      apply (rule ccorres_rhs_assoc)+
      apply (clarsimp simp: hrs_htd_update ptBits_def objBits_simps archObjSize_def
                            X64_H.createObject_def bit_simps)
      apply (ctac pre only: add: placeNewObject_pdpte[simplified ptTranslationBits_def])
        apply csymbr
        apply (rule ccorres_return_C)
          apply simp
         apply simp
        apply simp
       apply wp
      apply vcg
     apply clarify
     apply (intro conjI)
      apply (clarsimp simp: invs_pspace_aligned' invs_pspace_distinct' invs_valid_global'
                            APIType_capBits_def invs_queues invs_valid_objs' invs_urz bit_simps)
     apply clarsimp
     apply (clarsimp simp: ccap_relation_def APIType_capBits_def
                           framesize_to_H_def cap_to_H_simps cap_pdpt_cap_lift
                           vmrights_to_H_def bit_simps)
     apply (clarsimp simp: isFrameType_def)

    \<comment> \<open>PML4Object\<close>
    apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
     apply (simp add: object_type_from_H_def Kernel_C_defs)
     apply (simp add: ccorres_cond_univ_iff ccorres_cond_empty_iff
                asidInvalid_def sle_positive APIType_capBits_def shiftL_nat
                objBits_simps archObjSize_def
                ptBits_def pageBits_def pdBits_def word_sle_def word_sless_def)
     apply (rule ccorres_rhs_assoc)+
     apply (clarsimp simp: hrs_htd_update ptBits_def objBits_simps archObjSize_def
                           X64_H.createObject_def bit_simps)
     apply (ctac pre only: add: placeNewObject_pml4e[simplified ptTranslationBits_def])
       apply (ctac add: copyGlobalMappings_ccorres)
         apply csymbr
         apply (rule ccorres_return_C)
           apply simp
          apply simp
         apply simp
        apply wp
       apply (vcg exspec=copyGlobalMappings_modifies)
      apply (wp placeNewObject_pml4_at'[simplified bitSimps objBits_simps archObjSize_def, simplified])
     apply vcg
    apply clarify
    apply (intro conjI)
     apply (clarsimp simp: invs_pspace_aligned' invs_pspace_distinct' invs_valid_global'
                           APIType_capBits_def invs_queues invs_valid_objs' invs_urz bit_simps)
    apply clarsimp
    apply (clarsimp simp: ccap_relation_def APIType_capBits_def
                          framesize_to_H_def cap_to_H_simps cap_pml4_cap_lift
                          vmrights_to_H_def bit_simps)
    apply (clarsimp simp: isFrameType_def c_valid_cap_def cl_valid_cap_def asidInvalid_def)
    done
qed


lemma Arch_createObject_ccorres:
  assumes t: "toAPIType newType = None"
  shows "ccorres (\<lambda>a b. ccap_relation (ArchObjectCap a) b) ret__struct_cap_C_'
     (createObject_hs_preconds regionBase newType userSize deviceMemory)
     (createObject_c_preconds regionBase newType userSize deviceMemory)
     []
     (Arch.createObject newType regionBase userSize deviceMemory)
     (Call Arch_createObject_'proc)"
  apply (clarsimp simp: createObject_c_preconds_def createObject_hs_preconds_def)
  apply (rule ccorres_gen_asm)
  apply clarsimp
  apply (frule range_cover.aligned)
  apply (cut_tac t)
  apply (cinit' lift: t_' regionBase_' userSize_' deviceMemory_')
   apply (subst bind_return[symmetric])
   apply (ctac add: Mode_createObject_ccorres)
     apply (rule ccorres_return_C; simp)
    apply wp
   apply (vcg exspec=Mode_createObject_modifies)
  apply (simp add: createObject_c_preconds_def createObject_hs_preconds_def)
  done

(* FIXME: with the current state of affairs, we could simplify gs_new_cnodes *)
lemma gsCNodes_update_ccorres:
  "ccorresG rf_sr G dc xf (\<lambda>_. bits = sz + 4)
        \<lbrace> h_t_array_valid (hrs_htd \<acute>t_hrs) (cte_Ptr ptr) (2 ^ sz) \<rbrace> hs
     (modify (gsCNodes_update (\<lambda>m a. if a = ptr then Some sz else m a)))
     (Basic (globals_update (ghost'state_'_update
                  (gs_new_cnodes sz ptr bits))))"
  apply (rule ccorres_from_vcg)
  apply vcg_step
  apply (clarsimp simp: split_def simpler_modify_def gs_new_cnodes_def)
  apply (case_tac "ghost'state_' (globals x)")
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def fun_upd_def
                        carch_state_relation_def cmachine_state_relation_def
                        ghost_size_rel_def ghost_assertion_data_get_def
                 cong: if_cong)
  apply (rule cvariable_array_ptr_upd[unfolded fun_upd_def], simp_all)
  done

(* FIXME: move *)
lemma map_to_tcbs_upd:
  "map_to_tcbs (ksPSpace s(t \<mapsto> KOTCB tcb')) = map_to_tcbs (ksPSpace s)(t \<mapsto> tcb')"
  apply (rule ext)
  apply (clarsimp simp: map_comp_def projectKOs split: option.splits if_splits)
  done

(* FIXME: move *)
lemma cmap_relation_updI:
  "\<lbrakk>cmap_relation am cm f rel; am dest = Some ov; rel nv nv'; inj f\<rbrakk> \<Longrightarrow> cmap_relation (am(dest \<mapsto> nv)) (cm(f dest \<mapsto> nv')) f rel"
  apply (clarsimp simp: cmap_relation_def)
  apply (rule conjI)
   apply (drule_tac t="dom cm" in sym)
   apply fastforce
  apply clarsimp
  apply (case_tac "x = dest")
   apply simp
  apply clarsimp
  apply (subgoal_tac "f x \<noteq> f dest")
   apply simp
   apply force
  apply clarsimp
  apply (drule (1) injD)
  apply simp
  done

lemma cep_relations_drop_fun_upd:
  "\<lbrakk> f x = Some v; tcbEPNext_C v' = tcbEPNext_C v; tcbEPPrev_C v' = tcbEPPrev_C v \<rbrakk>
      \<Longrightarrow> cendpoint_relation (f (x \<mapsto> v')) = cendpoint_relation f"
  "\<lbrakk> f x = Some v; tcbEPNext_C v' = tcbEPNext_C v; tcbEPPrev_C v' = tcbEPPrev_C v \<rbrakk>
      \<Longrightarrow> cnotification_relation (f (x \<mapsto> v')) = cnotification_relation f"
  by (intro ext cendpoint_relation_upd_tcb_no_queues[where thread=x]
                cnotification_relation_upd_tcb_no_queues[where thread=x]
          | simp split: if_split)+

lemma threadSet_domain_ccorres [corres]:
  "ccorres dc xfdc
           (tcb_at' thread)
           {s. thread' s = tcb_ptr_to_ctcb_ptr thread \<and> d' s = ucast d} hs
           (threadSet (tcbDomain_update (\<lambda>_. d)) thread)
           (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_mem_update (heap_update (Ptr &(thread' s\<rightarrow>[''tcbDomain_C''])::machine_word ptr) (d' s)))) s))"
  apply (rule ccorres_guard_imp2)
   apply (rule threadSet_ccorres_lemma4 [where P=\<top> and P'=\<top>])
    apply vcg
   prefer 2
   apply (rule conjI, simp)
   apply assumption
  apply clarsimp
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  apply (clarsimp simp: cmachine_state_relation_def carch_state_relation_def cpspace_relation_def
                        fpu_null_state_heap_update_tag_disj_simps)
  apply (clarsimp simp: update_tcb_map_tos typ_heap_simps')
  apply (simp add: map_to_ctes_upd_tcb_no_ctes map_to_tcbs_upd tcb_cte_cases_def)
  apply (simp add: cep_relations_drop_fun_upd
                   cvariable_relation_upd_const ko_at_projectKO_opt)
  apply (rule conjI)
   apply (drule ko_at_projectKO_opt)
   apply (erule (2) cmap_relation_upd_relI)
     subgoal by (simp add: ctcb_relation_def)
    apply assumption
   apply simp
  apply (erule cready_queues_relation_not_queue_ptrs)
   apply (rule ext, simp split: if_split)
  apply (rule ext, simp split: if_split)
  done

lemma createObject_ccorres:
  notes APITypecapBits_simps[simp] =
          APIType_capBits_def[split_simps
          object_type.split apiobject_type.split]
  shows
    "ccorres ccap_relation ret__struct_cap_C_'
     (createObject_hs_preconds regionBase newType userSize isdev)
     (createObject_c_preconds regionBase newType userSize isdev)
     []
     (createObject newType regionBase userSize isdev)
     (Call createObject_'proc)"
proof -
  note if_cong[cong]

  have canonical_tcb_offset[simp]:
    "\<lbrakk> canonical_address regionBase; is_aligned regionBase 11\<rbrakk>
       \<Longrightarrow> sign_extend 47 (regionBase + 0x400) - 0x400 = regionBase"
    apply (drule canonical_address_add[where f="0x400"]; simp?)
    apply (simp add: sign_extend_canonical_address[symmetric])
    done

  have aligned_and: "\<And>p. is_aligned p 1 \<Longrightarrow> p && 0xFFFFFFFFFFFFFFFE = (p::machine_word)"
    by word_bitwise (simp add: is_aligned_nth)

  have gsCNodes_update:
    "\<And>f. (\<lambda>ks. ks \<lparr>gsCNodes := f (gsCNodes ks)\<rparr>) = gsCNodes_update f"
    by (rule ext) simp

  show ?thesis
  apply (clarsimp simp: createObject_c_preconds_def
                        createObject_hs_preconds_def)
  apply (rule ccorres_gen_asm_state)
  apply (cinit lift: t_' regionBase_' userSize_' deviceMemory_')
   apply (rule ccorres_cond_seq)
   (* Architecture specific objects. *)
   apply (rule_tac
            Q="createObject_hs_preconds regionBase newType userSize isdev" and
            S="createObject_c_preconds1 regionBase newType userSize isdev" and
            R="createObject_hs_preconds regionBase newType userSize isdev" and
            T="createObject_c_preconds1 regionBase newType userSize isdev"
            in ccorres_Cond_rhs)
    apply (subgoal_tac "toAPIType newType = None")
     apply clarsimp
     apply (rule ccorres_rhs_assoc)+
     apply (rule ccorres_guard_imp)
       apply (ctac (no_vcg) add: Arch_createObject_ccorres)
        apply (rule ccorres_return_C_Seq)
        apply (rule ccorres_return_C)
          apply clarsimp
         apply clarsimp
        apply clarsimp
       apply wp[1]
      apply clarsimp
     apply (clarsimp simp: createObject_c_preconds_def
                           region_actually_is_bytes
                           region_actually_is_bytes_def)
    apply (clarsimp simp: object_type_from_H_def
                          X64_H.toAPIType_def Kernel_C_defs
                          nAPIObjects_def word_sle_def createObject_c_preconds_def
                          word_le_nat_alt split:
                          apiobject_type.splits object_type.splits)
   apply (subgoal_tac "\<exists>apiType. newType = APIObjectType apiType")
    apply clarsimp
    apply (rule ccorres_guard_imp)
      apply (rule_tac apiType=apiType in ccorres_apiType_split)

          (* Untyped *)
          apply (clarsimp simp: Kernel_C_defs object_type_from_H_def
                                X64_H.toAPIType_def nAPIObjects_def
                                word_sle_def
                        intro!: Corres_UL_C.ccorres_cond_empty
                                Corres_UL_C.ccorres_cond_univ ccorres_rhs_assoc)
          apply (rule_tac
                   A ="createObject_hs_preconds regionBase
                         (APIObjectType apiobject_type.Untyped)
                          (unat (userSizea :: machine_word)) isdev" and
                   A'=UNIV in
                   ccorres_guard_imp)
            apply (rule ccorres_symb_exec_r)
              apply (rule ccorres_return_C, simp, simp, simp)
             apply vcg
            apply (rule conseqPre, vcg, clarsimp)
           apply simp
          apply (clarsimp simp: ccap_relation_def cap_to_H_def
                                getObjectSize_def apiGetObjectSize_def cap_untyped_cap_lift
                                aligned_add_aligned sign_extend_canonical_address
                         split: option.splits)
          apply (subst word_le_mask_eq, clarsimp simp: mask_def, unat_arith,
                 auto simp: word_bits_conv untypedBits_defs)[1]

         (* TCB *)
         apply (clarsimp simp: Kernel_C_defs object_type_from_H_def
                               toAPIType_def nAPIObjects_def word_sle_def
                       intro!: Corres_UL_C.ccorres_cond_empty
                               Corres_UL_C.ccorres_cond_univ ccorres_rhs_assoc)
         apply (rule_tac
                  A ="createObject_hs_preconds regionBase
                        (APIObjectType apiobject_type.TCBObject) (unat userSizea) isdev" and
                  A'="createObject_c_preconds1 regionBase
                        (APIObjectType apiobject_type.TCBObject) (unat userSizea) isdev" in
                  ccorres_guard_imp2)
          apply (rule ccorres_symb_exec_r)
            apply (ccorres_remove_UNIV_guard)
            apply (simp add: hrs_htd_update)
            apply (ctac (c_lines 4) add: ccorres_placeNewObject_tcb[simplified])
              apply simp
              apply (rule ccorres_pre_curDomain)
              apply ctac
                apply (rule ccorres_symb_exec_r)
                  apply (rule ccorres_return_C, simp, simp, simp)
                 apply vcg
                apply (rule conseqPre, vcg, clarsimp)
               apply wp
              apply vcg
             apply (simp add: obj_at'_real_def)
             apply (wp placeNewObject_ko_wp_at')
            apply (vcg exspec=Arch_initContext_modifies)
           apply clarsimp
           apply vcg
          apply (rule conseqPre, vcg, clarsimp)
         apply (clarsimp simp: createObject_hs_preconds_def
                               createObject_c_preconds_def)
         apply (frule invs_pspace_aligned')
         apply (frule invs_pspace_distinct')
         apply (frule invs_queues)
         apply (frule invs_sym')
         apply (simp add: getObjectSize_def objBits_simps word_bits_conv
                          apiGetObjectSize_def
                          tcbBlockSizeBits_def new_cap_addrs_def projectKO_opt_tcb)
         apply (clarsimp simp: range_cover.aligned
                               region_actually_is_bytes_def APIType_capBits_def)
         apply (frule(1) ghost_assertion_size_logic_no_unat)
         apply (clarsimp simp: ccap_relation_def cap_to_H_def
                               getObjectSize_def apiGetObjectSize_def
                               cap_thread_cap_lift
                               aligned_add_aligned
                        split: option.splits)
         apply (frule range_cover.aligned)
         apply (clarsimp simp: ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs
                               tcb_ptr_to_ctcb_ptr_def
                               invs_valid_objs' invs_urz isFrameType_def)

        (* Endpoint *)
        apply (clarsimp simp: Kernel_C_defs object_type_from_H_def
                              toAPIType_def nAPIObjects_def word_sle_def
                      intro!: ccorres_cond_empty ccorres_cond_univ ccorres_rhs_assoc)
        apply (rule_tac
                 A ="createObject_hs_preconds regionBase
                       (APIObjectType apiobject_type.EndpointObject)
                       (unat (userSizea :: machine_word)) isdev" and
                 A'="createObject_c_preconds1 regionBase
                       (APIObjectType apiobject_type.EndpointObject)
                       (unat userSizea) isdev" in
                 ccorres_guard_imp2)
         apply (simp add: hrs_htd_update)
         apply (ctac (no_vcg) pre only: add: ccorres_placeNewObject_endpoint)
           apply (rule ccorres_symb_exec_r)
             apply (rule ccorres_return_C, simp, simp, simp)
            apply vcg
           apply (rule conseqPre, vcg, clarsimp)
          apply wp
         apply (clarsimp simp: ccap_relation_def cap_to_H_def getObjectSize_def
                               objBits_simps apiGetObjectSize_def epSizeBits_def
                               cap_endpoint_cap_lift sign_extend_canonical_address
                        split: option.splits
                        dest!: range_cover.aligned)
        apply (clarsimp simp: createObject_hs_preconds_def isFrameType_def)
        apply (frule invs_pspace_aligned')
        apply (frule invs_pspace_distinct')
        apply (frule invs_queues)
        apply (frule invs_sym')
        apply (auto simp: getObjectSize_def objBits_simps apiGetObjectSize_def
                          epSizeBits_def word_bits_conv
                   elim!: is_aligned_no_wrap'
                  intro!: range_cover_simpleI)[1]

       (* Notification *)
       apply (clarsimp simp: createObject_c_preconds_def)
       apply (clarsimp simp: getObjectSize_def objBits_simps apiGetObjectSize_def
                             epSizeBits_def word_bits_conv word_sle_def word_sless_def)
       apply (clarsimp simp: Kernel_C_defs object_type_from_H_def
                             toAPIType_def nAPIObjects_def word_sle_def
                     intro!: ccorres_cond_empty ccorres_cond_univ ccorres_rhs_assoc)
       apply (rule_tac
                A ="createObject_hs_preconds regionBase
                      (APIObjectType apiobject_type.NotificationObject)
                      (unat (userSizea :: machine_word)) isdev" and
                A'="createObject_c_preconds1 regionBase
                      (APIObjectType apiobject_type.NotificationObject)
                      (unat userSizea) isdev" in
                ccorres_guard_imp2)
        apply (simp add: hrs_htd_update)
        apply (ctac (no_vcg) pre only: add: ccorres_placeNewObject_notification)
          apply (rule ccorres_symb_exec_r)
            apply (rule ccorres_return_C, simp, simp, simp)
           apply vcg
          apply (rule conseqPre, vcg, clarsimp)
         apply wp
        apply (clarsimp simp: ccap_relation_def cap_to_H_def
                              getObjectSize_def sign_extend_canonical_address
                              apiGetObjectSize_def ntfnSizeBits_def objBits_simps
                              cap_notification_cap_lift
                       dest!: range_cover.aligned
                       split: option.splits)
       apply (clarsimp simp: createObject_hs_preconds_def isFrameType_def)
       apply (frule invs_pspace_aligned')
       apply (frule invs_pspace_distinct')
       apply (frule invs_queues)
       apply (frule invs_sym')
       apply (auto simp: getObjectSize_def objBits_simps
                         apiGetObjectSize_def
                         ntfnSizeBits_def word_bits_conv
                  elim!: is_aligned_no_wrap'
                 intro!: range_cover_simpleI)[1]

      (* CapTable *)
      apply (clarsimp simp: createObject_c_preconds_def)
      apply (clarsimp simp: getObjectSize_def objBits_simps
                  apiGetObjectSize_def
                  ntfnSizeBits_def word_bits_conv)
      apply (clarsimp simp: Kernel_C_defs object_type_from_H_def
                            toAPIType_def nAPIObjects_def
                            word_sle_def word_sless_def zero_le_sint
                    intro!: ccorres_cond_empty ccorres_cond_univ ccorres_rhs_assoc
                            ccorres_move_c_guards ccorres_Guard_Seq)
      apply (rule_tac
               A ="createObject_hs_preconds regionBase
                     (APIObjectType apiobject_type.CapTableObject)
                     (unat (userSizea :: machine_word)) isdev" and
               A'="createObject_c_preconds1 regionBase
                     (APIObjectType apiobject_type.CapTableObject)
                     (unat userSizea) isdev" in
               ccorres_guard_imp2)
       apply (simp add:field_simps hrs_htd_update)
       apply (ctac pre only: add: ccorres_placeNewObject_captable)
         apply (subst gsCNodes_update)
         apply (ctac add: gsCNodes_update_ccorres)
           apply (rule ccorres_symb_exec_r)
             apply (rule ccorres_return_C, simp, simp, simp)
            apply vcg
           apply (rule conseqPre, vcg, clarsimp)
          apply (rule hoare_triv[of \<top>], simp add:hoare_TrueI)
         apply vcg
        apply wp
       apply vcg
      apply (rule conjI)
       apply (clarsimp simp: createObject_hs_preconds_def isFrameType_def)
       apply (frule invs_pspace_aligned')
       apply (frule invs_pspace_distinct')
       apply (frule invs_queues)
       apply (frule invs_sym')
       apply (frule(1) ghost_assertion_size_logic_no_unat)
       apply (clarsimp simp: getObjectSize_def objBits_simps
                             apiGetObjectSize_def
                             cteSizeBits_def word_bits_conv add.commute createObject_c_preconds_def
                             region_actually_is_bytes_def
                             invs_valid_objs' invs_urz
                      elim!: is_aligned_no_wrap'
                       dest: word_of_nat_le
                     intro!: range_coverI)
      apply (clarsimp simp: createObject_hs_preconds_def hrs_htd_update isFrameType_def)
      apply (frule range_cover.strong_times_64[folded addr_card_wb], simp+)
      apply (subst h_t_array_valid_retyp, simp+)
       apply (simp add: power_add cte_C_size cteSizeBits_def)
      apply (clarsimp simp: ccap_relation_def cap_to_H_def cap_cnode_cap_lift
                            getObjectSize_def apiGetObjectSize_def cteSizeBits_def
                            objBits_simps field_simps is_aligned_power2
                            addr_card_wb is_aligned_weaken[where y=2]
                            is_aligned_neg_mask_weaken
                     split: option.splits)
      apply (rule conjI)
       apply (frule range_cover.aligned)
       apply (simp add: aligned_and is_aligned_weaken sign_extend_canonical_address)
      apply (subst word_le_mask_eq[symmetric, THEN eqTrueI])
        apply (clarsimp simp: mask_def untypedBits_defs)
        apply unat_arith
       apply (clarsimp simp: word_bits_conv)
      apply simp
     apply auto[1]
    apply (clarsimp simp: createObject_c_preconds_def)
    apply (clarsimp simp:nAPIOBjects_object_type_from_H)?
    apply (intro impI conjI, simp_all)[1]
   apply (clarsimp simp: nAPIObjects_def object_type_from_H_def Kernel_C_defs
                  split: object_type.splits)
  apply (clarsimp simp: createObject_c_preconds_def
                        createObject_hs_preconds_def)
  done
qed

lemma ccorres_guard_impR:
  "\<lbrakk>ccorres_underlying sr \<Gamma> r xf arrel axf W Q' hs f g; (\<And>s s'. \<lbrakk>(s, s') \<in> sr; s' \<in> A'\<rbrakk> \<Longrightarrow> s' \<in> Q')\<rbrakk>
  \<Longrightarrow> ccorres_underlying sr \<Gamma> r xf arrel axf W A' hs f g"
  by (rule ccorres_guard_imp2,simp+)

lemma typ_clear_region_dom:
 "dom (clift (hrs_htd_update (typ_clear_region ptr bits) hp) :: 'b :: mem_type typ_heap)
  \<subseteq>  dom ((clift hp) :: 'b :: mem_type typ_heap)"
   apply (clarsimp simp:lift_t_def lift_typ_heap_def comp_def)
   apply (clarsimp simp:lift_state_def)
   apply (case_tac hp)
   apply (clarsimp simp:)
   apply (case_tac x)
   apply (clarsimp simp:s_valid_def h_t_valid_def)
    apply (clarsimp simp:valid_footprint_def Let_def)
    apply (drule spec)
    apply (erule(1) impE)
   apply clarsimp
   apply (rule conjI)
    apply (clarsimp simp add:map_le_def)
    apply (drule_tac x = aa in bspec)
     apply simp
    apply (drule sym)
     apply simp
    apply (clarsimp simp:proj_d_def)
    apply (clarsimp simp:hrs_htd_update_def typ_clear_region_def
     split:if_splits option.splits)
   apply (clarsimp simp:proj_d_def)
   apply (clarsimp simp:hrs_htd_update_def typ_clear_region_def
     split:if_splits option.splits)
  done

lemma tcb_range_subseteq:
  "is_aligned x (objBitsKO (KOTCB ko))
   \<Longrightarrow> {ptr_val (tcb_ptr_to_ctcb_ptr x)..+size_of TYPE(tcb_C)} \<subseteq> {x..x + 2 ^ objBitsKO (KOTCB ko) - 1}"
  apply (simp add:ptr_val_def tcb_ptr_to_ctcb_ptr_def)
  apply (rule subset_trans)
  apply (rule intvl_sub_offset[where z = "2^objBitsKO (KOTCB ko)"])
   apply (simp add:ctcb_offset_defs size_of_def objBits_simps')
   apply (subst intvl_range_conv)
     apply simp
    apply (simp add:objBits_simps' word_bits_conv)
   apply simp
  done

lemma pspace_no_overlap_induce_tcb:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state))
      (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::tcb_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
   \<Longrightarrow> {ptr_val xa..+size_of TYPE(tcb_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp:cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def)
  apply (subgoal_tac "xa\<in>tcb_ptr_to_ctcb_ptr ` dom (map_to_tcbs (ksPSpace s))")
    prefer 2
    apply (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp: image_def projectKO_opt_tcb map_comp_def
                 split: option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
  apply (rule disjoint_subset[OF tcb_range_subseteq[simplified]])
   apply (erule(1) pspace_alignedD')
  apply (subst intvl_range_conv)
   apply (simp add: word_bits_def)+
  done

lemma pspace_no_overlap_induce_endpoint:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state))
      (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::endpoint_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
   \<Longrightarrow> {ptr_val xa..+size_of TYPE(endpoint_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp: cpspace_relation_def)
  apply (clarsimp simp: cmap_relation_def)
  apply (subgoal_tac "xa\<in>ep_Ptr ` dom (map_to_eps (ksPSpace s))")
   prefer 2
   subgoal by (simp add: domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp: image_def projectKO_opt_ep map_comp_def
                 split: option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
  apply (subst intvl_range_conv)
    apply simp
   apply (simp add: word_bits_def)
  apply (simp add: size_of_def)
  apply (subst intvl_range_conv[where bits = epSizeBits,simplified epSizeBits_def, simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps' archObjSize_def
              split: arch_kernel_object.split_asm)
   apply (simp add: word_bits_conv)
  apply (simp add: objBits_simps' archObjSize_def
            split: arch_kernel_object.split_asm)
  done

lemma pspace_no_overlap_induce_notification:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state))
      (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::notification_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
   \<Longrightarrow> {ptr_val xa..+size_of TYPE(notification_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp: cpspace_relation_def)
  apply (clarsimp simp: cmap_relation_def size_of_def)
  apply (subgoal_tac "xa\<in>ntfn_Ptr ` dom (map_to_ntfns (ksPSpace s))")
   prefer 2
   apply (simp add: domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp: image_def projectKO_opt_ntfn map_comp_def
                 split: option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
  apply (subst intvl_range_conv)
    apply simp
   apply (simp add: word_bits_def)
  apply (subst intvl_range_conv[where bits = ntfnSizeBits,simplified ntfnSizeBits_def, simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps' archObjSize_def
              split: arch_kernel_object.split_asm)
   apply (simp add: word_bits_conv)
  apply (simp add: objBits_simps' archObjSize_def
            split: arch_kernel_object.split_asm)
  done

lemma ctes_of_ko_at_strong:
  "\<lbrakk>ctes_of s p = Some a;is_aligned p cteSizeBits\<rbrakk> \<Longrightarrow>
  (\<exists>ptr ko. (ksPSpace s ptr = Some ko \<and> {p ..+ 2^cteSizeBits} \<subseteq> obj_range' ptr ko))"
  apply (clarsimp simp: map_to_ctes_def Let_def split:if_split_asm)
   apply (intro exI conjI,assumption)
   apply (simp add:obj_range'_def objBits_simps is_aligned_no_wrap' field_simps)
   apply (subst intvl_range_conv[where bits = cteSizeBits,simplified])
     apply simp
    apply (simp add:word_bits_def objBits_simps')
   apply (simp add:field_simps)
  apply (intro exI conjI,assumption)
  apply (clarsimp simp:objBits_simps obj_range'_def word_and_le2)
  apply (cut_tac intvl_range_conv[where bits = cteSizeBits and ptr = p, simplified])
    defer
    apply simp
   apply (simp add:word_bits_conv objBits_simps')
  apply (intro conjI)
   apply (rule order_trans[OF word_and_le2])
   apply clarsimp
  apply clarsimp
  apply (thin_tac "P \<or> Q" for P Q)
  apply (erule order_trans)
  apply (subst word_plus_and_or_coroll2[where x = p and w = "mask tcbBlockSizeBits",symmetric])
  apply (clarsimp simp:tcb_cte_cases_def field_simps split:if_split_asm)
      apply (subst p_assoc_help)
      apply (rule word_plus_mono_right[OF _ is_aligned_no_wrap'])
        apply (simp add: objBits_simps')
       apply (rule Aligned.is_aligned_neg_mask)
       apply (rule le_refl,simp)
      apply (simp add: objBits_simps')
     apply (subst p_assoc_help)
     apply (rule word_plus_mono_right[OF _ is_aligned_no_wrap'])
       apply (simp add: objBits_simps')
      apply (rule Aligned.is_aligned_neg_mask)
      apply (rule le_refl,simp)
     apply (simp add: objBits_simps')
    apply (subst p_assoc_help)
    apply (rule word_plus_mono_right[OF _ is_aligned_no_wrap'])
    apply (simp add:objBits_simps')
     apply (rule Aligned.is_aligned_neg_mask)
     apply (rule le_refl,simp)
    apply (simp add: objBits_simps')
   apply (subst p_assoc_help)
   apply (rule word_plus_mono_right[OF _ is_aligned_no_wrap'])
     apply (simp add: objBits_simps')
    apply (rule Aligned.is_aligned_neg_mask)
    apply (rule le_refl,simp)
   apply (simp add: objBits_simps')
  apply (subst p_assoc_help)+
  apply (rule word_plus_mono_right[OF _ is_aligned_no_wrap'])
    apply (simp add: objBits_simps')
   apply (rule Aligned.is_aligned_neg_mask)
   apply (rule le_refl,simp)
  apply (simp add: objBits_simps')
  done

lemma pspace_no_overlap_induce_cte:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state))
      (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::cte_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
   \<Longrightarrow> {ptr_val xa..+size_of TYPE(cte_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp: cpspace_relation_def)
  apply (clarsimp simp: cmap_relation_def size_of_def)
  apply (subgoal_tac "xa\<in>cte_Ptr ` dom (ctes_of s)")
   prefer 2
   apply (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp: image_def projectKO_opt_cte map_comp_def
                 split: option.splits kernel_object.split_asm)
  apply (frule ctes_of_is_aligned)
  apply (simp add: objBits_simps)
  apply (drule ctes_of_ko_at_strong)
   apply simp
  apply (clarsimp simp: objBits_simps')
  apply (erule disjoint_subset)
  apply (frule(1) pspace_no_overlapD')
  apply (subst intvl_range_conv)
    apply simp
   apply (simp add: word_bits_def)
  apply (simp add: obj_range'_def)
  done

lemma pspace_no_overlap_induce_asidpool:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state)) (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::asid_pool_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
     \<Longrightarrow> {ptr_val xa..+size_of TYPE(asid_pool_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp:cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def size_of_def)
  apply (subgoal_tac "xa\<in>ap_Ptr ` dom (map_to_asidpools (ksPSpace s))")
    prefer 2
    apply (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp:image_def projectKO_opt_asidpool
    map_comp_def split:option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
   apply (subst intvl_range_conv)
     apply simp
    apply (simp add: word_bits_def)
   apply (subst intvl_range_conv[where bits = 12,simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def pageBits_def split:arch_kernel_object.split_asm)
    apply (clarsimp elim!:is_aligned_weaken)
  apply (simp only: is_aligned_neg_mask_eq)
  apply (erule disjoint_subset[rotated])
  apply (clarsimp simp: field_simps)
  apply (simp add: p_assoc_help)
   apply (rule word_plus_mono_right)
   apply (clarsimp simp:objBits_simps archObjSize_def pageBits_def split:arch_kernel_object.split_asm)+
  done

lemma pspace_no_overlap_induce_user_data:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state)) (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::user_data_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
     \<Longrightarrow> {ptr_val xa..+size_of TYPE(user_data_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp:cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def size_of_def)
  apply (subgoal_tac "xa\<in>Ptr ` dom (heap_to_user_data (ksPSpace s) (underlying_memory (ksMachineState s)))")
    prefer 2
    apply (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp: image_def heap_to_user_data_def projectKO_opt_user_data map_comp_def
                 split: option.splits kernel_object.splits)
  apply (frule(1) pspace_no_overlapD')
  apply (clarsimp simp: word_bits_def)
   apply (subst intvl_range_conv[where bits = 12,simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add:objBits_simps archObjSize_def pageBits_def split:arch_kernel_object.split_asm)
    apply (clarsimp elim!:is_aligned_weaken)
  apply (subst intvl_range_conv, simp, simp)
  apply (clarsimp simp: field_simps)
  apply (simp add: p_assoc_help)
  apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def split:arch_kernel_object.split_asm)+
  done

lemma pspace_no_overlap_induce_device_data:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state)) (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::user_data_device_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
     \<Longrightarrow> {ptr_val xa..+size_of TYPE(user_data_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp: cpspace_relation_def)
  apply (clarsimp simp: cmap_relation_def size_of_def)
  apply (subgoal_tac "xa\<in>Ptr ` dom (heap_to_device_data (ksPSpace s) (underlying_memory (ksMachineState s)))")
    prefer 2
    apply (simp add: domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp: image_def heap_to_device_data_def projectKO_opt_user_data_device map_comp_def
                 split: option.splits kernel_object.splits)
  apply (frule(1) pspace_no_overlapD')
  apply (clarsimp simp: word_bits_def)
   apply (subst intvl_range_conv[where bits = 12,simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def pageBits_def split: arch_kernel_object.split_asm)
    apply (clarsimp elim!: is_aligned_weaken)
  apply (subst intvl_range_conv, simp, simp)
  apply (clarsimp simp: field_simps)
  apply (simp add: p_assoc_help)
  apply (clarsimp simp: objBits_simps archObjSize_def pageBits_def split:arch_kernel_object.split_asm)+
  done

lemma typ_region_bytes_dom:
 "typ_uinfo_t TYPE('b) \<noteq> typ_uinfo_t TYPE (word8)
    \<Longrightarrow> dom (clift (hrs_htd_update (typ_region_bytes ptr bits) hp) :: 'b :: mem_type typ_heap)
  \<subseteq>  dom ((clift hp) :: 'b :: mem_type typ_heap)"
  apply (clarsimp simp: liftt_if split: if_splits)
  apply (case_tac "{ptr_val x ..+ size_of TYPE('b)} \<inter> {ptr ..+ 2 ^ bits} = {}")
   apply (clarsimp simp: h_t_valid_def valid_footprint_def Let_def
                         hrs_htd_update_def split_def typ_region_bytes_def)
   apply (drule spec, drule(1) mp)
   apply (simp add: size_of_def split: if_split_asm)
   apply (drule subsetD[OF equalityD1], rule IntI, erule intvlI, simp)
   apply simp
  apply (clarsimp simp: set_eq_iff)
  apply (drule(1) h_t_valid_intvl_htd_contains_uinfo_t)
  apply (clarsimp simp: hrs_htd_update_def typ_region_bytes_def split_def
                 split: if_split_asm)
  done

lemma lift_t_typ_region_bytes_none:
  "\<lbrakk> \<And>x (v :: 'a). lift_t g hp x = Some v
    \<Longrightarrow> {ptr_val x ..+ size_of TYPE('a)} \<inter> {ptr ..+ 2 ^ bits} = {};
     typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE(8 word) \<rbrakk> \<Longrightarrow>
  lift_t g (hrs_htd_update (typ_region_bytes ptr bits) hp)
    = (lift_t g hp :: (('a :: mem_type) ptr) \<Rightarrow> _)"
  apply atomize
  apply (subst lift_t_typ_region_bytes, simp_all)
   apply (clarsimp simp: liftt_if hrs_htd_def split: if_splits)
  apply (rule ext, simp add: restrict_map_def)
  apply (rule ccontr, clarsimp split: if_splits)
  apply (clarsimp simp: liftt_if hrs_htd_def split: if_splits)
  apply (clarsimp simp: set_eq_iff intvl_self)
  done

lemma typ_bytes_cpspace_relation_clift_userdata:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (user_data_C ptr \<rightharpoonup> user_data_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (rule pspace_no_overlap_induce_user_data[simplified], auto)
  done


lemma typ_bytes_cpspace_relation_clift_devicedata:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (user_data_device_C ptr \<rightharpoonup> user_data_device_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (rule pspace_no_overlap_induce_device_data[simplified], auto)
  done


lemma pspace_no_overlap_induce_pte:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state)) (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::pte_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
     \<Longrightarrow> {ptr_val xa..+size_of TYPE(pte_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp:cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def)
  apply (subgoal_tac "xa\<in>pte_Ptr ` dom (map_to_ptes (ksPSpace s))")
    prefer 2
    apply (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp: image_def projectKO_opt_pte map_comp_def
                 split: option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
   apply (subst intvl_range_conv)
     apply simp
    apply (simp add: word_bits_def)
   apply (subst intvl_range_conv[where bits = 3,simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)
   apply (simp add: word_bits_conv)
  apply (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)
  done

lemma pspace_no_overlap_induce_pde:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state)) (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::pde_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
     \<Longrightarrow> {ptr_val xa..+size_of TYPE(pde_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp:cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def)
  apply (subgoal_tac "xa\<in>pde_Ptr ` dom (map_to_pdes (ksPSpace s))")
    prefer 2
    subgoal by (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp:image_def projectKO_opt_pde
    map_comp_def split:option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
   apply (subst intvl_range_conv)
     apply simp
    apply (simp add: word_bits_def)
   apply (subst intvl_range_conv[where bits = 3,simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)
   apply (simp add:word_bits_conv)
  by (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)

lemma pspace_no_overlap_induce_pdpte:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state)) (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::pdpte_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
     \<Longrightarrow> {ptr_val xa..+size_of TYPE(pdpte_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp:cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def)
  apply (subgoal_tac "xa\<in>pdpte_Ptr ` dom (map_to_pdptes (ksPSpace s))")
    prefer 2
    subgoal by (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp:image_def projectKO_opt_pdpte
    map_comp_def split:option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
   apply (subst intvl_range_conv)
     apply simp
    apply (simp add: word_bits_def)
   apply (subst intvl_range_conv[where bits = 3,simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)
   apply (simp add:word_bits_conv)
  by (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)

lemma pspace_no_overlap_induce_pml4e:
  "\<lbrakk>cpspace_relation (ksPSpace (s::kernel_state)) (underlying_memory (ksMachineState s)) hp;
    pspace_aligned' s; clift hp xa = Some (v::pml4e_C);
    is_aligned ptr bits; bits < word_bits;
    pspace_no_overlap' ptr bits s\<rbrakk>
     \<Longrightarrow> {ptr_val xa..+size_of TYPE(pml4e_C)} \<inter> {ptr..+2 ^ bits} = {}"
  apply (clarsimp simp:cpspace_relation_def)
  apply (clarsimp simp:cmap_relation_def)
  apply (subgoal_tac "xa\<in>pml4e_Ptr ` dom (map_to_pml4es (ksPSpace s))")
    prefer 2
    subgoal by (simp add:domI)
  apply (thin_tac "S = dom K" for S K)+
  apply (thin_tac "\<forall>x\<in> S. K x" for S K)+
  apply (clarsimp simp:image_def projectKO_opt_pml4e
    map_comp_def split:option.splits kernel_object.split_asm)
  apply (frule(1) pspace_no_overlapD')
   apply (subst intvl_range_conv)
     apply simp
    apply (simp add: word_bits_def)
   apply (subst intvl_range_conv[where bits = 3,simplified])
    apply (drule(1) pspace_alignedD')
    apply (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)
   apply (simp add:word_bits_conv)
  by (simp add: objBits_simps archObjSize_def bit_simps split:arch_kernel_object.split_asm)


lemma typ_bytes_cpspace_relation_clift_tcb:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (tcb_C ptr \<rightharpoonup> tcb_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_tcb[simplified])
  done

lemma typ_bytes_cpspace_relation_clift_pml4e:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (pml4e_C ptr \<rightharpoonup> pml4e_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_pml4e[unfolded size_of_def,simplified])
  done

lemma typ_bytes_cpspace_relation_clift_pdpte:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (pdpte_C ptr \<rightharpoonup> pdpte_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_pdpte[unfolded size_of_def,simplified])
  done

lemma typ_bytes_cpspace_relation_clift_pde:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (pde_C ptr \<rightharpoonup> pde_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_pde[unfolded size_of_def,simplified])
  done

lemma typ_bytes_cpspace_relation_clift_pte:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (pte_C ptr \<rightharpoonup> pte_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_pte[unfolded size_of_def,simplified])
  done

lemma typ_bytes_cpspace_relation_clift_endpoint:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (endpoint_C ptr \<rightharpoonup> endpoint_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_endpoint[simplified])
  done

lemma typ_bytes_cpspace_relation_clift_notification:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (notification_C ptr \<rightharpoonup> notification_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_notification[simplified])
  done

lemma typ_bytes_cpspace_relation_clift_asid_pool:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (asid_pool_C ptr \<rightharpoonup> asid_pool_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none, simp_all)
  apply (erule(5) pspace_no_overlap_induce_asidpool[simplified])
  done

lemma typ_bytes_cpspace_relation_clift_cte:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "pspace_no_overlap' ptr bits s"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp) = ((clift hp) :: (cte_C ptr \<rightharpoonup> cte_C))"
  (is "?lhs = ?rhs")
  using assms
  apply -
  apply (rule lift_t_typ_region_bytes_none)
   apply (erule(5) pspace_no_overlap_induce_cte)
  apply (simp add: cte_C_size)
  done

lemma pspace_no_overlap_obj_atD':
  "obj_at' P p s \<Longrightarrow> pspace_no_overlap' ptr bits s
    \<Longrightarrow> \<exists>ko. P ko \<and> is_aligned p (objBitsKO (injectKOS ko))
        \<and> {p .. p + (2 ^ objBitsKO (injectKOS ko)) - 1}
            \<inter> {ptr .. (ptr && ~~ mask bits) + 2 ^ bits - 1} = {}"
  apply (clarsimp simp: obj_at'_def)
  apply (drule(1) pspace_no_overlapD')
  apply (clarsimp simp: projectKOs project_inject)
  apply auto
  done

lemma typ_bytes_cpspace_relation_clift_gptr:
assumes "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState (s::kernel_state))) hp"
  and "is_aligned ptr bits" "bits < word_bits"
  and "pspace_aligned' s"
  and "kernel_data_refs \<inter> {ptr ..+ 2^bits} = {}"
  and "ptr_span (ptr' :: 'a ptr) \<subseteq> kernel_data_refs"
  and "typ_uinfo_t TYPE('a :: mem_type) \<noteq> typ_uinfo_t TYPE(8 word)"
 shows "clift (hrs_htd_update (typ_region_bytes ptr bits) hp)
    ptr'
  = (clift hp) ptr'"
  (is "?lhs = ?rhs ptr'")
  using assms
  apply -
   apply (case_tac "ptr' \<notin> dom ?rhs")
   apply (frule contra_subsetD[OF typ_region_bytes_dom[where ptr = ptr and bits = bits], rotated])
    apply simp
   apply fastforce
  apply (clarsimp simp: liftt_if hrs_htd_update_def split_def split: if_splits)
  apply (simp add: h_t_valid_typ_region_bytes)
  apply blast
  done

lemma cmap_array_typ_region_bytes_triv[OF refl]:
  "ptrf = (Ptr :: _ \<Rightarrow> 'b ptr)
    \<Longrightarrow> carray_map_relation bits' (map_comp f (ksPSpace s)) (h_t_valid htd c_guard) ptrf
    \<Longrightarrow> is_aligned ptr bits
    \<Longrightarrow> pspace_no_overlap' ptr bits s
    \<Longrightarrow> pspace_aligned' s
    \<Longrightarrow> typ_uinfo_t TYPE('b :: c_type) \<noteq> typ_uinfo_t TYPE(8 word)
    \<Longrightarrow> size_of TYPE('b) = 2 ^ bits'
    \<Longrightarrow> objBitsT (koType TYPE('a :: pspace_storable)) \<le> bits
    \<Longrightarrow> objBitsT (koType TYPE('a :: pspace_storable)) \<le> bits'
    \<Longrightarrow> bits' < word_bits
    \<Longrightarrow> carray_map_relation bits' (map_comp (f :: _ \<Rightarrow> 'a option) (ksPSpace s))
        (h_t_valid (typ_region_bytes ptr bits htd) c_guard) ptrf"
  apply (frule(7) cmap_array_typ_region_bytes[where ptrf=ptrf])
  apply (subst(asm) restrict_map_subdom, simp_all)
  apply (drule(1) pspace_no_overlap_disjoint')
  apply (simp add: upto_intvl_eq)
  apply (rule order_trans[OF map_comp_subset_dom])
  apply auto
  done

lemma intvl_mult_is_union:
  "{p..+n * m} = (\<Union>i < m. {p + of_nat (i * n)..+ n})"
  apply (cases "n = 0")
   apply simp
  apply (simp add: intvl_def, safe, simp_all)
   apply (rule_tac x="k div n" in bexI)
    apply (rule_tac x="k mod n" in exI)
    apply (simp only: Abs_fnat_hom_mult Abs_fnat_hom_add, simp)
   apply (simp add: More_Divides.td_gal_lt[symmetric] mult.commute)
  apply (rule_tac x="xa * n + k" in exI, simp)
  apply (subst add.commute, rule order_less_le_trans, erule add_less_mono1)
  apply (case_tac m, simp_all)
  done

lemma h_t_array_first_element_at:
  "h_t_array_valid htd p n
    \<Longrightarrow> 0 < n
    \<Longrightarrow> gd p
    \<Longrightarrow> h_t_valid htd gd (p :: ('a :: wf_type) ptr)"
  apply (clarsimp simp: h_t_array_valid_def h_t_valid_def valid_footprint_def
                        Let_def CTypes.sz_nzero[unfolded size_of_def])
  apply(drule_tac x="y" in spec, erule impE)
   apply (erule order_less_le_trans, simp add: size_of_def)
  apply (clarsimp simp: uinfo_array_tag_n_m_def upt_conv_Cons)
  apply (erule map_le_trans[rotated])
  apply (simp add: list_map_mono split: if_split)
  done

lemma aligned_intvl_disjointI:
  "is_aligned p sz \<Longrightarrow> is_aligned q sz'
    \<Longrightarrow> p \<notin> {q ..+ 2 ^ sz'}
    \<Longrightarrow> q \<notin> {p ..+ 2 ^ sz}
    \<Longrightarrow> {p..+2 ^ sz} \<inter> {q..+2 ^ sz'} = {}"
  apply (frule(1) aligned_ranges_subset_or_disjoint[where p=p and p'=q])
  apply (simp add: upto_intvl_eq[symmetric])
  apply (elim disjE, simp_all)
   apply (erule notE, erule subsetD, simp add: intvl_self)
  apply (erule notE, erule subsetD, simp add: intvl_self)
  done

end

definition
  "cnodes_retype_have_size R bits cns
    = (\<forall>ptr' sz'. cns ptr' = Some sz'
        \<longrightarrow> is_aligned ptr' (cte_level_bits + sz')
            \<and> ({ptr' ..+ 2 ^ (cte_level_bits + sz')} \<inter> R = {}
                \<or> cte_level_bits + sz' = bits))"

lemma cnodes_retype_have_size_mono:
  "cnodes_retype_have_size T bits cns \<and> S \<subseteq> T
    \<longrightarrow> cnodes_retype_have_size S bits cns"
  by (auto simp add: cnodes_retype_have_size_def)

context kernel_m begin

lemma gsCNodes_typ_region_bytes:
  "cvariable_array_map_relation (gsCNodes \<sigma>) ((^) 2) cte_Ptr (hrs_htd hrs)
    \<Longrightarrow> cnodes_retype_have_size {ptr..+2 ^ bits} bits (gsCNodes \<sigma>)
    \<Longrightarrow> 0 \<notin> {ptr..+2 ^ bits} \<Longrightarrow> is_aligned ptr bits
    \<Longrightarrow> clift (hrs_htd_update (typ_region_bytes ptr bits) hrs)
        = (clift hrs :: cte_C ptr \<Rightarrow> _)
    \<Longrightarrow> cvariable_array_map_relation (gsCNodes \<sigma>) ((^) 2) cte_Ptr
        (typ_region_bytes ptr bits (hrs_htd hrs))"
  apply (clarsimp simp: cvariable_array_map_relation_def
                        h_t_array_valid_def)
  apply (elim allE, drule(1) mp)
  apply (subst valid_footprint_typ_region_bytes)
   apply (simp add: uinfo_array_tag_n_m_def typ_uinfo_t_def typ_info_word)
  apply (clarsimp simp: cnodes_retype_have_size_def field_simps)
  apply (elim allE, drule(1) mp)
  apply (subgoal_tac "size_of TYPE(cte_C) * 2 ^ v = 2 ^ (cte_level_bits + v)")
  prefer 2
   apply (simp add: cte_C_size cte_level_bits_def power_add)
  apply (clarsimp simp add: upto_intvl_eq[symmetric] field_simps)
  apply (case_tac "p \<in> {ptr ..+ 2 ^ bits}")
   apply (drule h_t_array_first_element_at[where p="Ptr p" and gd=c_guard for p,
       unfolded h_t_array_valid_def, simplified])
     apply simp
    apply (rule is_aligned_c_guard[where m=3], simp+)
       apply clarsimp
      apply (simp add: align_of_def)
     apply (simp add: size_of_def cte_level_bits_def power_add)
    apply (simp add: cte_level_bits_def)
   apply (drule_tac x="cte_Ptr p" in fun_cong)
   apply (simp add: liftt_if[folded hrs_htd_def] hrs_htd_update
                    h_t_valid_def valid_footprint_typ_region_bytes
             split: if_split_asm)
   apply (subgoal_tac "p \<in> {p ..+ size_of TYPE(cte_C)}")
    apply (simp add: cte_C_size)
    apply blast
   apply (simp add: intvl_self)
  apply (simp only: upto_intvl_eq mask_in_range[symmetric])
  apply (rule aligned_ranges_subset_or_disjoint_coroll, simp_all)
  done

lemma tcb_ctes_typ_region_bytes:
  "cvariable_array_map_relation (map_to_tcbs (ksPSpace \<sigma>))
      (\<lambda>x. 5) cte_Ptr (hrs_htd hrs)
    \<Longrightarrow> pspace_no_overlap' ptr bits \<sigma>
    \<Longrightarrow> pspace_aligned' \<sigma>
    \<Longrightarrow> is_aligned ptr bits
    \<Longrightarrow> cpspace_tcb_relation (ksPSpace \<sigma>) hrs
    \<Longrightarrow> cvariable_array_map_relation (map_to_tcbs (ksPSpace \<sigma>)) (\<lambda>x. 5)
        cte_Ptr (typ_region_bytes ptr bits (hrs_htd hrs))"
  apply (clarsimp simp: cvariable_array_map_relation_def
                        h_t_array_valid_def)
  apply (drule spec, drule mp, erule exI)
  apply (subst valid_footprint_typ_region_bytes)
   apply (simp add: uinfo_array_tag_n_m_def typ_uinfo_t_def typ_info_word)
  apply (clarsimp simp only: map_comp_Some_iff projectKOs
                        pspace_no_overlap'_def is_aligned_neg_mask_weaken
                        field_simps upto_intvl_eq[symmetric])
  apply (elim allE, drule(1) mp)
  apply simp
  apply (drule(1) pspace_alignedD')
  apply (erule disjoint_subset[rotated])
  apply (simp add: upto_intvl_eq[symmetric])
  apply (rule intvl_start_le)
  apply (simp add: objBits_simps' cte_C_size)
  done

lemma ccorres_typ_region_bytes_dummy:
  "ccorresG rf_sr
     AnyGamma dc xfdc
     (invs' and ct_active' and sch_act_simple and
      pspace_no_overlap' ptr bits and
      (cnodes_retype_have_size S bits o gsCNodes)
      and K (bits < word_bits \<and> is_aligned ptr bits \<and> 4 \<le> bits
         \<and> 0 \<notin> {ptr..+2 ^ bits}
         \<and> {ptr ..+ 2 ^ bits} \<subseteq> S
         \<and> kernel_data_refs \<inter> {ptr..+2 ^ bits} = {}))
     UNIV hs
     (return ())
     (global_htd_update (\<lambda>_. (typ_region_bytes ptr bits)))"
  apply (rule ccorres_from_vcg)
  apply (clarsimp simp: return_def)
  apply (simp add: rf_sr_def)
  apply vcg
  apply (clarsimp simp: cstate_relation_def Let_def)
  apply (frule typ_bytes_cpspace_relation_clift_tcb)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_pte)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_pde)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_pdpte)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_pml4e)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_endpoint)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_notification)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_asid_pool)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_cte)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_userdata)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_devicedata)
      apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_gptr[where ptr'="x64KSSKIMPML4_Ptr"])
        apply (simp add: invs_pspace_aligned')+
  apply (frule typ_bytes_cpspace_relation_clift_gptr[where ptr'="intStateIRQNode_array_Ptr"])
        apply (simp add: invs_pspace_aligned')+
  apply (simp add: carch_state_relation_def cmachine_state_relation_def)
  apply (simp add: cpspace_relation_def htd_safe_typ_region_bytes)
  apply (simp add: h_t_valid_clift_Some_iff)
  apply (simp add: hrs_htd_update gsCNodes_typ_region_bytes
                   cnodes_retype_have_size_mono[where T=S]
                   tcb_ctes_typ_region_bytes[OF _ _ invs_pspace_aligned'])
  apply (simp add: cmap_array_typ_region_bytes_triv invs_pspace_aligned' bit_simps
                   objBitsT_simps word_bits_def zero_ranges_are_zero_typ_region_bytes
             cong: conj_cong)
  apply (rule conjI, rule htd_safe_typ_region_bytes, simp, blast)
  by (clarsimp simp: global_ioport_bitmap_relation_def fpu_null_state_relation_def
                     typ_bytes_cpspace_relation_clift_gptr
                     cpspace_relation_def bit_simps word_bits_def invs_pspace_aligned')

lemma region_is_typeless_cong:
  "t_hrs_' (globals t) = t_hrs_' (globals s)
   \<Longrightarrow> region_is_typeless ptr sz s = region_is_typeless ptr sz t"
  by (simp add:region_is_typeless_def)

lemma region_is_bytes_cong:
  "t_hrs_' (globals t) = t_hrs_' (globals s)
   \<Longrightarrow> region_is_bytes ptr sz s = region_is_bytes ptr sz t"
  by (simp add:region_is_bytes'_def)

lemma insertNewCap_sch_act_simple[wp]:
 "\<lbrace>sch_act_simple\<rbrace>insertNewCap a b c\<lbrace>\<lambda>_. sch_act_simple\<rbrace>"
  by (simp add:sch_act_simple_def,wp)

lemma insertNewCap_ct_active'[wp]:
 "\<lbrace>ct_active'\<rbrace>insertNewCap a b c\<lbrace>\<lambda>_. ct_active'\<rbrace>"
  apply (simp add:ct_in_state'_def)
  apply (rule hoare_pre)
  apply wps
  apply (wp insertNewCap_ksCurThread | simp)+
  done

lemma updateMDB_ctes_of_cap:
  "\<lbrace>\<lambda>s. (\<forall>x\<in>ran(ctes_of s). P (cteCap x)) \<and> no_0 (ctes_of s)\<rbrace>
    updateMDB srcSlot t
  \<lbrace>\<lambda>r s. \<forall>x\<in>ran (ctes_of s). P (cteCap x)\<rbrace>"
  apply (rule hoare_pre)
  apply wp
  apply (clarsimp)
  apply (erule ranE)
  apply (clarsimp simp:modify_map_def split:if_splits)
   apply (drule_tac x = z in bspec)
    apply fastforce
   apply simp
  apply (drule_tac x = x in bspec)
   apply fastforce
  apply simp
  done

lemma insertNewCap_caps_no_overlap'':
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
      Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
shows "\<lbrace>cte_wp_at' (\<lambda>_. True) cptr and valid_pspace'
        and caps_no_overlap'' ptr us
        and K  (cptr \<noteq> (0::machine_word)) and K (untypedRange x \<inter> {ptr..(ptr && ~~ mask us) + 2 ^ us - 1} = {})\<rbrace>
 insertNewCap srcSlot cptr x
          \<lbrace>\<lambda>rv s. caps_no_overlap'' ptr us s\<rbrace>"
  apply (clarsimp simp:insertNewCap_def caps_no_overlap''_def)
  apply (rule hoare_pre)
   apply (wp getCTE_wp updateMDB_ctes_of_cap)
  apply (clarsimp simp:cte_wp_at_ctes_of valid_pspace'_def
    valid_mdb'_def valid_mdb_ctes_def no_0_def split:if_splits)
  apply (erule ranE)
  apply (clarsimp split:if_splits)
  apply (frule_tac c=  "(cteCap xa)" and q = xb in caps_no_overlapD''[rotated])
   apply (clarsimp simp:cte_wp_at_ctes_of)
  apply clarsimp
  apply blast
  done

lemma insertNewCap_caps_overlap_reserved':
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
      Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
shows "\<lbrace>cte_wp_at' (\<lambda>_. True) cptr and valid_pspace' and caps_overlap_reserved' S
        and valid_cap' x and K  (cptr \<noteq> (0::machine_word)) and K (untypedRange x \<inter> S = {})\<rbrace>
       insertNewCap srcSlot cptr x
       \<lbrace>\<lambda>rv s. caps_overlap_reserved' S s\<rbrace>"
   apply (clarsimp simp:insertNewCap_def caps_overlap_reserved'_def)
   apply (rule hoare_pre)
   apply (wp getCTE_wp updateMDB_ctes_of_cap)
   apply (clarsimp simp:cte_wp_at_ctes_of valid_pspace'_def
    valid_mdb'_def valid_mdb_ctes_def no_0_def split:if_splits)
   apply (erule ranE)
   apply (clarsimp split:if_splits)
   apply (drule usableRange_subseteq[rotated])
     apply (simp add:valid_cap'_def)
    apply blast
   apply (drule_tac p = xaa in caps_overlap_reserved'_D)
     apply simp
    apply simp
   apply blast
  done

lemma insertNewCap_pspace_no_overlap':
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
      Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
shows "\<lbrace>pspace_no_overlap' ptr sz and pspace_aligned'
  and pspace_distinct' and cte_wp_at' (\<lambda>_. True) cptr\<rbrace>
  insertNewCap srcSlot cptr x
  \<lbrace>\<lambda>rv s. pspace_no_overlap' ptr sz s\<rbrace>"
   apply (clarsimp simp:insertNewCap_def)
   apply (rule hoare_pre)
   apply (wp updateMDB_pspace_no_overlap'
     setCTE_pspace_no_overlap' getCTE_wp)
   apply (clarsimp simp:cte_wp_at_ctes_of)
   done

lemma insertNewCap_cte_at:
  "\<lbrace>cte_at' p\<rbrace> insertNewCap srcSlot q cap
   \<lbrace>\<lambda>rv. cte_at' p\<rbrace>"
  apply (clarsimp simp:insertNewCap_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  done

lemma createObject_invs':
  "\<lbrace>\<lambda>s. invs' s \<and> ct_active' s \<and> pspace_no_overlap' ptr (APIType_capBits ty us) s
          \<and> caps_no_overlap'' ptr (APIType_capBits ty us) s \<and> ptr \<noteq> 0 \<and>
          caps_overlap_reserved' {ptr..ptr + 2 ^ APIType_capBits ty us - 1} s \<and>
          (ty = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us) \<and>
          is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us \<le> maxUntypedSizeBits \<and>
          canonical_address ptr \<and> ptr \<in> kernel_mappings \<and>
          {ptr..ptr + 2 ^ APIType_capBits ty us - 1} \<inter> kernel_data_refs = {} \<and>
          0 < gsMaxObjectSize s
    \<rbrace> createObject ty ptr us dev\<lbrace>\<lambda>r s. invs' s \<rbrace>"
  apply (simp add:createObject_def3)
  apply (rule hoare_pre)
  apply (wp createNewCaps_invs'[where sz = "APIType_capBits ty us"])
  apply (subgoal_tac "APIType_capBits ty us < word_bits")
   apply (clarsimp simp: range_cover_full invs_pspace_in_kernel_mappings' pspace_in_kernel_mappings'_def)
  apply (fastforce simp: untypedBits_defs word_bits_def)
  done

lemma createObject_sch_act_simple[wp]:
  "\<lbrace>\<lambda>s. sch_act_simple s
    \<rbrace>createObject ty ptr us dev\<lbrace>\<lambda>r s. sch_act_simple s \<rbrace>"
 apply (simp add:sch_act_simple_def)
 apply wp
 done

lemma createObject_ct_active'[wp]:
  "\<lbrace>\<lambda>s. ct_active' s \<and> pspace_aligned' s \<and> pspace_distinct' s
     \<and>  pspace_no_overlap' ptr (APIType_capBits ty us) s
     \<and>  is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits
    \<rbrace>createObject ty ptr us dev\<lbrace>\<lambda>r s. ct_active' s \<rbrace>"
 apply (simp add:ct_in_state'_def createObject_def3)
 apply (rule hoare_pre)
 apply wp
 apply wps
 apply (wp createNewCaps_pred_tcb_at')
 apply (intro conjI)
 apply (auto simp:range_cover_full)
 done

lemma createObject_notZombie[wp]:
  "\<lbrace>\<top>\<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>r s. \<not> isZombie r\<rbrace>"
  apply (rule hoare_pre)
  apply (simp add:createObject_def)
   apply wpc
    apply (wp| clarsimp simp add:isCap_simps)+
   apply wpc
    apply (wp| clarsimp simp add:isCap_simps)+
  done

lemma createObject_valid_cap':
  "\<lbrace>\<lambda>s. pspace_no_overlap' ptr (APIType_capBits ty us) s \<and>
         valid_pspace' s \<and>
         is_aligned ptr (APIType_capBits ty us) \<and> canonical_address ptr \<and>
         ptr \<in> kernel_mappings \<and>
          APIType_capBits ty us < word_bits \<and>
         (ty = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us \<and> us \<le> 42) \<and>
         (ty = APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits) \<and> ptr \<noteq> 0\<rbrace>
    createObject ty ptr us dev \<lbrace>\<lambda>r s. s \<turnstile>' r\<rbrace>"
  apply (simp add:createObject_def3)
  apply (rule hoare_pre)
  apply wp
   apply (rule_tac Q = "\<lambda>r s. r \<noteq> [] \<and> Q r s" for Q in hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_strengthen_post[OF createNewCaps_ret_len])
      apply clarsimp
     apply (rule hoare_strengthen_post[OF createNewCaps_valid_cap'[where sz = "APIType_capBits ty us"]])
    apply assumption
   apply clarsimp
  apply (clarsimp simp add:word_bits_conv range_cover_full)
  apply (cases ty; simp add: APIType_capBits_def maxUntypedSizeBits_def bit_simps)
  apply (rename_tac t, case_tac t; simp add: objBits_simps')
  done

lemma createObject_untypedRange:
  assumes split:
    "\<lbrace>P\<rbrace> createObject ty ptr us dev
     \<lbrace>\<lambda>m s. (toAPIType ty = Some apiobject_type.Untyped \<longrightarrow>
                            Q {ptr..ptr + 2 ^ us - 1} s) \<and>
            (toAPIType ty \<noteq> Some apiobject_type.Untyped \<longrightarrow> Q {} s)\<rbrace>"
  shows "\<lbrace>P\<rbrace> createObject ty ptr us dev\<lbrace>\<lambda>m s. Q (untypedRange m) s\<rbrace>"
  including no_pre
  using split
  apply (simp add: createObject_def)
  apply (case_tac "toAPIType ty")
   apply (simp add: split | wp)+
   apply (simp add: valid_def return_def bind_def split_def)
  apply (case_tac a, simp_all)
      apply (simp add: valid_def return_def simpler_gets_def simpler_modify_def
                       bind_def split_def curDomain_def)+
  done

lemma createObject_capRange:
shows "\<lbrace>P\<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>m s. capRange m = {ptr.. ptr + 2 ^ (APIType_capBits ty us) - 1}\<rbrace>"
  apply (simp add:createObject_def)
  apply (case_tac "ty")
    apply (simp_all add:toAPIType_def X64_H.toAPIType_def)
        apply (rule hoare_pre)
         apply wpc
             apply wp
        apply (simp add:split untypedRange.simps objBits_simps capRange_def APIType_capBits_def | wp)+
       apply (wpsimp simp: X64_H.createObject_def capRange_def APIType_capBits_def
                        bit_simps acapClass.simps)+
  done

lemma createObject_capRange_helper:
assumes static: "\<lbrace>P\<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>m s. Q {ptr.. ptr + 2 ^ (APIType_capBits ty us) - 1} s\<rbrace>"
shows "\<lbrace>P\<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>m s. Q (capRange m) s\<rbrace>"
  apply (rule hoare_pre)
   apply (rule hoare_strengthen_post[OF hoare_vcg_conj_lift])
     apply (rule static)
    apply (rule createObject_capRange)
   apply simp
  apply simp
  done

lemma createObject_caps_overlap_reserved':
  "\<lbrace>\<lambda>s. caps_overlap_reserved' S s \<and>
         pspace_aligned' s \<and>
         pspace_distinct' s \<and> pspace_no_overlap' ptr (APIType_capBits ty us) s \<and>
         is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits
    \<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>rv. caps_overlap_reserved' S\<rbrace>"
  apply (simp add:createObject_def3)
  apply (wp createNewCaps_caps_overlap_reserved'[where sz = "APIType_capBits ty us"])
  apply (clarsimp simp:range_cover_full)
  done

lemma createObject_caps_overlap_reserved_ret':
  "\<lbrace>\<lambda>s.  caps_overlap_reserved' {ptr..ptr + 2 ^ APIType_capBits ty us - 1} s \<and>
         pspace_aligned' s \<and>
         pspace_distinct' s \<and> pspace_no_overlap' ptr (APIType_capBits ty us) s \<and>
         is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits
    \<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>rv. caps_overlap_reserved' (untypedRange rv)\<rbrace>"
  apply (simp add:createObject_def3)
  apply (rule hoare_pre)
  apply wp
   apply (rule_tac Q = "\<lambda>r s. r \<noteq> [] \<and> Q r s" for Q in hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_strengthen_post[OF createNewCaps_ret_len])
      apply clarsimp
     apply (rule hoare_strengthen_post[OF createNewCaps_caps_overlap_reserved_ret'[where sz = "APIType_capBits ty us"]])
    apply assumption
   apply (rename_tac rv s)
   apply (case_tac rv,simp)
   apply clarsimp
   apply (erule caps_overlap_reserved'_subseteq)
   apply (rule untypedRange_in_capRange)
  apply (clarsimp simp add:word_bits_conv range_cover_full)
  done

lemma createObject_descendants_range':
  "\<lbrace>\<lambda>s.  descendants_range_in' {ptr..ptr + 2 ^ APIType_capBits ty us - 1} q (ctes_of s) \<and>
         pspace_aligned' s \<and>
         pspace_distinct' s \<and> pspace_no_overlap' ptr (APIType_capBits ty us) s \<and>
         is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits
    \<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>rv s. descendants_range' rv q (ctes_of s)\<rbrace>"
  apply (simp add:createObject_def3)
  apply (rule hoare_pre)
  apply wp
   apply (rule_tac Q = "\<lambda>r s. r \<noteq> [] \<and> Q r s" for Q in hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_strengthen_post[OF createNewCaps_ret_len])
      apply clarsimp
     apply (rule hoare_strengthen_post[OF createNewCaps_descendants_range_ret'[where sz = "APIType_capBits ty us"]])
    apply assumption
   apply fastforce
  apply (clarsimp simp add:word_bits_conv range_cover_full)
  done

lemma createObject_descendants_range_in':
  "\<lbrace>\<lambda>s.  descendants_range_in' S q (ctes_of s) \<and>
         pspace_aligned' s \<and>
         pspace_distinct' s \<and> pspace_no_overlap' ptr (APIType_capBits ty us) s \<and>
         is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits
    \<rbrace>createObject ty ptr us dev \<lbrace>\<lambda>rv s. descendants_range_in' S q (ctes_of s)\<rbrace>"
  apply (simp add:createObject_def3 descendants_range_in'_def2)
  apply (wp createNewCaps_null_filter')
  apply clarsimp
  apply (intro conjI)
   apply simp
  apply (simp add:range_cover_full)
  done

lemma createObject_idlethread_range:
  "\<lbrace>\<lambda>s. is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits
        \<and> ksIdleThread s \<notin> {ptr..ptr + 2 ^ (APIType_capBits ty us) - 1}\<rbrace>
   createObject ty ptr us dev \<lbrace>\<lambda>cap s. ksIdleThread s \<notin> capRange cap\<rbrace>"
  apply (simp add:createObject_def3)
  apply (rule hoare_pre)
  apply wp
   apply (rule_tac Q = "\<lambda>r s. r \<noteq> [] \<and> Q r s" for Q in hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_strengthen_post[OF createNewCaps_ret_len])
      apply clarsimp
     apply (rule hoare_strengthen_post[OF createNewCaps_idlethread_ranges[where sz = "APIType_capBits ty us"]])
    apply assumption
   apply clarsimp
  apply (clarsimp simp:word_bits_conv range_cover_full)
  done

lemma caps_overlap_reserved_empty'[simp]:
  "caps_overlap_reserved' {} s = True"
  by (simp add:caps_overlap_reserved'_def)

lemma createObject_IRQHandler:
  "\<lbrace>\<top>\<rbrace> createObject ty ptr us dev
    \<lbrace>\<lambda>rv s. rv = IRQHandlerCap x \<longrightarrow> P rv s x\<rbrace>"
  apply (simp add:createObject_def3)
  apply (rule hoare_pre)
  apply wp
   apply (rule_tac Q = "\<lambda>r s. r \<noteq> [] \<and> Q r s" for Q in hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_strengthen_post[OF createNewCaps_ret_len])
      apply clarsimp
     apply (rule hoare_strengthen_post[OF createNewCaps_IRQHandler[where irq = x and P = "\<lambda>_ _. False"]])
    apply assumption
   apply (rename_tac rv s)
   apply (case_tac rv; clarsimp)
  apply (clarsimp simp:word_bits_conv)
  done

lemma createObject_capClass[wp]:
  "\<lbrace> \<lambda>s. is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits
   \<rbrace> createObject ty ptr us dev
   \<lbrace>\<lambda>rv s. capClass rv = PhysicalClass\<rbrace>"
  apply (simp add:createObject_def3)
  apply (rule hoare_pre)
  apply wp
   apply (rule_tac Q = "\<lambda>r s. r \<noteq> [] \<and> Q r s" for Q in hoare_strengthen_post)
   apply (rule hoare_vcg_conj_lift)
     apply (rule hoare_strengthen_post[OF createNewCaps_ret_len])
      apply clarsimp
     apply (rule hoare_strengthen_post[OF createNewCaps_range_helper])
    apply assumption
   apply (rename_tac rv s)
   apply (case_tac rv; clarsimp)
  apply (clarsimp simp:word_bits_conv )
  apply (rule range_cover_full)
   apply (simp add:word_bits_conv)+
  done

lemma createObject_child:
  "\<lbrace>\<lambda>s.
     is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits \<and>
     {ptr .. ptr + (2^APIType_capBits ty us) - 1} \<subseteq> (untypedRange cap) \<and> isUntypedCap cap
   \<rbrace> createObject ty ptr us dev
   \<lbrace>\<lambda>rv s. sameRegionAs cap rv\<rbrace>"
  apply (rule hoare_assume_pre)
  apply (simp add:createObject_def3)
  apply wp
   apply (rule hoare_chain [OF createNewCaps_range_helper[where sz = "APIType_capBits ty us"]])
    apply (fastforce simp:range_cover_full)
   apply clarsimp
   apply (drule_tac x = ptr in spec)
   apply (case_tac "(capfn ptr)")
              apply (simp_all add: capUntypedPtr_def sameRegionAs_def Let_def isCap_simps)+
        apply clarsimp+
    apply (rename_tac arch_capability d v0 v1 f)
    apply (simp add: X64_H.capUntypedSize_def bit_simps)+
    apply (case_tac arch_capability,
           auto simp: X64_H.capUntypedSize_def bit_simps
                      is_aligned_no_wrap' add.commute[where b=ptr]
               split: arch_capability.split)
  done

lemma createObject_parent_helper:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte)
         \<and> {ptr .. ptr + (2^APIType_capBits ty us) - 1} \<subseteq> untypedRange (cteCap cte)) p s \<and>
         pspace_aligned' s \<and>
         pspace_distinct' s \<and>
         pspace_no_overlap' ptr (APIType_capBits ty us) s \<and>
         is_aligned ptr (APIType_capBits ty us) \<and> APIType_capBits ty us < word_bits \<and>
         (ty = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < us)
    \<rbrace>
    createObject ty ptr us dev
    \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and> (sameRegionAs (cteCap cte) rv)) p\<rbrace>"
  apply (rule hoare_post_imp [where Q="\<lambda>rv s. \<exists>cte. cte_wp_at' ((=) cte) p s
                                           \<and> isUntypedCap (cteCap cte) \<and>
                                sameRegionAs (cteCap cte) rv"])
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (wp hoare_vcg_ex_lift)
   apply (rule hoare_vcg_conj_lift)
   apply (simp add:createObject_def3)
    apply (wp createNewCaps_cte_wp_at')
   apply (wp createObject_child)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI)
   apply (erule range_cover_full)
    apply simp
  apply simp
  done

lemma insertNewCap_untypedRange:
  "\<lbrace>\<lambda>s. cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and> P untypedRange (cteCap cte)) srcSlot s\<rbrace>
    insertNewCap srcSlot destSlot x
   \<lbrace>\<lambda>rv s. cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and> P untypedRange (cteCap cte)) srcSlot s\<rbrace>"
  apply (simp add:insertNewCap_def)
  apply (wp updateMDB_weak_cte_wp_at setCTE_cte_wp_at_other getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  done

lemma createObject_caps_no_overlap'':
  " \<lbrace>\<lambda>s. caps_no_overlap'' (ptr + (1 + of_nat n << APIType_capBits newType userSize))
                     sz s \<and>
     pspace_aligned' s \<and> pspace_distinct' s \<and>
     pspace_no_overlap' (ptr + (of_nat n << APIType_capBits newType userSize)) (APIType_capBits newType userSize) s
     \<and> is_aligned ptr (APIType_capBits newType userSize)
     \<and> APIType_capBits newType userSize < word_bits\<rbrace>
   createObject newType (ptr + (of_nat n << APIType_capBits newType userSize)) userSize dev
   \<lbrace>\<lambda>rv s. caps_no_overlap'' (ptr + (1 + of_nat n << APIType_capBits newType userSize))
                     sz s \<rbrace>"
  apply (clarsimp simp:createObject_def3 caps_no_overlap''_def2)
  apply (wp createNewCaps_null_filter')
  apply clarsimp
  apply (intro conjI)
   apply simp
  apply (rule range_cover_full)
   apply (erule aligned_add_aligned)
     apply (rule is_aligned_shiftl_self)
    apply simp
   apply simp
  done

lemma createObject_ex_cte_cap_wp_to:
  "\<lbrace>\<lambda>s. ex_cte_cap_wp_to' P p s \<and> is_aligned ptr (APIType_capBits ty us) \<and> pspace_aligned' s
    \<and> pspace_distinct' s \<and> (APIType_capBits ty us) < word_bits  \<and> pspace_no_overlap' ptr (APIType_capBits ty us) s \<rbrace>
    createObject ty ptr us dev
   \<lbrace>\<lambda>rv s. ex_cte_cap_wp_to' P p s \<rbrace>"
  apply (clarsimp simp:ex_cte_cap_wp_to'_def createObject_def3)
  apply (rule hoare_pre)
   apply (wp hoare_vcg_ex_lift)
   apply wps
   apply (wp createNewCaps_cte_wp_at')
  apply clarsimp
  apply (intro exI conjI)
      apply assumption
     apply (rule range_cover_full)
    apply (clarsimp simp:cte_wp_at_ctes_of)
   apply simp
  apply simp
  done

lemma range_cover_one:
  "\<lbrakk>is_aligned (ptr :: 'a :: len word) us; us\<le> sz;sz < len_of TYPE('a)\<rbrakk>
  \<Longrightarrow> range_cover ptr sz us (Suc 0)"
  apply (clarsimp simp:range_cover_def)
  apply (rule Suc_leI)
  apply (rule unat_less_power)
   apply simp
  apply (rule shiftr_less_t2n)
   apply simp
  apply (rule le_less_trans[OF word_and_le1])
  apply (simp add:mask_def)
  done

lemma createObject_no_inter:
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
      Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
shows
  "\<lbrace>\<lambda>s. range_cover ptr sz (APIType_capBits newType userSize) (n + 2) \<and> ptr \<noteq> 0\<rbrace>
  createObject newType (ptr + (of_nat n << APIType_capBits newType userSize)) userSize dev
  \<lbrace>\<lambda>rv s. untypedRange rv \<inter>
  {ptr + (1 + of_nat n << APIType_capBits newType userSize) ..
   ptrend } =
  {}\<rbrace>"
  apply (rule createObject_untypedRange)
  apply (clarsimp | wp)+
  apply (clarsimp simp: blah toAPIType_def APIType_capBits_def
    X64_H.toAPIType_def split: object_type.splits)
  apply (clarsimp simp:shiftl_t2n field_simps)
  apply (drule word_eq_zeroI)
  apply (drule(1) range_cover_no_0[where p = "Suc n"])
   apply simp
  apply (simp add:field_simps)
  done

lemma range_cover_bound'':
  "\<lbrakk>range_cover ptr sz us n; x < of_nat n\<rbrakk>
  \<Longrightarrow> ptr + x * 2 ^ us + 2 ^ us - 1 \<le> (ptr && ~~ mask sz) + 2 ^ sz - 1"
  apply (frule range_cover_cell_subset)
   apply assumption
  apply (drule(1) range_cover_subset_not_empty)
   apply (clarsimp simp: field_simps)
  done

lemma caps_no_overlap''_cell:
  "\<lbrakk>range_cover ptr sz us n;caps_no_overlap'' ptr sz s;p < n\<rbrakk>
    \<Longrightarrow> caps_no_overlap'' (ptr + (of_nat p << us)) us s"
  apply (clarsimp simp:caps_no_overlap''_def)
  apply (drule(1) bspec)
  apply (subgoal_tac  "{ptr + (of_nat p << us)..(ptr + (of_nat p << us) && ~~ mask us) + 2 ^ us - 1}
                      \<subseteq>  {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}")
   apply (erule impE)
    apply (rule ccontr)
    apply clarify
    apply (drule(1) disjoint_subset2[rotated -1])
    apply simp
   apply (erule subsetD)+
   apply simp
  apply (subst is_aligned_neg_mask_eq)
   apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
     apply (simp add:is_aligned_shiftl_self)
    apply (simp add:range_cover_sz')
   apply simp
  apply (frule range_cover_cell_subset[where x = "of_nat p"])
   apply (rule word_of_nat_less)
   apply (simp add:range_cover.unat_of_nat_n)
  apply (simp add:shiftl_t2n field_simps)
  done

lemma caps_no_overlap''_le:
  "\<lbrakk>caps_no_overlap'' ptr sz s;us \<le> sz;sz < word_bits\<rbrakk>
    \<Longrightarrow> caps_no_overlap'' ptr us s"
  apply (clarsimp simp:caps_no_overlap''_def)
  apply (drule(1) bspec)
  apply (subgoal_tac  "{ptr..(ptr && ~~ mask us) + 2 ^ us - 1}
                      \<subseteq>  {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}")
   apply (erule impE)
    apply (rule ccontr)
    apply clarify
    apply (drule(1) disjoint_subset2[rotated -1])
    apply simp
   apply (erule subsetD)+
   apply simp
  apply clarsimp
  apply (frule neg_mask_diff_bound[where ptr = ptr])
  apply (simp add:p_assoc_help)
   apply (rule word_plus_mcs[where x = "2 ^ us - 1 + (ptr && ~~ mask sz)"])
    apply (simp add:field_simps)
   apply (simp add:field_simps)
   apply (simp add:p_assoc_help)
   apply (rule word_plus_mono_right)
   apply (simp add: word_bits_def)
   apply (erule two_power_increasing)
   apply simp
  apply (rule is_aligned_no_overflow')
   apply (simp add:is_aligned_neg_mask)
  done

lemma caps_no_overlap''_le2:
  "\<lbrakk>caps_no_overlap'' ptr sz s;ptr \<le> ptr'; ptr' && ~~ mask sz = ptr && ~~ mask sz\<rbrakk>
    \<Longrightarrow> caps_no_overlap'' ptr' sz s"
  apply (clarsimp simp:caps_no_overlap''_def)
  apply (drule(1) bspec)
  apply (subgoal_tac  "{ptr'..(ptr' && ~~ mask sz) + 2 ^ sz - 1}
                      \<subseteq>  {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}")
   apply (erule impE)
    apply (rule ccontr)
    apply clarify
    apply (drule(1) disjoint_subset2[rotated -1])
    apply simp
   apply (erule subsetD)+
   apply simp
  apply clarsimp
  done

lemma range_cover_head_mask:
  "\<lbrakk>range_cover (ptr :: machine_word) sz us (Suc n); ptr \<noteq> 0\<rbrakk>
  \<Longrightarrow> ptr + (of_nat n << us) && ~~ mask sz = ptr && ~~ mask sz"
  apply (case_tac n)
   apply clarsimp
  apply (clarsimp simp:range_cover_tail_mask)
  done

lemma pspace_no_overlap'_strg:
  "pspace_no_overlap' ptr sz s \<and> sz' \<le> sz \<and> sz < word_bits \<longrightarrow> pspace_no_overlap' ptr sz' s"
  apply clarsimp
  apply (erule(2) pspace_no_overlap'_le)
  done

lemma cte_wp_at_no_0:
  "\<lbrakk>invs' s; cte_wp_at' (\<lambda>_. True) ptr s\<rbrakk> \<Longrightarrow> ptr \<noteq> 0"
  by (clarsimp dest!:invs_mdb' simp:valid_mdb'_def valid_mdb_ctes_def no_0_def cte_wp_at_ctes_of)

lemma insertNewCap_descendants_range_in':
  "\<lbrace>\<lambda>s. valid_pspace' s \<and> descendants_range_in' S p (ctes_of s)
    \<and> capRange x \<inter> S = {}
    \<and> cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and> sameRegionAs (cteCap cte) x) p s
    \<and> cte_wp_at' (\<lambda>cte. cteCap cte = capability.NullCap) dslot s
    \<and> descendants_range' x p (ctes_of s) \<and> capClass x = PhysicalClass
   \<rbrace> insertNewCap p dslot x
    \<lbrace>\<lambda>rv s. descendants_range_in' S p (ctes_of s)\<rbrace>"
  apply (clarsimp simp:insertNewCap_def descendants_range_in'_def)
  apply (wp getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (intro conjI allI)
   apply (clarsimp simp:valid_pspace'_def valid_mdb'_def
     valid_mdb_ctes_def no_0_def split:if_splits)
  apply (clarsimp simp: descendants_of'_mdbPrev split:if_splits)
  apply (cut_tac p = p and m = "ctes_of s" and parent = p and s = s
        and parent_cap = "cteCap cte" and parent_node = "cteMDBNode cte"
        and site = dslot and site_cap = capability.NullCap and site_node = "cteMDBNode ctea"
        and c' = x
    in mdb_insert_again_child.descendants)
   apply (case_tac cte ,case_tac ctea)
   apply (rule mdb_insert_again_child.intro[OF mdb_insert_again.intro])
      apply (simp add:mdb_ptr_def vmdb_def valid_pspace'_def valid_mdb'_def
            mdb_ptr_axioms_def mdb_insert_again_axioms_def )+
    apply (intro conjI allI impI)
      apply clarsimp
      apply (erule(1) ctes_of_valid_cap')
     apply (clarsimp simp:valid_mdb_ctes_def)
    apply clarsimp
   apply (rule mdb_insert_again_child_axioms.intro)
   apply (clarsimp simp: nullPointer_def)+
   apply (clarsimp simp:isMDBParentOf_def valid_pspace'_def
      valid_mdb'_def valid_mdb_ctes_def)
   apply (frule(2) ut_revocableD'[rotated 1])
   apply (clarsimp simp:isCap_simps)
  apply (clarsimp cong: if_cong)
  done

lemma insertNewCap_cte_wp_at_other:
  "\<lbrace>cte_wp_at' (\<lambda>cte. P (cteCap cte)) p and K (slot \<noteq> p)\<rbrace> insertNewCap srcSlot slot x
            \<lbrace>\<lambda>rv. cte_wp_at' (\<lambda>cte. P (cteCap cte)) p \<rbrace>"
  apply (clarsimp simp:insertNewCap_def)
  apply (wp updateMDB_weak_cte_wp_at setCTE_cte_wp_at_other getCTE_wp)
  apply (clarsimp simp:cte_wp_at_ctes_of)
  done

lemma range_cover_bound3:
  "\<lbrakk>range_cover ptr sz us n; x < of_nat n\<rbrakk>
  \<Longrightarrow> ptr + x * 2 ^ us + 2 ^ us - 1 \<le> ptr + (of_nat n) * 2 ^ us - 1"
  apply (frule range_cover_subset[where p = "unat x"])
    apply (simp add:unat_less_helper)
   apply (rule ccontr,simp)
  apply (drule(1) range_cover_subset_not_empty)
   apply (clarsimp simp: field_simps)
  done

lemma range_cover_gsMaxObjectSize:
  "cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap dev (ptr &&~~ mask sz) sz idx) srcSlot s
    \<Longrightarrow> range_cover ptr sz (APIType_capBits newType userSize) (length destSlots)
    \<Longrightarrow> valid_global_refs' s
    \<Longrightarrow> unat num = length destSlots
    \<Longrightarrow> unat (num << (APIType_capBits newType userSize) :: machine_word) \<le> gsMaxObjectSize s
        \<and> 2 ^ APIType_capBits newType userSize \<le> gsMaxObjectSize s"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule (1) valid_global_refsD_with_objSize)
  apply clarsimp
  apply (rule conjI)
   apply (frule range_cover.range_cover_compare_bound)
   apply (drule range_cover.unat_of_nat_n_shift, rule order_refl)
   apply (drule_tac s="unat num" in sym)
   apply simp
  apply (clarsimp simp: range_cover_def)
  apply (erule order_trans[rotated])
  apply simp
  done

lemma APIType_capBits_min:
  "(tp = APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> userSize)
    \<Longrightarrow> 4 \<le> APIType_capBits tp userSize"
  by (simp add: APIType_capBits_def objBits_simps' bit_simps untypedBits_defs
         split: object_type.split ArchTypes_H.apiobject_type.split)

end

context begin interpretation Arch . (*FIXME: arch_split*)

lemma createNewCaps_1_gsCNodes_p:
  "\<lbrace>\<lambda>s. P (gsCNodes s p) \<and> p \<noteq> ptr\<rbrace> createNewCaps newType ptr 1 n dev\<lbrace>\<lambda>rv s. P (gsCNodes s p)\<rbrace>"
  apply (simp add: createNewCaps_def)
  apply (rule hoare_pre)
   apply (wp mapM_x_wp' | wpc | simp add: createObjects_def)+
  done

lemma createObject_gsCNodes_p:
  "\<lbrace>\<lambda>s. P (gsCNodes s p) \<and> p \<noteq> ptr\<rbrace> createObject t ptr sz dev\<lbrace>\<lambda>rv s. P (gsCNodes s p)\<rbrace>"
  apply (simp add: createObject_def)
  apply (rule hoare_pre)
   apply (wp mapM_x_wp' | wpc | simp add: createObjects_def)+
  done

lemma createObject_cnodes_have_size:
  "\<lbrace>\<lambda>s. is_aligned ptr (APIType_capBits newType userSize)
      \<and> cnodes_retype_have_size R (APIType_capBits newType userSize) (gsCNodes s)\<rbrace>
    createObject newType ptr userSize dev
  \<lbrace>\<lambda>rv s. cnodes_retype_have_size R (APIType_capBits newType userSize) (gsCNodes s)\<rbrace>"
  apply (simp add: createObject_def)
  apply (rule hoare_pre)
   apply (wp mapM_x_wp' | wpc | simp add: createObjects_def)+
  apply (cases newType, simp_all add: X64_H.toAPIType_def)
  apply (clarsimp simp: APIType_capBits_def objBits_simps'
                              cnodes_retype_have_size_def cte_level_bits_def
                       split: if_split_asm)
  done

lemma range_cover_not_in_neqD:
  "\<lbrakk> x \<notin> {ptr..ptr + (of_nat n << APIType_capBits newType userSize) - 1};
    range_cover ptr sz (APIType_capBits newType userSize) n; n' < n \<rbrakk>
  \<Longrightarrow> x \<noteq> ptr + (of_nat n' << APIType_capBits newType userSize)"
  apply (clarsimp simp only: shiftl_t2n mult.commute)
  apply (erule notE, rule subsetD, erule_tac p=n' in range_cover_subset)
    apply simp+
  apply (rule is_aligned_no_overflow)
  apply (rule aligned_add_aligned)
    apply (erule range_cover.aligned)
   apply (simp add: is_aligned_mult_triv2)
  apply simp
  done

crunch gsMaxObjectSize[wp]: createObject "\<lambda>s. P (gsMaxObjectSize s)"
  (simp: crunch_simps unless_def wp: crunch_wps)

end

context kernel_m begin

lemma ceqv_restore_as_guard:
  "ceqv Gamma xf' rv' t t' d (Guard C_Guard {s. xf' s = rv'} d)"
  apply (simp add: ceqv_def)
  apply (auto elim!: exec_Normal_elim_cases intro: exec.Guard)
  done

lemma insertNewCap_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call insertNewCap_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
         \<and> byte_regions_unmodified' s t}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre, vcg exspec=mdb_node_ptr_set_mdbPrev_preserves_bytes
    exspec=mdb_node_ptr_set_mdbNext_preserves_bytes
    exspec=mdb_node_get_mdbNext_modifies exspec=mdb_node_new_modifies)
  apply (safe intro!: byte_regions_unmodified_hrs_mem_update
    elim!: byte_regions_unmodified_trans byte_regions_unmodified_trans[rotated],
    simp_all add: h_t_valid_field)
  done

lemma byte_regions_unmodified_flip_eq:
  "byte_regions_unmodified hrs' hrs
    \<Longrightarrow> hrs_htd hrs' = hrs_htd hrs
    \<Longrightarrow> byte_regions_unmodified hrs hrs'"
  by (simp add: byte_regions_unmodified_def)

lemma insertNewCap_preserves_bytes_flip:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call insertNewCap_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
         \<and> byte_regions_unmodified' t s}"
  by (rule allI, rule conseqPost,
    rule insertNewCap_preserves_bytes[rule_format],
    auto elim: byte_regions_unmodified_flip_eq)

lemma copyGlobalMappings_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call copyGlobalMappings_'proc
      {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
         \<and> byte_regions_unmodified' s t}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (clarsimp simp only: whileAnno_def)
  apply (subst whileAnno_def[symmetric, where V=undefined
       and I="{t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
         \<and> byte_regions_unmodified' s t}" for s])
  apply (rule conseqPre, vcg)
  apply (safe intro!: byte_regions_unmodified_hrs_mem_update
    elim!: byte_regions_unmodified_trans byte_regions_unmodified_trans[rotated],
    (simp_all add: h_t_valid_field)+)
  done

lemma hrs_htd_update_canon:
  "hrs_htd_update (\<lambda>_. f (hrs_htd hrs)) hrs = hrs_htd_update f hrs"
  by (cases hrs, simp add: hrs_htd_update_def hrs_htd_def)

lemma Arch_createObject_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call Arch_createObject_'proc
      {t. \<forall>nt. t_' s = object_type_from_H nt
         \<longrightarrow> (\<forall>x \<in> - {ptr_val (regionBase_' s) ..+ 2 ^ getObjectSize nt (unat (userSize_' s))}.
             hrs_htd (t_hrs_' (globals t)) x = hrs_htd (t_hrs_' (globals s)) x)
         \<and> byte_regions_unmodified' t s}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply clarsimp
  apply (rule conseqPre,
         vcg exspec=cap_frame_cap_new_modifies
             exspec=cap_page_table_cap_new_modifies
             exspec=addrFromPPtr_modifies
             exspec=cap_page_directory_cap_new_modifies
             exspec=copyGlobalMappings_preserves_bytes)
  apply (safe intro!: byte_regions_unmodified_hrs_mem_update)
  apply (simp_all add: h_t_valid_field hrs_htd_update)
             apply (safe intro!: ptr_retyp_d ptr_retyps_out)
             apply (simp_all add: object_type_from_H_def Kernel_C_defs APIType_capBits_def bit_simps
                           split: object_type.split_asm ArchTypes_H.apiobject_type.split_asm)
   apply (rule byte_regions_unmodified_flip, simp)
   apply (rule byte_regions_unmodified_trans[rotated], assumption)
   apply (simp_all add: hrs_htd_update_canon hrs_htd_update)
  done

lemma ptr_arr_retyps_eq_outside_dom:
  "x \<notin> {ptr_val (p :: 'a ptr) ..+ n * size_of TYPE ('a :: wf_type)}
    \<Longrightarrow> ptr_arr_retyps n p htd x = htd x"
  by (simp add: ptr_arr_retyps_def htd_update_list_same2)

lemma Arch_initFpuContext_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call Arch_initFpuContext_'proc
       {t. hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
           \<and> byte_regions_unmodified' t s}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply (rule allI, rule conseqPre, vcg, clarsimp)
  apply (intro byte_regions_unmodified_hrs_mem_update byte_regions_unmodified_refl)
  apply (simp_all add: typ_heap_simps)
  done

context begin

private abbreviation
  "preserves_bytes_inv P s \<equiv>
    {t. P s \<longrightarrow> P t \<and> hrs_htd (t_hrs_' (globals t)) = hrs_htd (t_hrs_' (globals s))
                    \<and> byte_regions_unmodified' t s}"

private lemma preserves_bytes_modifies_inv_prop:
  "modifies_inv_prop (preserves_bytes_inv P)"
  by (clarsimp simp: modifies_inv_prop_def modifies_inv_refl_def modifies_inv_incl_def
                     byte_regions_unmodified_def)

private abbreviation
  "registers_Ptr_valid \<equiv> \<lambda>s. s \<Turnstile>\<^sub>c registers_Ptr &(context_' s\<rightarrow>[''registers_C''])"

private lemmas registers_modifies_inv_intros =
  modifies_inv_intros[OF preserves_bytes_modifies_inv_prop[where P="registers_Ptr_valid"]]

private method preserves_bytes_inv methods vcg =
  (hoare_rule HoarePartial.ProcNoRec1;
   intro allI registers_modifies_inv_intros;
   clarsimp;
   (rule conseqPre, vcg);
   clarsimp;
   rule byte_regions_unmodified_hrs_mem_update;
   clarsimp simp: typ_heap_simps)

lemma Mode_initContext_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call Mode_initContext_'proc (preserves_bytes_inv registers_Ptr_valid s)"
  by (preserves_bytes_inv \<open>vcg\<close>)

lemma Arch_initContext_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call Arch_initContext_'proc (preserves_bytes_inv registers_Ptr_valid s)"
  by (preserves_bytes_inv \<open>vcg exspec=Mode_initContext_preserves_bytes
                               exspec=Arch_initFpuContext_preserves_bytes\<close>)

end

lemma createObject_preserves_bytes:
  "\<forall>s. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s} Call createObject_'proc
      {t. \<forall>nt. t_' s = object_type_from_H nt
         \<longrightarrow> (\<forall>x \<in> - {ptr_val (regionBase_' s) ..+ 2 ^ getObjectSize nt (unat (userSize_' s))}.
             hrs_htd (t_hrs_' (globals t)) x = hrs_htd (t_hrs_' (globals s)) x)
         \<and> byte_regions_unmodified' t s}"
  apply (hoare_rule HoarePartial.ProcNoRec1)
  apply clarsimp
  apply (rule conseqPre,
         vcg exspec=Arch_createObject_preserves_bytes
             exspec=cap_thread_cap_new_modifies
             exspec=cap_endpoint_cap_new_modifies
             exspec=cap_notification_cap_new_modifies
             exspec=cap_cnode_cap_new_modifies
             exspec=cap_untyped_cap_new_modifies
             exspec=Arch_initContext_preserves_bytes)
  apply (safe intro!: byte_regions_unmodified_hrs_mem_update,
         simp_all add: h_t_valid_field hrs_htd_update)
  apply (safe intro!: ptr_retyp_d ptr_retyps_out trans[OF ptr_retyp_d ptr_retyp_d]
                      ptr_arr_retyps_eq_outside_dom)
  apply (simp_all add: object_type_from_H_def Kernel_C_defs APIType_capBits_def
                       objBits_simps' cte_C_size power_add ctcb_offset_def ctcb_size_bits_def
                       byte_regions_unmodified_def
                split: object_type.split_asm ArchTypes_H.apiobject_type.split_asm)
    apply (erule notE, erule subsetD[rotated], rule intvl_start_le intvl_sub_offset, simp)+
  done

lemma offset_intvl_first_chunk_subsets:
  "range_cover (p :: addr) sz bits n
    \<Longrightarrow> i < of_nat n
    \<Longrightarrow> {p + (i << bits) ..+ 2 ^ bits} \<subseteq> {p + (i << bits) ..+ (n - unat i) * 2 ^ bits}
        \<and> {p + ((i + 1) << bits) ..+ (n - unat (i + 1)) * 2 ^ bits}
            \<le> {p + (i << bits) ..+ (n - unat i) * 2 ^ bits}
        \<and> {p + (i << bits) ..+ 2 ^ bits}
            \<inter> {p + ((i + 1) << bits) ..+ (n - unat (i + 1)) * 2 ^ bits}
            = {}"
  apply (strengthen intvl_start_le)
  apply (strengthen order_trans[OF _
      intvl_sub_offset[where x="2 ^ bits" and y="(n - unat (i + 1)) * 2 ^ bits"]])
  apply (frule range_cover_sz')
  apply (cut_tac n=i in unatSuc)
   apply unat_arith
  apply (simp add: word_shiftl_add_distrib field_simps TWO)
  apply (simp add: mult_Suc[symmetric] del: mult_Suc)
  apply (frule unat_less_helper)
  apply (cut_tac p="p + (i << bits)" and k="2 ^ bits"
    and z="(n - unat (i + 1)) * 2 ^ bits" in init_intvl_disj)
   apply (simp add: field_simps)
   apply (drule range_cover.strong_times_64, simp)
   apply (simp add: addr_card_def word_bits_def card_word)
   apply (erule order_le_less_trans[rotated])
   apply (simp add: mult_Suc[symmetric] del: mult_Suc)
  apply (simp add: Int_commute field_simps)
  apply unat_arith
  done

lemma offset_intvl_first_chunk_subsets_unat:
  "range_cover (p :: addr) sz bits n
    \<Longrightarrow> unat n' = n
    \<Longrightarrow> i < of_nat n
    \<Longrightarrow> {p + (i << bits) ..+ 2 ^ bits} \<subseteq> {p + (i << bits) ..+ unat (n' - i) * 2 ^ bits}
        \<and> {p + ((i + 1) << bits) ..+ unat (n' - (i + 1)) * 2 ^ bits}
            \<le> {p + (i << bits) ..+ unat (n' - i) * 2 ^ bits}
        \<and> {p + (i << bits) ..+ 2 ^ bits}
            \<inter> {p + ((i + 1) << bits) ..+ unat (n' - (i + 1)) * 2 ^ bits}
            = {}"
  apply (subgoal_tac "unat (n' - (i + 1)) = unat n' - unat (i + 1)
        \<and> unat (n' - i) = unat n' - unat i")
   apply (frule(1) offset_intvl_first_chunk_subsets)
   apply simp
  apply (intro conjI unat_sub)
   apply (rule word_minus_one_le_leq, simp)
   apply (simp add: word_less_nat_alt unat_of_nat)
  apply (simp add: word_le_nat_alt word_less_nat_alt unat_of_nat)
  done

lemma retype_offs_region_actually_is_zero_bytes:
  "\<lbrakk> ctes_of s p = Some cte; (s, s') \<in> rf_sr; untyped_ranges_zero' s;
      cteCap cte = UntypedCap False (ptr &&~~ mask sz) sz idx;
      idx \<le> unat (ptr && mask sz);
      range_cover ptr sz (getObjectSize newType userSize) num_ret \<rbrakk>
    \<Longrightarrow> region_actually_is_zero_bytes ptr
            (num_ret * 2 ^ APIType_capBits newType userSize) s'"
  using word_unat_mask_lt[where w=ptr and m=sz]
  apply -
  apply (frule range_cover.sz(1))
  apply (drule(2) ctes_of_untyped_zero_rf_sr)
   apply (simp add: untypedZeroRange_def max_free_index_def word_size)
  apply clarify
  apply (strengthen heap_list_is_zero_mono2[mk_strg I E]
      region_actually_is_bytes_subset[mk_strg I E])
  apply (simp add: getFreeRef_def word_size)
  apply (rule intvl_both_le)
   apply (rule order_trans, rule word_plus_mono_right, erule word_of_nat_le)
    apply (simp add: word_plus_and_or_coroll2 add.commute word_and_le2)
   apply (simp add: word_plus_and_or_coroll2 add.commute)
  apply (subst unat_plus_simple[THEN iffD1], rule is_aligned_no_wrap',
    rule is_aligned_neg_mask2)
   apply (rule word_of_nat_less, simp)
  apply (simp add: unat_of_nat_eq[OF order_less_trans, OF _ power_strict_increasing[where n=sz]]
    unat_sub[OF word_of_nat_le])
  apply (subst word_plus_and_or_coroll2[where x=ptr and w="mask sz", symmetric])
  apply (subst unat_plus_simple[THEN iffD1],
    simp add: word_plus_and_or_coroll2 add.commute word_and_le2)
  apply simp
  apply (rule order_trans[rotated], erule range_cover.range_cover_compare_bound)
  apply simp
  done

lemma createNewCaps_valid_cap_hd:
    "\<lbrace>\<lambda>s. pspace_no_overlap' ptr sz s \<and>
        valid_pspace' s \<and> n \<noteq> 0 \<and>
        sz \<le> maxUntypedSizeBits \<and> canonical_address ptr \<and>
        (ptr && ~~ mask sz) \<in> kernel_mappings \<and>
        range_cover ptr sz (APIType_capBits ty us) n \<and>
        (ty = APIObjectType ArchTypes_H.CapTableObject \<longrightarrow> 0 < us) \<and>
        (ty = APIObjectType ArchTypes_H.apiobject_type.Untyped \<longrightarrow>
              minUntypedSizeBits \<le> us \<and> us \<le> maxUntypedSizeBits) \<and>
       ptr \<noteq> 0 \<rbrace>
    createNewCaps ty ptr n us dev
  \<lbrace>\<lambda>r s. s \<turnstile>' hd r\<rbrace>"
  apply (cases "n = 0")
   apply simp
  apply (rule hoare_chain)
    apply (rule hoare_vcg_conj_lift)
     apply (rule createNewCaps_ret_len)
    apply (rule createNewCaps_valid_cap'[where sz=sz])
   apply (clarsimp simp: range_cover_n_wb canonical_address_neq_mask)
  apply simp
  done

lemma insertNewCap_ccorres:
  "ccorres dc xfdc (pspace_aligned' and pspace_canonical' and valid_mdb' and cte_wp_at' (\<lambda>_. True) slot
          and valid_objs' and valid_cap' cap)
     ({s. cap_get_tag (cap_' s) = scast cap_untyped_cap
         \<longrightarrow> (case untypedZeroRange (cap_to_H (the (cap_lift (cap_' s)))) of None \<Rightarrow> True
          | Some (a, b) \<Rightarrow> region_actually_is_zero_bytes a (unat ((b + 1) - a)) s)}
       \<inter> {s. ccap_relation cap (cap_' s)} \<inter> {s. parent_' s = Ptr parent}
       \<inter> {s. slot_' s = Ptr slot}) []
     (insertNewCap parent slot cap)
     (Call insertNewCap_'proc)"
  (is "ccorres _ _ ?P ?P' _ _ _")
  apply (rule ccorres_guard_imp2, rule insertNewCap_ccorres1)
  apply (clarsimp simp: cap_get_tag_isCap)
  apply (clarsimp simp: ccap_relation_def map_option_Some_eq2)
  apply (simp add: untypedZeroRange_def Let_def)
  done

lemma createObject_untyped_region_is_zero_bytes:
  "\<forall>\<sigma>. \<Gamma>\<turnstile>\<^bsub>/UNIV\<^esub> {s. let tp = (object_type_to_H (t_' s));
          sz = APIType_capBits tp (unat (userSize_' s))
      in (\<not> to_bool (deviceMemory_' s)
              \<longrightarrow> region_actually_is_zero_bytes (ptr_val (regionBase_' s)) (2 ^ sz) s)
                    \<and> canonical_address (ptr_val (regionBase_' s))
                    \<and> sz < 64 \<and> (tp = APIObjectType ArchTypes_H.apiobject_type.Untyped \<longrightarrow> sz \<ge> minUntypedSizeBits)}
      Call createObject_'proc
   {t. cap_get_tag (ret__struct_cap_C_' t) = scast cap_untyped_cap
         \<longrightarrow> (case untypedZeroRange (cap_to_H (the (cap_lift (ret__struct_cap_C_' t)))) of None \<Rightarrow> True
          | Some (a, b) \<Rightarrow> region_actually_is_zero_bytes a (unat ((b + 1) - a)) t)}"
  apply (rule allI, rule conseqPre, vcg exspec=copyGlobalMappings_modifies
      exspec=Arch_initContext_modifies)
  apply (clarsimp simp: cap_tag_defs Let_def)
  apply (simp add: cap_lift_untyped_cap cap_tag_defs cap_to_H_simps
                   cap_untyped_cap_lift_def object_type_from_H_def)
  apply (simp add: untypedZeroRange_def split: if_split)
  apply (clarsimp simp: getFreeRef_def Let_def object_type_to_H_def APIType_capBits_def
                        less_mask_eq word_less_nat_alt
                 dest!: sign_extend_canonical_address[THEN iffD2, THEN sym])
  done

lemma range_cover_n_le':
  "range_cover ptr sz sbit n \<Longrightarrow> 2 ^ sbit * n \<le> 2 ^ sz"
  "range_cover ptr sz sbit n \<Longrightarrow> n \<le> 2 ^ sz"
  unfolding atomize_conj atomize_imp
  apply (rule context_conjI, rule impI)
  apply (rule nat_le_power_trans, erule range_cover.range_cover_n_le, erule range_cover.sz)
  apply (erule tfl_imp_trans, rule impI)
  apply (erule le_trans[rotated])
  apply (rule rsubst[of "\<lambda>r. r \<le> 2 ^ sbit * n", OF _ nat_mult_1])
  apply (rule mult_le_mono1, rule one_le_power, simp)
  done

lemma createNewObjects_ccorres:
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
      Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
and   hoare_TrueI[simp add]
defines "unat_eq a b \<equiv> unat a = b"
shows  "ccorres dc xfdc
     (invs' and sch_act_simple and ct_active'
                  and (cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap isdev (ptr && ~~ mask sz) sz idx) srcSlot)
                  and (\<lambda>s. \<forall>slot\<in>set destSlots. cte_wp_at' (\<lambda>c. cteCap c = NullCap) slot s)
                  and (\<lambda>s. \<forall>slot\<in>set destSlots. ex_cte_cap_wp_to' (\<lambda>_. True) slot s)
                  and (\<lambda>s. \<exists>n. gsCNodes s cnodeptr = Some n \<and> unat start + length destSlots \<le> 2 ^ n)
                  and (pspace_no_overlap' ptr sz)
                  and caps_no_overlap'' ptr sz
                  and caps_overlap_reserved' {ptr .. ptr + of_nat (length destSlots) * 2^ (getObjectSize newType userSize) - 1}
                  and (\<lambda>s. descendants_range_in' {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1} srcSlot (ctes_of s))
                  and cnodes_retype_have_size {ptr .. ptr + of_nat (length destSlots) * 2^ (getObjectSize newType userSize) - 1}
                      (APIType_capBits newType userSize) o gsCNodes
                  and (K (srcSlot \<notin> set destSlots
                    \<and> destSlots \<noteq> []
                    \<and> range_cover ptr sz (getObjectSize newType userSize) (length destSlots)
                    \<and> ptr \<noteq> 0
                    \<and> sz \<le> maxUntypedSizeBits
                    \<and> APIType_capBits newType userSize \<le> maxUntypedSizeBits
                    \<and> canonical_address (ptr && ~~ mask sz) \<and> (ptr && ~~ mask sz) \<in> kernel_mappings
                    \<and> {ptr .. ptr + of_nat (length destSlots) * 2^ (getObjectSize newType userSize) - 1}
                      \<inter> kernel_data_refs = {}
                    \<and> cnodeptr \<notin> {ptr .. ptr + (of_nat (length destSlots) << APIType_capBits newType userSize) - 1}
                    \<and> 0 \<notin> {ptr..(ptr && ~~ mask sz) + 2 ^ sz - 1}
                    \<and> is_aligned ptr 4
                    \<and> (newType = APIObjectType apiobject_type.Untyped \<longrightarrow> userSize \<le> maxUntypedSizeBits)
                    \<and> (newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> userSize < 59)
                    \<and> (newType = APIObjectType apiobject_type.Untyped \<longrightarrow> minUntypedSizeBits \<le> userSize)
                    \<and> (newType = APIObjectType apiobject_type.CapTableObject \<longrightarrow> 0 < userSize)
                    \<and> (isdev \<longrightarrow> newType = APIObjectType ArchTypes_H.apiobject_type.Untyped \<or>
                                           isFrameType newType)
                    \<and> (unat num = length destSlots)
                    )))
    ({s. (\<not> isdev \<longrightarrow> region_actually_is_zero_bytes ptr
            (length destSlots * 2 ^ APIType_capBits newType userSize) s)}
           \<inter> {s. t_' s = object_type_from_H newType}
           \<inter> {s. parent_' s = cte_Ptr srcSlot}
           \<inter> {s. destCNode_' s = cte_Ptr cnodeptr}
           \<inter> {s. destOffset_' s = start \<and> (\<forall>n. n < length destSlots \<longrightarrow> destSlots ! n = cnodeptr + ((start + of_nat n) * 0x20))}
           \<inter> {s. destLength_' s = num \<and> unat num \<noteq> 0}
           \<inter> {s. regionBase_' s = Ptr ptr }
           \<inter> {s. unat_eq (userSize_' s) userSize}
           \<inter> {s. deviceMemory_' s = from_bool isdev}
     ) []
     (createNewObjects newType srcSlot destSlots ptr userSize isdev)
     (Call createNewObjects_'proc)"
  unfolding from_bool_to_bool_iff
  supply if_cong[cong]
  apply (rule ccorres_gen_asm_state)
  apply clarsimp
  apply (subgoal_tac "unat (of_nat (getObjectSize newType userSize)) = getObjectSize newType userSize")
   prefer 2
   apply (rule unat_of_nat64)
   apply (rule less_le_trans[OF getObjectSize_max_size]; clarsimp simp: word_bits_def untypedBits_defs)
  apply (subgoal_tac "\<forall>n < length destSlots. canonical_address (ptr + (of_nat n << APIType_capBits newType userSize))")
   prefer 2 subgoal by (simp add: shiftl_t2n field_simps range_cover_canonical_address)
  apply (cinit lift: t_' parent_' destCNode_' destOffset_' destLength_' regionBase_' userSize_' deviceMemory_')
   apply (rule ccorres_rhs_assoc2)+
   apply (rule ccorres_rhs_assoc)
   apply (rule_tac Q' = "Q'
     \<inter> {s. objectSize_' s = of_nat (APIType_capBits newType userSize)}
     \<inter> {s. nextFreeArea_' s = Ptr ptr } "
     and R="(\<lambda>s. unat (num << (APIType_capBits newType userSize) :: machine_word)
        \<le> gsMaxObjectSize s) and R''"
     for Q' R'' in ccorres_symb_exec_r)
     apply (rule ccorres_guard_imp[where A="X and Q"
         and A'=Q' and Q=Q and Q'=Q' for X Q Q', rotated]
         (* this moves the gsMaxObjectSize bit into the ccorres_symb_exec_r
            vcg proof *))
       apply clarsimp
      apply clarsimp
     apply (cinitlift objectSize_' nextFreeArea_')
     apply simp
     apply (clarsimp simp: whileAnno_def)
     apply (rule ccorres_rel_imp)
      apply (rule_tac Q="{s. \<not> isdev \<longrightarrow> region_actually_is_zero_bytes
            (ptr + (i_' s << APIType_capBits newType userSize))
            (unat (num - i_' s) * 2 ^ APIType_capBits newType userSize) s}"
            in ccorres_zipWithM_x_while_genQ[where j=1, OF _ _ _ _ _ i_xf_for_sequence, simplified])
          apply clarsimp
          apply (subst upt_enum_offset_trivial)
            apply (rule word_leq_le_minus_one)
             apply (rule word_of_nat_le)
             apply (drule range_cover.range_cover_n_less)
             apply (simp add:word_bits_def minus_one_norm)
            apply (erule range_cover_not_zero[rotated],simp)
           apply simp
          apply (rule ccorres_guard_impR)
           apply (rule_tac xf'=i_' in ccorres_abstract, ceqv)
           apply (rule_tac P="rv' = of_nat n" in ccorres_gen_asm2, simp)
           apply (rule ccorres_rhs_assoc)+
           apply (rule ccorres_add_return)
           apply (simp only: hrs_htd_update)
           apply ((rule ccorres_Guard_Seq[where S=UNIV])+)?
           apply (rule ccorres_split_nothrow,
                rule_tac S="{ptr .. ptr + of_nat (length destSlots) * 2^ (getObjectSize newType userSize) - 1}"
                  in ccorres_typ_region_bytes_dummy, ceqv)
             apply (rule ccorres_Guard_Seq)+
             apply (ctac add:createObject_ccorres)
               apply (rule ccorres_move_array_assertion_cnode_ctes
                           ccorres_move_c_guard_cte)+
               apply (rule ccorres_add_return2)
               apply (ctac (no_vcg) add: insertNewCap_ccorres)
                apply (rule ccorres_move_array_assertion_cnode_ctes
                            ccorres_return_Skip')+
               apply wp
              apply (clarsimp simp: createObject_def3 conj_ac)
              apply (wp createNewCaps_valid_pspace_extras[where sz = sz]
                createNewCaps_cte_wp_at[where sz = sz]
                createNewCaps_valid_cap_hd[where sz = sz])
                apply (rule range_cover_one)
                  apply (rule aligned_add_aligned[OF is_aligned_shiftl_self])
                   apply (simp add:range_cover.aligned)
                  apply (simp add:range_cover_def)
                 apply (simp add:range_cover_def)
                apply (simp add:range_cover_def)
               apply (simp add:range_cover.sz)
              apply (wp createNewCaps_1_gsCNodes_p[simplified]
                        createNewCaps_cte_wp_at'[where sz=sz])[1]
             apply clarsimp
             apply (vcg exspec=createObject_untyped_region_is_zero_bytes)
            apply (simp add:size_of_def)
            apply (rule_tac P = "\<lambda>s. cte_wp_at' (\<lambda>cte. isUntypedCap (cteCap cte) \<and>
              {ptr .. ptr + (of_nat (length destSlots)<< APIType_capBits newType userSize) - 1} \<subseteq> untypedRange (cteCap cte)) srcSlot s
              \<and> pspace_no_overlap'  ((of_nat n << APIType_capBits newType userSize) + ptr) sz s
              \<and> caps_no_overlap'' ((of_nat n << APIType_capBits newType userSize) + ptr) sz s
              \<and> caps_overlap_reserved'  {(of_nat n << APIType_capBits newType userSize) +
                 ptr.. ptr + of_nat (length destSlots) * 2^ (getObjectSize newType userSize) - 1 } s
              \<and> kernel_data_refs \<inter> {ptr .. ptr + (of_nat (length destSlots) << APIType_capBits newType userSize) - 1} = {}
              \<and> (\<forall>n < length destSlots. cte_at' (cnodeptr + (start * 0x20 + of_nat n * 0x20)) s
                    \<and> ex_cte_cap_wp_to' (\<lambda>_. True) (cnodeptr + (start * 0x20 + of_nat n * 0x20)) s)
              \<and> invs' s
              \<and> 2 ^ APIType_capBits newType userSize \<le> gsMaxObjectSize s
              \<and> (\<exists>cn. gsCNodes s cnodeptr = Some cn \<and> unat start + length destSlots \<le> 2 ^ cn)
              \<and> cnodeptr \<notin> {ptr .. ptr + (of_nat (length destSlots)<< APIType_capBits newType userSize) - 1}
              \<and> (\<forall>k < length destSlots - n.
                 cte_wp_at' (\<lambda>c. cteCap c = NullCap)
                 (cnodeptr + (of_nat k * 0x20 + start * 0x20 + of_nat n * 0x20)) s)
              \<and> descendants_range_in' {(of_nat n << APIType_capBits newType userSize) +
                 ptr.. (ptr && ~~ mask sz) + 2 ^ sz  - 1} srcSlot (ctes_of s)"
              in hoare_pre(1))
             apply wp
            apply (clarsimp simp:createObject_hs_preconds_def conj_comms add.commute[where b=ptr]
                   invs_valid_pspace' invs_pspace_distinct' invs_pspace_aligned'
                   invs_pspace_canonical' invs_ksCurDomain_maxDomain')
            apply (subst intvl_range_conv)
              apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
               subgoal by (simp add:is_aligned_shiftl_self)
              apply (fold_subgoals (prefix))[2]
             subgoal premises prems using prems
               by (simp_all add: range_cover_sz'[where 'a=machine_word_len, folded word_bits_def]
                                 word_bits_def range_cover_def)
            apply (simp add: range_cover_not_in_neqD canonical_address_neq_mask)
            apply (intro conjI)
                    apply (drule_tac p = n in range_cover_no_0)
                      apply (simp add:shiftl_t2n mult.commute)+
                   apply (cut_tac x=num in unat_lt2p, simp)
                   apply (simp add: unat_arith_simps unat_of_nat, simp split: if_split)
                              apply (intro impI, erule order_trans[rotated], simp)
                  apply (erule pspace_no_overlap'_le)
                   apply (fold_subgoals (prefix))[2]
                  subgoal premises prems using prems
                            by (simp add:range_cover.sz[where 'a=machine_word_len, folded word_bits_def])+
                 subgoal by (simp add: range_cover_neg_mask_offset)
                apply (rule range_cover_one)
                  apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
                   apply (simp add: is_aligned_shiftl_self)
                  apply (fold_subgoals (prefix))[2]
                 subgoal premises prems using prems
                           by (simp add: range_cover_sz'[where 'a=machine_word_len, folded word_bits_def]
                                         range_cover.sz[where 'a=machine_word_len, folded word_bits_def])+
                apply (simp add: word_bits_def range_cover_def)
               apply (rule range_cover_full)
                apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
                 apply (simp add:is_aligned_shiftl_self)
                apply (fold_subgoals (prefix))[2]
               subgoal premises prems using prems
                         by (simp add: range_cover_sz'[where 'a=machine_word_len, folded word_bits_def]
                                       range_cover.sz[where 'a=machine_word_len, folded word_bits_def])+
              apply (erule caps_overlap_reserved'_subseteq)
              apply (frule_tac x="of_nat n" in range_cover_bound3)
               apply (rule word_of_nat_less)
               apply (simp add: range_cover.unat_of_nat_n)
              apply (clarsimp simp: shiftl_t2n blah mult.commute)
             apply (erule disjoint_subset[rotated])
             apply (rule_tac p1 = n in subset_trans[OF _ range_cover_subset])
                apply (simp add: upto_intvl_eq is_aligned_add range_cover.aligned is_aligned_shiftl)
                apply (simp add: shiftl_t2n mult.commute)
               apply simp+
            apply (erule caps_overlap_reserved'_subseteq)
            apply (frule_tac x = "of_nat n" in range_cover_bound3)
             apply (rule word_of_nat_less)
             apply (simp add: range_cover.unat_of_nat_n)
            apply (clarsimp simp:  shiftl_t2n blah mult.commute)
           apply (clarsimp simp: createObject_c_preconds_def add.commute[where b=ptr] from_bool_to_bool_iff
                           cong: region_is_bytes_cong)
           apply vcg
          apply (clarsimp simp: cte_C_size conj_comms untypedBits_defs)
          apply (simp cong: conj_cong)
          apply (intro conjI impI)
              apply (simp add: unat_eq_def)
             apply (drule range_cover_sz')
             apply (simp add: unat_eq_def word_less_nat_alt)
            apply (simp add: hrs_htd_update typ_region_bytes_actually_is_bytes)
           apply clarsimp
           apply (erule heap_list_is_zero_mono)
           apply (subgoal_tac "unat (num - of_nat n) \<noteq> 0")
            apply simp
           apply (simp only: unat_eq_0, clarsimp simp: unat_of_nat)
          apply (frule range_cover_sz')
          apply (clarsimp simp: Let_def hrs_htd_update
                                APIType_capBits_def[where ty="APIObjectType ArchTypes_H.apiobject_type.Untyped"])
         apply (simp, subst range_cover.unat_of_nat_n)
          apply (erule range_cover_le)
          subgoal by simp
         subgoal by (simp add:word_unat.Rep_inverse')
        apply clarsimp
        apply (rule conseqPre, vcg exspec=insertNewCap_preserves_bytes_flip
                                   exspec=createObject_preserves_bytes)
        apply (clarsimp simp del: imp_disjL)
        apply (frule(1) offset_intvl_first_chunk_subsets_unat,
          erule order_less_le_trans)
         apply (drule range_cover.weak)
         apply (simp add: word_le_nat_alt unat_of_nat)

        apply (drule spec, drule mp, rule refl[where t="object_type_from_H newType"])
        apply clarsimp
        apply (rule context_conjI)
         apply (simp add: hrs_htd_update)
         apply (simp add: region_actually_is_bytes'_def, rule ballI)
         apply (drule bspec, erule(1) subsetD)
         apply (drule(1) orthD2)
         apply (simp add: Ball_def unat_eq_def typ_bytes_region_out)
        apply (erule trans[OF heap_list_h_eq2 heap_list_is_zero_mono2, rotated])
         apply (simp add: word_shiftl_add_distrib field_simps)
        apply (rule sym, rule byte_regions_unmodified_region_is_bytes)
          apply (erule byte_regions_unmodified_trans, simp_all)[1]
          apply (simp add: byte_regions_unmodified_def)
         apply simp
        apply assumption

       apply (clarsimp simp:conj_comms field_simps
                       createObject_hs_preconds_def range_cover_sz')
       apply (subgoal_tac "is_aligned (ptr + (1 + of_nat n << APIType_capBits newType userSize))
         (APIType_capBits newType userSize)")
        prefer 2
        apply (rule aligned_add_aligned[OF range_cover.aligned],assumption)
         apply (rule is_aligned_shiftl_self)
        apply (simp)
       apply (simp add: range_cover_one[OF _  range_cover.sz(2) range_cover.sz(1)])
       including no_pre
       apply (wp insertNewCap_invs' insertNewCap_valid_pspace' insertNewCap_caps_overlap_reserved'
                 insertNewCap_pspace_no_overlap' insertNewCap_caps_no_overlap'' insertNewCap_descendants_range_in'
                 insertNewCap_untypedRange hoare_vcg_all_lift insertNewCap_cte_at static_imp_wp)
         apply (wp insertNewCap_cte_wp_at_other)
        apply (wp hoare_vcg_all_lift static_imp_wp insertNewCap_cte_at)
       apply (clarsimp simp:conj_comms |
         strengthen invs_valid_pspace' invs_pspace_aligned'
         invs_pspace_distinct')+
       apply (frule range_cover.range_cover_n_less)
       apply (subst upt_enum_offset_trivial)
         apply (rule word_leq_le_minus_one[OF word_of_nat_le])
          apply (fold_subgoals (prefix))[3]
          subgoal premises prems using prems
             by (simp add:word_bits_conv minus_one_norm range_cover_not_zero[rotated])+
       apply (simp add: intvl_range_conv aligned_add_aligned[OF range_cover.aligned]
              is_aligned_shiftl_self range_cover_sz')
       apply (subst intvl_range_conv)
         apply (erule aligned_add_aligned[OF range_cover.aligned])
          apply (rule is_aligned_shiftl_self, rule le_refl)
        apply (erule range_cover_sz')
       apply (subst intvl_range_conv)
         apply (erule aligned_add_aligned[OF range_cover.aligned])
          apply (rule is_aligned_shiftl_self, rule le_refl)
        apply (erule range_cover_sz')
       apply (rule hoare_pre)
        apply (strengthen pspace_no_overlap'_strg[where sz = sz])
        apply (clarsimp simp:range_cover.sz conj_comms)
        apply (wp createObject_invs'
                  createObject_caps_overlap_reserved_ret' createObject_valid_cap'
                  createObject_descendants_range' createObject_idlethread_range
                  hoare_vcg_all_lift createObject_IRQHandler createObject_parent_helper
                  createObject_caps_overlap_reserved' createObject_caps_no_overlap''
                  createObject_pspace_no_overlap' createObject_cte_wp_at'
                  createObject_ex_cte_cap_wp_to createObject_descendants_range_in'
                  createObject_caps_overlap_reserved'
                  hoare_vcg_prop createObject_gsCNodes_p createObject_cnodes_have_size)
        apply (rule hoare_vcg_conj_lift[OF createObject_capRange_helper])
         apply (wp createObject_cte_wp_at' createObject_ex_cte_cap_wp_to
                   createObject_no_inter[where sz = sz] hoare_vcg_all_lift static_imp_wp)+
       apply (clarsimp simp:invs_pspace_aligned' invs_pspace_distinct' invs_valid_pspace'
         field_simps range_cover.sz conj_comms range_cover.aligned range_cover_sz'
         is_aligned_shiftl_self aligned_add_aligned[OF range_cover.aligned])
       apply (drule_tac x = n and  P = "\<lambda>x. x< length destSlots \<longrightarrow> Q x" for Q in spec)+
       apply clarsimp
       apply (simp add: range_cover_not_in_neqD)
       apply (intro conjI)
                            subgoal by (simp add: word_bits_def range_cover_def)
                           subgoal by (clarsimp simp: cte_wp_at_ctes_of invs'_def valid_state'_def
                                                      valid_global_refs'_def cte_at_valid_cap_sizes_0)
                          subgoal by (erule range_cover_le, simp)
                         subgoal by (simp add: range_cover_in_kernel_mappings shiftl_t2n field_simps)
                        subgoal by (simp add: range_cover_no_0 shiftl_t2n field_simps)
                       apply (erule caps_no_overlap''_le)
                        apply (simp add:range_cover.sz[where 'a=machine_word_len, folded word_bits_def])+
                      apply (erule caps_no_overlap''_le2)
                       apply (erule range_cover_compare_offset,simp+)
                      apply (simp add: range_cover_tail_mask[OF range_cover_le]
                                       range_cover_head_mask[OF range_cover_le])
                     subgoal by (clarsimp simp: APIType_capBits_def objBits_simps' untypedBits_defs)
                    apply (rule contra_subsetD)
                     apply (rule order_trans[rotated], erule range_cover_cell_subset,
                       erule of_nat_mono_maybe[rotated], simp)
                     apply (simp add: upto_intvl_eq shiftl_t2n mult.commute
                                      aligned_add_aligned[OF range_cover.aligned is_aligned_mult_triv2])
                    subgoal by simp
                   apply (rule disjoint_subset2[where B="{ptr .. foo}" for foo, rotated], simp add: Int_commute)
                   apply (rule order_trans[rotated], erule_tac p="Suc n" in range_cover_subset, simp+)
                   subgoal by (simp add: upto_intvl_eq shiftl_t2n mult.commute
                                         aligned_add_aligned[OF range_cover.aligned is_aligned_mult_triv2])
                  apply (simp add:cte_wp_at_no_0)
                 apply (erule caps_overlap_reserved'_subseteq)
                 subgoal by (clarsimp simp:range_cover_compare_offset blah)
                apply (erule descendants_range_in_subseteq')
                subgoal by (clarsimp simp:range_cover_compare_offset blah)
               apply (drule_tac x = 0 in spec)
               subgoal by simp
              apply (erule caps_overlap_reserved'_subseteq)
              apply (clarsimp simp:range_cover_compare_offset blah)
              apply (frule_tac x = "of_nat n" in range_cover_bound3)
               subgoal by (simp add:word_of_nat_less range_cover.unat_of_nat_n blah)
              subgoal by (simp add:field_simps shiftl_t2n blah)
             apply (simp add:shiftl_t2n field_simps)
             apply (rule contra_subsetD)
              apply (rule_tac x1 = 0 in subset_trans[OF _ range_cover_cell_subset,rotated ])
                apply (erule_tac p = n in range_cover_offset[rotated])
                subgoal by simp
               apply simp
               apply (rule less_diff_gt0)
               subgoal by (simp add:word_of_nat_less range_cover.unat_of_nat_n blah)
              apply (clarsimp simp: field_simps)
               apply (clarsimp simp: valid_idle'_def pred_tcb_at'_def
               dest!:invs_valid_idle' elim!: obj_atE')
             apply (drule(1) pspace_no_overlapD')
             apply (rule_tac x = "ksIdleThread s" in in_empty_interE[rotated], simp)
              prefer 2
              apply (simp add:Int_ac)
             subgoal by (clarsimp simp: blah)
            subgoal by blast
           apply (erule descendants_range_in_subseteq')
           apply (clarsimp simp: blah)
           apply (rule order_trans[rotated], erule_tac x="of_nat n" in range_cover_bound'')
            subgoal by (simp add: word_less_nat_alt unat_of_nat)
           subgoal by (simp add: shiftl_t2n field_simps)
          apply (rule order_trans[rotated],
            erule_tac p="Suc n" in range_cover_subset, simp_all)[1]
          subgoal by (simp add: upto_intvl_eq shiftl_t2n mult.commute
                   aligned_add_aligned[OF range_cover.aligned is_aligned_mult_triv2])
         apply (erule cte_wp_at_weakenE')
         apply (clarsimp simp:shiftl_t2n field_simps)
         apply (erule subsetD)
         apply (erule subsetD[rotated])
         apply (rule_tac p1 = n in subset_trans[OF _ range_cover_subset])
            prefer 2
            apply (simp add:field_simps )
           apply (fold_subgoals (prefix))[2]
           subgoal premises prems using prems by (simp add:field_simps )+
        apply (clarsimp simp: word_shiftl_add_distrib)
        apply (clarsimp simp:blah field_simps shiftl_t2n)
        apply (drule word_eq_zeroI)
        apply (drule_tac p = "Suc n" in range_cover_no_0)
          apply (simp add:field_simps)+
       apply clarsimp
       apply (rule conjI)
        apply (subgoal_tac "of_nat (x + 1) << 5 \<noteq> (0::machine_word)")
         apply (simp add: word_of_nat_plus field_simps shiftl_t2n)
        apply (frule range_cover_n_le'(2))
        apply (subgoal_tac "x < 2 ^ sz")
         prefer 2 apply simp
        apply (drule (1) less_le_trans[OF _ power_increasing], simp)
        apply (match premises in H: \<open>x < 2 ^ maxUntypedSizeBits\<close> for x \<Rightarrow>
                \<open>match premises in K[thin]: _ (multi) \<Rightarrow> \<open>insert H\<close>\<close>)
        apply (rule word_shift_nonzero[where m=maxUntypedSizeBits])
          apply (simp add: less_eq_Suc_le)
          apply (drule PackedTypes.of_nat_mono_maybe_le
                         [where X="2 ^ maxUntypedSizeBits" and 'a=machine_word_len, rotated];
                 simp add: untypedBits_defs)
         apply (simp add: untypedBits_defs)
        apply (rule notI, erule Word.of_nat_0[THEN iffD1, THEN exE])
        apply (rename_tac q; case_tac q; clarsimp simp: untypedBits_defs)
       apply (drule_tac x = "Suc x" in spec)
       subgoal by (clarsimp simp: field_simps)
      apply clarsimp
      apply (subst range_cover.unat_of_nat_n)
       apply (erule range_cover_le)
       apply simp
      apply (simp add:word_unat.Rep_inverse')
      subgoal by (clarsimp simp:range_cover.range_cover_n_less[where 'a=machine_word_len, simplified])
     subgoal by clarsimp
    apply vcg
   apply (rule conseqPre, vcg, clarsimp)
   apply (frule(1) ghost_assertion_size_logic)
   apply (drule range_cover_sz')
   subgoal by (intro conjI impI; simp add: o_def word_of_nat_less)
  apply (rule conjI)
   apply (frule range_cover.aligned)
   apply (frule range_cover_full[OF range_cover.aligned])
    apply (simp add:range_cover_def word_bits_def)
   apply (clarsimp simp: invs_valid_pspace' conj_comms intvl_range_conv
        createObject_hs_preconds_def range_cover.aligned range_cover_full)
   apply (frule(1) range_cover_gsMaxObjectSize, fastforce, assumption)
   apply (simp add: intvl_range_conv[OF range_cover.aligned range_cover_sz']
                    order_trans[OF _ APIType_capBits_min])
   apply (intro conjI)
           subgoal by (simp add: word_bits_def range_cover_def)
          apply (clarsimp simp:rf_sr_def cstate_relation_def Let_def)
          apply (erule pspace_no_overlap'_le)
           apply (fold_subgoals (prefix))[2]
           subgoal premises prems using prems
                     by (simp add:range_cover.sz[where 'a=machine_word_len, simplified] word_bits_def)+
         apply (erule contra_subsetD[rotated])
         subgoal by (rule order_trans[rotated], rule range_cover_subset'[where n=1],
           erule range_cover_le, simp_all, (clarsimp simp: neq_Nil_conv)+)
        apply (rule disjoint_subset2[rotated])
         apply (simp add:Int_ac)
        apply (erule range_cover_subset[where p = 0,simplified])
         subgoal by simp
        subgoal by simp
       subgoal by (simp add: Int_commute shiftl_t2n mult.commute)
      apply (erule cte_wp_at_weakenE')
      apply (clarsimp simp:blah word_and_le2 shiftl_t2n field_simps)
      apply (frule range_cover_bound''[where x = "of_nat (length destSlots) - 1"])
       subgoal by (simp add: range_cover_not_zero[rotated])
      subgoal by (simp add:field_simps)
     subgoal by (erule range_cover_subset[where p=0, simplified]; simp)
    apply clarsimp
    apply (drule_tac x = k in spec)
    apply simp
    apply (drule(1) bspec[OF _ nth_mem])+
    subgoal by (clarsimp simp: field_simps)
   apply clarsimp
   apply (drule(1) bspec[OF _ nth_mem])+
   subgoal by (clarsimp simp:cte_wp_at_ctes_of)
  apply clarsimp
  apply (frule range_cover_sz')
  apply (frule(1) range_cover_gsMaxObjectSize, fastforce, assumption)
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (drule(1) ghost_assertion_size_logic)+
  apply (simp add: o_def)
  apply (case_tac newType,
         simp_all add: object_type_from_H_def Kernel_C_defs
                       nAPIObjects_def APIType_capBits_def split:apiobject_type.splits)[1]
         subgoal by (simp add:unat_eq_def word_unat.Rep_inverse' word_less_nat_alt)
        subgoal by (clarsimp simp:objBits_simps', unat_arith)
       apply (fold_subgoals (prefix))[3]
       subgoal premises prems using prems
         by (clarsimp simp: objBits_simps' unat_eq_def word_unat.Rep_inverse'
                            word_less_nat_alt)+
    by (clarsimp simp: bit_simps pageBitsForSize_def framesize_to_H_def
                       X86_SmallPage_def X86_LargePage_def X64_HugePage_def)+

end

end
