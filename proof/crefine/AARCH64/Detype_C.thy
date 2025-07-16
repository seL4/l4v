(*
 * Copyright 2023, Proofcraft Pty Ltd
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

theory Detype_C
imports Ctac_lemmas_C TcbQueue_C
begin

lemma typ_clear_region_out:
  "x \<notin> {p..+2 ^ bits} \<Longrightarrow> typ_clear_region p bits d x = d x"
  unfolding typ_clear_region_def
  by simp

lemma typ_bytes_region_out:
  "x \<notin> {p..+2 ^ bits} \<Longrightarrow> typ_region_bytes p bits d x = d x"
  unfolding typ_region_bytes_def
  by simp

lemma h_t_valid_ptr_clear_region:
  fixes p :: "'a :: c_type ptr"
  shows "typ_clear_region ptr bits hp,g \<Turnstile>\<^sub>t p =
   ({ptr_val p ..+ size_of (TYPE ('a))} \<inter> {ptr ..+ 2 ^ bits} = {} \<and> hp,g \<Turnstile>\<^sub>t p)"
  unfolding h_t_valid_def
  apply (clarsimp simp: valid_footprint_def Let_def)
  apply (rule iffI)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: disjoint_iff_not_equal)
    apply (drule intvlD)
    apply (clarsimp simp: size_of_def)
    apply (drule spec, drule (1) mp)
    apply (clarsimp simp: typ_clear_region_def)
   apply clarsimp
   apply (drule spec, drule (1) mp)
   apply (clarsimp simp: typ_clear_region_def split: if_split_asm)
  apply clarsimp
  apply (drule spec, drule (1) mp)
  apply (subgoal_tac "ptr_val p + of_nat y \<notin> {ptr..+2 ^ bits}")
  apply (simp add: typ_clear_region_out)
  apply clarsimp
  apply (drule intvlD)
  apply (clarsimp simp: disjoint_iff_not_equal )
  apply (drule_tac x = "ptr_val p + of_nat y" in bspec)
   apply (rule intvlI)
   apply (simp add: size_of_def)
  apply (drule_tac x = "ptr + of_nat k" in bspec)
   apply (erule intvlI)
  apply simp
  done

lemma map_of_le:
  "map_le (map_of xs) m \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> \<forall>(x, v) \<in> set xs. m x = Some v"
  apply (induct xs)
   apply simp
  apply clarsimp
  apply (clarsimp simp: map_le_def dom_map_of_conv_image_fst)
  apply (drule(1) bspec, simp)
  apply (simp(no_asm_use) split: if_split_asm)
   apply (fastforce simp: image_def)
  apply simp
  done

lemma list_map_le_singleton:
  "map_le (list_map xs) [n \<mapsto> x] = (xs = [] \<or> n = 0 \<and> xs = [x])"
  apply (simp add: list_map_def)
  apply (rule iffI)
   apply (drule map_of_le)
    apply simp
   apply (cases xs, simp_all add: list_map_def upt_conv_Cons
                       split: if_split_asm del: upt.simps)
   apply (case_tac list, simp_all add: upt_conv_Cons del: upt.simps)
  apply auto
  done

lemma neq_types_not_typ_slice_eq:
  "\<lbrakk> s \<noteq> t \<rbrakk> \<Longrightarrow> typ_slice_t s k \<noteq> [(t, v)]"
  using ladder_set_self[where s=s and n=k]
  by clarsimp

lemma valid_footprint_typ_region_bytes:
  assumes neq_byte: "td \<noteq> typ_uinfo_t TYPE (word8)"
  shows "valid_footprint (typ_region_bytes ptr bits hp) p td =
   ({p ..+ size_td td} \<inter> {ptr ..+ 2 ^ bits} = {} \<and> valid_footprint hp p td)"
  apply (clarsimp simp: valid_footprint_def Let_def)
  apply (rule iffI)
  apply clarsimp
  apply (rule conjI)
   apply (clarsimp simp: disjoint_iff_not_equal)
    apply (drule intvlD)
    apply (clarsimp simp: size_of_def)
    apply (drule spec, drule (1) mp)
    apply (clarsimp simp: typ_region_bytes_def list_map_le_singleton neq_byte
                          neq_types_not_typ_slice_eq)
   apply clarsimp
   apply (drule spec, drule (1) mp)
   apply (clarsimp simp: typ_region_bytes_def list_map_le_singleton neq_byte
                         neq_types_not_typ_slice_eq
                  split: if_split_asm)
  apply clarsimp
  apply (drule spec, drule (1) mp)
  apply (subgoal_tac "p + of_nat y \<notin> {ptr..+2 ^ bits}")
  apply (simp add: typ_bytes_region_out)
  apply clarsimp
  apply (drule intvlD)
  apply (clarsimp simp: disjoint_iff_not_equal )
  apply (drule_tac x = "p + of_nat y" in bspec)
   apply (rule intvlI)
   apply (simp add: size_of_def)
  apply (drule_tac x = "ptr + of_nat k" in bspec)
   apply (erule intvlI)
  apply simp
  done

lemma h_t_valid_typ_region_bytes:
  fixes p :: "'a :: c_type ptr"
  assumes neq_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE (word8)"
  shows "typ_region_bytes ptr bits hp,g \<Turnstile>\<^sub>t p =
   ({ptr_val p ..+ size_of (TYPE ('a))} \<inter> {ptr ..+ 2 ^ bits} = {} \<and> hp,g \<Turnstile>\<^sub>t p)"
  unfolding h_t_valid_def
  by (simp add: valid_footprint_typ_region_bytes[OF neq_byte]
                size_of_def)

lemma heap_list_s_heap_list':
  fixes p :: "'a :: c_type ptr"
  shows "hrs_htd hp,\<top> \<Turnstile>\<^sub>t p \<Longrightarrow>
  heap_list_s (lift_state hp) (size_of TYPE('a)) (ptr_val p) =
  heap_list (hrs_mem hp) (size_of TYPE('a)) (ptr_val p)"
  apply (cases hp)
  apply (simp add: hrs_htd_def hrs_mem_def heap_list_s_heap_list)
  done

lemma lift_t_typ_clear_region:
  assumes doms: "\<And>x :: 'a :: mem_type ptr. \<lbrakk> hrs_htd hp,g \<Turnstile>\<^sub>t x; x \<in> - (Ptr ` {ptr ..+2 ^ bits}) \<rbrakk>
  \<Longrightarrow> {ptr_val x..+size_of TYPE('a)} \<inter> {ptr..+2 ^ bits} = {}"
  shows "(lift_t g (hrs_htd_update (typ_clear_region ptr bits) hp) :: 'a :: mem_type typ_heap) =
          lift_t g hp |` (- Ptr ` {ptr ..+2 ^ bits})"
  apply (rule ext)
  apply (case_tac "({ptr_val x..+size_of TYPE('a)} \<inter> {ptr..+2 ^ bits} = {} \<and> hrs_htd hp,g \<Turnstile>\<^sub>t x)")
  apply (clarsimp simp add: lift_t_def lift_typ_heap_if s_valid_def h_t_valid_ptr_clear_region)
   apply (subgoal_tac "x \<in> - Ptr ` {ptr..+2 ^ bits}")
   apply clarsimp
    apply (subst heap_list_s_heap_list')
     apply (clarsimp simp add: hrs_htd_update h_t_valid_ptr_clear_region)
     apply (erule h_t_valid_taut)
    apply (subst heap_list_s_heap_list')
     apply (clarsimp elim!:  h_t_valid_taut)
    apply simp
   apply clarsimp
   apply (drule (1) orthD2)
   apply (erule contrapos_np, rule intvl_self)
   apply (simp add: size_of_def wf_size_desc_gt)
  apply (simp add: lift_t_def lift_typ_heap_if s_valid_def h_t_valid_ptr_clear_region  del: disj_not1 split del: if_split)
  apply (subst if_not_P)
   apply simp
   apply (case_tac "x \<in> (- Ptr ` {ptr..+2 ^ bits})")
   apply (simp del: disj_not1)
   apply (erule contrapos_pn)
   apply simp
   apply (erule doms)
   apply simp
  apply simp
  done

lemma image_Ptr:
  "Ptr ` S = {x. ptr_val x \<in> S}"
  apply (safe, simp_all)
  apply (case_tac x, simp_all)
  done

lemma lift_t_typ_region_bytes:
  assumes doms: "\<And>x :: 'a :: mem_type ptr. \<lbrakk> hrs_htd hp,g \<Turnstile>\<^sub>t x; x \<in> - (Ptr ` {ptr ..+2 ^ bits}) \<rbrakk>
  \<Longrightarrow> {ptr_val x..+size_of TYPE('a)} \<inter> {ptr..+2 ^ bits} = {}"
  assumes neq_byte: "typ_uinfo_t TYPE('a) \<noteq> typ_uinfo_t TYPE (word8)"
  shows "(lift_t g (hrs_htd_update (typ_region_bytes ptr bits) hp) :: 'a :: mem_type typ_heap) =
          lift_t g hp |` (- Ptr ` {ptr ..+2 ^ bits})"
  apply (rule ext)
  apply (case_tac "({ptr_val x..+size_of TYPE('a)} \<inter> {ptr..+2 ^ bits} = {} \<and> hrs_htd hp,g \<Turnstile>\<^sub>t x)")
   apply (clarsimp simp add: lift_t_def lift_typ_heap_if s_valid_def
                             h_t_valid_typ_region_bytes neq_byte)
   apply (subgoal_tac "x \<in> - Ptr ` {ptr..+2 ^ bits}")
    apply clarsimp
    apply (subst heap_list_s_heap_list')
     apply (clarsimp simp add: hrs_htd_update h_t_valid_typ_region_bytes neq_byte)
     apply (erule h_t_valid_taut)
    apply (subst heap_list_s_heap_list')
     apply (clarsimp elim!:  h_t_valid_taut)
    apply simp
   apply (simp add: image_Ptr)
   apply (cut_tac p=x in mem_type_self)
   apply blast
  apply (simp add: lift_t_def lift_typ_heap_if s_valid_def neq_byte
                   h_t_valid_typ_region_bytes  del: disj_not1 split del: if_split)
  apply (clarsimp simp add: restrict_map_def)
  apply (blast dest: doms)
  done

context kernel
begin

lemma cmap_relation_h_t_valid:
  fixes p :: "'a :: c_type ptr"
  shows "\<lbrakk>cmap_relation am (cslift s' :: 'a typ_heap) f rel; s' \<Turnstile>\<^sub>c p;
  \<And>v v' x. \<lbrakk>f x = p; am x = Some v; cslift s' p = Some v'; rel v v'\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  unfolding cmap_relation_def
  apply (clarsimp simp: h_t_valid_clift_Some_iff)
  apply (drule equalityD2)
  apply (drule (1) subsetD [OF _ domI])
  apply clarsimp
  apply (drule (1) bspec [OF _ domI])
  apply clarsimp
  done

lemma valid_untyped_capE:
  assumes vuc: "s \<turnstile>' UntypedCap d ptr bits idx"
  and rl: "\<lbrakk>is_aligned ptr bits; valid_untyped' d ptr bits idx s; ptr \<noteq> 0; bits < word_bits \<rbrakk> \<Longrightarrow> P"
  shows P
proof (rule rl)
  from vuc show al: "is_aligned ptr bits" and vu: "valid_untyped' d ptr bits idx s" and p0: "ptr \<noteq> 0"
    unfolding valid_cap'_def capAligned_def by auto

  from al p0 show wb: "bits < word_bits"
    by (clarsimp elim!: is_aligned_get_word_bits[where 'a=machine_word_len, folded word_bits_def])
qed

(* FIXME: move *)
lemma valid_untyped_pspace_no_overlap':
 assumes vuc: "s \<turnstile>' UntypedCap d ptr bits idx"
  and    idx: "idx< 2^ bits"
  and psp_al: "pspace_aligned' s" "pspace_distinct' s"
  shows  "pspace_no_overlap' (ptr + of_nat idx) bits s"

proof -
  note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  from vuc have al: "is_aligned ptr bits" and vu: "valid_untyped' d ptr bits idx s" and p0: "ptr \<noteq> 0"
    and wb: "bits < word_bits"
    by (auto elim!: valid_untyped_capE)

  from vuc idx
   have [simp]: "(ptr + (of_nat idx) && ~~ mask bits) = ptr"
    apply -
    apply (rule is_aligned_add_helper[THEN conjunct2])
     apply (clarsimp simp:valid_cap'_def capAligned_def)+
    apply (rule word_of_nat_less)
    apply simp
    done

  show "pspace_no_overlap' (ptr + of_nat idx) bits s"
    using vuc idx psp_al
    apply -
    apply (clarsimp simp:valid_cap'_def valid_untyped'_def pspace_no_overlap'_def)
    apply (drule_tac x = x in spec)
    apply (frule(1) pspace_alignedD')
    apply (frule(1) pspace_distinctD')
    apply (clarsimp simp:ko_wp_at'_def obj_range'_def p_assoc_help)
    done
  qed

lemma cmap_relation_disjoint:
  fixes  rel :: "'a :: pspace_storable \<Rightarrow> 'b :: mem_type \<Rightarrow> bool" and x :: "'b :: mem_type ptr"
  assumes vuc: "s \<turnstile>' UntypedCap d ptr bits idx"
  and   invs: "invs' s"
  and     cm: "cmap_relation (proj \<circ>\<^sub>m (ksPSpace s)) (cslift s') Ptr rel"
  and     ht: "s' \<Turnstile>\<^sub>c x"
  and     tp: "\<And>ko v. proj ko = Some v \<Longrightarrow> koType TYPE('a) = koTypeOf ko"
  and     xv: "x \<notin> Ptr ` {ptr..+2 ^ bits}"
  and    sof: "size_td (typ_info_t TYPE('b)) \<le> 2 ^ objBits (undefined :: 'a)"
  shows  "{ptr_val x..+size_of TYPE('b)} \<inter> {ptr..+2 ^ bits} = {}"
proof -
  from vuc have al: "is_aligned ptr bits"
    and vu: "valid_untyped' d ptr bits idx s" and p0: "ptr \<noteq> 0"
    and wb: "bits < word_bits"
    and [simp]: "(ptr && ~~ mask bits) = ptr"
    by (auto elim!: valid_untyped_capE)

  note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  let ?ran = "{ptr..ptr + 2 ^ bits - 1}"
  let ?s = "(s\<lparr>ksPSpace := (ksPSpace s) |` (- ?ran)\<rparr>)"
  from cm ht obtain ko and v :: 'a where ks: "ksPSpace s (ptr_val x) = Some ko" and po: "proj ko = Some v"
    apply (rule cmap_relation_h_t_valid)
    apply (clarsimp simp: map_comp_Some_iff)
    done

  let ?oran = "{ptr_val x .. ptr_val x + 2 ^ objBitsKO ko - 1}"
  let ?ran' = "{ptr..+2 ^ bits}"
  let ?oran' = "{ptr_val x..+2 ^ objBitsKO ko}"

  have ran' [simp]: "?ran' = ?ran" using al wb upto_intvl_eq by blast

  have oran' [simp]: "?oran' = ?oran"
  proof (rule upto_intvl_eq)
    from invs have "pspace_aligned' s" ..
    with ks show "is_aligned (ptr_val x) (objBitsKO ko)"  ..
  qed

  from xv have "ptr_val x \<in> (- ?ran)" apply (simp only: ran' Compl_iff)
    apply (erule contrapos_nn)
    apply (erule image_eqI [rotated])
    apply simp
    done

  hence "ksPSpace ?s (ptr_val x) = Some ko" using ks by auto
  hence "?oran \<inter> ?ran = {}"
  proof (rule pspace_no_overlapD'[where p = ptr and bits = bits,simplified])
    from invs have "valid_pspace' s" ..
    with vu al show "pspace_no_overlap' ptr bits ?s" using valid_untyped_no_overlap
      by (clarsimp simp: mask_def add_diff_eq)
  qed

  hence "?oran' \<inter> ?ran' = {}" by simp
  thus "{ptr_val x..+size_of TYPE('b)} \<inter> ?ran' = {}"
  proof (rule disjoint_subset [rotated])
    have "objBits (undefined :: 'a) = objBitsKO ko" using po
      apply (simp add: objBits_def)
      apply (rule koType_objBitsKO)
      apply (subst iffD1 [OF project_koType])
      apply (fastforce simp add: project_inject)
      apply (erule tp)
      done
    thus "{ptr_val x..+size_of TYPE('b)} \<subseteq> ?oran'" using sof
      apply -
      apply (rule intvl_start_le)
      apply (simp add: size_of_def)
      done
  qed
qed

lemma vut_subseteq:
notes blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
shows "\<lbrakk>s \<turnstile>' UntypedCap d ptr bits idx;idx < 2 ^ bits\<rbrakk>
 \<Longrightarrow> Ptr ` {ptr + of_nat idx..ptr + 2 ^ bits - 1} \<subseteq> Ptr ` {ptr ..+ 2^bits}" (is "\<lbrakk>?a1;?a2\<rbrakk> \<Longrightarrow> ?b \<subseteq> ?c")
  apply (subgoal_tac  "?c =  Ptr ` {ptr ..ptr + 2 ^ bits - 1}")
   apply (simp add:inj_image_subset_iff)
   apply (clarsimp simp:blah valid_cap'_def capAligned_def)
   apply (rule is_aligned_no_wrap')
     apply simp+
    apply (rule word_of_nat_less)
    apply simp
  apply (rule arg_cong[where f = "\<lambda>x. Ptr ` x"])
  apply (rule upto_intvl_eq)
  apply (clarsimp simp:valid_cap'_def capAligned_def)+
  done

(* CLAG : IpcCancel_C *)
lemma tcb_ptr_to_ctcb_ptr_imageD:
  "x \<in> tcb_ptr_to_ctcb_ptr ` S \<Longrightarrow> ctcb_ptr_to_tcb_ptr x \<in> S"
  apply (erule imageE)
  apply simp
  done

lemma ctcb_ptr_to_tcb_ptr_imageI:
  "ctcb_ptr_to_tcb_ptr x \<in> S \<Longrightarrow> x \<in> tcb_ptr_to_ctcb_ptr ` S"
  apply (drule imageI [where f = tcb_ptr_to_ctcb_ptr])
  apply simp
  done

lemma aligned_ranges_subset_or_disjointE [consumes 2, case_names disjoint subset1 subset2]:
  "\<lbrakk>is_aligned p n; is_aligned p' n';
   {p..p + 2 ^ n - 1} \<inter> {p'..p' + 2 ^ n' - 1} = {}  \<Longrightarrow> P;
   {p..p + 2 ^ n - 1} \<subseteq> {p'..p' + 2 ^ n' - 1} \<Longrightarrow> P;
   {p'..p' + 2 ^ n' - 1} \<subseteq> {p..p + 2 ^ n - 1} \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (drule (1) aligned_ranges_subset_or_disjoint)
  apply blast
  done

lemma valid_untyped_cap_ko_at_disjoint:
  assumes vu: "s \<turnstile>' UntypedCap d ptr bits idx"
  and   koat: "ko_at' ko x s"
  and     pv: "{x .. x + 2 ^ objBits ko - 1} \<inter> {ptr .. ptr + 2 ^ bits - 1} \<noteq> {}"
  shows   "{x .. x + 2 ^ objBits ko - 1} \<subseteq> {ptr .. ptr + 2 ^ bits - 1}"

proof -
  from vu have "is_aligned ptr bits"
    unfolding valid_cap'_def capAligned_def by simp

  moreover from koat have "is_aligned x (objBits ko)"
    by (rule obj_atE') (simp add: objBits_def project_inject)

  ultimately show ?thesis
  proof (cases rule: aligned_ranges_subset_or_disjointE)
    case disjoint
    thus ?thesis using pv by auto
  next
    case subset2 thus ?thesis .
  next
    case subset1
    note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex
    have  "\<not> ko_wp_at' (\<lambda>ko. {ptr..ptr + 2 ^ bits - 1} \<subset> obj_range' x ko) x s"
      using vu unfolding valid_cap'_def valid_untyped'_def
      apply clarsimp
      apply (drule_tac x = x in spec)
      apply (clarsimp simp: ko_wp_at'_def mask_def add_diff_eq)
      done

    with koat have "\<not> {ptr..ptr + 2 ^ bits - 1} \<subset> {x..x + 2 ^ objBits ko - 1}"
      apply -
      apply (erule obj_atE')+
      apply (simp add: ko_wp_at'_def obj_range'_def not_less objBits_def project_inject
                        mask_def add_diff_eq)
      done

    thus ?thesis using subset1
      by (simp add: psubset_eq del: Icc_eq_Icc)
  qed
qed

(* FIXME x64: tcb bits change *)
lemma tcb_ptr_to_ctcb_ptr_in_range:
  fixes tcb :: tcb
  assumes tat: "ko_at' tcb x s"
  shows "ptr_val (tcb_ptr_to_ctcb_ptr x) \<in> {x..x + 2 ^ objBits tcb - 1}"
proof -
  from tat have al: "is_aligned x tcbBlockSizeBits" by (clarsimp elim!: obj_atE' simp: objBits_simps')
  hence "x \<le> x + 2 ^ tcbBlockSizeBits - 1"
    by (rule is_aligned_no_overflow)

  moreover from al have "x \<le> x + 2 ^ ctcb_size_bits"
    by (rule is_aligned_no_wrap') (simp add: ctcb_size_bits_def objBits_defs)

  ultimately show ?thesis
    unfolding tcb_ptr_to_ctcb_ptr_def
    by (simp add: ctcb_offset_defs objBits_simps' add.commute)
       (subst word_plus_mono_right; simp)
qed

lemma tcb_ptr_to_ctcb_ptr_in_range':
  fixes tcb :: tcb
  assumes al: "is_aligned (ctcb_ptr_to_tcb_ptr x) tcbBlockSizeBits"
  shows "{ptr_val x ..+ size_of TYPE (tcb_C)}
          \<subseteq> {ctcb_ptr_to_tcb_ptr x..+2 ^ objBits tcb}"
proof -
  from al have "ctcb_ptr_to_tcb_ptr x \<le> ctcb_ptr_to_tcb_ptr x + 2 ^ tcbBlockSizeBits - 1"
    by (rule is_aligned_no_overflow)

  moreover from al have "ctcb_ptr_to_tcb_ptr x \<le> ctcb_ptr_to_tcb_ptr x + 2 ^ ctcb_size_bits"
    by (rule is_aligned_no_wrap') (simp add: ctcb_size_bits_def objBits_defs)

  moreover from al have "is_aligned (ptr_val x) ctcb_size_bits" by (rule ctcb_ptr_to_tcb_ptr_aligned)
  moreover from al have "{ctcb_ptr_to_tcb_ptr x..+2 ^ objBits tcb} = {ctcb_ptr_to_tcb_ptr x.. ctcb_ptr_to_tcb_ptr x + 2 ^ objBits tcb - 1}"
    apply -
    apply (rule upto_intvl_eq)
     apply (simp add: objBits_simps)
    done

  ultimately show ?thesis
    unfolding ctcb_ptr_to_tcb_ptr_def ctcb_offset_defs
    apply -
    apply (clarsimp simp: field_simps objBits_simps' size_of_def)
    apply (drule intvlD)
    apply clarsimp
    apply (rule conjI)
     apply (erule order_trans, erule is_aligned_no_wrap')
     apply (rule of_nat_power)
      apply simp
     apply simp
    apply (rule word_plus_mono_right)
     apply (simp add: word_le_nat_alt unat_of_nat)
    apply (erule is_aligned_no_wrap')
    apply simp
    done
qed

lemma valid_untyped_cap_ctcb_member:
  fixes tcb :: tcb
  assumes vu: "s \<turnstile>' UntypedCap d ptr bits idx"
  and   koat: "ko_at' tcb x s"
  and     pv: "ptr_val (tcb_ptr_to_ctcb_ptr x) \<in> {ptr .. ptr + 2 ^ bits - 1}"
  shows   "x \<in> {ptr .. ptr + 2 ^ bits - 1}"
  using vu
proof -
  from vu koat have "{x..x + 2 ^ objBits tcb - 1} \<subseteq> {ptr..ptr + 2 ^ bits - 1}"
  proof (rule valid_untyped_cap_ko_at_disjoint)
    from koat have "ptr_val (tcb_ptr_to_ctcb_ptr x) \<in> {x..x + 2 ^ objBits tcb - 1}"
      by (rule tcb_ptr_to_ctcb_ptr_in_range)
    thus "{x..x + 2 ^ objBits tcb - 1} \<inter> {ptr..ptr + 2 ^ bits - 1} \<noteq> {}" using pv
      apply -
      apply rule
      apply (drule (1) orthD1)
      apply simp
      done
  qed

  thus ?thesis
  proof (rule set_mp)
    from koat have "is_aligned x (objBits tcb)"  by (clarsimp elim!: obj_atE' simp: objBits_simps)
    thus "x \<in> {x..x + 2 ^ objBits tcb - 1}"
      apply (rule base_member_set [simplified field_simps])
      apply (simp add: objBits_simps' word_bits_conv)
      done
  qed
qed

lemma ko_at_is_aligned' [intro?]:
  "ko_at' ko p s \<Longrightarrow> is_aligned p (objBits ko)"
  apply (erule obj_atE')
  apply (simp add: objBits_def project_inject)
  done

lemma cmap_relation_disjoint_tcb:
  fixes x :: "tcb_C ptr"
  assumes vuc: "s \<turnstile>' UntypedCap d ptr bits idx"
  and    invs: "invs' s"
  and      cm: "cmap_relation (projectKO_opt \<circ>\<^sub>m (ksPSpace s)) (cslift s') tcb_ptr_to_ctcb_ptr ctcb_relation"
  and      ht: "s' \<Turnstile>\<^sub>c x"
  and      xv: "x \<notin> Ptr ` {ptr..+2 ^ bits}"
  shows  "{ptr_val x..+size_of TYPE(tcb_C)} \<inter> {ptr..+2 ^ bits} = {}"
proof -
  let ?ran = "{ptr..ptr + 2 ^ bits - 1}"
  let ?s = "(s\<lparr>ksPSpace := (ksPSpace s) |` (- ?ran)\<rparr>)"
  from cm ht invs obtain tcb :: tcb where koat: "ko_at' tcb  (ctcb_ptr_to_tcb_ptr x) s"
    apply -
    apply (erule (1) cmap_relation_h_t_valid)
    apply (drule (1) map_to_ko_atI')
    apply clarsimp
    done

  let ?oran = "{ctcb_ptr_to_tcb_ptr x .. ctcb_ptr_to_tcb_ptr x + 2 ^ objBits tcb - 1}"
  let ?ran' = "{ptr..+2 ^ bits}"
  let ?oran' = "{ctcb_ptr_to_tcb_ptr x..+2 ^ objBits tcb}"

  from vuc have al: "is_aligned ptr bits" and vu: "valid_untyped' d ptr bits idx s" and p0: "ptr \<noteq> 0"
    and wb: "bits < word_bits"
    by (auto elim!: valid_untyped_capE)

  have ran' [simp]: "?ran' = ?ran" using al wb upto_intvl_eq by blast

  have oran' [simp]: "?oran' = ?oran"
  proof (rule upto_intvl_eq)
    from koat show "is_aligned (ctcb_ptr_to_tcb_ptr x) (objBits tcb)"  ..
  qed

  show ?thesis
  proof (rule disjoint_subset)
    from xv koat have "\<not> ?oran \<subseteq> ?ran"
      apply -
      apply (erule contrapos_nn)
      apply (drule tcb_ptr_to_ctcb_ptr_in_range)
      apply (rule image_eqI [where x = "ptr_val x"])
       apply simp
      apply (drule (1) subsetD)
      apply simp
      done

    thus "{ctcb_ptr_to_tcb_ptr x..+2 ^ objBits tcb} \<inter> {ptr..+2 ^ bits} = {}"
      apply (rule contrapos_np)
      apply (rule valid_untyped_cap_ko_at_disjoint [OF vuc koat])
      apply simp
      done

    from koat show "{ptr_val x..+size_of TYPE(tcb_C)} \<subseteq> {ctcb_ptr_to_tcb_ptr x..+2 ^ objBits tcb}"
      by (metis tcb_ptr_to_ctcb_ptr_in_range' tcb_aligned' obj_at'_weakenE)
  qed
qed

lemma ctes_of_is_aligned:
  fixes s :: "kernel_state"
  assumes ks: "ctes_of s p = Some cte"
  shows "is_aligned p (objBits cte)"
proof -
  have "cte_wp_at' ((=) cte) p s" using ks by (clarsimp simp: cte_wp_at_ctes_of)
  thus ?thesis
    apply (simp add: cte_wp_at_cases' objBits_simps' cte_level_bits_def)
    apply (erule disjE)
     apply simp
    apply clarsimp
    supply cteSizeBits_def[simp]
    apply (drule_tac y = n in aligned_add_aligned [where m = cte_level_bits, simplified cte_level_bits_def])
     apply (simp add: tcb_cte_cases_def is_aligned_def split: if_split_asm)
     apply (simp add: word_bits_conv)
    apply simp
    done
qed

lemma cte_wp_at_casesE' [consumes 1, case_names cte tcb]:
  "\<lbrakk>cte_wp_at' P p s;
  \<And>cte. \<lbrakk> ksPSpace s p = Some (KOCTE cte); is_aligned p cte_level_bits; P cte; ps_clear p cteSizeBits s \<rbrakk> \<Longrightarrow> R;
  \<And>n tcb getF setF. \<lbrakk>
     ksPSpace s (p - n) = Some (KOTCB tcb);
     is_aligned (p - n) tcbBlockSizeBits;
     tcb_cte_cases n = Some (getF, setF);
     P (getF tcb); ps_clear (p - n) tcbBlockSizeBits s\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (fastforce simp: cte_wp_at_cases')


(* FIXME: MOVE *)
lemma tcb_cte_cases_in_range3:
  assumes tc: "tcb_cte_cases (y - x) = Some v"
  and     al: "is_aligned x tcbBlockSizeBits"
  shows   "y + 2 ^ cteSizeBits - 1 \<le> x + 2 ^ tcbBlockSizeBits - 1"
proof -
  note [simp] = objBits_defs ctcb_size_bits_def
  from tc obtain q where yq: "y = x + q" and qv: "q \<le> 2 ^ ctcb_size_bits - 1"
    unfolding tcb_cte_cases_def
    by (simp add: diff_eq_eq split: if_split_asm)

  have "q + (2 ^ cteSizeBits - 1) \<le> (2 ^ ctcb_size_bits - 1) + (2 ^ cteSizeBits - 1)" using qv
    by (rule word_plus_mcs_3) simp
  also have "\<dots> \<le> 2 ^ tcbBlockSizeBits - 1" by simp
  finally have "x + (q + (2 ^ cteSizeBits - 1)) \<le> x + (2 ^ tcbBlockSizeBits - 1)"
    apply (rule word_plus_mono_right)
    apply (rule is_aligned_no_overflow' [OF al])
    done

  thus ?thesis using yq by (simp add: field_simps)
qed


lemma tcb_cte_in_range:
  "\<lbrakk> ksPSpace s p = Some (KOTCB tcb); is_aligned p tcbBlockSizeBits;
  tcb_cte_cases n = Some (getF, setF) \<rbrakk>
  \<Longrightarrow> {p + n.. (p + n) + 2 ^ objBits (cte :: cte) - 1} \<subseteq> {p .. p + 2 ^ objBits tcb - 1}"
  apply (rule range_subsetI)
  apply (erule (1) tcb_cte_cases_in_range1 [where y = "p + n" and x = p, simplified])
  apply (frule (1) tcb_cte_cases_in_range3 [where y = "p + n" and x = p, simplified])
  apply (simp add: objBits_simps)
  done

lemma tcb_cte_cases_aligned:
  "\<lbrakk>is_aligned p tcbBlockSizeBits; tcb_cte_cases n = Some (getF, setF)\<rbrakk>
  \<Longrightarrow> is_aligned (p + n) (objBits (cte :: cte))"
  apply (erule aligned_add_aligned)
   apply (simp add: tcb_cte_cases_def is_aligned_def objBits_simps' split: if_split_asm)
  apply (simp add: objBits_simps')
  done

lemma tcb_cte_in_range':
  "\<lbrakk> ksPSpace s p = Some (KOTCB tcb); is_aligned p tcbBlockSizeBits;
  tcb_cte_cases n = Some (getF, setF) \<rbrakk>
  \<Longrightarrow> {p + n..+2 ^ objBits (cte :: cte)} \<subseteq> {p ..+ 2 ^ objBits tcb}"
  apply (subst upto_intvl_eq)
    apply (erule (1) tcb_cte_cases_aligned)
   apply (simp add: objBits_def)
  apply (subst upto_intvl_eq)
   apply (simp add: objBits_simps)
  apply (simp add: objBits_def)
  apply (erule (2) tcb_cte_in_range[unfolded objBits_def, simplified])
  done

(* clagged from above :( Were I smarter or if I cared more I could probably factor out more \<dots>*)
lemma cmap_relation_disjoint_cte:
  assumes vuc: "s \<turnstile>' UntypedCap d ptr bits idx"
  and   invs: "invs' s"
  and     cm: "cmap_relation (ctes_of s) (cslift s') Ptr ccte_relation"
  and     ht: "s' \<Turnstile>\<^sub>c (x :: cte_C ptr)"
  and     xv: "x \<notin> Ptr ` {ptr..+2 ^ bits}"
  shows  "{ptr_val x..+size_of TYPE(cte_C)} \<inter> {ptr..+2 ^ bits} = {}"
proof -
  from vuc have al: "is_aligned ptr bits" and vu: "valid_untyped' d ptr bits idx s" and p0: "ptr \<noteq> 0"
    and wb: "bits < word_bits" and [simp]: "(ptr && ~~ mask bits) = ptr"
    by (auto elim!: valid_untyped_capE)

  note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  let ?ran = "{ptr..ptr + 2 ^ bits - 1}"
  let ?s = "(s\<lparr>ksPSpace := (ksPSpace s) |` (- ?ran)\<rparr>)"
  from cm ht obtain cte where ks: "ctes_of s (ptr_val x) = Some cte"
    apply (rule cmap_relation_h_t_valid)
    apply (clarsimp simp: map_comp_Some_iff)
    done

  let ?oran = "{ptr_val x .. ptr_val x + 2 ^ objBits cte - 1}"

  let ?ran' = "{ptr..+2 ^ bits}"
  let ?oran' = "{ptr_val x..+2 ^ objBits cte}"

  have ran' [simp]: "?ran' = ?ran" using al wb upto_intvl_eq by auto

  have oran' [simp]: "?oran' = ?oran"
  proof (rule upto_intvl_eq)
    from ks show "is_aligned (ptr_val x) (objBits cte)"
      by (rule ctes_of_is_aligned)
  qed

  from xv have px: "ptr_val x \<in> (- ?ran)"
    apply (simp only: ran' Compl_iff)
    apply (erule contrapos_nn)
    apply (erule image_eqI [rotated])
    apply simp
    done

  from ks have "cte_wp_at' ((=) cte) (ptr_val x) s" by (clarsimp simp: cte_wp_at_ctes_of)
  thus ?thesis
  proof (cases rule: cte_wp_at_casesE')
    case (cte cte')

    hence "ksPSpace ?s (ptr_val x) = Some (injectKOS cte)" using px by simp
    hence "?oran \<inter> ?ran = {}"
      unfolding objBits_def
    proof (rule pspace_no_overlapD'[where p = ptr and bits = bits,simplified])
      from invs have "valid_pspace' s" ..
      with vu al show "pspace_no_overlap' ptr bits ?s" using valid_untyped_no_overlap
        by (clarsimp simp: mask_def add_diff_eq)
    qed
    hence "?oran' \<inter> ?ran' = {}" by simp
    thus ?thesis by (simp add: objBits_simps' size_of_def)
  next
    case (tcb n tcb _ _)

    hence koat: "ko_at' tcb (ptr_val x - n) s"
      apply -
      apply (erule obj_atI', simp_all add: objBits_simps)
      done

    let ?tran = "{ptr_val x - n .. (ptr_val x - n) + 2 ^ objBits tcb - 1}"
    have ot: "?oran \<subseteq> ?tran"
      by (rule tcb_cte_in_range[where p = "ptr_val x - n" and n = "n",
                                simplified diff_add_cancel]) fact+

    also
    from xv have "\<not> \<dots> \<subseteq> ?ran"
    proof (rule contrapos_nn)
      assume "?tran \<subseteq> ?ran"
      with ot have "?oran \<subseteq> ?ran" by (rule order_trans)
      hence "ptr_val x \<in> ?ran"
      proof (rule subsetD)
        from tcb have "is_aligned (ptr_val x) (objBits cte)"
          apply -
          apply (drule (1) tcb_cte_cases_aligned)
          apply simp
          done
        hence "ptr_val x \<le> ptr_val x + 2 ^ objBits cte - 1"
          by (rule is_aligned_no_overflow)
        thus "ptr_val x \<in> ?oran" by (rule first_in_uptoD)
      qed
      thus "x \<in> Ptr ` {ptr..+2 ^ bits}"
        unfolding ran'
        by (rule image_eqI [where x = "ptr_val x", rotated]) simp
    qed

    hence "?tran \<inter> ?ran' = {}"
      apply (rule contrapos_np)
      apply (rule valid_untyped_cap_ko_at_disjoint [OF vuc koat])
      apply simp
      done

    finally have "{ptr_val x..+2 ^ objBits cte} \<inter> ?ran' = {}"
      using ot unfolding oran'
      by blast
    thus ?thesis by (simp add: objBits_simps' size_of_def)
  qed
qed

lemma cmap_relation_disjoint_user_data:
  fixes x :: "user_data_C ptr"
  assumes vuc: "s \<turnstile>' UntypedCap d ptr bits idx"
  and    invs: "invs' s"
  and      cm: "cmap_relation (heap_to_user_data (ksPSpace s) (underlying_memory (ksMachineState s))) (cslift s') Ptr cuser_user_data_relation"
  and      ht: "s' \<Turnstile>\<^sub>c x"
  and      xv: "x \<notin> Ptr ` {ptr..+2 ^ bits}"
  shows  "{ptr_val x..+size_of TYPE(user_data_C)} \<inter> {ptr..+2 ^ bits} = {}"
proof -
  from vuc have al: "is_aligned ptr bits" and vu: "valid_untyped' d ptr bits idx s" and p0: "ptr \<noteq> 0"
    and wb: "bits < word_bits" and [simp]:"ptr && ~~ mask bits = ptr"
    by (auto elim!: valid_untyped_capE)

  note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  let ?ran = "{ptr..ptr + 2 ^ bits - 1}"
  let ?s = "(s\<lparr>ksPSpace := (ksPSpace s) |` (- ?ran)\<rparr>)"
  from cm ht have ks: "ksPSpace s (ptr_val x) = Some KOUserData"
    apply (rule cmap_relation_h_t_valid)
    apply (clarsimp simp: map_comp_Some_iff heap_to_user_data_def Let_def projectKO_opts_defs)
    apply (case_tac k')
        apply simp_all
    done

  let ?oran = "{ptr_val x .. ptr_val x + 2 ^ objBitsKO KOUserData - 1}"

  let ?ran' = "{ptr..+2 ^ bits}"
  let ?oran' = "{ptr_val x..+2 ^ objBitsKO KOUserData}"

  have ran' [simp]: "?ran' = ?ran" using al wb upto_intvl_eq by auto

  have oran' [simp]: "?oran' = ?oran"
  proof (rule upto_intvl_eq)
    from invs have "pspace_aligned' s" ..
    with ks show "is_aligned (ptr_val x) (objBitsKO KOUserData)"  ..
  qed

  from xv have "ptr_val x \<in> (- ?ran)"
    apply (simp only: ran' Compl_iff)
    apply (erule contrapos_nn)
    apply (erule image_eqI [rotated])
    apply simp
    done

  hence "ksPSpace ?s (ptr_val x) = Some KOUserData" using ks by simp
  hence "?oran \<inter> ?ran = {}"
  proof (rule pspace_no_overlapD'[where p = ptr and bits = bits,simplified])
    from invs have "valid_pspace' s" ..
    with vu al show "pspace_no_overlap' ptr bits ?s" using valid_untyped_no_overlap
        by (clarsimp simp: mask_def add_diff_eq)
  qed

  hence "?oran' \<inter> ?ran' = {}" by simp
  thus "{ptr_val x..+size_of TYPE(user_data_C)} \<inter> ?ran' = {}"
  proof (rule disjoint_subset [rotated])
    show "{ptr_val x..+size_of TYPE(user_data_C)} \<subseteq> ?oran'"
      apply -
      apply (rule intvl_start_le)
      apply (simp add: size_of_def objBits_simps pageBits_def)
      done
  qed
qed

lemma cmap_relation_disjoint_device_data:
  fixes x :: "user_data_device_C ptr"
  assumes vuc: "s \<turnstile>' UntypedCap d ptr bits idx"
  and    invs: "invs' s"
  and      cm: "cmap_relation (heap_to_device_data (ksPSpace s) (underlying_memory (ksMachineState s))) (cslift s') Ptr cuser_user_data_device_relation"
  and      ht: "s' \<Turnstile>\<^sub>c x"
  and      xv: "x \<notin> Ptr ` {ptr..+2 ^ bits}"
  shows  "{ptr_val x..+size_of TYPE(user_data_device_C)} \<inter> {ptr..+2 ^ bits} = {}"
proof -
  from vuc have al: "is_aligned ptr bits" and vu: "valid_untyped' d ptr bits idx s" and p0: "ptr \<noteq> 0"
    and wb: "bits < word_bits" and [simp]:"ptr && ~~ mask bits = ptr"
    by (auto elim!: valid_untyped_capE)

  note blah[simp del] =  atLeastAtMost_iff atLeastatMost_subset_iff atLeastLessThan_iff
          Int_atLeastAtMost atLeastatMost_empty_iff split_paired_Ex

  let ?ran = "{ptr..ptr + 2 ^ bits - 1}"
  let ?s = "(s\<lparr>ksPSpace := (ksPSpace s) |` (- ?ran)\<rparr>)"
  from cm ht have ks: "ksPSpace s (ptr_val x) = Some KOUserDataDevice"
    apply (rule cmap_relation_h_t_valid)
    apply (clarsimp simp: map_comp_Some_iff heap_to_device_data_def Let_def projectKO_opts_defs)
    apply (case_tac k')
        apply simp_all
    done

  let ?oran = "{ptr_val x .. ptr_val x + 2 ^ objBitsKO KOUserDataDevice - 1}"

  let ?ran' = "{ptr..+2 ^ bits}"
  let ?oran' = "{ptr_val x..+2 ^ objBitsKO KOUserDataDevice}"

  have ran' [simp]: "?ran' = ?ran" using al wb upto_intvl_eq by auto

  have oran' [simp]: "?oran' = ?oran"
  proof (rule upto_intvl_eq)
    from invs have "pspace_aligned' s" ..
    with ks show "is_aligned (ptr_val x) (objBitsKO KOUserDataDevice)"  ..
  qed

  from xv have "ptr_val x \<in> (- ?ran)"
    apply (simp only: ran' Compl_iff)
    apply (erule contrapos_nn)
    apply (erule image_eqI [rotated])
    apply simp
    done

  hence "ksPSpace ?s (ptr_val x) = Some KOUserDataDevice" using ks by simp
  hence "?oran \<inter> ?ran = {}"
  proof (rule pspace_no_overlapD'[where p = ptr and bits = bits,simplified])
    from invs have "valid_pspace' s" ..
    with vu al show "pspace_no_overlap' ptr bits ?s" using valid_untyped_no_overlap
        by (clarsimp simp: mask_def add_diff_eq)
  qed

  hence "?oran' \<inter> ?ran' = {}" by simp
  thus "{ptr_val x..+size_of TYPE(user_data_device_C)} \<inter> ?ran' = {}"
  proof (rule disjoint_subset [rotated])
    show "{ptr_val x..+size_of TYPE(user_data_device_C)} \<subseteq> ?oran'"
      apply -
      apply (rule intvl_start_le)
      apply (simp add: size_of_def objBits_simps pageBits_def)
      done
  qed
qed


lemma tcb_queue_relation_live_restrict:
  assumes vuc: "s \<turnstile>' capability.UntypedCap d ptr bits idx"
  and     rel: "\<forall>t \<in> set q. tcb_at' t s"
  and    live: "\<forall>t \<in> set q. ko_wp_at' live' t s"
  and      rl: "\<forall>(p :: machine_word) P. ko_wp_at' P p s \<and> (\<forall>ko. P ko \<longrightarrow> live' ko) \<longrightarrow> p \<notin> {ptr..ptr + 2 ^ bits - 1}"
  shows "tcb_queue_relation' getNext getPrev (cm |` (- Ptr ` {ptr..+2 ^ bits})) q cend chead =
  tcb_queue_relation' getNext getPrev cm q cend chead"
proof (rule tcb_queue_relation'_cong [OF refl refl refl])
  fix p
  assume "p \<in> tcb_ptr_to_ctcb_ptr ` set q"

  hence pin: "ctcb_ptr_to_tcb_ptr p \<in> set q" by (rule tcb_ptr_to_ctcb_ptr_imageD)

  with rel have "tcb_at' (ctcb_ptr_to_tcb_ptr p) s" ..
  then obtain tcb :: tcb where koat: "ko_at' tcb (ctcb_ptr_to_tcb_ptr p) s"
    by (clarsimp simp: obj_at'_real_def ko_wp_at'_def)

  from live pin have "ko_wp_at' live' (ctcb_ptr_to_tcb_ptr p) s" ..
  hence notin: "(ctcb_ptr_to_tcb_ptr p) \<notin> {ptr..ptr + 2 ^ bits - 1}"
    by (fastforce intro!: rl [rule_format])

  from vuc have al: "is_aligned ptr bits" and wb: "bits < word_bits"
    by (auto elim!: valid_untyped_capE)

  hence ran': " {ptr..+2 ^ bits} = {ptr..ptr + 2 ^ bits - 1}" by (simp add: upto_intvl_eq)

  hence "p \<in> - Ptr ` {ptr..+2 ^ bits}" using vuc koat notin
    apply -
    apply (erule contrapos_np)
    apply (erule (1) valid_untyped_cap_ctcb_member)
    apply fastforce
    done

  thus "(cm |` (- Ptr ` {ptr..+2 ^ bits})) p = cm p" by simp
qed

fun
  epQ :: "endpoint \<Rightarrow> machine_word list"
  where
  "epQ IdleEP = []"
  | "epQ (RecvEP ts) = ts"
  | "epQ (SendEP ts) = ts"

lemma ep_queue_live:
  assumes invs: "invs' s"
  and     koat: "ko_at' ep p s"
  shows   "\<forall>t \<in> set (epQ ep). ko_wp_at' live' t s"
proof
  fix t
  assume tin: "t \<in> set (epQ ep)"

  from invs koat tin show "ko_wp_at' live' t s"
    apply -
    apply (drule sym_refs_ko_atD')
     apply clarsimp
    apply (cases ep)
    by (auto elim!: ko_wp_at'_weakenE [OF _ refs_of_live'])
qed

fun
  ntfnQ :: "ntfn \<Rightarrow> machine_word list"
  where
  "ntfnQ (WaitingNtfn ts) = ts"
  | "ntfnQ _ = []"

lemma ntfn_queue_live:
  assumes invs: "invs' s"
  and     koat: "ko_at' ntfn p s"
  shows   "\<forall>t \<in> set (ntfnQ (ntfnObj ntfn)). ko_wp_at' live' t s"
proof
  fix t
  assume tin: "t \<in> set (ntfnQ (ntfnObj ntfn))"

  from invs koat tin show "ko_wp_at' live' t s"
    apply -
    apply (drule sym_refs_ko_atD')
     apply clarsimp
    apply (cases "ntfnObj ntfn")
      apply (auto elim!: ko_wp_at'_weakenE [OF _ refs_of_live']
                  dest!: bspec)
    done
qed

lemma cendpoint_relation_restrict:
  assumes vuc: "s \<turnstile>' capability.UntypedCap d ptr bits idx"
  and    invs: "invs' s"
  and      rl: "\<forall>(p :: machine_word) P. ko_wp_at' P p s \<and> (\<forall>ko. P ko \<longrightarrow> live' ko) \<longrightarrow> p \<notin> {ptr..ptr + 2 ^ bits - 1}"
  and    meps: "map_to_eps (ksPSpace s) p = Some ep"
  shows "cendpoint_relation (cslift s' |` (- Ptr ` {ptr..+2 ^ bits})) ep b = cendpoint_relation (cslift s') ep b"
proof -
  from invs have "valid_objs' s" ..
  with meps have vep: "valid_ep' ep s"
    apply -
    apply (clarsimp simp add: map_comp_Some_iff)
    apply (erule (1) valid_objsE')
    apply (simp add: valid_obj'_def)
    done

  from meps have koat: "ko_at' ep p s" by (rule map_to_ko_atI') fact+

  show ?thesis
  proof (cases ep)
    case (RecvEP ts)

    from vep RecvEP have tats: "\<forall>t \<in> set ts. tcb_at' t s"
      by (simp add: valid_ep'_def)

    have tlive: "\<forall>t\<in>set ts. ko_wp_at' live' t s" using RecvEP invs koat
      apply -
      apply (drule (1) ep_queue_live)
      apply simp
      done

    show ?thesis using RecvEP
      unfolding cendpoint_relation_def Let_def
      by (simp add: tcb_queue_relation_live_restrict [OF vuc tats tlive rl])
  next
    case (SendEP ts)

    from vep SendEP have tats: "\<forall>t \<in> set ts. tcb_at' t s"
      by (simp add: valid_ep'_def)

    have tlive: "\<forall>t\<in>set ts. ko_wp_at' live' t s" using SendEP invs koat
      apply -
      apply (drule (1) ep_queue_live)
      apply simp
      done

    show ?thesis using SendEP
      unfolding cendpoint_relation_def Let_def
      by (simp add: tcb_queue_relation_live_restrict [OF vuc tats tlive rl])
  next
    case IdleEP
    thus ?thesis unfolding cendpoint_relation_def Let_def by simp
  qed
qed

lemma cnotification_relation_restrict:
  assumes vuc: "s \<turnstile>' capability.UntypedCap d ptr bits idx"
  and    invs: "invs' s"
  and      rl: "\<forall>(p :: machine_word) P. ko_wp_at' P p s \<and> (\<forall>ko. P ko \<longrightarrow> live' ko) \<longrightarrow> p \<notin> {ptr..ptr + 2 ^ bits - 1}"
  and    meps: "map_to_ntfns (ksPSpace s) p = Some ntfn"
  shows "cnotification_relation (cslift s' |` (- Ptr ` {ptr..+2 ^ bits})) ntfn b = cnotification_relation (cslift s') ntfn b"
proof -
  from invs have "valid_objs' s" ..
  with meps have vep: "valid_ntfn' ntfn s"
    apply -
    apply (clarsimp simp add: map_comp_Some_iff)
    apply (erule (1) valid_objsE')
    apply (simp add: valid_obj'_def)
    done

  from meps have koat: "ko_at' ntfn p s" by (rule map_to_ko_atI') fact+

  show ?thesis
  proof (cases "ntfnObj ntfn")
    case (WaitingNtfn ts)

    with vep have tats: "\<forall>t \<in> set ts. tcb_at' t s"
      by (simp add: valid_ntfn'_def)

    have tlive: "\<forall>t\<in>set ts. ko_wp_at' live' t s" using WaitingNtfn invs koat
      apply -
      apply (drule (1) ntfn_queue_live)
      apply simp
      done

    show ?thesis using WaitingNtfn
      unfolding cnotification_relation_def Let_def
      by (simp add: tcb_queue_relation_live_restrict [OF vuc tats tlive rl])
  qed (simp_all add: cnotification_relation_def Let_def)
qed

declare bij_Ptr[simp]

lemma surj_tcb_ptr_to_ctcb_ptr [simp]:
  "surj tcb_ptr_to_ctcb_ptr"
  by (rule surjI [where f = "ctcb_ptr_to_tcb_ptr"], simp)

lemma bij_tcb_ptr_to_ctcb_ptr [simp]:
  "bij tcb_ptr_to_ctcb_ptr" by (simp add: bijI)


lemma inj_ctcb_ptr_to_tcb_ptr [simp]:
  "inj ctcb_ptr_to_tcb_ptr"
  apply (rule injI)
  apply (simp add: ctcb_ptr_to_tcb_ptr_def)
  done

lemma surj_ctcb_ptr_to_tcb_ptr [simp]:
  "surj ctcb_ptr_to_tcb_ptr"
  by (rule surjI [where f = "tcb_ptr_to_ctcb_ptr"], simp)

lemma bij_ctcb_ptr_to_tcb_ptr [simp]:
  "bij ctcb_ptr_to_tcb_ptr" by (simp add: bijI)

lemma cmap_relation_restrict_both:
  "\<lbrakk> cmap_relation am cm f rel; bij f\<rbrakk> \<Longrightarrow> cmap_relation (am |` (- S)) (cm |` (- f ` S)) f rel"
  unfolding cmap_relation_def
  apply (rule conjI)
   apply (clarsimp simp: image_Int bij_image_Compl_eq bij_def)
  apply (rule ballI)
  apply (clarsimp simp: image_iff2 bij_def)
  done

lemma cmap_relation_restrict_both_proj:
  "\<lbrakk> cmap_relation (projectKO_opt \<circ>\<^sub>m am) cm f rel; bij f\<rbrakk>
  \<Longrightarrow> cmap_relation (projectKO_opt \<circ>\<^sub>m (am |` (- S))) (cm |` (- f ` S)) f rel"
  unfolding cmap_relation_def
  apply (rule conjI)
   apply (rule equalityI)
    apply rule
    apply (clarsimp simp: map_comp_restrict_map_Some_iff image_iff2 bij_def)
    apply (erule (1) cmap_domE1)
    apply simp
   apply (clarsimp simp: image_Int bij_image_Compl_eq bij_def)
   apply (erule (1) cmap_domE2)
   apply (clarsimp simp: image_Int bij_image_Compl_eq bij_def map_comp_restrict_map_Some_iff intro!: imageI)
  apply clarsimp
  apply (subst restrict_in)
   apply (clarsimp simp add: image_iff map_comp_restrict_map_Some_iff inj_eq bij_def)
  apply (clarsimp simp add: map_comp_restrict_map_Some_iff)
  apply (drule (1) bspec [OF _ domI])
  apply simp
  done

declare not_snd_assert[simp]

lemma ccorres_stateAssert_fwd:
  "ccorres r xf (P and R) P' hs b c \<Longrightarrow> ccorres r xf P P' hs (stateAssert R vs >>= (\<lambda>_. b)) c"
  apply (rule ccorresI')
  apply (simp add: stateAssert_def bind_assoc)
  apply (drule not_snd_bindD)
   apply (fastforce simp add: in_monad)
  apply clarsimp
  apply (frule not_snd_bindI1)
  apply simp
  apply (erule (1) ccorresE)
      apply simp
     apply assumption
    apply assumption
   apply assumption
  apply (fastforce simp: in_monad')
  done

(* FIXME: generalise to above *)
lemma tcb_ptr_to_ctcb_ptr_comp:
  "tcb_ptr_to_ctcb_ptr = Ptr o (\<lambda>p. p + ctcb_offset)"
  apply (rule ext)
  apply (simp add: tcb_ptr_to_ctcb_ptr_def)
  done

lemma tcb_ptr_to_ctcb_ptr_to_Ptr:
  "tcb_ptr_to_ctcb_ptr ` {p..+b} = Ptr ` {p + ctcb_offset..+b}"
  apply (simp add:  tcb_ptr_to_ctcb_ptr_comp image_comp [symmetric])
  apply (rule equalityI)
   apply clarsimp
   apply (rule imageI)
   apply (drule intvlD)
   apply clarsimp
   apply (subgoal_tac "p + ctcb_offset + of_nat k \<in> {p + ctcb_offset..+b}")
    apply (simp add: field_simps)
   apply (erule intvlI)
  apply clarsimp
  apply (drule intvlD)
  apply clarsimp
  apply (rule image_eqI)
   apply simp
  apply (erule intvlI)
  done


lemma valid_untyped_cap_ctcb_member':
  fixes tcb :: tcb
  shows "\<lbrakk>s \<turnstile>' capability.UntypedCap d ptr bits idx; ko_at' tcb x s;
  ptr_val (tcb_ptr_to_ctcb_ptr x) \<in> {ptr..+2 ^ bits}\<rbrakk>
  \<Longrightarrow> x \<in> {ptr..+ 2 ^ bits}"
  apply (rule valid_untyped_capE, assumption)
  apply (simp only: upto_intvl_eq)
  apply (erule (2) valid_untyped_cap_ctcb_member)
  done

lemma cpspace_tcb_relation_address_subset:
  assumes     vuc: "s \<turnstile>' capability.UntypedCap d ptr bits idx"
  and        invs: "invs' s"
  and     ctcbrel: "cpspace_tcb_relation (ksPSpace s) (t_hrs_' (globals s'))"
  shows "cmap_relation (map_to_tcbs (ksPSpace s |` (- {ptr..+2 ^ bits - unat ctcb_offset})))
      (cslift s' |` (- tcb_ptr_to_ctcb_ptr ` {ptr..+2 ^ bits - unat ctcb_offset})) tcb_ptr_to_ctcb_ptr
      ctcb_relation
   = cmap_relation (map_to_tcbs (ksPSpace s |` (- {ptr..+2 ^ bits})))
        (cslift s' |` (- Ptr ` {ptr..+2 ^ bits})) tcb_ptr_to_ctcb_ptr
        ctcb_relation" (is "cmap_relation ?am ?cm tcb_ptr_to_ctcb_ptr ctcb_relation
  = cmap_relation ?am' ?cm' tcb_ptr_to_ctcb_ptr ctcb_relation")
proof (rule cmap_relation_cong)
  from vuc have al: "is_aligned ptr bits" and wb: "bits < word_bits" by (auto elim: valid_untyped_capE)

  have r1: "\<And>x tcb. \<lbrakk> (map_to_tcbs (ksPSpace s) x) = Some tcb; x \<in> {ptr..+2 ^ bits}\<rbrakk>
    \<Longrightarrow> x \<in> {ptr..+2 ^ bits - unat ctcb_offset}"
  proof (subst intvl_aligned_top [where 'a=machine_word_len, folded word_bits_def, OF _ al _ _ wb])
    fix x tcb
    assume mtcb: "map_to_tcbs (ksPSpace s) x = Some tcb" and xin: "x \<in> {ptr..+2 ^ bits}"

    from mtcb invs have koat: "ko_at' tcb x s"
      by (fastforce simp: map_comp_Some_iff intro: aligned_distinct_obj_atI')

    thus "is_aligned x (objBits tcb)"
      by (clarsimp elim!: obj_atE' simp: objBits_def)

    (* FIXME: generalise *)
    with xin koat show "objBits tcb \<le> bits" using wb
      apply -
      apply (frule is_aligned_no_overflow)
      apply (drule valid_untyped_cap_ko_at_disjoint [OF vuc])
      apply (erule contrapos_pn)
      apply (subst upto_intvl_eq [OF al])
      apply (erule orthD1)
      apply simp
      apply (drule (1) range_subsetD)
      apply clarsimp
      apply (drule (1) word_sub_mono2 [where b = "(2 :: machine_word) ^ objBits tcb - 1"
        and d = "2 ^ bits - 1", simplified field_simps])
      apply (subst field_simps [symmetric], subst olen_add_eqv [symmetric])
      apply (simp add: field_simps)
      apply (subst field_simps [symmetric], subst olen_add_eqv [symmetric])
      apply (rule is_aligned_no_overflow' [OF al])
      apply (subgoal_tac "(2 :: machine_word) ^ objBits tcb \<noteq> 0")
       apply (simp add: word_le_nat_alt unat_minus_one le_diff_iff word_bits_def)
      apply (simp add: objBits_simps)
      done

    show "unat ctcb_offset < 2 ^ objBits tcb"
      by (fastforce simp add: ctcb_offset_defs objBits_simps' project_inject)

    show "x \<in> {ptr..+2 ^ bits}" by fact
  qed

  show "dom ?am = dom ?am'"
    apply (rule dom_eqI)
    apply (clarsimp dest!: r1 simp: map_comp_restrict_map_Some_iff)
    apply (clarsimp dest!: intvl_mem_weaken simp: map_comp_restrict_map_Some_iff)
    done

  let ?ran = "{ptr..+2 ^ bits}"
  let ?small_ran = "{ptr..+2 ^ bits - unat ctcb_offset}"

  show "dom ?cm = dom ?cm'"
  proof (rule dom_eqI)
    fix x y
    assume "?cm' x = Some y"
    hence cl: "cslift s' x = Some y" and xni: "x \<notin> Ptr ` ?ran"
      by (auto simp: restrict_map_Some_iff)

    with ctcbrel obtain x' tcb where mt: "map_to_tcbs (ksPSpace s) x' = Some tcb"
      and xv: "x = tcb_ptr_to_ctcb_ptr x'"
      by (fastforce elim!: cmap_relation_h_t_valid simp add: h_t_valid_clift_Some_iff)

    have "(cslift s' |` (- tcb_ptr_to_ctcb_ptr ` ?small_ran)) x = Some y"
    proof (subst restrict_in)
      show "x \<in> - tcb_ptr_to_ctcb_ptr ` ?small_ran" using xni
      proof (rule contrapos_np)
        assume "x \<notin> - tcb_ptr_to_ctcb_ptr ` ?small_ran"
        hence "x \<in> tcb_ptr_to_ctcb_ptr ` ?small_ran" by simp
        hence "x \<in> Ptr ` {ptr + ctcb_offset ..+ 2 ^ bits - unat ctcb_offset}" by (simp add: tcb_ptr_to_ctcb_ptr_to_Ptr)
        thus "x \<in> Ptr ` ?ran"
          by (clarsimp intro!: imageI elim!: intvl_plus_sub_offset)
      qed
    qed fact
    thus "\<exists>y. (cslift s' |` (- tcb_ptr_to_ctcb_ptr ` ?small_ran)) x = Some y" ..
  next
    fix x y
    assume "?cm x = Some y"
    hence cl: "cslift s' x = Some y" and xni: "x \<notin> tcb_ptr_to_ctcb_ptr ` ?small_ran"
      by (auto simp: restrict_map_Some_iff)

    with ctcbrel obtain x' tcb where mt: "map_to_tcbs (ksPSpace s) x' = Some tcb" and xv: "x = tcb_ptr_to_ctcb_ptr x'"
      by (fastforce elim!: cmap_relation_h_t_valid simp add: h_t_valid_clift_Some_iff)

    from mt invs have koat: "ko_at' tcb x' s" by (rule map_to_ko_atI')

    have "(cslift s' |` (- Ptr ` ?ran)) x = Some y"
    proof (subst restrict_in)
      show "x \<in> - Ptr ` ?ran" using xni
        apply (rule contrapos_np)
        apply (simp add: xv)
        apply (rule imageI)
        apply (rule r1 [OF mt])
        apply (rule valid_untyped_cap_ctcb_member' [OF vuc koat])
        apply (erule imageE)
        apply simp
        done
    qed fact
    thus "\<exists>y. (cslift s' |` (- Ptr ` ?ran)) x = Some y" ..
  qed
qed (clarsimp simp: map_comp_Some_iff restrict_map_Some_iff)

lemma heap_to_user_data_restrict:
  "heap_to_user_data (mp |` S) bhp = (heap_to_user_data mp bhp |` S)"
  unfolding heap_to_user_data_def
  apply (rule ext)
  apply (case_tac "p \<in> S")
  apply (simp_all add: Let_def map_comp_def split: option.splits)
  done

lemma heap_to_device_data_restrict:
  "heap_to_device_data (mp |` S) bhp = (heap_to_device_data mp bhp |` S)"
  unfolding heap_to_device_data_def
  apply (rule ext)
  apply (case_tac "p \<in> S")
  apply (simp_all add: Let_def map_comp_def split: option.splits)
  done

lemma ccorres_stateAssert_after:
  assumes "ccorres r xf (P and (\<lambda>s. (\<forall>(rv,s') \<in> fst (f s). R s'))) P' hs f c"
  shows "ccorres r xf P P' hs (do _ \<leftarrow> f; stateAssert R vs od) c" using assms
  apply (clarsimp simp: ccorres_underlying_def split: xstate.splits)
  apply (drule snd_stateAssert_after)
  apply clarsimp
  apply (drule (1) bspec)
  apply (clarsimp simp: split_def)
  apply (rule conjI)
   apply clarsimp
   apply (rename_tac s)
   apply (erule_tac x=n in allE)
   apply (erule_tac x="Normal s" in allE)
   apply clarsimp
   apply (simp add: bind_def stateAssert_def get_def assert_def)
   apply (rule bexI)
    prefer 2
    apply assumption
   apply (clarsimp simp: return_def fail_def)
   apply fastforce
  apply fastforce
  done

lemma word_add_offset_pageBits_in_S:
  assumes v: "\<And>v. v < 2 ^ pageBits \<Longrightarrow> (x + v \<in> S) = ((x :: machine_word) \<in> S)"
  assumes n: "n < 8"
  shows "(x + ucast (y::9 word) * 8 + n \<in> S) = (x \<in> S)"
  apply (simp add: add.assoc)
  apply (subst v)
   apply (rule word_add_offset_less[where n=3 and m=9, simplified], rule n)
      apply (rule less_le_trans, rule ucast_less; simp)
     apply (simp add: pageBits_def)
    apply (rule less_le_trans, rule ucast_less; simp)
   apply (simp add: pageBits_def)
  apply (rule refl)
  done

lemma heap_to_user_data_update_region:
  assumes foo: "\<And>x y v. \<lbrakk> map_to_user_data psp x = Some y;
                           v < 2 ^ pageBits \<rbrakk> \<Longrightarrow> (x + v \<in> S) = (x \<in> S)"
  shows
  "heap_to_user_data psp (\<lambda>x. if x \<in> S then v else f x)
     = (\<lambda>x. if x \<in> S \<inter> dom (map_to_user_data psp) then Some (K (word_rcat [v,v,v,v,v,v,v,v]))
             else heap_to_user_data psp f x)"
  apply (rule ext)
  apply (simp add: heap_to_user_data_def Let_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule ext)
   apply (clarsimp simp: byte_to_word_heap_def Let_def foo
                         word_add_offset_pageBits_in_S
                         word_add_offset_pageBits_in_S[where n=0, simplified])
  apply clarsimp
  apply (case_tac "map_to_user_data psp x"; clarsimp)
  apply (rule ext)
  apply (clarsimp simp: byte_to_word_heap_def Let_def foo
                        word_add_offset_pageBits_in_S
                        word_add_offset_pageBits_in_S[where n=0, simplified])
  done

lemma heap_to_device_data_update_region:
  assumes foo: "\<And>x y v. \<lbrakk> map_to_user_data_device psp x = Some y;
                           v < 2 ^ pageBits \<rbrakk> \<Longrightarrow> (x + v \<in> S) = (x \<in> S)"
  shows
  "heap_to_device_data psp (\<lambda>x. if x \<in> S then v else f x)
     = (\<lambda>x. if x \<in> S \<inter> dom (map_to_user_data_device psp) then Some (K (word_rcat [v,v,v,v,v,v,v,v]))
             else heap_to_device_data psp f x)"
  apply (rule ext)
  apply (simp add: heap_to_device_data_def Let_def)
  apply (rule conjI)
   apply clarsimp
   apply (rule ext)
   apply (clarsimp simp: byte_to_word_heap_def Let_def foo
                         word_add_offset_pageBits_in_S
                         word_add_offset_pageBits_in_S[where n=0, simplified])
  apply clarsimp
  apply (case_tac "map_to_user_data_device psp x"; clarsimp)
  apply (rule ext)
  apply (clarsimp simp: byte_to_word_heap_def Let_def foo
                        word_add_offset_pageBits_in_S
                        word_add_offset_pageBits_in_S[where n=0, simplified])
  done

lemma ksPSpace_ksMSu_comm:
  "ksPSpace_update f (ksMachineState_update g s) =
   ksMachineState_update g (ksPSpace_update f s)"
  by simp

lemma ksPSpace_update_ext:
  "(\<lambda>s. s\<lparr>ksPSpace := f (ksPSpace s)\<rparr>) = (ksPSpace_update f)"
  by (rule ext) simp

lemma hrs_ghost_update_comm:
  "(t_hrs_'_update f \<circ> ghost'state_'_update g) =
   (ghost'state_'_update g \<circ> t_hrs_'_update f)"
  by (rule ext) simp

lemma htd_safe_typ_clear_region:
  "htd_safe S htd \<Longrightarrow> htd_safe S (typ_clear_region ptr bits htd)"
  apply (clarsimp simp: htd_safe_def dom_s_def typ_clear_region_def)
  apply (simp add: subset_iff)
  apply blast
  done

lemma htd_safe_typ_region_bytes:
  "htd_safe S htd \<Longrightarrow> {ptr ..+ 2 ^ bits} \<subseteq> S \<Longrightarrow> htd_safe S (typ_region_bytes ptr bits htd)"
  apply (clarsimp simp: htd_safe_def dom_s_def typ_region_bytes_def)
  apply (simp add: subset_iff)
  apply blast
  done

lemma untyped_cap_rf_sr_ptr_bits_domain:
  "cte_wp_at' (\<lambda>cte. cteCap cte = capability.UntypedCap d ptr bits idx) p s
    \<Longrightarrow> invs' s \<Longrightarrow> (s, s') \<in> rf_sr
    \<Longrightarrow> {ptr..+2 ^ bits} \<subseteq> domain"
  apply (clarsimp simp: cte_wp_at_ctes_of)
  apply (frule ctes_of_valid', clarsimp)
  apply (drule valid_global_refsD', clarsimp)
  apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        valid_cap'_def capAligned_def)
  apply (simp only: upto_intvl_eq)
  apply blast
  done

lemma distinct_aligned_addresses_accumulate:
  "is_aligned p n \<Longrightarrow> is_aligned ptr bits
    \<Longrightarrow> n \<ge> m \<Longrightarrow> n < size p \<Longrightarrow> m \<le> bits
    \<Longrightarrow> (\<forall>y<2 ^ (n - m). p + (y << m) \<notin> {ptr..ptr + 2 ^ bits - 1})
    \<Longrightarrow> {p .. p + 2 ^ n - 1} \<inter> {ptr..ptr + 2 ^ bits - 1} = {}"
  apply safe
  apply (simp only: mask_in_range[symmetric])
  apply (drule_tac x="(x && mask n) >> m" in spec)
  apply (simp add: shiftr_shiftl1 word_bw_assocs)
  apply (drule mp, rule shiftr_less_t2n)
   apply (subst add_diff_inverse, simp, rule and_mask_less', simp add: word_size)
  apply (clarsimp simp: multiple_mask_trivia word_bw_assocs neg_mask_twice max_absorb2)
  done

lemma offs_in_intvl_iff:
  "(p + x \<in> {p ..+ n}) = (unat x < n)"
  apply (simp add: intvl_def, safe)
   apply (erule order_le_less_trans[rotated], simp add: unat_of_nat)
  apply (rule exI, erule conjI[rotated])
  apply simp
  done

lemma objBits_koTypeOf:
  fixes v :: "'a :: pspace_storable" shows
  "objBits v = objBitsT (koType TYPE('a))"
  using project_inject[where v=v, THEN iffD2, OF refl]
      project_koType[THEN iffD1, OF exI[where x=v]]
  by (simp add: objBits_def objBitsT_koTypeOf[symmetric])

lemma cmap_array_typ_region_bytes:
  "ptrf = (Ptr :: _ \<Rightarrow> 'b ptr)
    \<Longrightarrow> carray_map_relation bits' amap (h_t_valid htd c_guard) ptrf
    \<Longrightarrow> is_aligned ptr bits
    \<Longrightarrow> typ_uinfo_t TYPE('b :: c_type) \<noteq> typ_uinfo_t TYPE(8 word)
    \<Longrightarrow> size_of TYPE('b) = 2 ^ bits'
    \<Longrightarrow> objBitsT (koType TYPE('a :: pspace_storable)) \<le> bits
    \<Longrightarrow> objBitsT (koType TYPE('a :: pspace_storable)) \<le> bits'
    \<Longrightarrow> bits' < word_bits
    \<Longrightarrow> carray_map_relation bits' (restrict_map (amap :: _ \<Rightarrow> 'a option) (- {ptr ..+ 2 ^ bits}))
        (h_t_valid (typ_region_bytes ptr bits htd) c_guard) ptrf"
  apply (clarsimp simp: carray_map_relation_def h_t_valid_typ_region_bytes)
  apply (case_tac "h_t_valid htd c_guard (ptrf p)", simp_all)
   apply (clarsimp simp: objBits_koTypeOf)
   apply (drule spec, drule(1) iffD2, clarsimp)
   apply (rule iffI[rotated])
    apply clarsimp
    apply (drule equals0D, erule notE, erule IntI[rotated])
    apply (simp only: upto_intvl_eq is_aligned_neg_mask2 mask_in_range[symmetric])
   apply (simp only: upto_intvl_eq, rule distinct_aligned_addresses_accumulate,
     simp_all add: upto_intvl_eq[symmetric] word_size word_bits_def)
   apply clarsimp
   apply (drule_tac x="p + (y << objBitsT (koType TYPE('a)))" in spec)+
   apply (simp add: is_aligned_add[OF is_aligned_weaken is_aligned_shiftl])
   apply (simp add: is_aligned_add_helper shiftl_less_t2n word_bits_def)
  apply clarsimp
  apply (drule_tac x=p in spec)
  apply (clarsimp simp: objBits_koTypeOf)
  apply auto
  done

lemma map_comp_restrict_map:
  "(f \<circ>\<^sub>m (restrict_map m S)) = (restrict_map (f \<circ>\<^sub>m m) S)"
  by (rule ext, simp add: restrict_map_def map_comp_def)

lemma modify_machinestate_assert_cnodes_swap:
  "do x \<leftarrow> modify (ksMachineState_update f);
    y \<leftarrow> stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s) S) []; g od
    = do y \<leftarrow> stateAssert (\<lambda>s. \<not> cNodePartialOverlap (gsCNodes s) S) [];
        x \<leftarrow> modify (ksMachineState_update f); g od"
  by (simp add: fun_eq_iff exec_modify stateAssert_def
                bind_assoc exec_get assert_def)

lemma h_t_array_valid_typ_region_bytes:
  "h_t_array_valid htd (p :: ('a :: c_type) ptr) n
    \<Longrightarrow> {ptr_val p..+n * size_of TYPE('a)} \<inter> {ptr..+2 ^ bits} = {}
    \<Longrightarrow> h_t_array_valid (typ_region_bytes ptr bits htd) p n"
  apply (clarsimp simp: h_t_array_valid_def)
  apply (subst valid_footprint_typ_region_bytes)
   apply (simp add: uinfo_array_tag_n_m_def typ_uinfo_t_def typ_info_word)
  apply (simp add: field_simps)
  done

lemma cvariable_array_map_relation_detype:
  "cvariable_array_map_relation mp szs ptrfun htd
    \<Longrightarrow> ptrfun = (Ptr :: _ \<Rightarrow> ('a :: c_type ptr))
    \<Longrightarrow> \<forall>p v. mp p = Some v \<longrightarrow> p \<notin> {ptr ..+ 2 ^ bits}
        \<longrightarrow> {p ..+ szs v * size_of TYPE('a)} \<inter> {ptr ..+ 2 ^ bits} = {}
    \<Longrightarrow> cvariable_array_map_relation (mp |` (- {ptr..+2 ^ bits}))
        szs ptrfun (typ_region_bytes ptr bits htd)"
  apply (clarsimp simp: cvariable_array_map_relation_def restrict_map_def)
  apply (elim allE, (drule(1) mp)+)
  apply (simp add: h_t_array_valid_typ_region_bytes)
  done

lemma zero_ranges_are_zero_typ_region_bytes:
  "zero_ranges_are_zero rs hrs
    \<Longrightarrow> zero_ranges_are_zero rs (hrs_htd_update (typ_region_bytes ptr bits) hrs)"
  apply (clarsimp simp: zero_ranges_are_zero_def)
  apply (drule(1) bspec)
  apply (clarsimp simp: region_actually_is_bytes'_def typ_region_bytes_def hrs_htd_update)
  done

lemma modify_machinestate_assert_ptables_swap:
  "do x \<leftarrow> modify (ksMachineState_update f);
    y \<leftarrow> stateAssert (\<lambda>s. \<not> pTablePartialOverlap (gsPTTypes (ksArchState s)) S) []; g od
   = do y \<leftarrow> stateAssert (\<lambda>s. \<not> pTablePartialOverlap (gsPTTypes (ksArchState s)) S) [];
        x \<leftarrow> modify (ksMachineState_update f); g od"
  by (simp add: fun_eq_iff exec_modify stateAssert_def
                bind_assoc exec_get assert_def)

lemma deleteObjects_ccorres':
  notes if_cong[cong]
  shows
  (* the 4 \<le> bits appears related to smallest retypeable object size, see valid_cap_def *)
  "ccorres dc xfdc
     (cte_wp_at' (\<lambda>cte. cteCap cte = capability.UntypedCap d ptr bits idx) p and
      (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s)) and
      invs' and ct_active' and sch_act_simple and
      K ( 4 \<le> bits \<and> bits < word_bits))
     UNIV hs
     (deleteObjects ptr bits)
     (Basic (\<lambda>s. globals_update
       (t_hrs_'_update (hrs_htd_update (typ_region_bytes ptr bits)) \<circ>
        ghost'state_'_update (gs_clear_region ptr bits)) s))"
  apply (rule ccorres_grab_asm)
  apply (rule ccorres_name_pre)
  apply (simp add: deleteObjects_def3 hrs_ghost_update_comm)
  apply (rule ccorres_assert)
  apply (rule ccorres_stateAssert_fwd)
  apply (subst bind_assoc[symmetric])
  apply (unfold freeMemory_def)
  apply (subst ksPSpace_update_ext)
  apply (subgoal_tac "bits \<le> word_bits")
  prefer 2
   apply (clarsimp simp:cte_wp_at_ctes_of)
  apply (clarsimp simp: mapM_x_storeWord_step[simplified word_size_bits_def]
             intvl_range_conv intvl_range_conv[where 'a=machine_word_len, folded word_bits_def]
             doMachineOp_modify modify_modify o_def ksPSpace_ksMSu_comm
             bind_assoc modify_machinestate_assert_cnodes_swap modify_machinestate_assert_ptables_swap
             modify_modify_bind)
  apply (rule ccorres_stateAssert_fwd)+
  apply (rule ccorres_stateAssert_after)
  apply (rule ccorres_from_vcg)
  apply (rule allI, rule conseqPre, vcg)
  apply (clarsimp simp: in_monad)
  apply (rule bexI [rotated])
   apply (rule iffD2 [OF in_modify])
   apply (rule conjI [OF refl refl])
  apply (clarsimp simp: simpler_modify_def)
proof -
  let ?mmu = "(\<lambda>h x. if ptr \<le> x \<and> x \<le> ptr + 2 ^ bits - 1 then 0 else h x)"
  let ?psu = "(\<lambda>h x. if ptr \<le> x \<and> x \<le> ptr + mask bits then None else h x)"

  fix s s'
  assume al: "is_aligned ptr bits"
    and cte: "cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d ptr bits idx) p s"
    and desc_range: "descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s)"
    and invs: "invs' s" and "ct_active' s"
    and "sch_act_simple s" and wb: "bits < word_bits" and b2: "4 \<le> bits"
    and "deletionIsSafe ptr bits s"
    and cNodePartial: "\<not> cNodePartialOverlap (gsCNodes s)
                                              (\<lambda>x. ptr \<le> x \<and> x \<le> ptr + mask bits)"
    and pTablePartial: "\<not> pTablePartialOverlap (gsPTTypes (ksArchState s))
                                              (\<lambda>x. ptr \<le> x \<and> x \<le> ptr + mask bits)"
    and sr: "(s, s') \<in> rf_sr"
    and safe_asids:
          "ksASIDMapSafe
            (ksArchState_update (\<lambda>_. gsPTTypes_update
                                       (\<lambda>_. ?psu (gsPTTypes (ksArchState s))) (ksArchState s))
             (gsCNodes_update (\<lambda>_. ?psu (gsCNodes s))
              (gsUserPages_update
                (\<lambda>_. ?psu (gsUserPages s))
                (ksMachineState_update
                  (underlying_memory_update ?mmu)
                  (s\<lparr>ksPSpace := ?psu (ksPSpace s) \<rparr>)))))" (is "ksASIDMapSafe ?t")

  interpret D: delete_locale s ptr bits p
    apply (unfold_locales)
      apply fact+
    done

  let ?ks = "?psu (ksPSpace s)"
  let ?ks' = "ksPSpace s |` (- {ptr..+2 ^ bits})"

  have psu_restrict: "\<forall>h. ?psu h = h |` (- {ptr..+2 ^ bits})"
    apply (intro allI ext)
    apply (subst upto_intvl_eq [OF al])
    apply (clarsimp simp: mask_2pm1 add_diff_eq)
    done

  have ks': "?ks = ?ks'" by (simp add: psu_restrict)

  let ?th = "hrs_htd_update (typ_region_bytes ptr bits)"
  let ?th_s = "?th (t_hrs_' (globals s'))"

  have map_to_ctes_delete':
    "map_to_ctes ?ks' = ctes_of s |` (- {ptr..+2 ^ bits})" using invs
    apply (subst ks' [symmetric])
    apply (subst map_to_ctes_delete [OF D.valid_untyped, simplified field_simps, simplified])
     apply clarsimp
    apply (rule ext)
    apply (subst upto_intvl_eq [OF al])
    apply (clarsimp simp: mask_2pm1 add_diff_eq)
    done

  note cm_disj = cmap_relation_disjoint [OF D.valid_untyped invs, atomize]
  note cm_disj_tcb = cmap_relation_disjoint_tcb [OF D.valid_untyped invs]
  note cm_disj_cte = cmap_relation_disjoint_cte [OF D.valid_untyped invs]
  note cm_disj_user = cmap_relation_disjoint_user_data [OF D.valid_untyped invs]
  note cm_disj_device = cmap_relation_disjoint_device_data [OF D.valid_untyped invs]

  note upto_rew = upto_intvl_eq[OF al, THEN eqset_imp_iff, symmetric, simplified]

  have rl: "\<forall>(p :: machine_word) P. ko_wp_at' P p s \<and>
            (\<forall>ko. P ko \<longrightarrow> live' ko) \<longrightarrow> p \<notin> {ptr..ptr + 2 ^ bits - 1}"
    apply (intro allI impI conjI)
    apply (elim conjE)
    using D.live_notRange
    apply (clarsimp simp: mask_def add_diff_eq)
    done

  note cmaptcb = cmap_relation_tcb [OF sr]
  note cmap_array_helper = arg_cong2[where f=carray_map_relation, OF refl map_comp_restrict_map]
  have trivia: "size_of TYPE(pte_C[vs_array_len]) = 2 ^ (ptBits VSRootPT_T)"
    by (auto simp: bit_simps Kernel_Config.config_ARM_PA_SIZE_BITS_40_def)
  note cmap_array = cmap_array_typ_region_bytes[where 'a=pte, OF refl _ al _ trivia(1)]
  note cmap_array = cmap_array[simplified, simplified objBitsT_simps b2
        bit_simps word_bits_def, simplified]

  note pspace_distinct' = invs_pspace_distinct'[OF invs] and
       pspace_aligned' = invs_pspace_aligned'[OF invs] and
       valid_objs' = invs_valid_objs'[OF invs] and
       valid_untyped'_def2 =
         valid_untyped'[OF pspace_distinct' pspace_aligned' al]

  have s_ksPSpace_adjust: "ksPSpace_update ?psu s = s\<lparr>ksPSpace := ?psu (ksPSpace s)\<rparr>"
    by simp

  from invs have "valid_global_refs' s" by fastforce
  with cte
  have ptr_refs: "kernel_data_refs \<inter> {ptr..ptr + 2 ^ bits - 1} = {}"
    by (fastforce simp: valid_global_refs'_def valid_refs'_def cte_wp_at_ctes_of ran_def)

  have bits_ge_3[simp]: "3 \<le> bits" using b2 by linarith

  (* calculation starts here *)
  have cs: "cpspace_relation (ksPSpace s) (underlying_memory (ksMachineState s))
                             (t_hrs_' (globals s'))"
    using sr
    by (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
  hence "cpspace_relation ?ks' (underlying_memory (ksMachineState s)) ?th_s"
    unfolding cpspace_relation_def
    using cendpoint_relation_restrict [OF D.valid_untyped invs rl]
      cnotification_relation_restrict [OF D.valid_untyped invs rl]
    using  cmap_array[simplified bit_simps]
    apply -
    apply (elim conjE)
    supply if_split[split del]
    apply ((subst lift_t_typ_region_bytes,
            rule cm_disj cm_disj_tcb cm_disj_cte cm_disj_user cm_disj_device
            , assumption +,
            simp_all add: objBits_simps' bit_simps
                          heap_to_user_data_restrict heap_to_device_data_restrict)[1])+ \<comment> \<open>waiting ...\<close>
    apply (simp add: map_to_ctes_delete' cmap_relation_restrict_both_proj
                     cmap_relation_restrict_both cmap_array_helper hrs_htd_update
                     bit_simps)
    apply (frule cmap_relation_restrict_both_proj[where f = tcb_ptr_to_ctcb_ptr], simp)
    apply (intro conjI)
      apply (erule iffD1[OF cpspace_tcb_relation_address_subset,
                         OF D.valid_untyped invs cmaptcb])
     apply (subst cmap_relation_cong [OF refl refl,
                                      where rel' = "cendpoint_relation (cslift s')"])
      apply (clarsimp simp: restrict_map_Some_iff image_iff
                            map_comp_restrict_map_Some_iff)
     apply (simp add: cmap_relation_restrict_both_proj)
    apply (subst cmap_relation_cong[OF refl refl,
                                    where rel' = "cnotification_relation (cslift s')"])
     apply (clarsimp simp: restrict_map_Some_iff image_iff
                           map_comp_restrict_map_Some_iff)
    apply (simp add: cmap_relation_restrict_both_proj)
    done

  moreover
  {
    assume "s' \<Turnstile>\<^sub>c armKSGlobalUserVSpace_Ptr "
    moreover
    from sr ptr_refs have "ptr_span armKSGlobalUserVSpace_Ptr
      \<inter> {ptr..ptr + 2 ^ bits - 1} = {}"
      by (fastforce simp: rf_sr_def cstate_relation_def Let_def)
    ultimately
    have "hrs_htd (hrs_htd_update (typ_region_bytes ptr bits) (t_hrs_' (globals s'))) \<Turnstile>\<^sub>t armKSGlobalUserVSpace_Ptr"
      using al wb
      apply (cases "t_hrs_' (globals s')")
      apply (simp add: hrs_htd_update_def hrs_htd_def h_t_valid_typ_region_bytes upto_intvl_eq)
      done
  }

  moreover
  have h2ud_eq:
       "heap_to_user_data (?psu (ksPSpace s))
                          (?mmu (underlying_memory (ksMachineState s))) =
        heap_to_user_data (?psu (ksPSpace s))
                          (underlying_memory (ksMachineState s))"
    supply mask_2pm1[simp] add_diff_eq[simp]
    apply (subst heap_to_user_data_update_region
                 [where S="{ptr..ptr + 2 ^ bits - 1}", simplified])
     prefer 2
     apply (rule ext)
     apply clarsimp
    apply (simp add: map_option_def map_comp_def
              split: if_split_asm option.splits)
    apply (frule pspace_alignedD'[OF _ pspace_aligned'])
    apply (case_tac "pageBits \<le> bits")
     apply (simp add: objBitsKO_def split: kernel_object.splits)
     apply clarsimp
     apply (rule aligned_range_offset_mem[simplified, OF _ _ al])
       apply assumption+
    apply (rule iffI[rotated], simp)
    apply (simp add: objBits_simps)
    apply (rule FalseE)
    apply (case_tac "ptr \<le> x", simp)
     apply clarsimp
     apply (frule_tac y="ptr + 2 ^ bits - 1" in le_less_trans)
      apply (simp only: not_le)
     apply (drule (1) is_aligned_no_wrap')
     apply simp
    apply (cut_tac cte[simplified cte_wp_at_ctes_of])
    apply clarsimp
    apply (frule ctes_of_valid'[OF _ valid_objs'])
    apply (frule pspace_distinctD'[OF _ pspace_distinct'])
    apply (clarsimp simp add: valid_cap'_def valid_untyped'_def2 capAligned_def)
    apply (drule_tac x=x in spec)
    apply (simp add: obj_range'_def objBitsKO_def mask_def)
    apply (simp only: not_le)
    apply (cut_tac is_aligned_no_overflow[OF al])
    apply (case_tac "ptr \<le> x + 2 ^ pageBits - 1",
           simp_all only: simp_thms not_le)
    apply clarsimp
    apply (thin_tac "psp = Some ko" for psp ko)+
    apply (thin_tac "ps_clear x y z" for x y z)
    apply (thin_tac "cteCap x = y" for x y)+
    apply (frule is_aligned_no_overflow)
    apply (simp only: x_power_minus_1)
    apply (frule_tac x=x in word_plus_strict_mono_right[of _ "2^pageBits"])
     apply (rule ccontr)
     apply (simp only: not_le)
     apply (frule_tac y="x" in less_le_trans, assumption)
     apply (simp add: word_sub_less_iff)
    apply simp
    done
  moreover
  have h2dd_eq:
       "heap_to_device_data (?psu (ksPSpace s))
                          (?mmu (underlying_memory (ksMachineState s))) =
        heap_to_device_data (?psu (ksPSpace s))
                          (underlying_memory (ksMachineState s))"
    supply mask_2pm1[simp] add_diff_eq[simp]
    apply (subst heap_to_device_data_update_region
                 [where S="{ptr..ptr + 2 ^ bits - 1}", simplified])
     prefer 2
     apply (rule ext)
     apply clarsimp
    apply (simp add: map_option_def map_comp_def
              split: if_split_asm option.splits)
    apply (frule pspace_alignedD'[OF _ pspace_aligned'])
    apply (case_tac "pageBits \<le> bits")
     apply (simp add: objBitsKO_def split: kernel_object.splits)
     apply clarsimp
     apply (rule aligned_range_offset_mem[simplified, OF _ _ al])
       apply assumption+
    apply (rule iffI[rotated], simp)
    apply (simp add: objBits_simps)
    apply (rule FalseE)
    apply (case_tac "ptr \<le> x", simp)
     apply clarsimp
     apply (frule_tac y="ptr + 2 ^ bits - 1" in le_less_trans)
      apply (simp only: not_le)
     apply (drule (1) is_aligned_no_wrap')
     apply simp
    apply (cut_tac cte[simplified cte_wp_at_ctes_of])
    apply clarsimp
    apply (frule ctes_of_valid'[OF _ valid_objs'])
    apply (frule pspace_distinctD'[OF _ pspace_distinct'])
    apply (clarsimp simp add: valid_cap'_def valid_untyped'_def2 capAligned_def)
    apply (drule_tac x=x in spec)
    apply (simp add: obj_range'_def objBitsKO_def mask_def)
    apply (simp only: not_le)
    apply (cut_tac is_aligned_no_overflow[OF al])
    apply (case_tac "ptr \<le> x + 2 ^ pageBits - 1",
           simp_all only: simp_thms not_le)
    apply clarsimp
    apply (thin_tac "psp = Some ko" for psp ko)+
    apply (thin_tac "ps_clear x y z" for x y z)
    apply (thin_tac "cteCap x = y" for x y)+
    apply (frule is_aligned_no_overflow)
    apply (simp only: x_power_minus_1)
    apply (frule_tac x=x in word_plus_strict_mono_right[of _ "2^pageBits"])
     apply (rule ccontr)
     apply (simp only: not_le)
     apply (frule_tac y="x" in less_le_trans, assumption)
     apply (simp add: word_sub_less_iff)
    apply simp
    done

  moreover {
    from D.valid_untyped invs have tcb_no_overlap:
      "\<And>p v. map_to_tcbs (ksPSpace s) p = Some v
        \<Longrightarrow> p \<notin> {ptr..+2 ^ bits}
        \<Longrightarrow> {p ..+ 2 ^ objBitsT TCBT} \<inter> {ptr..+2 ^ bits} = {}"
      apply (clarsimp simp: valid_cap'_def)
      apply (drule(1) map_to_ko_atI')
      apply (clarsimp simp: obj_at'_def valid_untyped'_def2 mask_2pm1)
      apply (elim allE, drule(1) mp)
      apply (clarsimp simp only: obj_range'_def upto_intvl_eq[symmetric] al add_mask_fold[symmetric])
      apply (subgoal_tac "objBitsKO (KOTCB v) = objBitsT TCBT")
       apply (subgoal_tac "p \<in> {p ..+ 2 ^ objBitsT TCBT}")
        apply simp
        apply blast
       apply (simp add: upto_intvl_eq)
      apply (clarsimp simp: objBits_simps objBitsT_simps)
      done

    from cNodePartial[folded add_mask_fold, simplified upto_rew]
    have cn_no_overlap:
      "\<And>p n. gsCNodes s p = Some n \<Longrightarrow> p \<notin> {ptr..+2 ^ bits}
          \<Longrightarrow> {p ..+ 2 ^ (n + cte_level_bits)} \<inter> {ptr..+2 ^ bits} = {}"
      apply (simp add: cNodePartialOverlap_def)
      apply (elim allE, drule(1) mp)
      apply (clarsimp simp flip: add_mask_fold)
      apply (frule base_member_set, simp add: word_bits_def)
      apply (clarsimp simp only: upto_intvl_eq[symmetric] field_simps)
      apply blast
      done

    from sr have "cvariable_array_map_relation (gsCNodes s|\<^bsub>(- {ptr..+2 ^ bits})\<^esub>) ((^) 2) cte_Ptr
       (typ_region_bytes ptr bits (hrs_htd (t_hrs_' (globals s'))))"
      "cvariable_array_map_relation (map_to_tcbs (ksPSpace s|\<^bsub>(- {ptr..+2 ^ bits})\<^esub>)) (\<lambda>x. 5) cte_Ptr
       (typ_region_bytes ptr bits (hrs_htd (t_hrs_' (globals s'))))"
      apply (simp_all add: map_comp_restrict_map rf_sr_def cstate_relation_def Let_def)
       apply (rule cvariable_array_map_relation_detype, clarsimp+)
       apply (drule(1) cn_no_overlap)
       apply (simp add: cte_level_bits_def power_add)
      apply (rule cvariable_array_map_relation_detype, clarsimp+)
      apply (drule(1) tcb_no_overlap)
      apply (erule disjoint_subset[rotated])
      apply (rule intvl_start_le)
      apply (simp add: objBitsT_simps objBits_defs)
      done
  }

  moreover from sr
    have "apsnd fst (gs_clear_region ptr bits (ghost'state_' (globals s'))) =
        (gsUserPages s|\<^bsub>(- {ptr..+2 ^ bits})\<^esub>, gsCNodes s|\<^bsub>(- {ptr..+2 ^ bits})\<^esub>)
        \<and> ghost_size_rel (gs_clear_region ptr bits (ghost'state_' (globals s')))
            (gsMaxObjectSize s)"
    apply (case_tac "ghost'state_' (globals s')")
    apply (simp add: rf_sr_def cstate_relation_def Let_def gs_clear_region_def
                  upto_intvl_eq[OF al] carch_state_relation_def
                  cmachine_state_relation_def ghost_size_rel_def
                  ghost_assertion_data_get_def restrict_map_def
                  if_flip[symmetric, where F=None])
    done

  moreover from sr
  have "fst (snd (snd (gs_clear_region ptr bits (ghost'state_' (globals s'))))) =
        gsPTTypes (ksArchState s)|\<^bsub>(- {ptr..+2 ^ bits})\<^esub>"
    by (simp add: rf_sr_def cstate_relation_def Let_def gs_clear_region_def
                  restrict_map_def if_flip[symmetric, where F=None])

  moreover from sr
  have "h_t_valid (typ_region_bytes ptr bits (hrs_htd (t_hrs_' (globals s'))))
                   c_guard intStateIRQNode_array_Ptr"
    apply (clarsimp simp: rf_sr_def cstate_relation_def Let_def)
    apply (simp add: h_t_valid_typ_region_bytes)
    apply (simp add: upto_intvl_eq al)
    apply (rule disjoint_subset[OF _ ptr_refs])
    apply (simp add: cinterrupt_relation_def cte_level_bits_def)
    done

  moreover
  from pTablePartial[folded add_mask_fold, simplified upto_rew]
  have "\<And>p v. \<lbrakk>gsPTTypes (ksArchState s) p = Some v; p \<notin> {ptr ..+ 2 ^ bits}\<rbrakk>
               \<Longrightarrow> {p ..+ 2 ^ pt_bits v} \<inter> {ptr ..+ 2 ^ bits} = {}"
    apply (simp add: pTablePartialOverlap_def)
    apply (elim allE, drule(1) mp)
    apply (clarsimp simp flip: add_mask_fold)
    apply (frule base_member_set, simp add: bit_simps)
    apply (clarsimp simp only: upto_intvl_eq[symmetric] field_simps power_add)
    apply blast
    done

  with sr
  have "cvariable_array_map_relation (gsPTTypes (ksArchState s)|\<^bsub>(- {ptr..+2 ^ bits})\<^esub>)
                                     (\<lambda>pt_t. 2 ^ ptTranslationBits pt_t)
                                     pte_Ptr
                                     (typ_region_bytes ptr bits (hrs_htd (t_hrs_' (globals s'))))"
    apply (simp add: map_comp_restrict_map rf_sr_def cstate_relation_def Let_def pte_bits_def
                     word_size_bits_def)
    apply (rule cvariable_array_map_relation_detype; clarsimp)
    apply (simp add: pt_bits_def table_size_def power_add pte_bits_def word_size_bits_def)
    done

  ultimately
  show "(?t, globals_update
               (%x. ghost'state_'_update (gs_clear_region ptr bits)
                      (t_hrs_'_update ?th x)) s') \<in> rf_sr"
    using sr untyped_cap_rf_sr_ptr_bits_domain[OF cte invs sr]
    by (simp add: rf_sr_def cstate_relation_def Let_def
                  psu_restrict cpspace_relation_def
                  carch_state_relation_def carch_globals_def
                  cmachine_state_relation_def
                  hrs_htd_update htd_safe_typ_region_bytes
                  zero_ranges_are_zero_typ_region_bytes)

qed

abbreviation (input)
  "global_htd_update f == Guard MemorySafety \<lbrace>htd_safe domain (hrs_htd \<acute>t_hrs)
        \<and> htd_safe domain (\<acute>(\<lambda>s. f s) (hrs_htd \<acute>t_hrs))\<rbrace>
    (Basic (\<lambda>s. globals_update (t_hrs_'_update (hrs_htd_update (f s))) s))"

lemma kernel_data_refs_domain_eq_rotate:
  "(kernel_data_refs = - domain) = (domain = - kernel_data_refs)"
  by blast

lemma deleteObjects_ccorres[corres]:
  "ccorres dc xfdc
     (cte_wp_at' (\<lambda>cte. cteCap cte = UntypedCap d ptr bits idx) p and
      (\<lambda>s. descendants_range' (UntypedCap d ptr bits idx) p (ctes_of s)) and
      invs' and ct_active' and sch_act_simple and
      K ( 4 \<le> bits \<and> bits < word_bits))
     UNIV hs
     (deleteObjects ptr bits)
     (Seq (global_htd_update (\<lambda>_. typ_region_bytes ptr bits))
          (Basic (\<lambda>s. globals_update
             (ghost'state_'_update (gs_clear_region ptr bits)) s)))"
  apply (rule ccorres_guard_imp2)
   apply (rule ccorres_Guard_Seq)
   apply (rule Corres_UL_C.ccorres_exec_cong
                 [THEN iffD2, OF _ deleteObjects_ccorres'[where idx=idx and p=p and d=d]])
   apply (simp add: exec_Basic_Seq_Basic o_def
                    hrs_ghost_update_comm[simplified o_def])
  apply clarsimp
  apply (frule(2) untyped_cap_rf_sr_ptr_bits_domain)
  by (clarsimp simp: rf_sr_def cstate_relation_def Let_def
                        kernel_data_refs_domain_eq_rotate htd_safe_typ_region_bytes
                        untyped_cap_rf_sr_ptr_bits_domain)

end
end
