(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ArraysMemInstance
imports Arrays CompoundCTypes
begin

primrec
  array_tag_n :: "nat \<Rightarrow> ('a::c_type,'b::finite) array typ_info"
where
  atn_base:
  "array_tag_n 0 = ((empty_typ_info (typ_name (typ_uinfo_t TYPE('a)) @ ''_array_'' @
      nat_to_bin_string (CARD('b::finite))))::('a::c_type,'b) array
          typ_info)"
| atn_rec:
  "array_tag_n (Suc n) = ((ti_typ_combine TYPE('a::c_type)
      (\<lambda>x. index x n) (\<lambda>x f. update f n x) (replicate n CHR ''1'')
          (array_tag_n n))::('a,'b::finite) array typ_info)"

definition array_tag :: "('a::c_type,'b::finite) array itself \<Rightarrow> ('a,'b) array typ_info" where
  "array_tag t \<equiv> array_tag_n (CARD('b))"

instance array :: (c_type,finite) c_type ..

overloading typ_info_array \<equiv> typ_info_t begin
definition typ_info_array: "typ_info_array (w::('a::c_type,'b::finite) array itself) \<equiv> array_tag w"
end

lemma field_names_array_tag_length [rule_format]:
  "x \<in> set (field_names_list (array_tag_n n)) \<longrightarrow> length x < n"
  by (induct n) auto

lemma replicate_mem_field_names_array_tag [simp]:
  "replicate n x \<notin> set (field_names_list (array_tag_n n))"
  by (fastforce dest: field_names_array_tag_length)

lemma aggregate_array_tag [simp]:
  "aggregate (array_tag_n n)"
  by (cases n; simp)

lemma wf_desc_array_tag [simp]:
  "wf_desc ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)"
  by (induct n; simp) (fastforce elim: wf_desc_ti_typ_combine)

lemma wf_size_desc_array_tag [simp]:
  "0 < n \<Longrightarrow> wf_size_desc ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)"
  apply(induct n; simp)
  apply(case_tac "n=0"; simp)
  apply(rule wf_size_desc_ti_typ_combine)
  apply simp
  done

lemma g_ind_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; n \<le> CARD('b) \<rbrakk> \<Longrightarrow>
   g_ind (lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) []) (\<lambda>x f. update f m x)"
  by (induct n; fastforce elim: g_ind_ti_typ_combine)

lemma fc_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; n \<le> CARD('b) \<rbrakk> \<Longrightarrow>
   fu_commutes (update_ti_t ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)) (\<lambda>x f. update f m x)"
  by (induct n; fastforce elim: fc_ti_typ_combine simp: fg_cons_def)

lemma f_ind_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; m < CARD('b) \<rbrakk> \<Longrightarrow>
   f_ind (\<lambda>x. index x m) (lf_fd ` lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) [])"
  by (induct n; fastforce elim: f_ind_ti_typ_combine)

lemma fa_fu_g_array_tag_udpate [simp]:
  "\<lbrakk> n \<le> m; m < CARD('b) \<rbrakk> \<Longrightarrow>
   fa_ind (lf_fd ` lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) []) (\<lambda>x f. update f m x)"
  by (induct n; fastforce elim: fa_ind_ti_typ_combine)

lemma wf_fdp_array_tag [simp]:
  "n \<le> CARD('b) \<Longrightarrow> wf_lf (lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) [])"
  by (induct n; fastforce elim: wf_lf_ti_typ_combine)

lemma upd_local_update [simp]:
  "upd_local (\<lambda>x f. update f n x)"
  unfolding upd_local_def
  by (metis update_update)

lemma fu_eq_mask_array_tag [simp, rule_format]:
  "n \<le> CARD('b) \<longrightarrow> (\<forall>m. (\<forall>k v. k < CARD('b) \<longrightarrow>
      index ((m v)::('a,'b) array) k = (if n \<le> k then
          index (undefined::('a::mem_type,'b::finite) array) k
          else index v k)) \<longrightarrow> fu_eq_mask (array_tag_n n) m)"
  apply(induct n; clarsimp)
   apply(rule fu_eq_mask_empty_typ_info)
   apply(clarsimp simp: array_index_eq)
  apply(rule fu_eq_mask_ti_typ_combine; clarsimp?)
   apply(drule_tac x="\<lambda>v. update (m v) n (index undefined n)" in spec)
   apply(erule impE)
    apply clarsimp
    apply(case_tac "k=n"; simp)
   apply(subgoal_tac "\<forall>v bs. m (update v n bs) = update (m v) n bs"; clarsimp)
   apply(clarsimp simp: array_index_eq)
   apply(case_tac "i=n"; clarsimp)
   apply(case_tac "Suc n \<le> i"; clarsimp)
  apply(clarsimp simp: fg_cons_def)
  done

lemma size_td_array_tag [simp]:
  "size_td (((array_tag_n n)::('a,'b::finite) array typ_info)) =
      n * size_of TYPE('a::c_type)"
  by (induct n; simp add: size_td_lt_ti_typ_combine size_of_def)

lemma align_td_array_tag:
  "0 < n \<Longrightarrow>
   align_td ((array_tag_n n)::('a,'b::finite) array typ_info) = (align_td (typ_info_t (TYPE('a::c_type))))"
  by (induct n; clarsimp)
     (case_tac "n = 0"; clarsimp simp: align_of_def max_def)

lemma align_field_array [simp]:
  "align_field ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)"
  by (induct_tac n; clarsimp)
     (metis align_field_ti_typ_combine align_of_def align_size_of dvd_mult size_td_array_tag)

instance array :: (mem_type,finite) mem_type_sans_size
  apply intro_classes
       apply(simp_all add: typ_info_array array_tag_def size_of_def norm_bytes_def)
   apply clarsimp
   apply(rule fu_eq_mask)
    apply(simp add: size_of_def)
   apply(rule fu_eq_mask_array_tag; simp)
  apply (clarsimp simp: align_of_def typ_info_array array_tag_def align_td_array_tag)
  apply (metis align_of_def align_size_of dvd_mult size_of_def)
  done

declare atn_base [simp del]
declare atn_rec [simp del]

lemma size_of_array [simp]:
  "size_of TYPE(('a,'b::finite) array) = CARD('b) * size_of TYPE('a::c_type)"
  by (simp add: size_of_def typ_info_array array_tag_def)

lemma size_td_array:
  "size_td (typ_info_t TYPE(('a,'b::finite) array)) = CARD('b) * size_of TYPE('a::c_type)"
  by (simp add: size_of_def typ_info_array array_tag_def)

lemma align_td_array:
  "2^align_td (typ_info_t TYPE(('a,'b::finite) array)) = align_of TYPE('a::c_type)"
  by (simp add: align_of_def typ_info_array array_tag_def align_td_array_tag)

end
