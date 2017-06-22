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

definition
  array_tag :: "('a::c_type,'b::finite) array itself \<Rightarrow> ('a,'b) array typ_info" where
  "array_tag t \<equiv> array_tag_n (CARD('b))"

instance array :: (c_type,finite) c_type ..

overloading typ_info_array \<equiv> typ_info_t begin
definition
  typ_info_array: "typ_info_array (w::('a::c_type,'b::finite) array itself) \<equiv> array_tag w"
end

lemma field_names_array_tag_length [rule_format]:
  "x \<in> set (field_names_list (array_tag_n n)) \<longrightarrow> length x < n"
apply(induct_tac n)
 apply simp
apply clarsimp
done

lemma replicate_mem_field_names_array_tag [simp]:
  "replicate n x \<notin> set (field_names_list (array_tag_n n))"
apply clarsimp
apply(drule field_names_array_tag_length)
apply simp
done

lemma aggregate_array_tag [simp]:
  "aggregate (array_tag_n n)"
apply(case_tac n)
 apply simp+
done

lemma wf_desc_array_tag [simp]:
  "wf_desc ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)"
apply(induct_tac n)
 apply simp+
apply(erule wf_desc_ti_typ_combine)
apply simp
done

lemma wf_size_desc_array_tag [simp, rule_format]:
  "0 < n \<longrightarrow> wf_size_desc ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)"
apply(induct n)
 apply simp+
apply(case_tac "n=0")
 apply simp
apply(rule wf_size_desc_ti_typ_combine)
apply simp
done

lemma g_ind_array_tag_udpate [simp]:
  "n \<le> m \<longrightarrow> n \<le> CARD('b) \<longrightarrow>
      g_ind (lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) []) (\<lambda>x f. update f m x)"
apply(induct_tac n)
 apply clarsimp+
apply(erule g_ind_ti_typ_combine)
 apply clarsimp+
done

lemma fc_array_tag_udpate [simp]:
  "n \<le> m \<longrightarrow> n \<le> CARD('b) \<longrightarrow>
      fu_commutes (update_ti_t ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)) (\<lambda>x f. update f m x)"
apply(induct_tac n)
 apply clarsimp+
apply(erule fc_ti_typ_combine)
  apply(clarsimp simp: fg_cons_def)
 apply clarsimp+
done

lemma f_ind_array_tag_udpate [simp, rule_format]:
  "n \<le> m \<longrightarrow> m < CARD('b) \<longrightarrow>
      f_ind (\<lambda>x. index x m) (lf_fd ` lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) [])"
apply(induct_tac n)
 apply clarsimp+
apply(erule f_ind_ti_typ_combine)
 apply clarsimp
apply simp
done

lemma fa_fu_g_array_tag_udpate [simp, rule_format]:
  "n \<le> m \<longrightarrow> m < CARD('b) \<longrightarrow>
      fa_ind (lf_fd ` lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) []) (\<lambda>x f. update f m x)"
apply(induct_tac n)
 apply clarsimp+
apply(erule fa_ind_ti_typ_combine)
apply clarsimp+
done

lemma wf_fdp_array_tag [simp, rule_format]:
  "n \<le> CARD('b) \<longrightarrow>
      wf_lf (lf_set ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info) [])"
apply(induct_tac n)
 apply clarsimp+
apply(erule wf_lf_ti_typ_combine)
      apply simp+
done

lemma upd_local_update [simp]:
  "upd_local (\<lambda>x f. update f n x)"
apply(auto simp: upd_local_def)
apply(subst cart_eq)
apply clarsimp
apply(subst (asm) cart_eq)
apply(drule_tac x=i in spec)
apply clarsimp
apply(case_tac "i=n")
 apply simp+
done

lemma fu_eq_mask_array_tag [simp, rule_format]:
  "n \<le> CARD('b) \<longrightarrow> (\<forall>m. (\<forall>k v. k < CARD('b) \<longrightarrow>
      index ((m v)::('a,'b) array) k = (if n \<le> k then
          index (undefined::('a::mem_type,'b::finite) array) k
          else index v k)) \<longrightarrow> fu_eq_mask (array_tag_n n) m)"
apply(induct n)
 apply clarsimp
 apply(rule fu_eq_mask_empty_typ_info)
 apply clarsimp
 apply(subst cart_eq)
 apply simp
apply clarsimp
apply(rule fu_eq_mask_ti_typ_combine)
     apply(drule_tac x="\<lambda>v. update (m v) n (index undefined n)" in spec)
     apply(erule impE)
      apply clarsimp
      apply(drule_tac x=k in spec)
      apply clarsimp
      apply(case_tac "k=n")
       apply simp
      apply clarsimp
     apply(subgoal_tac "\<forall>v bs. m (update v n bs) = update (m v) n bs")
      apply clarsimp+
     apply(subst cart_eq)
     apply clarsimp
     apply(drule_tac x=i in spec)
     apply clarsimp
     apply(case_tac "i=n")
      apply clarsimp+
     apply(frule_tac x="update v n bs" in spec)
     apply(drule_tac x="v" in spec)
     apply clarsimp
     apply(case_tac "Suc n \<le> i")
      apply clarsimp+
    apply(clarsimp simp: fg_cons_def)
   apply(clarsimp)
  apply simp
done

lemma size_td_array_tag [simp]:
  "size_td (((array_tag_n n)::('a,'b::finite) array typ_info)) =
      n * size_of TYPE('a::c_type)"
apply(induct_tac n)
 apply simp
apply simp
apply(simp add: size_td_lt_ti_typ_combine size_of_def)
done

lemma align_td_array_tag [rule_format]:
  "0 < n \<longrightarrow> align_td ((array_tag_n n)::('a,'b::finite) array typ_info) = (align_td (typ_info_t (TYPE('a::c_type))))"
apply(induct_tac n)
 apply simp
apply(clarsimp simp: ti_typ_combine_def Let_def)
apply(case_tac "n = 0")
 apply(clarsimp simp: align_of_def max_def)+
done

lemma align_field_array [simp]:
  "align_field ((array_tag_n n)::('a::mem_type,'b::finite) array typ_info)"
apply(induct_tac n)
 apply simp
apply clarsimp
apply(erule align_field_ti_typ_combine)
apply simp
apply(rule dvd_mult)
apply(subgoal_tac "align_of TYPE('a) dvd size_of TYPE('a)")
 apply(simp add: align_of_def)
apply(rule align_size_of)
done

instance array :: (mem_type,finite) mem_type_sans_size
apply intro_classes
     apply(simp_all add: typ_info_array array_tag_def size_of_def
                         norm_bytes_def)

 apply clarsimp
 apply(rule fu_eq_mask)
  apply(simp add: size_of_def)
 apply(rule fu_eq_mask_array_tag)
    apply simp+

apply(clarsimp simp: align_of_def typ_info_array array_tag_def)
apply(subst align_td_array_tag)
 apply simp
apply(rule dvd_trans)
 apply(subgoal_tac "align_of TYPE('a) dvd size_of TYPE('a)")
  apply(simp only: align_of_def)
 apply(rule align_size_of)
apply(simp add: size_of_def)
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
apply(simp add: align_of_def typ_info_array array_tag_def)
apply(subst align_td_array_tag)
 apply simp+
done

end
