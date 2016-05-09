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

instantiation array :: (c_type,finite) c_type
begin
instance ..
end

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

instantiation array :: (mem_type,finite) mem_type_sans_size
begin

instance
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

end

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

(* Showing arrays are in mem_type requires maximum sizes for objects,
   and maximum counts for elements *)
class oneMB_size = mem_type +
  assumes oneMB_size_ax: "size_of TYPE('a::c_type) < 2 ^ 19"

class fourthousand_count = finite +
  assumes fourthousand_count_ax: "CARD ('a) <= 2 ^ 13"

instantiation array :: (oneMB_size, fourthousand_count) mem_type
begin

instance
apply intro_classes
apply simp
apply (subgoal_tac "addr_card = 2 ^ (addr_bitsize - 19) * 2 ^ 19")
  apply (erule ssubst)
  apply (rule less_le_trans[where y = "card (UNIV::'b set) * 2 ^ 19"])
    apply (rule mult_less_mono2)
      apply (rule oneMB_size_ax)
    apply simp
  apply (rule mult_le_mono1)
    apply (rule le_trans[where j = "2 ^ 13"])
      apply (rule fourthousand_count_ax)
    apply simp
  apply simp
apply (simp add: addr_card)
done

end

class twoToSix_size = oneMB_size +
  assumes twoToSix_size_ax: "size_of TYPE('a::c_type) < 2 ^ 6"

instantiation array :: (twoToSix_size, fourthousand_count) oneMB_size
begin

instance
apply intro_classes
apply simp
  apply (rule order_less_le_trans)
   apply (rule mult_le_less_imp_less)
    apply (rule fourthousand_count_ax)
   apply (rule twoToSix_size_ax)
  apply simp
   apply simp
  apply simp
  done

end

instantiation word :: (len8) oneMB_size
begin
instance
apply intro_classes
apply(simp add: size_of_def)
apply(subgoal_tac "len_of TYPE('a) \<le> 128")
 apply simp
apply(rule len8_width)
done
end

instantiation word :: (len8) twoToSix_size
begin
instance
apply intro_classes
apply(simp add: size_of_def)
apply(subgoal_tac "len_of TYPE('a) \<le> 128")
 apply simp
apply(rule len8_width)
done
end

instantiation ptr :: (c_type) oneMB_size
begin
instance
apply intro_classes
apply (simp add: size_of_def)
done
end

instantiation ptr :: (c_type) twoToSix_size
begin
instance
apply intro_classes
apply (simp add: size_of_def)
done
end

class lt12 = finite +
  assumes lt12_ax: "CARD ('a) < 2 ^ 12"
class lt11 = lt12 +
  assumes lt11_ax: "CARD ('a) < 2 ^ 11"
class lt10 = lt11 +
  assumes lt10_ax: "CARD ('a) < 2 ^ 10"
class lt9 = lt10 +
  assumes lt9_ax: "CARD ('a) < 2 ^ 9"
class lt8 = lt9 +
  assumes lt8_ax: "CARD ('a) < 2 ^ 8"
class lt7 = lt8 +
  assumes lt7_ax: "CARD ('a) < 2 ^ 7"
class lt6 = lt7 +
  assumes lt6_ax: "CARD ('a) < 2 ^ 6"
class lt5 = lt6 +
  assumes lt5_ax: "CARD ('a) < 2 ^ 5"
class lt4 = lt5 +
  assumes lt4_ax: "CARD ('a) < 2 ^ 4"
class lt3 = lt4 +
  assumes lt3_ax: "CARD ('a) < 2 ^ 3"
class lt2 = lt3 +
  assumes lt2_ax: "CARD ('a) < 2 ^ 2"
class lt1 = lt2 +
  assumes lt1_ax: "CARD ('a) < 2 ^ 1"

instantiation bit0 :: (lt12) fourthousand_count
begin
instance
  by (intro_classes, insert lt12_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt12) fourthousand_count
begin
instance
  by (intro_classes, insert lt12_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt11) lt12
begin
instance
  by (intro_classes, insert lt11_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt11) lt12
begin
instance
  by (intro_classes, insert lt11_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt10) lt11
begin
instance
  by (intro_classes, insert lt10_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt10) lt11
begin
instance
  by (intro_classes, insert lt10_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt9) lt10
begin
instance
  by (intro_classes, insert lt9_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt9) lt10
begin
instance
  by (intro_classes, insert lt9_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt8) lt9
begin
instance
  by (intro_classes, insert lt8_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt8) lt9
begin
instance
  by (intro_classes, insert lt8_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt7) lt8
begin
instance
  by (intro_classes, insert lt7_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt7) lt8
begin
instance
  by (intro_classes, insert lt7_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt6) lt7
begin
instance
  by (intro_classes, insert lt6_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt6) lt7
begin
instance
  by (intro_classes, insert lt6_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt5) lt6
begin
instance
  by (intro_classes, insert lt5_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt5) lt6
begin
instance
  by (intro_classes, insert lt5_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt4) lt5
begin
instance
  by (intro_classes, insert lt4_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt4) lt5
begin
instance
  by (intro_classes, insert lt4_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt3) lt4
begin
instance
  by (intro_classes, insert lt3_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt3) lt4
begin
instance
  by (intro_classes, insert lt3_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt2) lt3
begin
instance
  by (intro_classes, insert lt2_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt2) lt3
begin
instance
  by (intro_classes, insert lt2_ax[where 'a = 'a], simp)
end

instantiation bit0 :: (lt1) lt2
begin
instance
  by (intro_classes, insert lt1_ax[where 'a = 'a], simp)
end

instantiation bit1 :: (lt1) lt2
begin
instance
  by (intro_classes, insert lt1_ax[where 'a = 'a], simp)
end

instantiation num1 :: lt1
begin
instance
  by (intro_classes, simp_all)
end

(* don't understand why this also seems to be necessary *)
instantiation num1 :: fourthousand_count
begin
instance
  by (intro_classes, simp)
end

(* introduce hackish handling of 8192 type by making a copy of the type
   under a constructor, and then manually showing that it is an instance of
   fourthousand_count *)
datatype ty8192 = ty8192 "8192"

lemma univ8192: "(UNIV::ty8192 set) = image ty8192 (UNIV::8192 set)"
apply (simp add: set_eq_iff image_iff)
apply (rule_tac allI)
apply (rule_tac ty8192.induct)
apply simp
done

instance "ty8192" :: finite
apply intro_classes
apply (simp add: univ8192)
done

lemma card8192[simp]: "CARD(ty8192) = CARD(8192)"
apply (simp add: univ8192 card_image inj_on_def)
done

instance "ty8192" :: fourthousand_count
by intro_classes simp


end
