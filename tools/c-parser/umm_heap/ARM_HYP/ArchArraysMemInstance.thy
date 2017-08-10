(*
 * Copyright 2017, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory ArchArraysMemInstance
imports "../ArraysMemInstance"
begin

(* Showing arrays are in mem_type requires maximum sizes for objects,
   and maximum counts for elements *)
class array_outer_max_size = mem_type +
  assumes array_outer_max_size_ax: "size_of TYPE('a::c_type) < 2 ^ 19"

class array_max_count = finite +
  assumes array_max_count_ax: "CARD ('a) <= 2 ^ 13"

instance array :: (array_outer_max_size, array_max_count) mem_type
apply intro_classes
apply simp
apply (subgoal_tac "addr_card = 2 ^ (addr_bitsize - 19) * 2 ^ 19")
  apply (erule ssubst)
  apply (rule less_le_trans[where y = "card (UNIV::'b set) * 2 ^ 19"])
    apply (rule mult_less_mono2)
      apply (rule array_outer_max_size_ax)
    apply simp
  apply (rule mult_le_mono1)
    apply (rule le_trans[where j = "2 ^ 13"])
      apply (rule array_max_count_ax)
    apply simp
  apply simp
apply (simp add: addr_card)
done

class array_inner_max_size = array_outer_max_size +
  assumes array_inner_max_size_ax: "size_of TYPE('a::c_type) < 2 ^ 6"

instance array :: (array_inner_max_size, array_max_count) array_outer_max_size
apply intro_classes
apply simp
  apply (rule order_less_le_trans)
   apply (rule mult_le_less_imp_less)
    apply (rule array_max_count_ax)
   apply (rule array_inner_max_size_ax)
  apply simp
   apply simp
  apply simp
  done

instance word :: (len8) array_outer_max_size
apply intro_classes
apply(simp add: size_of_def)
apply(subgoal_tac "len_of TYPE('a) \<le> 128")
 apply simp
apply(rule len8_width)
done

instance word :: (len8) array_inner_max_size
apply intro_classes
apply(simp add: size_of_def)
apply(subgoal_tac "len_of TYPE('a) \<le> 128")
 apply simp
apply(rule len8_width)
done

instance ptr :: (c_type) array_outer_max_size
apply intro_classes
apply (simp add: size_of_def)
done

instance ptr :: (c_type) array_inner_max_size
apply intro_classes
apply (simp add: size_of_def)
done

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

instance bit0 :: (lt12) array_max_count
  using lt12_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt12) array_max_count
  using lt12_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt11) lt12
  using lt11_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt11) lt12
  using lt11_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt10) lt11
  using lt10_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt10) lt11
  using lt10_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt9) lt10
  using lt9_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt9) lt10
  using lt9_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt8) lt9
  using lt8_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt8) lt9
  using lt8_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt7) lt8
  using lt7_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt7) lt8
  using lt7_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt6) lt7
  using lt6_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt6) lt7
  using lt6_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt5) lt6
  using lt5_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt5) lt6
  using lt5_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt4) lt5
  using lt4_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt4) lt5
  using lt4_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt3) lt4
  using lt3_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt3) lt4
  using lt3_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt2) lt3
  using lt2_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt2) lt3
  using lt2_ax[where 'a='a] by intro_classes simp

instance bit0 :: (lt1) lt2
  using lt1_ax[where 'a='a] by intro_classes simp

instance bit1 :: (lt1) lt2
  using lt1_ax[where 'a='a] by intro_classes simp

instance num1 :: lt1
  by (intro_classes, simp_all)

(* don't understand why this also seems to be necessary *)
instance num1 :: array_max_count
  by (intro_classes, simp)

(* introduce hackish handling of 8192 type by making a copy of the type
   under a constructor, and then manually showing that it is an instance of
   array_max_count *)
datatype array_max_count_ty = array_max_count_ty "8192"

(* ML c-parser code also needs to know at which array size to use this type *)
ML \<open>
  structure ArchArrayMaxCount = struct
    val array_max_count = 8192
  end
\<close>

lemma univ_array_max_count_ty:
  "(UNIV::array_max_count_ty set) = image array_max_count_ty (UNIV::8192 set)"
  apply (simp add: set_eq_iff image_iff)
  apply (rule_tac allI)
  apply (rule_tac array_max_count_ty.induct)
  apply simp
  done

instance "array_max_count_ty" :: finite
  apply intro_classes
  apply (simp add: univ_array_max_count_ty)
  done

lemma card_array_max_count_ty[simp]: "CARD(array_max_count_ty) = CARD(8192)"
  apply (simp add: univ_array_max_count_ty card_image inj_on_def)
  done

instance "array_max_count_ty" :: array_max_count
  by intro_classes simp

end
