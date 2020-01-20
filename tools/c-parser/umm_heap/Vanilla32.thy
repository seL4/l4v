(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* License: BSD, terms see file ./LICENSE *)

theory Vanilla32
imports "./$L4V_ARCH/Word_Mem_Encoding" "Word_Lib.Word_Lib" CTypes
begin



overloading typ_info_word \<equiv> typ_info_t begin
definition
  typ_info_word: "typ_info_word (w::'a::len8 word itself) \<equiv> word_tag w"
end

overloading typ_name_itself_word \<equiv> typ_name_itself begin
definition
  typ_name_itself_word: "typ_name_itself_word (w::'a::len8 word itself) \<equiv> typ_name (typ_info_t w)"
end

lemma align_of_word:
  "align_of TYPE('a::len8 word) = len_of TYPE('a) div 8"
  by (simp add: align_of_def typ_info_word word_tag_def len8_bytes)

instantiation word :: (len8) mem_type
begin

instance
proof intro_classes
  show "\<And>bs v w. length bs = size_of TYPE('a word) \<longrightarrow>
       update_ti_t (typ_info_t TYPE('a word)) bs v =
       update_ti_t (typ_info_t TYPE('a word)) bs w"
    by (simp add: typ_info_word word_tag_def size_of_def)
next
  show "wf_desc (typ_info_t TYPE('a word))"
    by (simp add: typ_info_word word_tag_def)
next
  have "8 dvd len_of TYPE('a)" by (rule len8_dv8)
  moreover have "0 < len_of TYPE('a)" by simp
  ultimately have "0 < len_of TYPE('a) div 8" by - (erule dvdE, simp)
  thus "wf_size_desc (typ_info_t TYPE('a word))"
    by (simp add: typ_info_word word_tag_def len8_pow)
next
  have "8 dvd len_of TYPE('a)" by (rule len8_dv8)
  thus "wf_lf (lf_set (typ_info_t TYPE('a word)) [])"
  by (auto simp: typ_info_word word_tag_def wf_lf_def
                 fd_cons_def fd_cons_double_update_def fd_cons_update_access_def
                 word_rcat_rsplit fd_cons_access_update_def fd_cons_length_def
                 length_word_rsplit_exp_size' word_size fd_cons_update_normalise_def
                 fd_cons_desc_def field_norm_def)
next
  show "size_of TYPE('a word) < addr_card"
    by (simp add: size_of_def typ_info_word word_tag_def)
       (rule len8_size)
next
  show "align_of TYPE('a word) dvd size_of TYPE('a word)"
    by (clarsimp simp: size_of_def align_of_word typ_info_word
                       word_tag_def)
next
  show "align_field (typ_info_t TYPE('a word))"
    by (clarsimp simp: typ_info_word word_tag_def align_field_def)
qed

end

instantiation word :: (len8) simple_mem_type
begin

instance
  apply intro_classes
  apply(clarsimp simp: typ_info_word word_tag_def typ_uinfo_t_def)
  done

end

class len_eq1 = len +
  assumes len_eq1: "len_of TYPE('a::len) = 1"
instance num1 :: len_eq1
by (intro_classes, simp)

(* naming scheme len_lg<digit1><digit2> means the log of the length is between
   digit1 and digit2 inclusive *)
class len_lg01 = len +
  assumes len_lg01: "len_of TYPE('a::len) \<in> {1,2}"
instance bit0 :: (len_eq1) len_lg01
by (intro_classes, simp add: len_eq1)
instance num1 :: len_lg01
by (intro_classes, simp)

class len_lg02 = len +
  assumes len_lg02: "len_of TYPE('a::len) \<in> {1,2,4}"
instance bit0 :: (len_lg01) len_lg02
apply intro_classes
apply (insert len_lg01[where 'a = 'a])
apply simp
done
instance num1 :: len_lg02
by (intro_classes, simp)

class len_lg03 = len +
  assumes len_lg03: "len_of TYPE('a::len) \<in> {1,2,4,8}"
instance bit0 :: (len_lg02) len_lg03
apply intro_classes
apply (insert len_lg02[where 'a = 'a])
apply simp
done
instance num1 :: len_lg03
by (intro_classes, simp)

class len_lg04 = len +
  assumes len_lg04: "len_of TYPE('a::len) \<in> {1,2,4,8,16}"
instance bit0 :: (len_lg03) len_lg04
apply intro_classes
apply (insert len_lg03[where 'a = 'a])
apply simp
done

instance num1 :: len_lg04
by (intro_classes, simp)
class len_lg15 = len +
  assumes len_lg15: "len_of TYPE('a::len) \<in> {2,4,8,16,32}"
instance bit0 :: (len_lg04) len_lg15
apply intro_classes
apply (insert len_lg04[where 'a = 'a])
apply simp
done

class len_lg26 = len +
  assumes len_lg26: "len_of TYPE('a::len) \<in> {4,8,16,32,64}"

instance bit0 :: (len_lg15) len_lg26
apply intro_classes
apply (insert len_lg15[where 'a = 'a])
apply simp
done

instance bit0 :: (len_lg26) len8
apply intro_classes
  apply simp
  apply (insert len_lg26[where 'a = 'a])
  apply (simp add: len_exp_def)
  apply (erule disjE)
    apply (simp add: bogus_log2lessthree_def len8_bytes len8_width)
  apply (erule disjE)
    apply (simp add: bogus_log2lessthree_def)
  apply (erule disjE)
    apply (simp add: bogus_log2lessthree_def)
  apply (erule disjE)
    apply (simp add: bogus_log2lessthree_def)
  apply (simp add: bogus_log2lessthree_def)
apply simp
apply auto
done

instance signed :: (len_eq1) len_eq1     using len_eq1  by (intro_classes, simp)
instance signed :: (len_lg01) len_lg01   using len_lg01 by (intro_classes, simp)
instance signed :: (len_lg02) len_lg02   using len_lg02 by (intro_classes, simp)
instance signed :: (len_lg03) len_lg03   using len_lg03 by (intro_classes, simp)
instance signed :: (len_lg04) len_lg04   using len_lg04 by (intro_classes, simp)
instance signed :: (len_lg15) len_lg15   using len_lg15 by (intro_classes, simp)
instance signed :: (len_lg26) len_lg26   using len_lg26 by (intro_classes, simp)

lemma
  "to_bytes (1*256*256*256 + 2*256*256 + 3*256 + (4::32 word)) bs = [4, 3, 2, 1]"
  by (simp add: to_bytes_def typ_info_word word_tag_def Let_def)

lemma size_td_words [simp]:
  "size_td (typ_info_t TYPE(8 word)) = 1"
  "size_td (typ_info_t TYPE(16 word)) = 2"
  "size_td (typ_info_t TYPE(32 word)) = 4"
  "size_td (typ_info_t TYPE(64 word)) = 8"
  by (auto simp: typ_info_word word_tag_def)

lemma align_td_words [simp]:
  "align_td (typ_info_t TYPE(8 word)) = 0"
  "align_td (typ_info_t TYPE(16 word)) = 1"
  "align_td (typ_info_t TYPE(32 word)) = 2"
  "align_td (typ_info_t TYPE(64 word)) = 3"
  by (auto simp: typ_info_word word_tag_def len8_bytes)

lemma size_of_words [simp]:
  "size_of TYPE(8 word) = 1"
  "size_of TYPE(16 word) = 2"
  "size_of TYPE(32 word) = 4"
  "size_of TYPE(64 word) = 8"
  by (auto simp: size_of_def)

lemma align_of_words [simp]:
  "align_of TYPE(8 word) = 1"
  "align_of TYPE(16 word) = 2"
  "align_of TYPE(32 word) = 4"
  "align_of TYPE(64 word) = 8"
  by (auto simp: align_of_word)

lemma size_td_swords [simp]:
  "size_td (typ_info_t TYPE(8 sword)) = 1"
  "size_td (typ_info_t TYPE(16 sword)) = 2"
  "size_td (typ_info_t TYPE(32 sword)) = 4"
  "size_td (typ_info_t TYPE(64 sword)) = 8"
  by (auto simp: typ_info_word word_tag_def)

lemma align_td_swords [simp]:
  "align_td (typ_info_t TYPE(8 sword)) = 0"
  "align_td (typ_info_t TYPE(16 sword)) = 1"
  "align_td (typ_info_t TYPE(32 sword)) = 2"
  "align_td (typ_info_t TYPE(64 sword)) = 3"
  by (auto simp: typ_info_word word_tag_def len8_bytes)

lemma size_of_swords [simp]:
  "size_of TYPE(8 sword) = 1"
  "size_of TYPE(16 sword) = 2"
  "size_of TYPE(32 sword) = 4"
  "size_of TYPE(64 sword) = 8"
  by (auto simp: size_of_def)

lemma align_of_swords [simp]:
  "align_of TYPE(8 sword) = 1"
  "align_of TYPE(16 sword) = 2"
  "align_of TYPE(32 sword) = 4"
  "align_of TYPE(64 sword) = 8"
  by (auto simp: align_of_word)


instantiation ptr :: (type) c_type
begin
instance ..
end

overloading typ_info_ptr \<equiv> typ_info_t begin
definition typ_info_ptr :: "'a::c_type ptr itself \<Rightarrow> 'a::c_type ptr field_desc typ_desc" where
  typ_info_ptr:
  "typ_info_ptr (p::'a::c_type ptr itself) \<equiv> TypDesc
    (TypScalar (addr_bitsize div 8) addr_align \<lparr>
        field_access = \<lambda>p bs. rev (word_rsplit (ptr_val p)),
        field_update = \<lambda>bs v. Ptr (word_rcat (rev bs)::addr) \<rparr> )
    (typ_name_itself TYPE('a) @ ''+ptr'')"
end

overloading typ_name_itself_ptr \<equiv> typ_name_itself begin
definition typ_name_itself_ptr:
  "typ_name_itself_ptr (p::'b::c_type ptr itself) \<equiv>
    typ_name_itself TYPE('b) @ ''+ptr''"
end

overloading typ_name_itself_unit \<equiv> typ_name_itself begin
definition
  typ_name_itself_unit [simp]:
  "typ_name_itself_unit (p::unit itself) \<equiv> ''void''"
end

lemma align_of_ptr [simp]:
  "align_of (p::'a::c_type ptr itself) = 2 ^ addr_align"
  by (simp add: align_of_def typ_info_ptr)

instantiation ptr :: (c_type) mem_type
begin
instance
  apply (intro_classes)
    apply (auto simp: to_bytes_def from_bytes_def
                 length_word_rsplit_exp_size' word_size
                 word_rcat_rsplit size_of_def  addr_card
                 typ_info_ptr fd_cons_double_update_def
                 fd_cons_update_access_def fd_cons_access_update_def
                 fd_cons_length_def fd_cons_update_normalise_def field_norm_def
                 super_update_bs_def word_rsplit_rcat_size norm_bytes_def
                 fd_consistent_def fd_cons_def wf_lf_def
                 fd_cons_desc_def align_field_def)
  done
end

instantiation ptr :: (c_type) simple_mem_type
begin
instance
  apply intro_classes
  apply(clarsimp simp: typ_info_ptr typ_uinfo_t_def)
  done
end

lemma size_td_ptr [simp]:
  "size_td (typ_info_t TYPE('a::c_type ptr)) = addr_bitsize div 8"
  by (simp add: typ_info_ptr)

lemma size_of_ptr [simp]:
  "size_of TYPE('a::c_type ptr) = addr_bitsize div 8"
  by (simp add: size_of_def)

lemma align_td_ptr [simp]: "align_td (typ_info_t TYPE('a::c_type ptr)) = addr_align"
  by (simp add: typ_info_ptr)

lemma ptr_add_word32_signed [simp]:
  fixes a :: "32 word ptr"
  shows "ptr_val (a +\<^sub>p x) = ptr_val a + 4 * of_int x"
  by (cases a) (simp add: CTypesDefs.ptr_add_def scast_id)

lemma ptr_add_word32 [simp]:
  fixes a :: "32 word ptr"
  shows "ptr_val (a +\<^sub>p uint x) = ptr_val a + 4 * x"
  by (cases a) (simp add: ptr_add_def scast_id)

lemma ptr_add_word64_signed [simp]:
  fixes a :: "64 word ptr"
  shows "ptr_val (a +\<^sub>p x) = ptr_val a + 8 * of_int x"
  by (cases a) (simp add: CTypesDefs.ptr_add_def scast_id)

lemma ptr_add_word64 [simp]:
  fixes a :: "64 word ptr"
  shows "ptr_val (a +\<^sub>p uint x) = ptr_val a + 8 * x"
  by (cases a) (simp add: ptr_add_def scast_id)

lemma ptr_add_0_id[simp]:"x +\<^sub>p 0 = x"
  by (simp add:CTypesDefs.ptr_add_def)

lemma from_bytes_ptr_to_bytes_ptr:
  "from_bytes (to_bytes (v::addr_bitsize word) bs) = (Ptr v :: 'a::c_type ptr)"
  by (simp add: from_bytes_def to_bytes_def typ_info_ptr word_tag_def
                typ_info_word word_size
                length_word_rsplit_exp_size' word_rcat_rsplit)

lemma ptr_aligned_coerceI:
  "ptr_aligned (ptr_coerce x::addr ptr) \<Longrightarrow> ptr_aligned (x::'a::mem_type ptr ptr)"
  by (simp add: ptr_aligned_def)

lemma lift_ptr_ptr [simp]:
  "\<And>p::'a::mem_type ptr ptr.
  lift h (ptr_coerce p) = ptr_val (lift h p)"
  by (simp add: lift_def h_val_def from_bytes_def
                typ_info_word word_tag_def typ_info_ptr)

lemmas Vanilla32_tags [simp] =
  typ_info_word typ_info_ptr typ_name_itself_ptr word_tag_def
  typ_name_itself_word

lemma ptr_typ_name [simp]:
  "typ_name (typ_info_t TYPE(('a :: c_type) ptr)) =  typ_name_itself TYPE('a) @ ''+ptr'' "
  by simp

lemma word_typ_name [simp]:
  "typ_name (typ_info_t TYPE('a::len8 word)) = ''word'' @ nat_to_bin_string (len_of TYPE('a))"
  by simp

lemma typ_name_words [simp]:
   "typ_name (typ_uinfo_t TYPE(8 word))  = ''word00010''"
   "typ_name (typ_uinfo_t TYPE(16 word)) = ''word000010''"
   "typ_name (typ_uinfo_t TYPE(32 word)) = ''word0000010''"
   "typ_name (typ_uinfo_t TYPE(64 word)) = ''word00000010''"
   "typ_name (typ_info_t  TYPE(8 word))  = ''word00010''"
   "typ_name (typ_info_t  TYPE(16 word)) = ''word000010''"
   "typ_name (typ_info_t  TYPE(32 word)) = ''word0000010''"
   "typ_name (typ_info_t  TYPE(64 word)) = ''word00000010''"
  by (auto simp: typ_uinfo_t_def nat_to_bin_string.simps)

lemma typ_name_swords [simp]:
   "typ_name (typ_uinfo_t TYPE(8 sword))  = ''word00010''"
   "typ_name (typ_uinfo_t TYPE(16 sword)) = ''word000010''"
   "typ_name (typ_uinfo_t TYPE(32 sword)) = ''word0000010''"
   "typ_name (typ_uinfo_t TYPE(64 sword)) = ''word00000010''"
   "typ_name (typ_info_t  TYPE(8 sword))  = ''word00010''"
   "typ_name (typ_info_t  TYPE(16 sword)) = ''word000010''"
   "typ_name (typ_info_t  TYPE(32 sword)) = ''word0000010''"
   "typ_name (typ_info_t  TYPE(64 sword)) = ''word00000010''"
  by (auto simp: typ_uinfo_t_def nat_to_bin_string.simps)

lemma ptr_arith[simp]:
  "(x +\<^sub>p a = y +\<^sub>p a) = ((x::('a::c_type) ptr) = (y::'a ptr))"
  by (clarsimp simp:CTypesDefs.ptr_add_def)

lemma ptr_arith'[simp]:
  "(ptr_coerce (x +\<^sub>p a) = ptr_coerce (y +\<^sub>p a)) = ((x::('a::c_type) ptr) = (y::'a ptr))"
  by (clarsimp simp:CTypesDefs.ptr_add_def)

end
