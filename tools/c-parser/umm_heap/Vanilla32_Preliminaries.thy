(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(* License: BSD, terms see file ./LICENSE *)

(* FIXME: rename this theory, it's not about 32 any more *)
theory Vanilla32_Preliminaries
imports CTypes
begin

section "Words and Pointers"

instantiation unit :: c_type
begin
instance ..
end

definition "unit_tag \<equiv> TypDesc (TypScalar 1 0
      (\<lparr> field_access = (\<lambda>v bs. [0]), field_update = (\<lambda>bs v. ())\<rparr>)) ''unit''"

declare unit_tag_def [simp]

overloading typ_info_unit \<equiv> typ_info_t begin
  definition typ_info_unit [simp]: "typ_info_unit (x::unit itself) \<equiv> unit_tag"
end

instantiation unit :: mem_type
begin
  definition
    to_bytes_unit :: "unit \<Rightarrow> byte list" where
    "to_bytes_unit a \<equiv> [0]"

  definition
    from_bytes_unit :: "byte list \<Rightarrow> unit" where
    "from_bytes_unit bs \<equiv> ()"

  definition
    size_of_unit :: "unit itself \<Rightarrow> nat" where
    "size_of_unit x \<equiv> 0"

  definition
    align_of_unit :: "unit itself \<Rightarrow> nat" where
    "align_of_unit x \<equiv> 1"

  instance
    apply intro_classes
    apply (auto simp: size_of_def align_of_def align_field_def addr_card
                      wf_lf_def fd_cons_desc_def
                      fd_cons_double_update_def fd_cons_update_access_def
                      fd_cons_access_update_def fd_cons_length_def)
  done
end

definition
  "bogus_log2lessthree (n::nat) ==
             if n = 128 then 4
             else if n = 64 then (3::nat)
             else if n = 32 then 2
             else if n = 16 then 1
             else if n = 8 then 0
             else undefined"
definition
  "len_exp (x::('a::len) itself) \<equiv> bogus_log2lessthree (len_of TYPE('a))"

lemma lx8' [simp] : "len_exp (x::8 itself) = 0"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx16' [simp]: "len_exp (x::16 itself) = 1"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx32' [simp]: "len_exp (x::32 itself) = 2"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx64' [simp]: "len_exp (x::64 itself) = 3"
by (simp add: len_exp_def bogus_log2lessthree_def)

lemma lx_signed' [simp]: "len_exp (x::('a::len) signed itself) = len_exp (TYPE('a))"
  by (simp add: len_exp_def)

(* Maybe not required, but keeps everything neat *)
class typ_num 

instantiation num0 and num1 :: typ_num
begin
instance ..
end

instantiation bit0 and bit1 :: (typ_num) typ_num
begin
instance ..
end

class signed_or_unsigned =  
  fixes signed_or_unsigned_as_str :: "'a itself \<Rightarrow> char list"

instantiation num0 :: signed_or_unsigned
begin

definition
  num0_signed_or_unsigned_def: "signed_or_unsigned_as_str (w :: num0 itself) = []" 

instance ..
end

instantiation num1 :: signed_or_unsigned
begin

definition
  num1_signed_or_unsigned_def: "signed_or_unsigned_as_str (w :: num1 itself) = []" 

instance ..
end

instantiation bit0 :: (type) signed_or_unsigned
begin

definition
  bit0_signed_or_unsigned_def: "signed_or_unsigned_as_str (w :: 'a bit0 itself) = []" 

instance ..
end

instantiation bit1 :: (type) signed_or_unsigned
begin

definition
  bit1_signed_or_unsigned_def: "signed_or_unsigned_as_str (w :: 'a bit1 itself) = []" 

instance ..
end

instantiation signed :: (type) signed_or_unsigned
begin

definition
  signed_signed_or_unsigned_def: "signed_or_unsigned_as_str (w :: 'a signed itself) = ''s''" 

instance ..
end

lemmas signed_or_unsigned = num0_signed_or_unsigned_def 
                            num1_signed_or_unsigned_def 
                            bit0_signed_or_unsigned_def 
                            bit1_signed_or_unsigned_def 
                            signed_signed_or_unsigned_def 

class len8 = signed_or_unsigned + len +
  (* this constraint gives us (in the most convoluted way possible) that we're only
     interested in words with a length that is divisible by 8 *)
  assumes len8_bytes: "len_of TYPE('a::len) = 8 * (2^len_exp TYPE('a))"
  (* len8_len class gives us that the words are \<le> than 128 bits.
     This is a wacky restriction really, but we're really only interested in words
     up to 64 bits, so who cares. *)
  assumes len8_width: "len_of TYPE('a::len) \<le> 128"
begin

lemma len8_size:
  "len_of TYPE('a) div 8 < addr_card"
  apply(subgoal_tac "len_of TYPE('a) \<le> 128")
   apply(simp add: addr_card)
  apply(rule len8_width)
  done

lemma len8_dv8:
  "8 dvd len_of TYPE('a)"
  by (simp add: len8_bytes)

lemma len8_pow:
  "\<exists>k. len_of TYPE('a) div 8 = 2^k"
  by (simp add: len8_bytes)

end

fun
  nat_to_bin_string :: "nat \<Rightarrow> char list"
  where
  ntbs: "nat_to_bin_string n = (if (n = 0) then ''0'' else (if n mod 2 = 1 then CHR ''1'' else CHR ''0'') # nat_to_bin_string (n div 2))"

declare nat_to_bin_string.simps [simp del]

lemma nat_to_bin_string_simps:
  "nat_to_bin_string 0 = ''0''"
  "n > 0 \<Longrightarrow> nat_to_bin_string n =
      (if n mod 2 = 1 then CHR ''1'' else CHR ''0'') # nat_to_bin_string (n div 2)"
  apply (induct n, auto simp: nat_to_bin_string.simps)
  done

instantiation word :: (len8) c_type
begin
instance ..
end

instance signed :: (len8) len8
  apply intro_classes
   apply (metis len8_bytes len_exp_def len_signed)
  apply (metis len8_width len_signed)
  done

end
