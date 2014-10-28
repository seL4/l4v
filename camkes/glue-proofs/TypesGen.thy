(* Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

theory TypesGen imports
  "../../tools/c-parser/CTranslation"
  "../../tools/autocorres/AutoCorres"
begin

declare [[allow_underscore_idents=true]]

install_C_file "types_gen.c"

autocorres [ts_rules=nondet] "types_gen.c"

context types_gen
begin

(* The following definitions and proofs are auto-generated. *)

definition
  seL4_MessageInfo_get_label :: "seL4_MessageInfo_C \<Rightarrow> word32"
where
  "seL4_MessageInfo_get_label x' = ((index (seL4_MessageInfo_C.words_C x') 0 && 0xfffff000) >> 12)"

definition
  seL4_MessageInfo_set_label :: "seL4_MessageInfo_C \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_set_label y'' label' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C y'') 0) && 0xfff) || ((label' && 0xfffff) << 12)))"

definition
  seL4_MessageInfo_get_capsUnwrapped :: "seL4_MessageInfo_C \<Rightarrow> word32"
where
  "seL4_MessageInfo_get_capsUnwrapped x' = ((index (seL4_MessageInfo_C.words_C x') 0 && 0xe00) >> 9)"

definition
  seL4_MessageInfo_set_capsUnwrapped :: "seL4_MessageInfo_C \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_set_capsUnwrapped y'' capsUnwrapped' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C y'') 0) && 0xfffff1ff) || ((capsUnwrapped' && 0x7) << 9)))"

definition
  seL4_MessageInfo_get_extraCaps :: "seL4_MessageInfo_C \<Rightarrow> word32"
where
  "seL4_MessageInfo_get_extraCaps x' = ((index (seL4_MessageInfo_C.words_C x') 0 && 0x180) >> 7)"

definition
  seL4_MessageInfo_set_extraCaps :: "seL4_MessageInfo_C \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_set_extraCaps y'' extraCaps' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C y'') 0) && 0xfffffe7f) || ((extraCaps' && 0x3) << 7)))"

definition
  seL4_MessageInfo_get_length :: "seL4_MessageInfo_C \<Rightarrow> word32"
where
  "seL4_MessageInfo_get_length x' = (index (seL4_MessageInfo_C.words_C x') 0 && 0x7f)"

definition
  seL4_MessageInfo_set_length :: "seL4_MessageInfo_C \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_set_length y'' length' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C y'') 0) && 0xffffff80) || (length' && 0x7f)))"

definition
  seL4_MessageInfo_new :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_new label' capsUnwrapped' extraCaps' length' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> (((label' && 0xfffff) << 12) || ((capsUnwrapped' && 0x7) << 9) || ((extraCaps' && 0x3) << 7) || (length' && 0x7f))))"


definition
  seL4_CapData_Badge_get_Badge :: "seL4_CapData_C \<Rightarrow> word32"
where
  "seL4_CapData_Badge_get_Badge x' = (index (seL4_CapData_C.words_C x') 0 && 0xfffffff)"

definition
  seL4_CapData_Badge_set_Badge :: "seL4_CapData_C \<Rightarrow> word32 \<Rightarrow> seL4_CapData_C"
where
  "seL4_CapData_Badge_set_Badge y'' Badge' = seL4_CapData_C.seL4_CapData_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_CapData_C.words_C y'') 0) && 0xf0000000) || (Badge' && 0xfffffff)))"

definition
  seL4_CapData_Badge_new :: "word32 \<Rightarrow> seL4_CapData_C"
where
  "seL4_CapData_Badge_new Badge' = seL4_CapData_C.seL4_CapData_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((((scast seL4_CapData_Badge) && 0x1) << 31) || (Badge' && 0xfffffff))))"


definition
  seL4_CapData_Guard_get_GuardBits :: "seL4_CapData_C \<Rightarrow> word32"
where
  "seL4_CapData_Guard_get_GuardBits x' = ((index (seL4_CapData_C.words_C x') 0 && 0x3ffff00) >> 8)"

definition
  seL4_CapData_Guard_set_GuardBits :: "seL4_CapData_C \<Rightarrow> word32 \<Rightarrow> seL4_CapData_C"
where
  "seL4_CapData_Guard_set_GuardBits y'' GuardBits' = seL4_CapData_C.seL4_CapData_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_CapData_C.words_C y'') 0) && 0xfc0000ff) || ((GuardBits' && 0x3ffff) << 8)))"

definition
  seL4_CapData_Guard_get_GuardSize :: "seL4_CapData_C \<Rightarrow> word32"
where
  "seL4_CapData_Guard_get_GuardSize x' = ((index (seL4_CapData_C.words_C x') 0 && 0xf8) >> 3)"

definition
  seL4_CapData_Guard_set_GuardSize :: "seL4_CapData_C \<Rightarrow> word32 \<Rightarrow> seL4_CapData_C"
where
  "seL4_CapData_Guard_set_GuardSize y'' GuardSize' = seL4_CapData_C.seL4_CapData_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_CapData_C.words_C y'') 0) && 0xffffff07) || ((GuardSize' && 0x1f) << 3)))"

definition
  seL4_CapData_Guard_new :: "word32 \<Rightarrow> word32 \<Rightarrow> seL4_CapData_C"
where
  "seL4_CapData_Guard_new GuardBits' GuardSize' = seL4_CapData_C.seL4_CapData_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((((scast seL4_CapData_Guard) && 0x1) << 31) || ((GuardBits' && 0x3ffff) << 8) || ((GuardSize' && 0x1f) << 3))))"


lemma seL4_MessageInfo_contents_eq: "seL4_MessageInfo_C.words_C x = seL4_MessageInfo_C.words_C y \<Longrightarrow> x = y"
  by (metis seL4_MessageInfo_C_idupdates(1))


lemma seL4_MessageInfo_new_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s'\<rbrace>
        seL4_MessageInfo_new' label' capsUnwrapped' extraCaps' length'
      \<lbrace>\<lambda>r s'. s = s' \<and> r = seL4_MessageInfo_new label' capsUnwrapped' extraCaps' length'\<rbrace>!"
  apply (rule allI)
  unfolding seL4_MessageInfo_new'_def seL4_MessageInfo_new_def apply wp
  apply clarsimp
  apply (rule seL4_MessageInfo_contents_eq)
  apply (clarsimp simp:cart_eq fcp_beta)
  apply word_bitwise?
  done

lemma seL4_MessageInfo_set_label_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s' \<and>
             label' && 0xfffff = label'\<rbrace>
         seL4_MessageInfo_set_label' x'' label'
       \<lbrace>\<lambda>r'' s'. s = s' \<and>
                 seL4_MessageInfo_get_capsUnwrapped r'' = seL4_MessageInfo_get_capsUnwrapped x'' \<and>
                 seL4_MessageInfo_get_extraCaps r'' = seL4_MessageInfo_get_extraCaps x'' \<and>
                 seL4_MessageInfo_get_length r'' = seL4_MessageInfo_get_length x''\<rbrace>!"
  apply (rule allI)
  unfolding seL4_MessageInfo_set_label'_def apply wp
  unfolding seL4_MessageInfo_get_capsUnwrapped_def seL4_MessageInfo_get_extraCaps_def seL4_MessageInfo_get_length_def apply (word_bitwise, clarsimp)
  done

lemma seL4_MessageInfo_set_capsUnwrapped_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s' \<and>
             capsUnwrapped' && 0x7 = capsUnwrapped'\<rbrace>
         seL4_MessageInfo_set_capsUnwrapped' x'' capsUnwrapped'
       \<lbrace>\<lambda>r'' s'. s = s' \<and>
                 seL4_MessageInfo_get_label r'' = seL4_MessageInfo_get_label x'' \<and>
                 seL4_MessageInfo_get_extraCaps r'' = seL4_MessageInfo_get_extraCaps x'' \<and>
                 seL4_MessageInfo_get_length r'' = seL4_MessageInfo_get_length x''\<rbrace>!"
  apply (rule allI)
  unfolding seL4_MessageInfo_set_capsUnwrapped'_def apply wp
  unfolding seL4_MessageInfo_get_label_def seL4_MessageInfo_get_extraCaps_def seL4_MessageInfo_get_length_def apply (word_bitwise, clarsimp)
  done

lemma seL4_MessageInfo_set_extraCaps_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s' \<and>
             extraCaps' && 0x3 = extraCaps'\<rbrace>
         seL4_MessageInfo_set_extraCaps' x'' extraCaps'
       \<lbrace>\<lambda>r'' s'. s = s' \<and>
                 seL4_MessageInfo_get_label r'' = seL4_MessageInfo_get_label x'' \<and>
                 seL4_MessageInfo_get_capsUnwrapped r'' = seL4_MessageInfo_get_capsUnwrapped x'' \<and>
                 seL4_MessageInfo_get_length r'' = seL4_MessageInfo_get_length x''\<rbrace>!"
  apply (rule allI)
  unfolding seL4_MessageInfo_set_extraCaps'_def apply wp
  unfolding seL4_MessageInfo_get_label_def seL4_MessageInfo_get_capsUnwrapped_def seL4_MessageInfo_get_length_def apply (word_bitwise, clarsimp)
  done

lemma seL4_MessageInfo_set_length_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s' \<and>
             length' && 0x7f = length'\<rbrace>
         seL4_MessageInfo_set_length' x'' length'
       \<lbrace>\<lambda>r'' s'. s = s' \<and>
                 seL4_MessageInfo_get_label r'' = seL4_MessageInfo_get_label x'' \<and>
                 seL4_MessageInfo_get_capsUnwrapped r'' = seL4_MessageInfo_get_capsUnwrapped x'' \<and>
                 seL4_MessageInfo_get_extraCaps r'' = seL4_MessageInfo_get_extraCaps x''\<rbrace>!"
  apply (rule allI)
  unfolding seL4_MessageInfo_set_length'_def apply wp
  unfolding seL4_MessageInfo_get_label_def seL4_MessageInfo_get_capsUnwrapped_def seL4_MessageInfo_get_extraCaps_def apply (word_bitwise, clarsimp)
  done


lemma seL4_CapData_contents_eq: "seL4_CapData_C.words_C x = seL4_CapData_C.words_C y \<Longrightarrow> x = y"
  by (metis seL4_CapData_C_idupdates(1))


lemma seL4_CapData_Badge_new_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s'\<rbrace>
        seL4_CapData_Badge_new' Badge'
      \<lbrace>\<lambda>r s'. s = s' \<and> r = seL4_CapData_Badge_new Badge'\<rbrace>!"
  apply (rule allI)
  unfolding seL4_CapData_Badge_new'_def seL4_CapData_Badge_new_def seL4_CapData_Badge_def apply wp
  apply clarsimp
  apply (rule seL4_CapData_contents_eq)
  apply (clarsimp simp:cart_eq fcp_beta)
  apply word_bitwise?
  done

lemma seL4_CapData_Badge_set_Badge_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s' \<and>
             Badge' && 0xfffffff = Badge'\<rbrace>
         seL4_CapData_Badge_set_Badge' x'' Badge'
       \<lbrace>\<lambda>r'' s'. s = s'\<rbrace>!"
  apply (rule allI)
  unfolding seL4_CapData_Badge_set_Badge'_def apply wp
  apply (word_bitwise, clarsimp)
  done


lemma seL4_CapData_Guard_new_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s'\<rbrace>
        seL4_CapData_Guard_new' GuardBits' GuardSize'
      \<lbrace>\<lambda>r s'. s = s' \<and> r = seL4_CapData_Guard_new GuardBits' GuardSize'\<rbrace>!"
  apply (rule allI)
  unfolding seL4_CapData_Guard_new'_def seL4_CapData_Guard_new_def seL4_CapData_Guard_def apply wp
  apply clarsimp
  apply (rule seL4_CapData_contents_eq)
  apply (clarsimp simp:cart_eq fcp_beta)
  apply word_bitwise?
  done

lemma seL4_CapData_Guard_set_GuardBits_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s' \<and>
             GuardBits' && 0x3ffff = GuardBits'\<rbrace>
         seL4_CapData_Guard_set_GuardBits' x'' GuardBits'
       \<lbrace>\<lambda>r'' s'. s = s' \<and>
                 seL4_CapData_Guard_get_GuardSize r'' = seL4_CapData_Guard_get_GuardSize x''\<rbrace>!"
  apply (rule allI)
  unfolding seL4_CapData_Guard_set_GuardBits'_def apply wp
  unfolding seL4_CapData_Guard_get_GuardSize_def apply (word_bitwise, clarsimp)
  done

lemma seL4_CapData_Guard_set_GuardSize_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s' \<and>
             GuardSize' && 0x1f = GuardSize'\<rbrace>
         seL4_CapData_Guard_set_GuardSize' x'' GuardSize'
       \<lbrace>\<lambda>r'' s'. s = s' \<and>
                 seL4_CapData_Guard_get_GuardBits r'' = seL4_CapData_Guard_get_GuardBits x''\<rbrace>!"
  apply (rule allI)
  unfolding seL4_CapData_Guard_set_GuardSize'_def apply wp
  unfolding seL4_CapData_Guard_get_GuardBits_def apply (word_bitwise, clarsimp)
  done

end
end
