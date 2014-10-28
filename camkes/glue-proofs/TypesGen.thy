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
  "seL4_MessageInfo_set_label seL4_MessageInfo label' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C seL4_MessageInfo) 0) && 0xfff) || ((label' && 0xfffff) << 12)))"

definition
  seL4_MessageInfo_get_capsUnwrapped :: "seL4_MessageInfo_C \<Rightarrow> word32"
where
  "seL4_MessageInfo_get_capsUnwrapped x' = ((index (seL4_MessageInfo_C.words_C x') 0 && 0xe00) >> 9)"

definition
  seL4_MessageInfo_set_capsUnwrapped :: "seL4_MessageInfo_C \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_set_capsUnwrapped seL4_MessageInfo capsUnwrapped' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C seL4_MessageInfo) 0) && 0xfffff1ff) || ((capsUnwrapped' && 0x7) << 9)))"

definition
  seL4_MessageInfo_get_extraCaps :: "seL4_MessageInfo_C \<Rightarrow> word32"
where
  "seL4_MessageInfo_get_extraCaps x' = ((index (seL4_MessageInfo_C.words_C x') 0 && 0x180) >> 7)"

definition
  seL4_MessageInfo_set_extraCaps :: "seL4_MessageInfo_C \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_set_extraCaps seL4_MessageInfo extraCaps' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C seL4_MessageInfo) 0) && 0xfffffe7f) || ((extraCaps' && 0x3) << 7)))"

definition
  seL4_MessageInfo_get_length :: "seL4_MessageInfo_C \<Rightarrow> word32"
where
  "seL4_MessageInfo_get_length x' = (index (seL4_MessageInfo_C.words_C x') 0 && 0x7f)"

definition
  seL4_MessageInfo_set_length :: "seL4_MessageInfo_C \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_set_length seL4_MessageInfo length' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> ((index (seL4_MessageInfo_C.words_C seL4_MessageInfo) 0) && 0xffffff80) || (length' && 0x7f)))"

definition
  seL4_MessageInfo_new :: "word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> word32 \<Rightarrow> seL4_MessageInfo_C"
where
  "seL4_MessageInfo_new label' capsUnwrapped' extraCaps' length' = seL4_MessageInfo_C.seL4_MessageInfo_C (FCP (\<lambda>x''. case x'' of
    0 \<Rightarrow> (((label' && 0xfffff) << 12) || ((capsUnwrapped' && 0x7) << 9) || ((extraCaps' && 0x3) << 7) || (length' && 0x7f))))"

lemma seL4_MessageInfo_contents_eq: "seL4_MessageInfo_C.words_C x = seL4_MessageInfo_C.words_C y \<Longrightarrow> x = y"
  by (metis seL4_MessageInfo_C_idupdates(1))

lemma seL4_MessageInfo_wp[THEN validNF_make_schematic_post, simplified]:
  "\<forall>s. \<lbrace>\<lambda>s'. s = s'\<rbrace>
        seL4_MessageInfo_new' label' capsUnwrapped' extraCaps' length'
      \<lbrace>\<lambda>r s'. s = s' \<and> r = seL4_MessageInfo_new label' capsUnwrapped' extraCaps' length'\<rbrace>!"
  apply (rule allI)
  unfolding seL4_MessageInfo_new'_def seL4_MessageInfo_new_def apply wp
  apply clarsimp
  apply (rule seL4_MessageInfo_contents_eq)
  apply (clarsimp simp:cart_eq fcp_beta)
  apply word_bitwise
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
  unfolding seL4_MessageInfo_get_capsUnwrapped_def seL4_MessageInfo_get_extraCaps_def seL4_MessageInfo_get_length_def
  apply (word_bitwise, clarsimp)
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
  unfolding seL4_MessageInfo_get_label_def seL4_MessageInfo_get_extraCaps_def seL4_MessageInfo_get_length_def
  apply (word_bitwise, clarsimp)
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
  unfolding seL4_MessageInfo_get_label_def seL4_MessageInfo_get_capsUnwrapped_def seL4_MessageInfo_get_length_def
  apply (word_bitwise, clarsimp)
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
  unfolding seL4_MessageInfo_get_label_def seL4_MessageInfo_get_capsUnwrapped_def seL4_MessageInfo_get_extraCaps_def
  apply (word_bitwise, clarsimp)
  done

end

end
