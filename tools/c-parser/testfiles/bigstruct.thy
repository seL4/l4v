(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory bigstruct
imports "../CTranslation"
begin

declare sep_conj_ac [simp add]
thm size_td_simps

install_C_file "bigstruct.c"

(*
instance foo :: mem_type
apply intro_classes

prefer 4
apply(simp add: foo_tag_def)
apply clarify
apply(rule fu_eq_mask)
 apply(simp add: size_td_simps typ_info_array
     array_tag_def align_td_array_tag size_of_def)
apply(simp add: size_td_simps typ_info_array
     array_tag_def align_td_array_tag size_of_def)
apply(rule fu_eq_mask_final_pad)
apply(rule fu_eq_mask_ti_typ_pad_combine)+
apply(rule fu_eq_mask_empty_typ_info)
apply(simp add: there_is_only_one)
apply(fastforce simp: fg_cons_def comp_def intro: fc_ti_typ_pad_combine)+

*)

end
