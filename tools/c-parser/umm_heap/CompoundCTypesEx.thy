(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
  Example C structure instantiation and related lemmas
*)

theory CompoundCTypesEx
imports CompoundCTypes
begin

record x_struct_ex =
  x_example :: "32 word"
  y_example :: "8 word"

definition x_struct_ex_tag :: "'a x_struct_ex_scheme typ_info" where
  "x_struct_ex_tag \<equiv> (
    final_pad \<circ>
    (ti_typ_pad_combine TYPE(8 word) y_example (y_example_update \<circ> (\<lambda>x _. x)) ''y_example'') \<circ>
    (ti_typ_pad_combine TYPE(32 word) x_example (x_example_update \<circ> (\<lambda>x _. x))  ''x_example''))
    (empty_typ_info ''x_struct_ex'')"

instantiation x_struct_ex_ext :: (type) c_type
begin
instance ..
end

overloading x_struct_ex_typ_tag \<equiv> typ_info_t begin
definition
x_struct_ex_typ_tag: "x_struct_ex_typ_tag (t::'a x_struct_ex_ext itself) \<equiv>
    (x_struct_ex_tag::'a x_struct_ex_scheme typ_info)"
end


lemma aggregate_x_struct_ex_tag [simp]:
  "aggregate x_struct_ex_tag"
  by (simp add: x_struct_ex_tag_def final_pad_def Let_def)

lemma
  "upd_local (x_example_update \<circ> (\<lambda>x _. x))"
apply(auto simp: upd_local_def )
apply(tactic {* Record.split_tac @{context} 1 *} )
apply simp
done

instantiation x_struct_ex_ext :: (unit_class) mem_type
begin
instance
apply intro_classes

apply(auto simp: x_struct_ex_typ_tag x_struct_ex_tag_def)

(* wf_desc *)
apply(fastforce intro: wf_desc_final_pad wf_desc_ti_typ_pad_combine)

(* wf_size_desc *)
apply(fastforce intro: wf_size_desc_ti_typ_pad_combine wf_size_desc_final_pad)

(* wf_lf *)
apply(fastforce intro: wf_lf_final_pad wf_lf_ti_typ_pad_combine
                      wf_desc_final_pad wf_desc_ti_typ_pad_combine
                      g_ind_ti_typ_pad_combine f_ind_ti_typ_pad_combine
                      fa_ind_ti_typ_pad_combine)

(* fu_eq_mask *)
apply(rule fu_eq_mask)
 apply(simp add: size_of_def  x_struct_ex_typ_tag x_struct_ex_tag_def)
apply(rule fu_eq_mask_final_pad)
apply(rule fu_eq_mask_ti_typ_pad_combine)+
apply(rule fu_eq_mask_empty_typ_info)
apply(simp add: there_is_only_one)
apply(fastforce simp: fg_cons_def intro: fc_ti_typ_pad_combine)+

(* align_of dvd size_of *)
apply(simp add: align_of_def size_of_def x_struct_ex_typ_tag
                x_struct_ex_tag_def)

(* align_field *)
apply(simp add: align_field_final_pad align_field_ti_typ_pad_combine)

(* max_size *)
apply(simp add: size_of_def x_struct_ex_typ_tag x_struct_ex_tag_def
                size_td_lt_final_pad size_td_lt_ti_typ_pad_combine
                size_td_lt_ti_typ_combine size_td_lt_ti_pad_combine padup_def
                addr_card align_of_final_pad align_of_def)
done
end

declare x_struct_ex_typ_tag [simp add]
declare x_struct_ex_tag_def [simp add]

lemma x_struct_ex_fnl [simp]:
  "field_names_list (x_struct_ex_tag::'a x_struct_ex_scheme typ_info) =
      [''x_example'',''y_example''] @
          padding_fields (x_struct_ex_tag::'a x_struct_ex_scheme typ_info)"
apply(clarsimp simp: field_names_list_def)
done


record y_struct_ex =
  x2_example :: "32 word ptr"
(*
  x3_example :: "32 word ptr"
  x4_example :: "32 word ptr"
  x5_example :: "32 word ptr"
  x6_example :: "32 word ptr"
  x7_example :: "32 word ptr"

  x12_example :: "32 word ptr"
  x13_example :: "32 word ptr"
  x14_example :: "32 word ptr"
  x15_example :: "32 word ptr"
  x16_example :: "32 word ptr"
  x17_example :: "32 word ptr"*)
  y2_example :: "x_struct_ex"

definition y_struct_ex_tag :: "'a y_struct_ex_scheme typ_info" where
  "y_struct_ex_tag \<equiv> (
    final_pad \<circ>
    (ti_typ_pad_combine TYPE(x_struct_ex) y2_example (y2_example_update \<circ> (\<lambda>x _. x)) ''y2_example'') \<circ>
    (ti_typ_pad_combine TYPE(32 word ptr) x2_example (x2_example_update \<circ> (\<lambda>x _. x))  ''x2_example'')
    )
    (empty_typ_info ''y_struct_ex'')"

instantiation y_struct_ex_ext :: (type) c_type
begin
instance ..
end

overloading y_struct_ex_typ_tag \<equiv> typ_info_t
begin
definition
y_struct_ex_typ_tag: "y_struct_ex_typ_tag (t::'a y_struct_ex_ext itself) \<equiv>
    (y_struct_ex_tag::'a y_struct_ex_scheme typ_info)"
end

instantiation y_struct_ex_ext :: (unit_class) mem_type
begin

instance
apply intro_classes

apply(auto simp: y_struct_ex_typ_tag y_struct_ex_tag_def align_of_def size_of_def)

(* wf_desc *)
apply(fastforce intro: wf_desc_final_pad wf_desc_ti_typ_pad_combine)

(* wf_size_desc *)
apply(fastforce intro: wf_size_desc_ti_typ_pad_combine wf_size_desc_final_pad)

(* wf_lf *)
apply(force intro: wf_lf_final_pad wf_lf_ti_typ_pad_combine
                      wf_desc_final_pad wf_desc_ti_typ_pad_combine
                      g_ind_ti_typ_pad_combine f_ind_ti_typ_pad_combine
                      fa_ind_ti_typ_pad_combine)

(* fu_eq_mask *)
apply(rule fu_eq_mask)
 apply(simp add: size_of_def  y_struct_ex_typ_tag y_struct_ex_tag_def)
apply(rule fu_eq_mask_final_pad)
apply(rule fu_eq_mask_ti_typ_pad_combine)+
apply(rule fu_eq_mask_empty_typ_info)
apply(simp add: there_is_only_one)
apply(fastforce simp: fg_cons_def intro: fc_ti_typ_pad_combine)+

(* align_field *)
apply(simp add: align_field_final_pad align_field_ti_typ_pad_combine)

(* max_size *)
apply(simp add: size_td_simps_1)
apply(simp add: size_td_simps_2 addr_card )
done

end

declare y_struct_ex_typ_tag [simp add]
declare y_struct_ex_tag_def [simp add]

lemma y_struct_ex_fnl [simp]:
  "field_names_list (y_struct_ex_tag::'a y_struct_ex_scheme typ_info) =
      [''x2_example'',''y2_example''] @
          padding_fields (y_struct_ex_tag::'a y_struct_ex_scheme typ_info)"
apply(clarsimp simp: field_names_list_def)
done

end
