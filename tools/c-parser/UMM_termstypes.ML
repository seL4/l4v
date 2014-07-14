(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature UMM_TERMS_TYPES =
sig

  val typ_tag_ty : typ
  val mk_tag_type : typ -> typ
  val empty_tag_tm : typ -> string -> term
  val heap_desc_ty : typ
  val heap_raw_ty : typ
  val typ_name_ty : typ

  val mk_aux_guard_t : term
  val mk_aux_heap_desc_t : term
  val mk_auxupd_ty : typ -> typ

  val mk_hrs_htd_update_t : term
  val mk_hrs_mem_t : term
  val mk_hrs_htd_t : term
  val mk_hrs_mem_update_t : term

  val mk_ptr_safe : term -> term -> term

  val mk_field_lookup : typ * string -> term
  val mk_field_lookup_nofs : typ * string -> term
  val mk_fg_cons_tm : typ -> typ -> string -> theory -> term

  val mk_sizetd : term -> term
  val mk_aligntd : term -> term
  val mk_typ_info_tm : typ -> term
  val mk_typ_info_of : typ -> term
  val mk_typ_name_of : typ -> term
  val mk_td_names : term -> term
  val mk_sizeof : term -> term
  val mk_tag_pad_tm : typ -> typ -> string -> theory -> term
  val final_pad_tm : typ -> term


end

structure UMM_TermsTypes : UMM_TERMS_TYPES =
struct

open TermsTypes
fun field_desc_ty ty =
    Type(@{type_name "CTypesDefs.field_desc_ext"}, [ty, unit])

fun mk_typ_desc_ty ty = Type(@{type_name "CTypesDefs.typ_desc"}, [ty])
fun mk_tag_type ty = mk_typ_desc_ty (field_desc_ty ty)


val normalisor_ty = mk_list_type word8 --> mk_list_type word8
val typ_tag_ty = mk_typ_desc_ty normalisor_ty

val tag_rung_ty = bool
val heap_desc_ty = addr_ty --> (mk_prod_ty (bool,nat --> mk_option_ty (mk_prod_ty (typ_tag_ty,tag_rung_ty))))
val heap_raw_ty = mk_prod_ty (heap_ty, heap_desc_ty)


val mk_auxupd_val_ty =  mk_prod_ty (bool, heap_desc_ty --> heap_desc_ty)
fun mk_auxupd_ty ty = ty --> mk_auxupd_val_ty
val mk_aux_guard_t = Const(@{const_name "fst"}, mk_auxupd_val_ty --> bool)
val mk_aux_heap_desc_t = Const(@{const_name "snd"}, mk_auxupd_val_ty --> heap_desc_ty
    --> heap_desc_ty)

val mk_hrs_htd_update_t = @{const "HeapRawState.hrs_htd_update"}
val mk_hrs_mem_t = @{const "HeapRawState.hrs_mem"}
val mk_hrs_htd_t = @{const "HeapRawState.hrs_htd"}
val mk_hrs_mem_update_t = @{const "HeapRawState.hrs_mem_update"}

val typ_name_ty = string_ty

fun mk_typ_name_tm ty =
    Const("CTypesDefs.typ_name", mk_tag_type ty --> typ_name_ty)

fun empty_tag_tm ty nm =
    Const(@{const_name "empty_typ_info"}, string_ty --> mk_tag_type ty) $
    mk_string nm

fun final_pad_tm ty =
    Const(@{const_name "final_pad"}, mk_tag_type ty --> mk_tag_type ty)

fun field_access_tm recty ty nm thy = let
  val recname = case recty of Type(rn, []) => rn
                            | _ => raise Fail "field_access_tm: Record type \
                                              \looks unlikely"
  val access_ty = recty --> ty
  val fldnm = Sign.intern_const thy (recname ^ "." ^ nm)
in
  Const(fldnm, access_ty)
end

fun field_update_tm recty ty nm thy = let
  val recname = case recty of Type(rn, []) => rn
                            | _ => raise Fail "field_access_tm: Record type \
                                              \looks unlikely"
  fun tytr ty = ty --> ty
  val update_ty = ty --> tytr recty
  val field_update_ty = tytr ty --> tytr recty
  val fldnm = Sign.intern_const thy (recname ^ "." ^ nm)
  val field_update = Const (suffix Record.updateN fldnm,
      field_update_ty)
  val K_rec_ty = ty --> tytr ty
in
  Const(@{const_name "Fun.comp"}, field_update_ty --> K_rec_ty --> update_ty) $
       field_update $ K_rec ty
end


fun mk_tag_pad_tm recty ty nm thy = let
  fun tytr ty = ty --> ty
  val access_ty = recty --> ty
  val update_ty = ty --> tytr recty
  val tag_ty = mk_tag_type recty
  val tag_pad_combine = Const(@{const_name "CompoundCTypes.ti_typ_pad_combine"},
      mk_itself_type ty --> access_ty --> update_ty --> field_name_ty -->
      tytr tag_ty)
  val field_access = field_access_tm recty ty nm thy
  val field_update = field_update_tm recty ty nm thy
in
  tag_pad_combine $ mk_TYPE ty $ field_access $ field_update $ mk_string nm
end

fun mk_fg_cons_tm recty ty nm thy =
  Const(@{const_name "fg_cons"}, (recty --> ty) --> (ty --> recty --> recty)
      --> bool) $
      field_access_tm recty ty nm thy $
      field_update_tm recty ty nm thy

fun mk_td_names tm =
    Const(@{const_name "td_names"}, type_of tm --> mk_set_type string_ty) $ tm

fun mk_sizetd tm = let
  val ty = type_of tm
in
  Const(@{const_name "size_td"}, ty --> nat) $ tm
end

fun mk_aligntd tm = let
  val ty = type_of tm
in
  Const(@{const_name "align_td"}, ty --> nat) $ tm
end

fun mk_typ_info_tm ty =
    Const("CTypesDefs.typ_info_t", mk_itself_type ty --> mk_tag_type ty)

fun mk_typ_info_of ty = mk_typ_info_tm ty $ mk_TYPE ty

fun mk_field_lookup (ty,f) =
    Const(@{const_name "CTypesDefs.field_lookup"},
          mk_tag_type ty --> qualified_field_name_ty -->
          nat --> mk_option_ty (mk_prod_ty (mk_tag_type ty, nat))) $
    mk_typ_info_of ty $
    mk_list_cons (mk_string f, Free("fs", qualified_field_name_ty)) $
    Free("m", nat)

fun mk_field_lookup_nofs (ty,f) =
    Const(@{const_name "CTypesDefs.field_lookup"},
          mk_tag_type ty --> qualified_field_name_ty -->
          nat --> mk_option_ty (mk_prod_ty (mk_tag_type ty, nat))) $
    mk_typ_info_of ty $
    mk_list_singleton (mk_string f) $
    mk_nat_numeral 0

fun mk_typ_name_of ty = mk_typ_name_tm ty $ mk_typ_info_of ty

fun mk_ptr_safe t d = let
  val ptrty = type_of t
in
  Const(@{const_name "ptr_safe"}, ptrty --> heap_desc_ty --> bool) $ t $ d
end

end
