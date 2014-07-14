(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* This is the "standard" instantiation of the MemoryModelExtras
   signature.

   Other implementations using the parser code may wish to 'use' a different
   file than this one.  The theory is that everything will "just work" as
   long as that file declares a structure MemoryModelExtras matching the
   signature.
*)

structure MemoryModelExtras : MEMORY_MODEL_EXTRAS =
struct

open TermsTypes UMM_TermsTypes
val extended_heap_ty = heap_raw_ty
fun check_safety {heap=h,ptrval} = let
  val heap_desc = mk_hrs_htd_t $ h
in
  (mk_ptr_safe ptrval heap_desc, safety_error)
end

fun dereference_ptr {heap,ptrval} = mk_lift(mk_hrs_mem_t $ heap,ptrval)

fun mk_heap_update_extended t = mk_hrs_mem_update_t $ t

fun mk_aux_guard t = mk_aux_guard_t $ t

fun mk_aux_update t = mk_hrs_htd_update_t $ (mk_aux_heap_desc_t $ t)

fun mk_aux_type ty = mk_auxupd_ty ty

val check_global_record_type = HeapStateType.hst_prove_globals

fun mk_lookup_proc_pair symtab naming addr = let
  val argTs = [fastype_of symtab, fastype_of naming, fastype_of addr]
  in (Const (@{const_name lookup_proc}, argTs ---> int)
        $ symtab $ naming $ addr,
    Const (@{const_name lookup_proc_safe}, argTs ---> HOLogic.boolT)
        $ symtab $ naming $ addr)
  end

structure UserTypeDeclChecking =
struct
  open UMM_Proofs
  type t = T
  type csenv = ProgramAnalysis.csenv
  val initial_state = umm_empty_state
  val finalise = umm_finalise
  fun struct_type _ {struct_type,state} thy =
      umm_struct_calculation (struct_type,state,thy)
  fun array_type _ {element_type, array_size, state} thy =
      umm_array_calculation element_type array_size state thy

end

end
