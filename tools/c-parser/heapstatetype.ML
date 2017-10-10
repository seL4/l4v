(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature HEAPSTATETYPE =
sig

  val hst_prove_globals : string -> theory -> theory
   (* string is the fully expanded name of the global record type *)

end

structure HeapStateType : HEAPSTATETYPE =
struct

open TermsTypes
open UMM_TermsTypes

fun hst_mem_lhs_t ty = Const(@{const_name "hst_mem"}, ty --> heap_ty)
fun hst_mem_rhs_t hrs ty =
    mk_comp_t (ty, heap_raw_ty, heap_ty) $ mk_hrs_mem_t $
              Const(hrs, ty --> heap_raw_ty)
fun hst_mem_update_lhs_t ty = Const(@{const_name "hst_mem_update"},
    (heap_ty --> heap_ty) --> ty --> ty)
fun hst_mem_update_rhs_t hrs ty =
    mk_comp_t (heap_ty --> heap_ty, heap_raw_ty --> heap_raw_ty, ty --> ty) $
              Const(hrs^"_update", (heap_raw_ty --> heap_raw_ty) --> ty --> ty) $ mk_hrs_mem_update_t


fun hst_htd_lhs_t ty = Const(@{const_name "hst_htd"}, ty --> heap_desc_ty)
fun hst_htd_rhs_t hrs ty =
    mk_comp_t (ty, heap_raw_ty, heap_desc_ty) $ mk_hrs_htd_t $
              Const(hrs, ty --> heap_raw_ty)
fun hst_htd_update_lhs_t ty = Const(@{const_name "hst_htd_update"},
    (heap_desc_ty --> heap_desc_ty) --> ty --> ty)
fun hst_htd_update_rhs_t hrs ty =
    mk_comp_t (heap_desc_ty --> heap_desc_ty, heap_raw_ty --> heap_raw_ty, ty --> ty) $
              Const(hrs^"_update", (heap_raw_ty --> heap_raw_ty) --> ty --> ty) $ mk_hrs_htd_update_t


fun hst_prove_globals fullrecname thy = let
  val recty = Type(fullrecname, [TVar(("'a",0), ["HOL.type"])])
  val hst'_instance_t =
      Logic.mk_of_class(recty, "SepFrame.heap_state_type'")
  val hst'_instance_ct = Thm.cterm_of (thy2ctxt thy) hst'_instance_t
  val is_hst'_thm =
      Goal.prove_internal (thy2ctxt thy) [] hst'_instance_ct
                          (fn _ => Class.intro_classes_tac (thy2ctxt thy) [])
  val thy = Axclass.add_arity is_hst'_thm thy
  val recty' =  Type(fullrecname, [alpha])
  val hrs = Sign.intern_const thy NameGeneration.global_heap_var
  val triples =
      [("hst_mem_",hst_mem_lhs_t,hst_mem_rhs_t),
       ("hst_mem_update",hst_mem_update_lhs_t,hst_mem_update_rhs_t),
       ("hst_htd_",hst_htd_lhs_t,hst_htd_rhs_t),
       ("hst_htd_update",hst_htd_update_lhs_t,hst_htd_update_rhs_t)]
  val defs = map (fn (n,l,r) =>
                     ((Binding.name (n ^ NameGeneration.global_rcd_name),
                       mk_defeqn(l recty', r hrs recty')),
                      []))
                 triples
  val (hst_thms, thy) = Global_Theory.add_defs true defs thy
  val thy' = thy |> Context.theory_map (Simplifier.map_ss (fn ss => ss addsimps hst_thms))
  val hst_instance_t =
      Logic.mk_of_class(recty, "SepFrame.heap_state_type")
  val hst_instance_ct = Thm.cterm_of (thy2ctxt thy') hst_instance_t
  val hst_thms = @{thms "hrs_simps"} @ [@{thm "split_def"}]
  val is_hst_thm =
      Goal.prove_internal (thy2ctxt thy')
          [] hst_instance_ct
          (fn _ =>
              Class.intro_classes_tac (thy2ctxt thy') [] THEN
              ALLGOALS (asm_full_simp_tac
                            (thy2ctxt thy' addsimps hst_thms)))
in
  Axclass.add_arity is_hst_thm thy'
end
end (* struct *)
