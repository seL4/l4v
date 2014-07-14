(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory AutoCorresAttributes
imports "~~/src/HOL/Main"
begin

ML_file "attributes.ML"

attribute_setup L1opt = {*
  Attrib.add_del
    (Thm.declaration_attribute L1PeepholeThms.add_thm)
    (Thm.declaration_attribute L1PeepholeThms.del_thm) *}
  "Peephole optimisations carried out after L1 SIMPL to monadic conversion."

attribute_setup L1unfold = {*
  Attrib.add_del
    (Thm.declaration_attribute L1UnfoldThms.add_thm)
    (Thm.declaration_attribute L1UnfoldThms.del_thm) *}
  "Definitions unfolded prior to L1 SIMPL to monadic conversion."

attribute_setup L1except = {*
  Attrib.add_del
    (Thm.declaration_attribute L1ExceptionThms.add_thm)
    (Thm.declaration_attribute L1ExceptionThms.del_thm) *}
  "Definitions used to rewrite control flow to reduce exception usage."

attribute_setup L2opt = {*
  Attrib.add_del
    (Thm.declaration_attribute L2PeepholeThms.add_thm)
    (Thm.declaration_attribute L2PeepholeThms.del_thm) *}
  "Peephole optimisations carried out after L2 monadic conversion."

attribute_setup L2unfold = {*
  Attrib.add_del
    (Thm.declaration_attribute L2UnfoldThms.add_thm)
    (Thm.declaration_attribute L2UnfoldThms.del_thm) *}
  "Definitions unfolded prior to L2 monadic conversion from L1."

attribute_setup heap_abs = {*
  Attrib.add_del
    (Thm.declaration_attribute HeapAbsThms.add_thm)
    (Thm.declaration_attribute HeapAbsThms.del_thm) *}
  "Heap abstraction rules."

attribute_setup heap_abs_fo = {*
  Attrib.add_del
    (Thm.declaration_attribute HeapAbsFOThms.add_thm)
    (Thm.declaration_attribute HeapAbsFOThms.del_thm) *}
  "First-order Heap abstraction rules."

attribute_setup word_abs = {*
  Attrib.add_del
    (Thm.declaration_attribute WordAbsThms.add_thm)
    (Thm.declaration_attribute WordAbsThms.del_thm) *}
  "Word abstraction rules."

attribute_setup polish = {*
  Attrib.add_del
    (Thm.declaration_attribute PolishSimps.add_thm)
    (Thm.declaration_attribute PolishSimps.del_thm) *}
  "Final simplification rules."

(* Set up the ts_rule attribute. *)
ML_file "monad_types.ML"
setup {*
 Attrib.setup (Binding.name "ts_rule") Monad_Types.ts_attrib
              "AutoCorres type strengthening rule"
*}

end
