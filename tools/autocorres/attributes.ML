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
 * Definition of various attributes.
 *
 * We define it early so that we can tag theorems that are defined prior to
 * the code that uses them.
 *)

structure L1UnfoldThms =
  Named_Thms (
    val name = Binding.name "L1unfold"
    val description = "Definitions unfolded prior to L1 SIMPL to monadic conversion."
    )

structure L1PeepholeThms =
  Named_Thms (
    val name = Binding.name "L1opt"
    val description = "Peephole optimisations carried out after L1 SIMPL to monadic conversion."
    )

structure L1ExceptionThms =
  Named_Thms (
    val name = Binding.name "L1exception"
    val description = "Exception control flow rewriting"
    )

structure L2UnfoldThms =
  Named_Thms (
    val name = Binding.name "L2unfold"
    val description = "Definitions unfolded prior to L2 monadic conversion from L1."
    )

structure L2PeepholeThms =
  Named_Thms (
    val name = Binding.name "L2peephole"
    val description = "Peephole optimisations carried out after L2 monadic conversion."
    )

structure HeapAbsThms =
  Named_Thms (
    val name = Binding.name "heap_abs"
    val description = "Heap Abstraction Rule"
    )

structure HeapAbsFOThms =
  Named_Thms (
    val name = Binding.name "heap_abs_fo"
    val description = "First-Order Heap Abstraction Rule"
    )

structure WordAbsThms =
  Named_Thms (
    val name = Binding.name "word_abs"
    val description = "Word Abstraction Rule"
    )

structure PolishSimps =
  Named_Thms (
    val name = Binding.name "polish"
    val description = "Final simplification rules."
    )
