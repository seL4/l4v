(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Title: Adaptation of example from HOL/Hoare/Separation
   Author: Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

chapter "Separation Algebra for Virtual Memory"

theory VM_Example
imports
  "../Sep_Tactics"
  "../Map_Extra"
begin

text {*
  Example instantiation of the abstract separation algebra to the sliced-memory
  model used for building a separation logic in ``Verification of Programs in
  Virtual Memory Using Separation Logic'' (PhD Thesis) by Rafal Kolanski.

  We wrap up the concept of physical and virtual pointers as well as value
  (usually a byte), and the page table root, into a datatype for instantiation.
  This avoids having to produce a hierarchy of type classes.

  The result is more general than the original. It does not mention the types
  of pointers or virtual memory addresses. Instead of supporting only
  singleton page table roots, we now support sets so we can identify a single
  0 for the monoid.
  This models multiple page tables in memory, whereas the original logic was
  only capable of one at a time.
*}

datatype ('p,'v,'value,'r) vm_sep_state
  = VMSepState "((('p \<times> 'v) \<rightharpoonup> 'value) \<times> 'r set)"

instantiation vm_sep_state :: (type, type, type, type) sep_algebra
begin

fun
  vm_heap :: "('a,'b,'c,'d) vm_sep_state \<Rightarrow> (('a \<times> 'b) \<rightharpoonup> 'c)" where
  "vm_heap (VMSepState (h,r)) = h"

fun
  vm_root :: "('a,'b,'c,'d) vm_sep_state \<Rightarrow> 'd set" where
  "vm_root (VMSepState (h,r)) = r"

definition
  sep_disj_vm_sep_state :: "('a, 'b, 'c, 'd) vm_sep_state
                            \<Rightarrow> ('a, 'b, 'c, 'd) vm_sep_state \<Rightarrow> bool" where
  "sep_disj_vm_sep_state x y = vm_heap x \<bottom> vm_heap y"

definition
  zero_vm_sep_state :: "('a, 'b, 'c, 'd) vm_sep_state" where
  "zero_vm_sep_state \<equiv> VMSepState (empty, {})"

fun
  plus_vm_sep_state :: "('a, 'b, 'c, 'd) vm_sep_state
                        \<Rightarrow> ('a, 'b, 'c, 'd) vm_sep_state
                        \<Rightarrow> ('a, 'b, 'c, 'd) vm_sep_state" where
  "plus_vm_sep_state (VMSepState (x,r)) (VMSepState (y,r'))
     = VMSepState (x ++ y, r \<union> r')"

instance
  apply intro_classes
        apply (simp add: zero_vm_sep_state_def sep_disj_vm_sep_state_def)
       apply (fastforce simp: sep_disj_vm_sep_state_def map_disj_def)
      apply (case_tac x, clarsimp simp: zero_vm_sep_state_def)
     apply (case_tac x, case_tac y)
     apply (fastforce simp: sep_disj_vm_sep_state_def map_add_ac)
    apply (case_tac x, case_tac y, case_tac z)
    apply (fastforce simp: sep_disj_vm_sep_state_def)
   apply (case_tac x, case_tac y, case_tac z)
   apply (fastforce simp: sep_disj_vm_sep_state_def map_add_disj)
  apply (case_tac x, case_tac y, case_tac z)
  apply (fastforce simp: sep_disj_vm_sep_state_def map_add_disj map_disj_com)
  done

end

end
