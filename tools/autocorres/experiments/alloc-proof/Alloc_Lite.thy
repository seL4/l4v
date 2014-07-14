(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Alloc_Lite
imports
  "../../AutoCorres"
begin

(* Parse the input file. *)
install_C_file  "alloc_lite.c"

(* Abstract the input file. *)
autocorres "alloc_lite.c"
print_theorems

(* Bodies of translated functions. *)
thm alloc_lite.max'_def
thm alloc_lite.align_up'_def
thm alloc_lite.ualloc'_def
thm alloc_lite.alloc'_def
thm alloc_lite.add_mem_pool'_def
thm alloc_lite.init_allocator'_def

end

end
