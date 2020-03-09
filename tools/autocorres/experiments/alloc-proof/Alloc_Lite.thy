(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Alloc_Lite
imports
  "AutoCorres.AutoCorres"
begin

external_file  "alloc_lite.c"

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
