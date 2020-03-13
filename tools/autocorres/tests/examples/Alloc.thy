(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Alloc
imports
  "AutoCorres.AutoCorres"
begin

external_file  "alloc.c"

(* Parse the input file. *)
install_C_file  "alloc.c"

(* Abstract the input file. *)
autocorres "alloc.c"

context alloc begin

(* Bodies of translated functions. *)
thm max'_def
thm align_up'_def
thm alloc'_def
thm dealloc'_def
thm add_mem_pool'_def
thm init_allocator'_def

end

end
