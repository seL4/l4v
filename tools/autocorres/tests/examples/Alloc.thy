(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Alloc
imports
  "../../AutoCorres"
begin

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
