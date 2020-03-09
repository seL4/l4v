(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Kmalloc
imports "AutoCorres.AutoCorres"
begin

external_file "kmalloc.c"

(* No proof here, just testing the parser. *)

consts
  KMC :: addr
  ptr_retyps :: "nat \<Rightarrow> addr \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"

install_C_file "kmalloc.c"
autocorres "kmalloc.c"

context kmalloc begin

(* C parser output. *)
thm alloc_body_def
thm sep_alloc_body_def
thm free_body_def
thm sep_free_body_def

(* Abstracted output. *)
thm alloc'_def
thm sep_alloc'_def
thm free'_def
thm sep_free'_def

end

end
