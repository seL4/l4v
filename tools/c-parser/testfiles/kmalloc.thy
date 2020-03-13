(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory kmalloc
imports "CParser.CTranslation" "$L4V_ARCH/imports/MachineWords"
begin

(* no proof here, just testing the parser *)

consts
  KMC :: word32
  ptr_retyps :: "nat \<Rightarrow> machine_word \<Rightarrow> heap_typ_desc \<Rightarrow> heap_typ_desc"

external_file "kmalloc.c"
install_C_file "kmalloc.c"

context kmalloc begin

thm alloc_body_def
thm free_body_def

end

end
