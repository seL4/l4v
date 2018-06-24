(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
