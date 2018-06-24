(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Swap
imports
  "AutoCorres.AutoCorres"
begin

external_file  "swap.c"

(* Parse the input file. *)
install_C_file  "swap.c"

(* Abstract the input file. *)
autocorres "swap.c"

context swap begin

(* Direct proof on the heap. *)
lemma
  fixes a :: "word32 ptr" and b :: "word32 ptr"
  shows
       "\<lbrace> \<lambda>s. is_valid_w32 s a \<and> heap_w32 s a = x
           \<and> is_valid_w32 s b \<and> heap_w32 s b = y \<rbrace>
           swap' a b
        \<lbrace> \<lambda>r s. heap_w32 s a = y \<and> heap_w32 s b = x \<rbrace>!"
  apply (unfold swap'_def)
  apply wp
  apply (auto simp: fun_upd_apply)
  done

end

end
