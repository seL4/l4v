(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Verification challenge by Norihisa Suzuki, posed in
 * "Automatic verification of programs with complex data structures", 1976.
 *)

theory Suzuki
imports
  "../../AutoCorres"
begin

install_C_file "suzuki.c"
autocorres [heap_abs_syntax] "suzuki.c"

context suzuki begin

thm suzuki_body_def
lemma
  "\<Gamma> \<turnstile>
     \<lbrace>distinct [\<acute>w, \<acute>x, \<acute>y, \<acute>z] \<and> (\<forall>p \<in> {\<acute>w, \<acute>x, \<acute>y, \<acute>z}. c_guard p)\<rbrace>
       Call suzuki_'proc
     \<lbrace>\<acute>ret__int = 4 (* Return value *)\<rbrace>"
  apply vcg
  oops

thm suzuki'_def
(* AutoCorres's heap abstraction makes the memory model much simpler. *)
lemma
  "\<lbrace>\<lambda>s. s = s0 \<and> distinct [w, x, y, z] \<and> (\<forall>p \<in> {w, x, y, z}. is_valid_node_C s p)\<rbrace>
     suzuki' w x y z
   \<lbrace>\<lambda>rv s. rv = 4 \<and> (* Return value *)
           (\<exists>w' x' y' z'. s = s0[w := w'][x := x'][y := y'][z := z']) (* Frame *)\<rbrace>!"
  apply (unfold suzuki'_def)
  apply wp
  (* Return value *)
  apply (clarsimp simp: fun_upd_apply)

  (* Frame rule *)
  (* FIXME: heap_abs_simps is still incomplete; need to unfold heap wrappers instead *)
  apply (clarsimp simp: suzuki.update_node_def suzuki.update_node_next_def suzuki.update_node_data_def
                        o_def fun_upd_apply)
  apply (blast intro: lifted_globals.fold_congs)
  done

end

end
