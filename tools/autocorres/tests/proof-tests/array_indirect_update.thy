(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
 * Regression for VER-320 and other array-related bugs.
 * Here we prove that writing a pointer that points into an array
 * will update the array.
 *)
theory array_indirect_update imports "AutoCorres.AutoCorres" begin

external_file "array_indirect_update.c"
install_C_file "array_indirect_update.c"
autocorres "array_indirect_update.c"

context array_indirect_update begin
thm foo'_def bar'_def

lemma
  "arr = (Ptr (symbol_table ''array'') :: 32 signed word ptr) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<forall>a\<in>set (array_addrs arr 10). is_valid_w32 s (ptr_coerce a) \<rbrace>
     bar'
   \<lbrace> \<lambda>_ s. heap_w32 s (ptr_coerce (arr +\<^sub>p 4)) = 3 \<rbrace>!"
  unfolding foo'_def bar'_def
  apply wp
  apply (clarsimp simp: set_array_addrs fun_upd_apply)
  apply (subgoal_tac "(4 :: nat) < 10")
   apply fastforce
  apply arith
  done

end
end
