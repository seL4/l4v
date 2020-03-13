(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory global_array_update imports "AutoCorres.AutoCorres" begin

external_file "global_array_update.c"
install_C_file "global_array_update.c"
autocorres "global_array_update.c"

context global_array_update begin
thm bar'_def bar2'_def

lemma "\<lbrace> \<lambda>s. \<forall>a\<in>set (array_addrs (Ptr (symbol_table ''foo'')
                                   :: 32 signed word ptr) 1024).
               is_valid_w32 s (ptr_coerce a) \<rbrace>
          bar'
       \<lbrace> \<lambda>_ s. heap_w32 s (ptr_coerce (Ptr (symbol_table ''foo'') +\<^sub>p 3
                                        :: 32 signed word ptr)) = 42 \<rbrace>!"
  unfolding bar'_def
  apply wp
  apply (clarsimp simp: set_array_addrs fun_upd_apply)
  done

end

end
