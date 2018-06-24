(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WhileLoopVarsPreserved imports
  "AutoCorres.AutoCorres"
begin

external_file "while_loop_vars_preserved.c"
install_C_file "while_loop_vars_preserved.c"

autocorres [ts_force nondet = loop] "while_loop_vars_preserved.c"

context while_loop_vars_preserved begin

lemma "\<lbrace> \<lambda>s. True \<rbrace> loop' var1 var2 var3 var4  \<lbrace> \<lambda>r s. r = var1 + var2 + var3 + var4 \<rbrace>"
  apply (unfold loop'_def)
  apply (subst whileLoop_add_inv [where I="\<lambda>(meow, woof, neigh, ii, squeek) s.
              ii = (var1 + var2 + var3 + var4 - (meow + woof + neigh + squeek))"
       and M="\<lambda>((meow, woof, neigh, ii, squeek), s).
                   unat meow + unat woof + unat neigh + unat squeek"])
  apply wp
  apply (auto simp: word_gt_0)
  done

end

end
