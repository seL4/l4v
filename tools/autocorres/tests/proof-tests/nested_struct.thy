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
 * Accessing nested structs.
 * Testcase for bug VER-321.
 *)
theory nested_struct imports "../../AutoCorres" begin

install_C_file "nested_struct.c"
autocorres "nested_struct.c"

context nested_struct begin

thm f'_def test'_def

lemma "\<lbrace> \<lambda>s. is_valid_point1_C s p1 \<and> is_valid_point2_C s p2 \<rbrace>
         test' p1 p2
       \<lbrace> \<lambda>_ s. num_C.n_C (point1_C.x_C (heap_point1_C s p1)) =
                 index (point2_C.n_C (heap_point2_C s p2)) 0 \<rbrace>!"
  unfolding test'_def f'_def
  apply wp
  apply (clarsimp simp: fun_upd_apply)
  done

thm g'_def

end

end