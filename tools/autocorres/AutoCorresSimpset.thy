(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory AutoCorresSimpset
imports SimplBucket
begin

(*
 * The simpset at the end of this file determines the
 * "full" simpset used internally within AutoCorres during
 * processing.
 *)

lemmas [simp del] =
  fun_upd_apply (* interferes with heap_lift *)
  ptr_coerce.simps ptr_add_0_id (* interferes with struct_rewrite *)
  word_neq_0_conv (* affects boolean expressions *)

end
