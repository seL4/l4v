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
 * Tests for handling Spec constructs emitted by the C parser.
 *)
theory Test_Spec_Translation
imports "../../AutoCorres"
begin

install_C_file "../parse-tests/bodyless_function.c"

(* FIXME: move these *)
lemma abs_spec_may_not_modify_globals[heap_abs]:
  "abs_spec st \<top> {(a, b). meq b a} {(a, b). meq b a}"
  apply (clarsimp simp: abs_spec_def meq_def)
  done
(* TODO: also handle may_only_modify_globals specs. This will be more difficult *)

lemma corresTA_L2_spec[word_abs]:
  "(\<And>s t. abstract_val (Q s) (P s t) id (P' s t)) \<Longrightarrow>
   corresTA Q rx ex (L2_spec {(s, t). P s t}) (L2_spec {(s, t). P' s t})"
  apply (monad_eq simp: L2_defs corresXF_def in_liftE split: sum.splits)
  apply (erule exI)
  done

autocorres "../parse-tests/bodyless_function.c"

context bodyless_function begin
(* We don't know what this function does, but it's guaranteed to not modify the global state. *)
thm bodyless_body_def bodyless'_def

(* Check that our translation did honour the given spec. *)
lemma "\<lbrace>P\<rbrace> bodyless' \<lbrace>\<lambda>_. P\<rbrace>!"
  apply (simp add: bodyless'_def)
  apply (monad_eq simp: validNF_def valid_def no_fail_def meq_def)
  done
end

end
