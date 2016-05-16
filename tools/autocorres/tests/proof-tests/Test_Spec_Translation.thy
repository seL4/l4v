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

install_C_file "test_spec_translation.c"

autocorres [ts_rules = nondet] "test_spec_translation.c"

context test_spec_translation begin

(* Check that our translation did honour the given spec. *)
lemma validNF_spec[wp]:
  "\<lbrace>\<lambda>s. (\<exists>t. (s, t) \<in> f) \<and> (\<forall>t. (s, t) \<in> f \<longrightarrow> P () t)\<rbrace> spec f \<lbrace>P\<rbrace>!"
  by (clarsimp simp: validNF_def valid_def no_fail_def spec_def)

(* We don't know what this function does, but it's guaranteed to modify only "reg". *)
thm magic_body_def magic'_def

lemma magic'_wp:
  "\<lbrace>P\<rbrace> magic' x \<lbrace>\<lambda>_ s. \<exists>x. P (s\<lparr>reg_'' := x\<rparr>)\<rbrace>!"
  apply (unfold magic'_def)
  apply wp
  apply (fastforce simp: lifted_globals.splits)
  done

(* This function is annotated with an assertion. *)
thm call_magic_body_def call_magic'_def

lemma call_magic'_wp:
  "of_int x < (42 :: 32 signed word) \<Longrightarrow>
   \<lbrace>P\<rbrace> call_magic' x \<lbrace>\<lambda>_ s. \<exists>x. P (s\<lparr>reg_'' := x\<rparr>)\<rbrace>!"
  apply (unfold call_magic'_def)
  apply (wp magic'_wp)
  apply (fastforce simp: lifted_globals.splits)
  done

(* This function is guaranteed to fail. *)
thm abort_body_def abort'_def abort_spec_def

lemma abort'_spec:
  "abort' = fail"
  apply (simp add: abort'_def)
  done

end

end
