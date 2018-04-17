(*
 *
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
theory Subseq_Abbreviation_Test

imports
  Subseq_Abbreviation
  "Monad_WP/NonDetMonad"

begin

experiment
  fixes a :: "(int, unit) nondet_monad"
    and b :: "int \<Rightarrow> (int, unit) nondet_monad"
    and c :: "(int, unit) nondet_monad"
begin

definition
  "test_foo z = do
    a; a;
    x \<leftarrow> b 2;
    x \<leftarrow> b z;
    a; a; a; a;
    x \<leftarrow> c;
    x \<leftarrow> a; a;
    return ()
  od"

subseq_abbreviation (input) foo_block bind
  "\<lambda>x. b x" "c" test_foo_def[simplified K_bind_def]
  reassoc: bind_assoc

end

end
