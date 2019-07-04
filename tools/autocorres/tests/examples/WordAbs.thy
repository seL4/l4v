(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory WordAbs
imports "AutoCorres.AutoCorres"
begin

external_file "word_abs.c"
install_C_file "word_abs.c"
autocorres
  [ (*signed_word_abs =
        S_and_S S_or_S S_xor_S not_S
        U_shiftl_U_abs_S U_shiftr_U_abs_S U_shiftl_S_abs_S U_shiftr_S_abs_S
        S_shiftl_U_abs_S S_shiftr_U_abs_S S_shiftl_S_abs_S S_shiftr_S_abs_S
        U_shiftl_U_abs_US U_shiftr_U_abs_US U_shiftl_S_abs_US U_shiftr_S_abs_US
        S_shiftl_U_abs_US S_shiftr_U_abs_US S_shiftl_S_abs_US S_shiftr_S_abs_US
  ,*) no_signed_word_abs =
        U_shiftl_U_no_abs U_shiftr_U_no_abs U_shiftl_S_no_abs U_shiftr_S_no_abs
        S_shiftl_U_no_abs S_shiftr_U_no_abs S_shiftl_S_no_abs S_shiftr_S_no_abs
        U_shiftl_U_abs_U U_shiftr_U_abs_U U_shiftl_S_abs_U U_shiftr_S_abs_U
        S_shiftl_U_abs_U S_shiftr_U_abs_U S_shiftl_S_abs_U S_shiftr_S_abs_U
  , unsigned_word_abs =
        ver366
        U_and_U U_or_U U_xor_U not_U
        U_shiftl_U_abs_U U_shiftr_U_abs_U U_shiftl_S_abs_U U_shiftr_S_abs_U
        S_shiftl_U_abs_U S_shiftr_U_abs_U S_shiftl_S_abs_U S_shiftr_S_abs_U
        U_shiftl_U_abs_US U_shiftr_U_abs_US U_shiftl_S_abs_US U_shiftr_S_abs_US
        S_shiftl_U_abs_US S_shiftr_U_abs_US S_shiftl_S_abs_US S_shiftr_S_abs_US
  , ts_rules = nondet
] "word_abs.c"

context word_abs begin

lemma "\<lbrace> P \<rbrace> ver366' 0 \<lbrace> \<lambda>v s. v = 0 \<and> P s \<rbrace>"
  by (wpsimp simp: ver366'_def)
lemma "\<lbrace> P \<rbrace> ver366' UINT_MAX \<lbrace> \<lambda>v s. v = UINT_MAX-1 \<and> P s \<rbrace>"
  by (wpsimp simp: ver366'_def UINT_MAX_def)

thm
        S_and_S'_def S_or_S'_def S_xor_S'_def not_S'_def
        U_and_U'_def U_or_U'_def U_xor_U'_def not_U'_def
thm
        U_shiftl_U_abs_US'_def U_shiftr_U_abs_US'_def U_shiftl_S_abs_US'_def U_shiftr_S_abs_US'_def
        S_shiftl_U_abs_US'_def S_shiftr_U_abs_US'_def S_shiftl_S_abs_US'_def S_shiftr_S_abs_US'_def
thm
        U_shiftl_U_abs_U'_def U_shiftr_U_abs_U'_def U_shiftl_S_abs_U'_def U_shiftr_S_abs_U'_def
        S_shiftl_U_abs_U'_def S_shiftr_U_abs_U'_def S_shiftl_S_abs_U'_def S_shiftr_S_abs_U'_def
thm
        U_shiftl_U_abs_S'_def U_shiftr_U_abs_S'_def U_shiftl_S_abs_S'_def U_shiftr_S_abs_S'_def
        S_shiftl_U_abs_S'_def S_shiftr_U_abs_S'_def S_shiftl_S_abs_S'_def S_shiftr_S_abs_S'_def
thm
        U_shiftl_U_no_abs'_def U_shiftr_U_no_abs'_def U_shiftl_S_no_abs'_def U_shiftr_S_no_abs'_def
        S_shiftl_U_no_abs'_def S_shiftr_U_no_abs'_def S_shiftl_S_no_abs'_def S_shiftr_S_no_abs'_def

end

end
