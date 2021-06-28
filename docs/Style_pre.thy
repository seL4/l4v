(*
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
*)

theory Style_pre
  imports Main
begin

text \<open>
This a helper theory for Style.thy.
\<close>

typedecl type_foo
typedecl type_bar

definition valid ::
  "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool" ("\<lbrace>_\<rbrace>/ _ /\<lbrace>_\<rbrace>")
  where
  "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> undefined"

definition
  pred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixl "and" 35)
  where
  "pred_conj P Q \<equiv> \<lambda>x. P x \<and> Q x"

end
