(*
     Copyright 2022, Proofcraft Pty Ltd
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

consts my_function :: 'a
axiomatization where my_function_def: "my_function \<equiv> undefined"

definition ccorres :: "'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> bool" where
  "ccorres rrel xf P Q hs a c \<equiv> undefined"

definition c_guard :: "'h \<Rightarrow> 'i \<Rightarrow> 'd" ("\<lbrace> _ = _ \<rbrace>") where
  "\<lbrace> ptr = cond \<rbrace> \<equiv> undefined"

definition ptr_select :: "'h \<Rightarrow> 'h" ("\<acute>") where
  "ptr_select \<equiv> undefined"

end
