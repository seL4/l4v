(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)
chapter \<open>Syntax\<close>
(*<*)
theory Syntax imports
  "CParser.CTranslation"
  "AutoCorres.AutoCorres"
begin
(*>*)

text \<open>
  To express properties about the execution of code, we introduce dedicated syntax to aid
  readability. This syntax is based on Hoare logic and used for stating the pre- and
  post-conditions of a function. The following describes a function @{term f} with pre-condition
  @{term P} and post-condition @{term Q}.

  @{term "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>"}

  By itself, this expression does not specify whether the function @{term f} terminates. We use a
  ``!'' to indicate non-failure, a property which subsumes termination of the function. Thus
  for the function above we would write the following to indicate the same and, in addition, that
  the function @{term f} does not fail.

  @{term "\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>!"}

  Throughout the following chapters we use an Isabelle tactic, wp, that performs weakest
  pre-condition reasoning over Hoare triples expressed this way. The tactic can take advantage of
  any previously proved lemmas tagged with the attribute ``[wp].'' Other Isabelle-specific notation
  will be introduced in the following chapters as it is used.
\<close>

(*<*)
end
(*>*)
