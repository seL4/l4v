(*
 * Copyright Florian Haftmann
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section \<open>Syntax bundles for traditional infix syntax\<close>

theory Syntax_Bundles
  imports "HOL-Library.Word"
begin

bundle bit_projection_infix_syntax
begin

notation bit  (infixl \<open>!!\<close> 100)

end

end
