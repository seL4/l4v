(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Function Declarations for Replies"

theory ReplyDecls_H

imports
  FaultMonad_H

begin

#INCLUDE_HASKELL SEL4/Object/Reply.lhs decls_only

end