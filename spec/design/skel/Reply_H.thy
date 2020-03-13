(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Replies"

theory Reply_H

imports
  ReplyDecls_H

begin

#INCLUDE_HASKELL SEL4/Object/Reply.lhs bodies_only

end