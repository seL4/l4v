(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "Replies"

theory Reply_H

imports
  ReplyDecls_H

begin

#INCLUDE_HASKELL SEL4/Object/Reply.lhs bodies_only

end