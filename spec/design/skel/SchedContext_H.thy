(*
 * Copyright 2018, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

chapter "SchedContexts"

theory SchedContext_H

imports
  SchedContextDecls_H
  TCBDecls_H
  ThreadDecls_H
  NotificationDecls_H
  ReplyDecls_H
  VSpace_H

begin

context begin interpretation Arch .
requalify_consts
  kernelWCETTicks
  kernelWCETUs
  ticksToUs
  maxTicksToUs
  getCurrentTime
end

#INCLUDE_HASKELL SEL4/Object/SchedContext.lhs bodies_only

end
