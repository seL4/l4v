(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Notifications"

theory Notification_H imports    "NotificationDecls_H"
    "TCB_H"
  TCB_H
  ThreadDecls_H
  CSpaceDecls_H
  ObjectInstances_H
begin

context begin interpretation Arch .
requalify_consts
  badgeRegister
end

#INCLUDE_HASKELL SEL4/Object/Notification.lhs bodies_only

end
