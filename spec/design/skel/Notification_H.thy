(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
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
