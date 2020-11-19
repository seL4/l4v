(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Function Declarations for TCBs"

theory TCBDecls_H
imports FaultMonad_H Invocations_H
begin

context begin interpretation Arch .
requalify_types
  user_monad
end

#INCLUDE_HASKELL SEL4/Object/TCB.lhs decls_only NOT archThreadGet archThreadSet takeWhileM sort_key tcbEPFindIndex awaken

end
