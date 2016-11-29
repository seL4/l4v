(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Fault Handlers"

theory FaultHandler_H
imports FaultHandlerDecls_H TCB_H
  "./$L4V_ARCH/ArchFaultHandler_H"
begin

context begin interpretation Arch .
requalify_consts
  syscallMessage
  fromVPtr
  exceptionMessage
  debugPrint
  makeArchFaultMessage
  handleArchFaultReply
end

#INCLUDE_HASKELL_PREPARSE SEL4/API/Failures.lhs

#INCLUDE_HASKELL SEL4/Kernel/FaultHandler.lhs bodies_only
#INCLUDE_HASKELL SEL4/API/Faults.lhs decls_only
#INCLUDE_HASKELL SEL4/API/Faults.lhs bodies_only

end
