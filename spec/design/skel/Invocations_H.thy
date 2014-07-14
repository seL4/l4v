(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory Invocations_H
imports
  Structures_H
  ArchRetypeDecls_H
  InvocationLabels_H
begin

#INCLUDE_HASKELL SEL4/API/Invocation.lhs Arch=ArchRetypeDecls_H NOT InvocationLabel isPDFlush isPageFlush

end
