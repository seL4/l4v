(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Initialisation"

theory KI_Decls_H
imports
  ThreadDecls_H
  KernelInitMonad_H
begin

#INCLUDE_HASKELL SEL4/Kernel/Init.lhs decls_only NOT isAligned funArray newKernelState distinct rangesBy doKernelOp runInit

end
