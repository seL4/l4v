(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Function Declarations for CSpace"

theory CSpaceDecls_H
imports FaultMonad_H
begin

#INCLUDE_HASKELL SEL4/Kernel/CSpace.lhs decls_only

end
