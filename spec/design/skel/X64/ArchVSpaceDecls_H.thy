(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Retyping Objects"

theory ArchVSpaceDecls_H
imports ArchRetypeDecls_H "../InvocationLabels_H"
begin

context Arch begin global_naming X64_H

#INCLUDE_HASKELL_PREPARSE SEL4/Object/Structures.lhs CONTEXT X64_H
#INCLUDE_HASKELL_PREPARSE SEL4/API/InvocationLabels/X64.lhs CONTEXT X64
#INCLUDE_HASKELL SEL4/Kernel/VSpace/X64.lhs CONTEXT X64_H decls_only ArchInv=
#INCLUDE_HASKELL SEL4/Object/IOPort/X64.lhs CONTEXT X64_H decls_only ArchInv=

end (* context X64 *)

end
