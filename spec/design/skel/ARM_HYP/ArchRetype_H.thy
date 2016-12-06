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

theory ArchRetype_H
imports
  ArchRetypeDecls_H
  ArchVSpaceDecls_H
  Hardware_H
  "../KI_Decls_H"
begin
context Arch begin global_naming ARM_HYP_H

#INCLUDE_HASKELL SEL4/Object/ObjectType/ARM_HYP.lhs CONTEXT ARM_HYP_H Arch.Types= ArchInv= bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/ARM_HYP.lhs bodies_only CONTEXT ARM_HYP_H NOT isPDFlushLabel isPageFlushLabel

end
end
