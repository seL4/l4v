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
context ARM begin

#INCLUDE_HASKELL SEL4/Object/ObjectType/ARM.lhs CONTEXT ARM Arch.Types=ArchTypes_H.ARM ArchInv=ArchRetypeDecls_H.ARM bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/ARM.lhs bodies_only CONTEXT ARM NOT isPDFlushLabel isPageFlushLabel

end
end
