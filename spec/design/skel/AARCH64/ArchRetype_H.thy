(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "Retyping Objects"

(* FIXME AARCH64: This file was copied *VERBATIM* from the RISCV64 version,
   with minimal text substitution! Remove this comment after updating,
   check copyright. *)
theory ArchRetype_H
imports
  ArchRetypeDecls_H
  ArchVSpaceDecls_H
  Hardware_H
  KI_Decls_H
  VCPU_H
begin

context Arch begin global_naming AARCH64_H

#INCLUDE_HASKELL SEL4/Object/ObjectType/AARCH64.hs CONTEXT AARCH64_H Arch.Types=ArchTypes_H ArchInv=ArchRetypeDecls_H NOT bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/AARCH64.hs CONTEXT AARCH64_H bodies_only \
  NOT isVSpaceFlushLabel isPageFlushLabel

end (* context AARCH64 *)
end
