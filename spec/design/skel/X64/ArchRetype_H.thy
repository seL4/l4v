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

context Arch begin global_naming X64_H

(* FIXME haskell-translator: VER-927 *)
defs setIOPortMask_def:
"setIOPortMask f l val \<equiv> (do
    ports \<leftarrow> gets (x64KSAllocatedIOPorts \<circ> ksArchState);
    ports' \<leftarrow> return $ ports aLU [(i,val). i \<leftarrow> [f .e. l]];
    modify (\<lambda> s. s \<lparr>
        ksArchState := (ksArchState s) \<lparr> x64KSAllocatedIOPorts := ports' \<rparr>\<rparr>)
od)"

#INCLUDE_HASKELL SEL4/Object/ObjectType/X64.lhs CONTEXT X64_H Arch.Types=ArchTypes_H ArchInv=ArchRetypeDecls_H NOT setIOPortMask bodies_only
#INCLUDE_HASKELL SEL4/API/Invocation/X64.lhs CONTEXT X64_H bodies_only

end (* context X64 *)
end
