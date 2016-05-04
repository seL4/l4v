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
  "./$L4V_ARCH/ArchRetypeDecls_H"
  "./$L4V_ARCH/ArchLabelFuns_H"
begin
requalify_types (in Arch)
  copy_register_sets irqcontrol_invocation
  invocation

#INCLUDE_HASKELL SEL4/API/Invocation.lhs Arch=Arch NOT InvocationLabel
#INCLUDE_HASKELL SEL4/API/InvocationLabels.lhs ONLY invocationType

context Arch begin
context begin global_naming global
requalify_types
  Invocations_H.invocation
end
end

end
