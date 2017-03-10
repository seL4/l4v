(*
 * Copyright 2016, Data61, CSIRO
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(DATA61_GPL)
 *)

(*
	Hypervisor code.
*)

theory Hypervisor_H
imports
  CNode_H
  "./$L4V_ARCH/ArchHypervisor_H"
  KernelInitMonad_H
begin

context begin interpretation Arch .
requalify_consts
  handleHypervisorFault
end

end
