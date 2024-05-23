(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "The API"

theory API_H
imports Syscall_H Delete_H
begin

text \<open>collects all API modules\<close>

#INCLUDE_HASKELL SEL4.lhs decls_only NOT callKernel

#INCLUDE_HASKELL SEL4.lhs NOT kernelExitAssertions fastpathKernelAssertions

end
