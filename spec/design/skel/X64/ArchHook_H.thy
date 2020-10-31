(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)

chapter "ArchHook"

theory ArchHook_H
imports KernelStateData_H
begin

context Arch begin global_naming X64_H

definition
  cEntryHook :: "unit kernel"
where
  "cEntryHook\<equiv> return ()"

definition
  cExitHook :: "unit kernel"
where
  "cExitHook\<equiv> return ()"

end
end
