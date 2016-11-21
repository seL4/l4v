(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "ArchHook"

theory ArchHook_H
imports "../KernelStateData_H"
    begin
    context Arch begin global_naming ARM

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
