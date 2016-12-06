(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "Register Set"

theory RegisterSet_H
imports
  "../../../lib/HaskellLib_H"
  "../../machine/ARM_HYP/MachineTypes"
begin
context Arch begin global_naming ARM_HYP_H

definition
  newContext :: "register => machine_word"
where
 "newContext \<equiv> (K 0) aLU initContext"

end
end
