(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

theory ArchTCB_H
imports "../TCBDecls_H"
begin
context ARM begin

#INCLUDE_HASKELL SEL4/Object/TCB/ARM.lhs CONTEXT ARM

end
end
