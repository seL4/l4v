(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)

chapter "The API"

theory API_H
imports Syscall_H Delete_H
begin

text {* collects all API modules *}

#INCLUDE_HASKELL SEL4.lhs

end
