(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(GD_GPL)
 *)


theory Setup_Locale
imports "../../../lib/Qualify" "../../../lib/Requalify"
begin

(* 
   We use a locale for namespacing architecture-specific definitions.
   An Arch locale is defined to precisely copy X64 so that we
   can open an architecture context in generic theories.

   Note that we always open X64 (as opposed to Arch) in X64-specific theories so that
   constants, facts and types are correctly under the "X64" namespace.

   We open Arch in generic theories when we want access to architecture-specific
   constants, facts and types but expect the block (begin ... end) 
   to be valid in all architectures.

*)

locale Arch


end
