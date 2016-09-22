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
imports "../../lib/Qualify" "../../lib/Requalify" "../../lib/Extend_Locale"
begin

(* 
   We use a locale for namespacing architecture-specific definitions.

   The global_naming command changes the underlying naming of the locale. The intention is that
   we liberally put everything into the "ARM" namespace, and then carefully unqualify (put into global namespace)
   or requalify (change qualifier to "Arch" instead of "ARM") in order to refer to entities in
   generic proofs.

*)

locale Arch

end
