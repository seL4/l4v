(*
 * Copyright 2014, General Dynamics C4 Systems
 *
 * SPDX-License-Identifier: GPL-2.0-only
 *)


theory Setup_Locale
imports "Lib.Qualify" "Lib.Requalify"
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
