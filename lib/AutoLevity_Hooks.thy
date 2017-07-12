(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *
 *)

theory AutoLevity_Hooks
imports "AutoLevity_Base"
begin

setup \<open>
case getenv "AUTOLEVITY" of
  "1" => AutoLevity_Base.setup_command_hook {trace_apply = false}
| "2" => AutoLevity_Base.setup_command_hook {trace_apply = true}
| _ => I
\<close>

end
