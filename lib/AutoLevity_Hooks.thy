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
