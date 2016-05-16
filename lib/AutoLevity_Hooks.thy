theory AutoLevity_Hooks
imports "AutoLevity_Theory_Report" (* AutoLevity_Base *)
begin
              
ML \<open>(AutoLevity_Base.setup_command_hook ()) : unit\<close>
setup \<open>AutoLevity_Theory_Report.setup_theory_hook\<close>

end
