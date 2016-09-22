(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory AutoLevity_Run
imports AutoLevity_Theory_Report
begin


ML \<open>
fun get_report thy =
let    

  val thy_nm = Context.theory_name thy;
  val _ = @{print} ("Reporting on " ^ thy_nm ^ "...")

  val trans = AutoLevity_Base.get_transactions ();

  val _ = if Symtab.defined trans (Context.theory_name thy) then () else raise Option; 

  val file_path = Path.append (Resources.master_directory thy) (Path.basic (thy_nm ^ ".lev"));

  val reports = AutoLevity_Theory_Report.get_reports_for_thy thy;
  val lines = AutoLevity_Theory_Report.string_reports_of reports;
    
  val _ = File.write_list file_path lines;
  
in () end handle Option => 
  ((@{print} ("No transaction record for " ^ (Context.theory_name thy)); ()))
\<close>
ML \<open>val theories = Thy_Info.get_names () |> map Thy_Info.get_theory\<close>

ML \<open>map get_report theories\<close>
end

