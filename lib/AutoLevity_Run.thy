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
fun levity_dump_for thy_name: string list option =
let
  val thy = Thy_Info.get_theory thy_name;
  val thy_short_name = Context.theory_name thy;

  val trans = AutoLevity_Base.get_transactions ();
in if Symtab.defined trans thy_short_name then
     AutoLevity_Theory_Report.get_reports_for_thy thy
     |> AutoLevity_Theory_Report.string_reports_of
     |> SOME
   else
     NONE
end;

fun levity_dump_all output_path: unit =
let
  val this_session = Session.get_name ();
  val temp_path = File.tmp_path output_path;

  (* Wrap individual theory reports in JSON dictionaries
     indexed by session name and theory name.
     Note that this closes and re-opens the output file
     over and over. But it's better than building the entire
     combined output in memory. *)
  fun dump_all _ [] = ()
    | dump_all (first: bool) (thy_name::remaining) = let
        val _ = @{print} ("Reporting on " ^ thy_name ^ "...")
        val separator = if first then "" else ", "; (* from previous item *)
        val json_key = [separator ^ quote thy_name ^ ":"];
        in case levity_dump_for thy_name of
              NONE => (
                @{print} ("No transaction record for " ^ thy_name);
                dump_all first remaining
                )
            | SOME thy_report => (
                File.append_list temp_path (json_key @ thy_report);
                dump_all false remaining
                )
        end;

  val thy_names = Thy_Info.get_names ();
  val _ = File.write_list temp_path ["{\n", quote this_session ^ ":\n", "{\n"];
  val _ = dump_all true thy_names;
  val _ = File.append_list temp_path ["}\n", "}"];
  val _ = OS.FileSys.rename {
            old = Path.implode (Path.expand temp_path),
            new = Path.implode (Path.expand output_path)
          };
in
    @{print} ("Report written to: " ^ Path.implode output_path);
    ()
end;
\<close>

ML \<open>
let
  val this_session = Session.get_name ();
  val output_path = Path.basic (this_session ^ ".lev")
                    |> Path.append (Resources.master_directory @{theory})
in
  levity_dump_all output_path
end
\<close>

end
