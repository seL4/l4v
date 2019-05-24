(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory AutoLevity_Hooks
imports
  AutoLevity_Base
  AutoLevity_Theory_Report
begin

(*
 * This file installs the dependency tracing hooks so that they
 * will be active in the current Isabelle session. These are the
 * toplevel command hooks for tracing dependencies, and a shutdown
 * hook for writing out the dependencies when the session finishes.
 *)

(* Install toplevel command hooks. *)
setup \<open>
case getenv "AUTOLEVITY" of
  "1" => (tracing ("Setting up AUTOLEVITY=1");
          AutoLevity_Base.setup_command_hook {trace_apply = false})
| "2" => (tracing ("Setting up AUTOLEVITY=2");
          AutoLevity_Base.setup_command_hook {trace_apply = true})
| _ => I
\<close>

(* Collect all the traces and write them to a combined file. *)
ML \<open>
structure AutoLevity_Combined_Report = struct

(* Session-qualified theory name -> JSON ouput lines *)
fun levity_report_for thy_name: string list option =
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

(* This has the usual race condition, but should be very unlikely in practice *)
fun local_temp_file path = let
  val dir = Path.dir path;
  val file = Path.file_name path;
  fun try_path () = let
    (* avoid colliding with other processes *)
    val pid = Posix.ProcEnv.getpid () |> Posix.Process.pidToWord |> SysWord.toInt;
    (* timestamp *)
    val now = Time.now () |> Time.toMilliseconds;
    (* serialized pseudorandom state within this process *)
    val rand = Random.random_range 100000 999999;
    val temp_id = Library.space_implode "-" (map string_of_int [pid, now, rand]);
    val temp_path = Path.append dir (Path.basic (file ^ ".tmp" ^ temp_id));
    in if File.exists temp_path
       then
         ((* again, this should be very unlikely in practice *)
          warning ("local_temp_file: (unlikely) failed attempt: " ^
                   Path.implode temp_path);
          try_path ())
       else
         (File.append temp_path ""; (* create empty file *)
          temp_path)
    end;
  in try_path () end;

(* Output all traces in this session to given path.
   Wraps each theory in the session in a JSON dictionary as follows:

   {
     "session": <escaped session name>,
     "content": [
       <theory "foo" content>,
       <theory "bar" content>,
       ...
     ]
   }
*)
fun levity_report_all output_path: unit =
let
  val this_session = Session.get_name ();
  (* Use a temp file for atomic output. Note that we don't use
     File.tmp_path or similar because the standard /tmp/isabelle-*
     tmpdir might not be on the same file system as output_path,
     whereas we can only rename atomically on the same file system *)
  val temp_path = local_temp_file output_path;

  (* Wrap individual theory reports in a JSON dictionary as follows:

     {
       "theory": <escaped theory name>,
       "content": <theory content as JSON dictionary>
     }

     Note that this closes and re-opens the output file
     over and over. But it's better than building the entire
     combined output in memory. *)
  fun dump_all _ [] = ()
    | dump_all (first: bool) (thy_name::remaining) = let
        val _ = @{print} ("Reporting on " ^ thy_name ^ "...")
        val separator = if first then "" else ", "; (* from previous item *)
        val json_start = [separator, "{", quote "theory", ":", JSON_string_encode thy_name, ",\n",
                          quote "content", ":"];
        val json_end = ["}\n"];
        in case levity_report_for thy_name of
              NONE => (
                @{print} ("No transaction record for " ^ thy_name);
                dump_all first remaining
                )
            | SOME thy_report => (
                File.append_list temp_path (json_start @ thy_report @ json_end);
                dump_all false remaining
                )
        end;

  val thy_names = Thy_Info.get_names ();
  val _ = File.write_list temp_path
            ["{", quote "session", ":", JSON_string_encode this_session, ",\n",
             quote "content", ":", "[\n"];
  val _ = dump_all true thy_names;
  val _ = File.append_list temp_path ["]\n", "}"];
  val _ = OS.FileSys.rename {
            old = Path.implode (Path.expand temp_path),
            new = Path.implode (Path.expand output_path)
          };
in
    @{print} ("Report written to: " ^ Path.implode output_path);
    ()
end;

(* Wrapper that outputs to the Isabelle build log directory *)
fun levity_session_log () =
let
  val this_session = Session.get_name ();
  val fname = this_session ^ ".lev";
  val output_path = Path.make ["log", fname]
                    |> Path.append (Path.explode (getenv "ISABELLE_OUTPUT"));
  val session_traces = AutoLevity_Base.get_transactions ();
in
  if Symtab.is_empty session_traces
  (* AutoLevity does not collect traces for interactive PIDE sessions,
   * so don't overwrite the levity log *)
  then warning ("No traces for session: " ^ this_session)
  else levity_report_all output_path
end
handle exn =>
  (* from Pure/Tools/build.ML *)
  (List.app (fn msg => writeln (encode_lines (YXML.content_of msg)))
            (Runtime.exn_message_list exn);
   Exn.reraise exn);

end
\<close>

(* Do the output when the Isabelle session finishes.
   The session shutdown hook requires a patch to Isabelle, so we wrap
   this code to be a no-op on vanilla Isabelle installations. *)
ML \<open>
try (ML_Context.eval ML_Compiler.flags @{here})
    (ML_Lex.read_text ("Session.register_shutdown_hook AutoLevity_Combined_Report.levity_session_log", @{here}))
\<close>

end
