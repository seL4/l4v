text \<open>
  In addition to named theorems, AutoCorres also stores definitions,
  theorems and other data in ML data structures.
  These can be useful for writing tools to process the AutoCorres output.

  See also: TraceDemo
\<close>
theory FunctionInfoDemo imports
  "../../AutoCorres"
begin

text \<open>Process a source file to populate our data structures.\<close>
install_C_file "function_info.c"
autocorres "function_info.c"
context function_info begin

section \<open>Function info\<close>
text \<open>
  Information about all AutoCorres-processed functions is stored in the
  AutoCorresFunctionInfo structure.
\<close>
ML \<open>
  val fn_info: FunctionInfo.fn_info =
      the (Symtab.lookup (AutoCorresFunctionInfo.get @{theory}) "function_info.c")
\<close>
  
text \<open>
  One FunctionInfo.fn_info structure is generated for each translated file.
  See the FunctionInfo structure for details about the stored data.
  As a start, we can show all function definitions:
\<close>
ML \<open>
  FunctionInfo.get_functions fn_info |> Symtab.dest |> map snd
  |> app (fn f => writeln ("Definition of " ^ #name f ^ ":\n" ^
                    Syntax.string_of_term @{context} (Thm.prop_of (#definition f))))
\<close>

section \<open>Heap info\<close>
text \<open>
  Information about the abstracted heap (if heap_abs is enabled) is also stored
  to the HeapInfo structure.
  See heap_lift_base.ML for which fields are contained in the structure.
\<close>
ML \<open>
  the (Symtab.lookup (HeapInfo.get @{theory}) "function_info.c")
\<close>

section \<open>Intermediate function info\<close>
text \<open>
  AutoCorres performs a translation in multiple stages; the intermediate definitions
  and correspondence theorems are also stored in AutoCorresData.
  Definitions are tagged with the name (phase ^ "def") and corres theorems with
  the name (phase ^ "corres").

  This data is probably not useful outside of debugging AutoCorres itself.
\<close>
ML \<open>
  let val fn_name = "rec"
      val phases = [
        "L1", (* translation from SIMPL syntax *)
        "L2", (* lift local variables *)
        "HL", (* heap abstraction *)
        "WA", (* word abstraction *)
        "TS"  (* type lifting *)
       ]
  in (
      (* defs *)
      map (fn phase =>
        AutoCorresData.get_def @{theory} "function_info.c" (phase ^ "def") fn_name)
        phases,
    
      (* corres *)
      map (fn phase =>
        AutoCorresData.get_thm @{theory} "function_info.c" (phase ^ "corres") fn_name)
        phases
    )
  end
\<close>

end
end