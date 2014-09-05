(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory TestSEL4
imports
  AutoCorres
  "../../spec/cspec/KernelInc_C"
begin

(*
 * Test to see if we can parse all of seL4.
 *)
autocorres [keep_going] "c/kernel_all.c_pp"

context kernel_all begin

declare [[show_question_marks = false]]
ML_file "~~/src/Tools/WWW_Find/unicode_symbols.ML"

ML {*

(* Fetch definition of a function. *)
fun get_function_def ctxt name =
  List.find is_some [
     try (Proof_Context.get_fact ctxt) (Facts.named (name ^ "'.simps")),
     try (Proof_Context.get_fact ctxt) (Facts.named (name ^ "'_def"))
     ]
  |> Option.map the

(* Render a thm to UTF-8 *)
fun render_thm ctxt thm =
  Print_Mode.setmp ["xsymbols", "brackets"]
    (fn _ => Display.pretty_thm ctxt thm
             |> Pretty.string_of
             |> YXML.parse_body
             |> XML.content_of) ()
    |> Symbol.explode
    |> map (fn n => the_default (ord n) (UnicodeSymbols.symbol_to_unicode n))
    |> UnicodeSymbols.utf8

(* Convert a path into one relative to this theory file. *)
fun mk_thy_relative thy filename =
  if OS.Path.isRelative filename then
    OS.Path.concat(Path.implode (Thy_Load.master_directory thy), filename)
  else
    filename

val _ = let

(* Get a list of all function names. *)
val function_names =
  FunctionInfo.init_fn_info @{context} "c/kernel_all.c_pp"
  |> FunctionInfo.get_functions
  |> Symtab.dest
  |> map fst
  |> sort string_ord

(* Fetch definitions. *)
val function_defs =
  map (get_function_def @{context}) function_names

(* Render them to text. *)
val function_txt =
  map (fn (name, def) =>
    case def of
      NONE => "(" ^ name ^ " missing)"
    | SOME def' => cat_lines (map (render_thm @{context}) def'))
    (function_names ~~ function_defs)
  |> surround "---" |> tl
  |> separate ""
  |> cat_lines

(* Final file with header and footer. *)
val final_txt =
  cat_lines [
    "",
    "AutoCorres output",
    "=================",
    "", ""
  ] ^ function_txt ^ "\n\n"
in
  File.write
    (Path.explode (mk_thy_relative @{theory} "sel4.txt"))
    final_txt
end

*}

end


end
