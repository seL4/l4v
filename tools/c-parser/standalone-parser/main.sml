(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure Main = struct

open OS.Process


(* takes a file name on the command-line, and attempts to parse it *)
fun die s = (print s; print "\n"; exit failure)
fun warn s = (TextIO.output(TextIO.stdErr, s^"\n");
              TextIO.flushOut TextIO.stdErr)
val execname = CommandLine.name


val _ = Feedback.errorThreshold := NONE;
val _ = Feedback.informf := (fn s => (TextIO.output(TextIO.stdOut, s);
                                      TextIO.flushOut TextIO.stdOut))

fun quote s = "\"" ^ s ^ "\""


val commas = String.concat o separate ", "
fun writeln s = Feedback.informStr(0,s)

fun print_addressed_vars cse = let
  open ProgramAnalysis
  val globs = get_globals cse
  val pfx1 = "There are "^Int.toString (length globs)^ " globals: "
  val _ = writeln (String.concat
                       (separate "\n   " (pfx1 :: map srcname globs)))
  val addressed = get_addressed cse
  val addr_vars = map MString.dest (MSymTab.keys addressed)
  val pfx2 = "There are "^Int.toString (length addr_vars)^
             " addressed variables: "
  val _ = writeln (String.concatWith "\n  " (pfx2 :: addr_vars))
in
  ()
end

fun print_embedded_fncalls cse = let
  open ProgramAnalysis
  val calls = get_embedded_fncalls cse
  fun filter call =
      case call of
        DirectCall s => let
        in
          case get_modifies cse s of
            NONE => SOME s
          | SOME varset => if not (Binaryset.isEmpty varset) then SOME s
                           else NONE
        end
      | _ => NONE
  val call_list = List.mapPartial filter (Binaryset.listItems calls)
  val pfx = "These " ^ Int.toString (length call_list) ^
            " functions MUST be shown to be side-effect free (and don't look as if they are): "
in
  writeln (String.concat (separate "\n   " (pfx :: call_list)))
end

val printmv = ProgramAnalysis.mvar_toString

fun print_modifies cse = let
  open ProgramAnalysis
  val functions = get_functions cse
  fun print f = let
    val fnm = if is_recursivefn cse f then f ^ " (recursive)" else f
  in
    writeln ("   " ^ StringCvt.padRight #" " 50 fnm ^ ":  " ^
             (case get_modifies cse f of
                NONE => "<is or calls unannotated proto>"
              | SOME varset =>
                String.concat
                    (separate " " (map printmv (Binaryset.listItems varset)))))
  end
in
  writeln "Modifies info:";
  app print functions
end

fun print_reads cse = let
  open ProgramAnalysis
  val functions = get_functions cse
  val reads = get_read_globals cse
  fun print f = let
    val vars = Binaryset.foldr (fn (mv,acc) => printmv mv :: acc)
                               []
                               (valOf (Symtab.lookup reads f))
               handle Option => ["<is or calls unannotated proto>"]
  in
    writeln ("   " ^ StringCvt.padRight #" " 50 f ^ ":  "^
             String.concat (separate " " vars))
  end
in
  writeln "Function reads:";
  app print functions
end

fun calc_protoes cse = let
  open ProgramAnalysis
  val functions = get_functions cse
  val defined_functions = get_defined_functions cse
  fun foldthis (f, acc) =
      if isSome (Symtab.lookup defined_functions f) then acc
      else Binaryset.add(acc, f)
in
  List.foldl foldthis (Binaryset.empty String.compare) functions
end

fun print_protoes cse = let
in
  writeln "Protoes (only):";
  Binaryset.app (fn v => writeln ("   " ^ v)) (calc_protoes cse)
end

fun print_unmodified_globals cse = let
in
  writeln "Unmodifed, unaddressed globals:";
  writeln ("   " ^
           (cse |> ProgramAnalysis.calc_untouched_globals
                |> MSymTab.keys
                |> map MString.dest
                |> commas))
end

val filename = ref ""
fun produce_dotfile cse = let
  open ProgramAnalysis
  val os = TextIO.openOut (!filename ^ ".dot")
  fun print s = TextIO.output(os, s ^ "\n")
  val fns = get_functions cse
  val {callgraph,...} = compute_callgraphs cse
  fun print_fn f = let
    val callees = case Symtab.lookup callgraph f of
                    NONE => Binaryset.empty String.compare
                  | SOME s => s
  in
    Binaryset.app (fn c => print (f ^ " -> " ^ c)) callees
  end
in
  print "digraph {";
  print "graph[fontsize=8]";
  print "node[shape=plaintext]";
  List.app print_fn fns;
  print "}";
  TextIO.closeOut os
end

fun produce_toposort cse = let
  open ProgramAnalysis
  fun lift f fnm = case Symtab.lookup f fnm of
                     NONE => []
                   | SOME s => Binaryset.listItems s
  val {callgraph,callers} = compute_callgraphs cse
  val toposort = Topo_Sort.topo_sort {cmp = String.compare,
                                      graph = lift callgraph,
                                      converse = lift callers}
                                     (get_functions cse)
  fun printcomp [] = raise Fail "Empty SCC??"
    | printcomp [x] = writeln ("   "^x)
    | printcomp list = writeln ("   " ^ commas list)
in
  writeln "Topological sort of functions in callgraph";
  List.app printcomp toposort
end


fun print_uncalledfns cse = let
  open ProgramAnalysis
  val {callgraph = graph,...} = compute_callgraphs cse
  val fns = get_functions cse
  fun foldthis (fname, acc) =
      case Symtab.lookup graph fname of
        NONE => fname :: acc
      | SOME s => if Binaryset.isEmpty s then fname::acc
                  else acc
  val uncalled = List.foldl foldthis [] fns
in
  writeln "Uncalled functions";
  List.app (fn s => writeln ("   "^s)) (List.rev uncalled)
end

fun print_fnspecs cse = let
  open ProgramAnalysis Absyn
  val specdb = function_specs cse
  val _ = writeln "Function specification information:"
  fun doit (fname, specs) () = let
  in
    writeln fname ;
    List.app (fn fs => writeln ("   "^fnspec2string fs)) specs
  end
in
  Symtab.fold doit specdb ()
end


datatype pc_problem = Reads of ProgramAnalysis.modify_var
                    | Writes of ProgramAnalysis.modify_var
                    | IsProto

fun mapOne f s =
    case Binaryset.find (fn _ => true) s of
      NONE => NONE
    | SOME i => SOME (f i)

fun print_bogus_pures cse = let
  open ProgramAnalysis Absyn
  val specdb = function_specs cse
  open Feedback
  fun foldthis (fname, fspecs) () = let
    open Binaryset
    val idset = all_IDattributes fspecs
    val pure_problem =
        case get_modifies cse fname of
          NONE => SOME IsProto
        | SOME s => mapOne Writes s
    val pc_attr = member(idset, "pure") orelse member(idset, "const")
  in
    if member(idset, "noreturn") then ()
    else
      case pure_problem of
        NONE => if not pc_attr then
                  informStr(2, "NOTE: "^fname^
                               " is pure, but not annotated pure or const")
                else ()
      | SOME (Writes mv) =>
        if pc_attr then
          informStr(1, "WARNING: "^fname^ " writes "^printmv mv^
                       " but is annotated pure or const")
        else ()
      | SOME IsProto =>
        if pc_attr then
          informStr(1, "WARNING: "^fname^" is annotated pure or const, but \
                                         \is an unannotated prototype")
        else ()
      | SOME _ => (* can't happen *) ()
  end
in
  Symtab.fold foldthis specdb ()
end

fun print_bogus_consts cse = let
  open ProgramAnalysis Absyn
  val specdb = function_specs cse
  val read_globals = get_read_globals cse
  fun foldthis (fname, fspecs) () = let
    val reads_prob =
        case Symtab.lookup read_globals fname of
          NONE => SOME IsProto
        | SOME s => mapOne Reads s
    val prob =
        case reads_prob of
          NONE => let
          in
            case get_modifies cse fname of
              NONE => SOME IsProto
            | SOME s => mapOne Writes s
          end
        | x => x
    val idset = all_IDattributes fspecs
    open Binaryset Feedback
    fun prob2str IsProto = "is or calls a proto"
      | prob2str (Reads mv) = "reads "^printmv mv
      | prob2str (Writes mv) = "writes "^printmv mv
  in
    if member(idset, "noreturn") then ()
    else
      case prob of
        NONE => if not (member(idset, "const")) then
                          informStr(2, "NOTE: "^fname^
                                       " is const, but not annotated const")
                        else ()
      | SOME p => if member (idset, "const") then
                    informStr(1, "WARNING: "^fname^" is declared const but "^
                                 prob2str p)
                  else ()
  end
in
  Symtab.fold foldthis specdb ()
end


fun print_unannotated_protoes cse = let
  open ProgramAnalysis
  val protoes = calc_protoes cse
  fun foldthis (fnm, acc) =
      case get_modifies cse fnm of
        NONE => fnm::acc
      | SOME _ => acc
in
  writeln "Unannotated protoes:";
  List.app (fn s => writeln ("   "^s))
           (List.rev (Binaryset.foldl foldthis [] protoes))
end

fun mmsizes cse = let
  open Absyn ProgramAnalysis
  val fns = get_fninfo cse
  fun foldthis (name,(rettype,_,pvis)) _ = let
    fun bytesize ty = case ty of Void => 0 | _ => sizeof cse ty
    val retsize = bytesize rettype
    val psizes = map (bytesize o get_vi_type) pvis
  in
    print (String.concatWith " " (Int.toString retsize :: name ::
                                  map Int.toString psizes));
    print "\n"
  end
in
  Symtab.fold foldthis fns ()
end


fun equal x y = (x = y)

fun cmdline_options hdlr args = let
  fun recurse args =
      case args of
        [] => args
      | h::t => if h = "--" then t
                else if String.isPrefix "--" h then let
                    val h' = String.extract (h, 2, NONE)
                    val flds = String.fields (equal #"=") h'
                  in
                    if length flds = 1 then (hdlr (h', NONE); recurse t)
                    else let
                        val a = hd flds
                        val () = hdlr (a, SOME (String.extract(h',size a,NONE)))
                      in
                        recurse t
                      end
                  end
                else if String.isPrefix "-" h andalso size h > 1 then let
                  in
                    if size h > 2 then
                      hdlr(String.substring(h,1,1),
                           SOME (String.extract(h,2,NONE)))
                    else
                      hdlr(String.substring(h,1,1), NONE);
                    recurse t
                  end
                else h::t
in
  recurse args
end

fun decl_toString d = let
  open Absyn
in
  case d of
    VarDecl (_, sw, _, _, _) => "declaration of global variable "^node sw
  | StructDecl (sw, _) => "declaration of struct "^node sw
  | TypeDecl tynms => "typedef of "^
                      String.concatWith ", " (map (node o #2) tynms)
  | ExtFnDecl {name,...} => "declaration of function "^node name
  | EnumDecl (sow,_) => "declaration of "^(case node sow of
                                             NONE => "anonymous"
                                           | SOME s => s)^
                        " enum"
end

fun print_fnslocs cse ast = let
  open Absyn
  fun recurse [] = ()
    | recurse (Decl dw :: t) =
      (warn ("Ignoring "^decl_toString (node dw)); recurse t)
    | recurse (FnDefn ((retty,fnm),params,specs,body) :: t) =
      (print (node fnm^" " ^
              SourcePos.toString (left fnm) ^ " " ^
              SourcePos.toString (right body)^"\n");
       recurse t)
in
  recurse ast
end

fun print_ast cse ast = let
  open Absyn_Serial

  fun serial_defn (FnDefn ((retty,fnm),params,specs,body))
    = Nm ("Function", [varspec_serial (retty,fnm),
        list_serial varspec_serial params,
        list_serial fnspec_serial specs,
        list_serial bi_serial (node body)])
    | serial_defn (Decl dw) = decl_serial (node dw)
  fun print_lines ss = app print (map (fn s => s ^ "\n") ss)
in
  app (print_lines o lines_serial o serial_defn) ast
end

fun adjusted_complex_fncalls cse ast = let
  open Absyn_Serial

  fun is_adjusted s = case snode s of
      Assign(_,e) => (case enode e of EFnCall _ => true | _ => false)
    | Return(SOME e) => (case enode e of EFnCall _ => true | _ => false)
    | _ => false
  fun note_adjusteds s = if is_adjusted s
    then print ("adjusted fncall at: " ^
              SourcePos.toString (sleft s) ^ " " ^
              SourcePos.toString (sright s)^"\n")
    else app note_adjusteds (sub_stmts s)
  fun note_bi (BI_Stmt s) = note_adjusteds s
    | note_bi _ = ()
  fun note_defn (FnDefn (_,_,_,body))
    = app note_bi (node body)
    | note_defn _ = ()
in app note_defn ast end

fun unhandled_asm cse ast = let
  open Absyn
  fun warn_asm asm = K () (ProgramAnalysis.split_asm_stmt asm)
    handle Fail s => print s
  fun warn_stmt s = case snode s of
      (AsmStmt asm) => warn_asm (AsmStmt asm)
    | _ => app warn_stmt (sub_stmts s)
  fun warn_bi (BI_Stmt s) = warn_stmt s
    | warn_bi _ = ()
  fun warn_defn (FnDefn (_,_,_,body))
    = app warn_bi (node body)
    | warn_defn _ = ()
in app warn_defn ast end

val analyses = ref ([] : (ProgramAnalysis.csenv -> Absyn.ext_decl list -> unit) list)
val includes = ref ([] : string list)
val error_lookahead = ref 15
val verbosity = Feedback.verbosity_level

fun add_analysis f = analyses := f :: !analyses
fun add_cse_analysis f = analyses := (fn cse => fn ast => f cse) :: !analyses

val cpp = ref (SOME "/usr/bin/cpp")
val parse_only = ref false
val underscore_idents = ref false
val show_help = ref false
val bad_option = ref false
val munge_info_fname = ref (NONE : string option)

val options = let
  open GetOpt
  fun intref r s =
    case Int.fromString s of
        NONE => (show_help := true; bad_option := true)
      | SOME i => r := i
  fun cse_analysis nm f =
    {short = "", long = [nm], help = "Do "^nm^" analysis",
     desc = NoArg (fn () => add_cse_analysis f)}
  fun ast_analysis nm f =
    {short = "", long = [nm], help = "Do "^nm^" analysis",
     desc = NoArg (fn () => add_analysis f)}
in
  [{short = "h?", long = ["help"], help = "Show usage information",
    desc = NoArg (fn () => show_help := true)},
   {short = "I", long = [], help = "Add include directory (repeatable)",
    desc = ReqArg ((fn dir => includes := dir :: !includes), "directory")},
   {short = "v", long = [], help = "Set parser error verbosity",
    desc = ReqArg (intref verbosity, "number")},
   {short = "l", long = [], help = "Set parser lookahead",
    desc = ReqArg (intref error_lookahead, "number")},
   cse_analysis "addressed_vars" print_addressed_vars,
   cse_analysis "bogus_const" print_bogus_consts,
   cse_analysis "bogus_pure" print_bogus_pures,
   {short = "", long = ["cpp"], help = "Set cpp path (see also --nocpp)",
    desc = ReqArg ((fn p => cpp := SOME p), "path")},
   cse_analysis "embedded_fncalls" print_embedded_fncalls,
   ast_analysis "fnslocs" print_fnslocs,
   cse_analysis "fnspecs" print_fnspecs,
   cse_analysis "mmbytes" mmsizes,
   cse_analysis "modifies" print_modifies,
   {short = "", long = ["munge_info_fname"], help = "Path for munge info",
    desc = ReqArg ((fn p => munge_info_fname := SOME p), "path")},
   {short = "", long = ["nocpp"], help = "Don't use cpp",
    desc = NoArg (fn () => cpp := NONE)},
   {short = "", long = ["nolinedirectives"], help = "Ignore #line directives",
    desc = NoArg (fn () => SourceFile.observe_line_directives := false)},
   cse_analysis "protoes"             print_protoes,
   {short = "", long = ["rawsyntaxonly"], help = "Don't perform any analyses",
    desc = NoArg (fn () => parse_only := true)},
   {short = "", long = ["underscore_idents"], help = "Allow identifiers starting with underscores",
    desc = NoArg (fn () => underscore_idents := true)},
   cse_analysis "reads" print_reads,
   cse_analysis "toposort" produce_toposort,
   cse_analysis "produce dotfile" produce_dotfile,
   cse_analysis "unannotated_protoes" print_unannotated_protoes,
   cse_analysis "uncalledfns" print_uncalledfns,
   cse_analysis "unmodifiedglobs" print_unmodified_globals,
   ast_analysis "ast" print_ast,
   ast_analysis "adjusted_complex_fncalls" adjusted_complex_fncalls,
   ast_analysis "unhandled_asm" unhandled_asm
  ]
end




fun docpp (SOME p) {includes, filename} =
  let
    val includes_string = String.concat (map (fn s => "-I\""^s^"\" ") includes)
    open OS.FileSys OS.Process
    val tmpname = tmpName()
    val cmdline =
        p ^ " " ^ includes_string ^ " -CC \"" ^ filename ^ "\" > " ^ tmpname
  in
    if isSuccess (system cmdline) then (tmpname, true)
    else raise Feedback.WantToExit ("cpp failed on "^filename)
  end
  | docpp NONE {filename, ...} = (filename, false)

val usage_msg = GetOpt.usageInfo {
    header =
    "Usage: \n  "^execname()^" [options] filename\n\n\
    \Use -l to adjust error lookahead. (The higher the number, the more the parser\n\
    \will try to make sense of stuff with parse errors.)\n\n\
    \For no analyses at all (not even typechecking), use --rawsyntaxonly.\n\n\
    \All options:\n",
    options = options
  }



fun doit args =
  let
    val (_, realargs) =
        GetOpt.getOpt {argOrder = GetOpt.RequireOrder, options = options,
                       errFn = die} args
    val _ = if !show_help then
              (print usage_msg ; OS.Process.exit OS.Process.success)
            else if !bad_option then die usage_msg
            else ()
  in
    case realargs of
      [] => die usage_msg
    | [fname] =>
      let
        val (ast,n) = StrictCParser.parse (docpp (!cpp)) (!error_lookahead)
                                          (List.rev (!includes)) fname
      in
        if !parse_only then ()
        else
          let
            val ((ast', inits), cse) =
                ProgramAnalysis.process_decls
                  {anon_vars = false, owners = [],
                   munge_info_fname = !munge_info_fname,
                   allow_underscore_idents = !underscore_idents}
                  (SyntaxTransforms.remove_typedefs ast)
            val _ = ProgramAnalysis.export_mungedb cse
            val _ = filename := fname
            fun do_analyses alist =
                case alist of
                  [] => exit (if !Feedback.numErrors = 0 then success else failure)
                | f::fs => let
                    val () = f cse ast'
                  in
                    do_analyses fs
                  end
          in
            do_analyses (List.rev (!analyses))
          end
      end
    | _ => die usage_msg
  end

end;
