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

fun usage() = die ("Usage: \n  "^execname()^
                   " [--cpp=path|--nocpp] [-v<verboseness>] [-l<int>] [-I<include-dir>]* filename\n\
                   \Use -l to adjust error lookahead.  (The higher the number, the more the parser\n\
                   \will try to make sense of stuff with parse errors.)\n\
                   \\n\
                   \For no analyses at all (not even typechecking), add --rawsyntaxonly\n\
                   \Alternatively, add any of the following for additional analyses:\n\
                   \  --addressed_vars\n\
                   \  --bogus_const\n\
                   \  --bogus_pure\n\
                   \  --dotfile\n\
                   \  --embedded_fncalls\n\
                   \  --fnslocs\n\
                   \  --fnspecs\n\
                   \  --mmbytes\n\
                   \  --mmwords\n\
                   \  --modifies\n\
                   \  --protoes\n\
                   \  --reads\n\
                   \  --toposort\n\
                   \  --unannotated_protoes\n\
                   \  --uncalledfns\n\
                   \  --unmodifiedglobs")

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


val analyses = ref ([] : (ProgramAnalysis.csenv -> Absyn.ext_decl list -> unit) list)
val includes = ref ([] : string list)
val error_lookahead = ref 15
val verbosity = Feedback.verbosity_level

fun add_analysis f = analyses := f :: !analyses
fun add_cse_analysis f = analyses := (fn cse => fn ast => f cse) :: !analyses

val cpp = ref (SOME "/usr/bin/cpp")
val parse_only = ref false

fun handler sopt =
    case sopt of
      ("h", _) => usage()
    | ("?", _) => usage()
    | ("I",SOME dir) => includes := dir:: !includes
    | ("v",SOME v) => let
      in
        case Int.fromString v of
          NONE => usage()
        | SOME v_i => verbosity := v_i
      end
    | ("l", SOME l) => let
      in
        case Int.fromString l of
            NONE => usage()
          | SOME v_i => error_lookahead := v_i
      end
    | ("addressed_vars", NONE) => add_cse_analysis print_addressed_vars
    | ("bogus_const", NONE) => add_cse_analysis print_bogus_consts
    | ("bogus_pure", NONE) => add_cse_analysis print_bogus_pures
    | ("cpp", SOME v) => if v = "" then cpp := NONE else cpp := SOME v
    | ("embedded_fncalls", NONE) => add_cse_analysis print_embedded_fncalls
    | ("fnslocs", NONE) => add_analysis print_fnslocs
    | ("fnspecs", NONE) => add_cse_analysis print_fnspecs
    | ("mmbytes", NONE) => add_cse_analysis mmsizes
    | ("modifies", NONE) => add_cse_analysis print_modifies
    | ("nolinedirectives", NONE) =>
         (SourceFile.observe_line_directives := false)
    | ("nocpp", NONE) => (cpp := NONE)
    | ("protoes", NONE) => add_cse_analysis print_protoes
    | ("reads", NONE) => add_cse_analysis print_reads
    | ("toposort", NONE) => add_cse_analysis produce_toposort
    | ("dotfile", NONE) => add_cse_analysis produce_dotfile
    | ("unannotated_protoes", NONE) => add_cse_analysis print_unannotated_protoes
    | ("uncalledfns", NONE) => add_cse_analysis print_uncalledfns
    | ("unmodifiedglobs", NONE) => add_cse_analysis print_unmodified_globals
    | ("rawsyntaxonly", NONE) => (parse_only := true)
    | _ => usage()

fun docpp (SOME p) {includes, filename} =
  let
    val includes_string = String.concat (map (fn s => "-I\""^s^"\" ") includes)
    open OS.FileSys OS.Process
    val tmpname = tmpName()
    val cmdline =
        p ^ " " ^ includes_string ^ " -CC \"" ^ filename ^ "\" > " ^ tmpname
  in
    if isSuccess (system cmdline) then tmpname
    else raise Feedback.WantToExit ("cpp failed on "^filename)
  end
  | docpp NONE {filename, ...} = filename

fun doit args =
    case cmdline_options handler args of
      [] => usage()
    | [fname] =>
      let
        val (ast,n) = StrictCParser.parse (docpp (!cpp)) (!error_lookahead) (List.rev (!includes)) fname
      in
        if !parse_only then ()
        else
          let
            val ((ast', inits), cse) = ProgramAnalysis.process_decls
                                           {anon_vars = false, owners = [],
                                            allow_underscore_idents = false}
                                           (SyntaxTransforms.remove_typedefs ast)
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
    | _ => usage()

end;
