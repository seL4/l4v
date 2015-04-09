(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure StrictCParser =
struct

structure StrictCLrVals = StrictCLrValsFun(structure Token = LrParser.Token)

structure StrictCLex = StrictCLexFun(structure Tokens = StrictCLrVals.Tokens);

structure StrictCParser =
  JoinWithArg(structure LrParser = LrParser
              structure ParserData = StrictCLrVals.ParserData
              structure Lex = StrictCLex)

fun invoke lookahead pi lexstream = let
  fun print_error (s,lpos,rpos) = Feedback.errorStr'(lpos,rpos,s)
in
  (#1 (StrictCParser.parse(lookahead,lexstream,print_error,pi)), !Feedback.numErrors)
end

val report_cpp_errors = Unsynchronized.ref 10 (* FIXME *)

fun parse cpp_option error_lookahead (includes : string list) fname = let
  val includes_string = String.concat (map (fn s => "-I\""^s^"\" ") includes)
  fun plural 1 = ""
    | plural _ = "s"
  val cpped_fname =
      case cpp_option of
          NONE => fname
        | SOME p =>
          let
            open OS.FileSys OS.Process
            val tmpname = tmpName()
            val err_tmpname = tmpName()
            val cmdline =
                p ^ " " ^ includes_string ^ " -CC \"" ^ fname ^ "\" > " ^ tmpname ^ " 2> " ^ err_tmpname
          in
            if isSuccess (system cmdline) then (OS.FileSys.remove err_tmpname; tmpname)
            else let val _ = OS.FileSys.remove tmpname
                     val (msg, rest) = File.read_lines (Path.explode err_tmpname) |> chop (!report_cpp_errors)
                     val _ = OS.FileSys.remove err_tmpname
                     val _ = warning ("cpp failed on " ^ fname ^ "\nCommand: " ^ cmdline ^
                                      "\n\nOutput:\n" ^ cat_lines (msg @
                                        (if null rest then [] else
                                         ["(... " ^ string_of_int (length rest) ^
                                          " more line" ^ plural (length rest) ^ ")"])))
                 in raise Feedback.WantToExit ("cpp failed on " ^ fname) end
          end
  val istream = TextIO.openIn cpped_fname
  val _ = Feedback.numErrors := 0 (* FIXME - global reference *)
  val lexarg = StrictCLex.UserDeclarations.new_state fname
  val lexer = StrictCParser.makeLexer (fn _ => inputLine istream) lexarg
  val pos = #source lexarg
in
  invoke error_lookahead pos lexer before
  (TextIO.closeIn istream;
   if cpped_fname <> fname then
     OS.FileSys.remove cpped_fname
   else ())
end


end;
