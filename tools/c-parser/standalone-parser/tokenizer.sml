(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

structure StrictCLrVals = StrictCLrValsFun(structure Token = LrParser.Token)

structure StrictCLex = StrictCLexFun(structure Tokens = StrictCLrVals.Tokens);

structure StrictCParser =
  JoinWithArg(structure LrParser = LrParser
              structure ParserData = StrictCLrVals.ParserData
              structure Lex = StrictCLex)

fun invoke pi lexstream = let
  val (StrictCParser.Token.TOKEN (nexttok, _), strm') = StrictCParser.Stream.get lexstream
  val tok_s = StrictCLrVals.ParserData.EC.showTerminal nexttok
in
  print (tok_s ^ " ");
  if tok_s <> "EOF" then invoke pi strm' else print "\n"
end

fun lexit (includes : string list) (fname : string) = let
  val includes_string = String.concat (map (fn s => "-I"^s^" ") includes)
  val cpped_fname = let
    open OS.FileSys OS.Process
    val tmpname = tmpName()
  in
    if isSuccess (system ("/usr/bin/cpp " ^ includes_string ^ " -CC " ^ fname ^
                          " > " ^ tmpname))
    then
      tmpname
    else raise Feedback.WantToExit ("cpp failed on "^fname)
  end
  val istream = TextIO.openIn cpped_fname
  val lexarg = StrictCLex.UserDeclarations.new_state fname
  val _ = Feedback.numErrors := 0
  val lexer = StrictCParser.makeLexer (fn _ => inputLine istream) lexarg
in
  invoke (#source lexarg) lexer before
  (TextIO.closeIn istream;
   if cpped_fname <> fname then
     OS.FileSys.remove cpped_fname
   else ())
end

open OS.Process

fun die s = (print s; print "\n"; exit failure)
fun warn s = (TextIO.output(TextIO.stdErr, s^"\n");
              TextIO.flushOut TextIO.stdErr)

fun usage() = die ("Usage: "^CommandLine.name()^ " filename1 filename2 ...")


fun handle_args acc_incs args =
    case args of
      [] => usage()
    | arg::rest => let
      in
        if String.isPrefix "-I" arg then
          handle_args (String.extract(arg,2,NONE) :: acc_incs) rest
        else let
            val incs = List.rev acc_incs
            val num_errors = List.app (lexit incs) args
          in
            exit success
          end
      end

structure Main = struct fun doit args = handle_args [] args end
