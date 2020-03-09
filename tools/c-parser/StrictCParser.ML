(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

fun parse docpp error_lookahead (includes : string list) fname = let
  val (cpped_fname, fname_is_tmp) = docpp {includes=includes,filename=fname}
  val istream = TextIO.openIn cpped_fname
  val _ = Feedback.numErrors := 0 (* FIXME - global reference *)
  val lexarg = StrictCLex.UserDeclarations.new_state fname
  val lexer = StrictCParser.makeLexer (fn _ => inputLine istream) lexarg
  val pos = #source lexarg
in
  invoke error_lookahead pos lexer before
  (TextIO.closeIn istream;
   if fname_is_tmp then
     OS.FileSys.remove cpped_fname
   else ())
end


end;
