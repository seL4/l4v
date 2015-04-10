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

fun parse docpp error_lookahead (includes : string list) fname = let
  val cpped_fname = docpp {includes=includes,filename=fname}
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
