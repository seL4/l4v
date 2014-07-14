(*
 * @TAG(OTHER_PRINCETON_OSS)
 *)

fun main() = let
  val name = CommandLine.name()
in
  case CommandLine.arguments() of
    [] => (TextIO.output(TextIO.stdErr, name ^ ": no arguments\n");
           OS.Process.exit OS.Process.failure)
  | args => List.app LexGen.lexGen args
end;

main();


