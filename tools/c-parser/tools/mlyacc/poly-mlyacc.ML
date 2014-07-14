(*
 * @TAG(OTHER_PRINCETON_OSS)
 *)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val dir = valOf (OS.Process.getEnv "MLYACC_PFX")

fun u f = use (dir ^ "/mlyacclib/" ^ f ^ ".ML");

val _ = u "MLY_base-sig";
val _ = u "MLY_join";
val _ = u "MLY_lrtable";
val _ = u "MLY_stream";
val _ = u "MLY_parser2";

fun u f = use (dir ^ "/src/" ^ f ^ ".ML");

fun usml f = use (dir ^ "/src/" ^ f ^ ".sml");

val _ = u "utils";
val _ = u "sigs";
val _ = u "verbose";
val _ = u "hdr";
val _ = usml "yacc-grm-sig";
val _ = usml "yacc-grm";
val _ = usml "yacc.lex";
val _ = u "parse";
val _ = u "core";
val _ = u "coreutils";
val _ = u "graph";
val _ = u "look";
val _ = u "lalr";
val _ = u "mklrtable";
val _ = u "grammar";
val _ = u "mkprstruct";
val _ = u "shrink";
val _ = u "absyn-sig";
val _ = u "yacc";
val _ = u "absyn";
val _ = u "link";
val _ = use (dir ^ "/src/poly-main.ML");

fun main () = main.main (CommandLine.arguments ());

val _ = PolyML.shareCommonData main;
val _ = PolyML.export (dir ^ "/mlyacc", main);


