(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val dir = valOf (OS.Process.getEnv "STP_PFX")

infix |>
fun x |> f = f x

fun readmlb fname = let
  val istr = TextIO.openIn fname
  fun recurse () =
      case TextIO.inputLine istr of
        NONE => ()
      | SOME s => let
          open Substring
          val s = s |> full |> dropr Char.isSpace |> dropl Char.isSpace |> string
          val lower_s = CharVector.map Char.toLower s
        in
          if not (String.isPrefix "mlton" lower_s) andalso
             (String.isSuffix "ml" lower_s orelse String.isSuffix "sig" lower_s)
          then
            use (dir ^ "/" ^ s)
          else ();
          recurse ()
        end
in
  recurse ()
end

structure MLton =
struct
  val eq = PolyML.pointerEq
end;

val _ = app (fn s => use (dir ^ "/../" ^ s))
        ["tools/mlyacc/mlyacclib/MLY_base-sig.ML",
         "tools/mlyacc/mlyacclib/MLY_join.ML",
         "tools/mlyacc/mlyacclib/MLY_lrtable.ML",
         "tools/mlyacc/mlyacclib/MLY_stream.ML",
         "tools/mlyacc/mlyacclib/MLY_parser2.ML"]

val _ = readmlb (dir ^ "/tokenizer.mlb");


fun main() = Main.doit (CommandLine.arguments())

val _ = PolyML.shareCommonData main;
val _ = PolyML.export(dir ^ "/tokenizer", main);
