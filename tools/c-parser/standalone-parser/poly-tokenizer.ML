(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)
val _ = PolyML.Compiler.prompt1:="";
val _ = PolyML.Compiler.prompt2:="";
val _ = PolyML.print_depth 0;
val dir = valOf (OS.Process.getEnv "STP_PFX")
val l4v_arch = valOf (OS.Process.getEnv "STP_ARCH")

infix |>
fun x |> f = f x

fun replace tgt replacement s =
    let
      val ss = Substring.full s
      val (pfx_s,sfx_s) = Substring.position tgt ss
    in
      if Substring.size sfx_s = 0 then s
      else
        Substring.concat [
          pfx_s,
          Substring.full replacement,
          Substring.triml (String.size tgt) sfx_s
        ]
    end

fun readmlb fname = let
  val istr = TextIO.openIn fname
  fun recurse () =
      case TextIO.inputLine istr of
        NONE => ()
      | SOME s => let
          open Substring
          val s = replace "$(L4V_ARCH)" l4v_arch s
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
