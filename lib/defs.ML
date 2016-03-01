signature OLD_DEFS=
sig
end

structure Old_Defs : OLD_DEFS =
struct

fun read ctxt (b, str) =
  Syntax.read_prop ctxt str handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in definition " ^ Binding.print b);

fun add_defs ((unchecked, overloaded), args) thy =
 (legacy_feature "Old 'defs' command -- use 'definition' (with 'overloading') instead";
 let
  val ctxt = Syntax.init_pretty_global thy;
 in
  thy |>
    (if unchecked then Global_Theory.add_defs_unchecked else Global_Theory.add_defs)
      overloaded
      (map (fn ((b, ax), srcs) => ((b, read ctxt (b, ax)), map (Attrib.attribute_cmd_global thy) srcs)) args)
  |> snd
  end);

val opt_unchecked_overloaded =
  Scan.optional (@{keyword "("} |-- Parse.!!!
    (((@{keyword "unchecked"} >> K true) --
        Scan.optional (@{keyword "overloaded"} >> K true) false ||
      @{keyword "overloaded"} >> K (false, true)) --| @{keyword ")"})) (false, false);

val _ =
  Outer_Syntax.command @{command_keyword defs} "define constants"
    (opt_unchecked_overloaded --
      Scan.repeat1 (Parse_Spec.thm_name ":" -- Parse.prop >> (fn ((x, y), z) => ((x, z), y)))
      >> (Toplevel.theory o add_defs));
end