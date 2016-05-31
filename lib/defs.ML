(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

signature OLD_DEFS=
sig
end

structure Old_Defs : OLD_DEFS =
struct

fun read ctxt (b, str) =
  Syntax.read_prop ctxt str handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in definition " ^ Binding.print b);

fun add_defs ctxt ((unchecked, overloaded), args) thy =
 (legacy_feature "Old 'defs' command -- use 'definition' (with 'overloading') instead";
  thy |>
    (if unchecked then Global_Theory.add_defs_unchecked else Global_Theory.add_defs)
      overloaded
      (map (fn ((b, ax), srcs) => ((b, read ctxt (b, ax)), map (Attrib.attribute_cmd ctxt) srcs)) args));

val opt_unchecked_overloaded =
  Scan.optional (@{keyword "("} |-- Parse.!!!
    (((@{keyword "unchecked"} >> K true) --
        Scan.optional (@{keyword "overloaded"} >> K true) false ||
      @{keyword "overloaded"} >> K (false, true)) --| @{keyword ")"})) (false, false);

fun syntax_alias global_alias local_alias b name =
  Local_Theory.declaration {syntax = true, pervasive = true} (fn phi =>
    let val b' = Morphism.binding phi b
    in Context.mapping (global_alias b' name) (local_alias b' name) end);

val const_alias = syntax_alias Sign.const_alias Proof_Context.const_alias;

(* Proof_Context.fact_alias doesn't work here, so we need to play a few tricks to get the right fact name *)

val _ =
  Outer_Syntax.command @{command_keyword defs} "define constants"
    (Parse.opt_target -- (opt_unchecked_overloaded --
      Scan.repeat1 (Parse_Spec.thm_name ":" -- Parse.prop >> (fn ((x, y), z) => ((x, z), y))))
      >> (fn (target, (b, args)) => Toplevel.local_theory NONE target (fn lthy =>
          let
               val args' = map (fn ((b, def), x) => ((Binding.suffix_name "__internal__" b, def), x)) args
               val (thms, lthy') = Local_Theory.background_theory_result (add_defs lthy (b, args')) lthy;
               val lthy'' = fold2 (fn ((b, _), _) => fn thm =>
                  fn lthy =>
                    let val (_, lthy') = Local_Theory.note ((b,[]), [thm]) lthy
                    in lthy' end) args thms lthy';
               val lthy''' = Local_Theory.raw_theory (fold (fn thm =>
                    Global_Theory.hide_fact true (Thm.derivation_name thm)) thms) lthy''
          in lthy''' end)));


val _ =
  Outer_Syntax.command @{command_keyword consts'} "localized consts declaration"
    (Parse.opt_target -- Scan.repeat1 Parse.const_binding >>
      (fn (target, bs) => Toplevel.local_theory NONE target (fn lthy =>
         fold (fn (b, raw_typ, mixfix) => fn lthy =>
           let val (Const (nm, _), lthy') = Local_Theory.background_theory_result
             (Sign.declare_const lthy ((b, Syntax.read_typ lthy raw_typ), mixfix)) lthy;
          in const_alias b nm lthy' end) bs lthy)))
end
