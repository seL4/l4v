(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(*
  Requalify constants, types and facts into the current naming
*)

theory Requalify
imports Main
keywords "requalify_facts" :: thy_decl and "requalify_types" :: thy_decl and "requalify_consts" :: thy_decl and
         "global_naming" :: thy_decl
begin

ML \<open>

local


fun all_facts_of ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val global_facts = Global_Theory.facts_of thy;
  in
   Facts.dest_static false [] global_facts
  end;

fun global_fact ctxt nm =
let
   val facts = Proof_Context.facts_of ctxt;
   val {name, thms, ...} = (Facts.retrieve (Context.Proof ctxt) facts (nm, Position.none));

   fun tl' (_ :: xs) = xs
     | tl' _ = []

   fun matches suf (gnm, gthms)  =
   let
     val gsuf = Long_Name.explode gnm |> tl' |> tl' |> Long_Name.implode;

   in suf = gsuf andalso eq_list (Thm.equiv_thm (Proof_Context.theory_of ctxt)) (thms, gthms)
   end
in
  case Long_Name.dest_local name of NONE => (name, thms) | SOME suf =>
    (case (find_first (matches suf) (all_facts_of ctxt)) of
       SOME x => x
     | NONE => raise Fail ("Couldn't find global equivalent of local fact: " ^ nm))
end

fun syntax_alias global_alias local_alias b (name : string) =
  Local_Theory.declaration {syntax = false, pervasive = true} (fn phi =>
    let val b' = Morphism.binding phi b
    in Context.mapping (global_alias b' name) (local_alias b' name) end);

val alias_fact = syntax_alias Global_Theory.alias_fact Proof_Context.alias_fact;
val const_alias = syntax_alias Sign.const_alias Proof_Context.const_alias;
val type_alias = syntax_alias Sign.type_alias Proof_Context.type_alias;

in

fun gen_requalify get_proper_nm parse_nm check_nm alias =
  (Parse.opt_target  --  Scan.repeat1 (Parse.position (Scan.ahead parse_nm -- Parse.name))
    >> (fn (target,bs) =>
      Toplevel.local_theory NONE target (fn lthy =>
      let

        fun read_entry ((entry, t), pos) lthy =
        let
          val local_nm = get_proper_nm lthy t;
          val _ = check_nm lthy (entry, (local_nm, pos));
          val b = Binding.make (Long_Name.base_name t, pos)

          val lthy' = lthy
          |> alias b local_nm

        in lthy' end

       in fold read_entry bs lthy  end)))

local

val get_const_nm = ((fst o dest_Const) oo (Proof_Context.read_const {proper = true, strict = false}))
val get_type_nm = ((fst o dest_Type) oo (Proof_Context.read_type_name {proper = true, strict = false}))
val get_fact_nm = (fst oo global_fact)

fun check_fact lthy (_, (nm, pos)) = Proof_Context.get_fact lthy (Facts.Named ((nm,pos), NONE))

in

val _ =
  Outer_Syntax.command @{command_keyword requalify_consts} "alias const with current naming"
    (gen_requalify get_const_nm Parse.const (fn lthy => fn (e, _) => get_const_nm lthy e) const_alias)

val _ =
  Outer_Syntax.command @{command_keyword requalify_types} "alias type with current naming"
    (gen_requalify get_type_nm Parse.typ (fn lthy => fn (e, _) => get_type_nm lthy e) type_alias)

val _ =
  Outer_Syntax.command @{command_keyword requalify_facts} "alias fact with current naming"
    (gen_requalify get_fact_nm Parse.thm check_fact alias_fact)

val _ =
  Outer_Syntax.command @{command_keyword global_naming} "change global naming of context block"
    (Parse.binding >> (fn naming =>
      Toplevel.local_theory NONE NONE
        (Local_Theory.map_background_naming (Name_Space.parent_path #> Name_Space.qualified_path true naming))))

end

end
\<close>

(*Tests and examples *)

locale Requalify_Locale
begin

typedecl requalify_type

definition "requalify_const == (undefined :: requalify_type)"


end

typedecl requalify_type
definition "requalify_const == (undefined :: requalify_type)"

context Requalify_Locale begin global_naming Requalify_Locale2

requalify_consts requalify_const
requalify_types requalify_type
requalify_facts requalify_const_def

end

term "requalify_const :: requalify_type"
term "Requalify_Locale2.requalify_const :: Requalify_Locale2.requalify_type"
lemma "Requalify_Locale2.requalify_const = (undefined :: Requalify_Locale2.requalify_type)"
  by (simp add: Requalify_Locale2.requalify_const_def)

consts requalify_test_f :: "'a \<Rightarrow> 'b \<Rightarrow> bool"

lemma
  assumes f1: "requalify_test_f requalify_const Requalify_Locale2.requalify_const"
  and f2: "requalify_test_f Requalify_Locale2.requalify_const Requalify.requalify_const"
  shows "requalify_test_f Requalify_Locale2.requalify_const requalify_const" "requalify_const = undefined"
  apply (rule f1)?
  apply (rule f2)
  apply (simp add: requalify_const_def)
  done

context Requalify_Locale begin

lemma
  assumes f1: "requalify_test_f requalify_const Requalify_Locale2.requalify_const"
  and f2: "requalify_test_f Requalify_Locale2.requalify_const Requalify.requalify_const"
  shows "requalify_test_f Requalify_Locale2.requalify_const requalify_const" "requalify_const = undefined"
  apply (rule f2)?
  apply (rule f1)
  apply (simp add: requalify_const_def)
  done

end

context Requalify_Locale begin global_naming global

requalify_consts Requalify.requalify_const
requalify_types Requalify.requalify_type
requalify_facts Requalify.requalify_const_def

end

context Requalify_Locale begin

lemma
  assumes f1: "requalify_test_f requalify_const Requalify_Locale2.requalify_const"
  and f2: "requalify_test_f Requalify_Locale2.requalify_const global.requalify_const"
  shows "requalify_test_f Requalify_Locale2.requalify_const requalify_const" "requalify_const = undefined"
  apply (rule f1)?
  apply (rule f2)
  apply (simp add: requalify_const_def)
  done
end

context begin interpretation Requalify_Locale .

lemma
  assumes f1: "requalify_test_f requalify_const Requalify_Locale2.requalify_const"
  and f2: "requalify_test_f Requalify_Locale2.requalify_const global.requalify_const"
  shows "requalify_test_f Requalify_Locale2.requalify_const requalify_const" "requalify_const = undefined"
  apply (rule f1)?
  apply (rule f2)
  apply (simp add: requalify_const_def)
  done
end

locale Requalify_Locale3
begin

typedecl requalify_type2
definition "requalify_const2 == (undefined :: requalify_type2)"

end

context begin interpretation Requalify_Locale3 .

requalify_consts requalify_const2
requalify_types requalify_type2
requalify_facts requalify_const2_def

end

lemma "(requalify_const2 :: requalify_type2) = undefined"
  by (simp add: requalify_const2_def)

context Requalify_Locale3 begin

lemma "(requalify_const2 :: requalify_type2) = undefined"
  by (simp add: requalify_const2_def)

end


end
