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
 * Extend a locale by seamlessly generating sublocales.
 *)

theory Extend_Locale
imports Main Defs
keywords "extend_locale" :: thy_decl
begin

ML \<open>
fun note_new_facts prev_lthy (lthy : local_theory) =
let
  val facts = Proof_Context.facts_of lthy;

  val local_facts = Facts.dest_static false [Proof_Context.facts_of prev_lthy] facts;

  val space = Facts.space_of (Proof_Context.facts_of lthy);

  fun make_binding (long_name, pos) =
    let val (qualifier, name) = split_last (Long_Name.explode long_name)
    in fold (Binding.qualify true) qualifier (Binding.make (name, pos)) end;

  fun add_entry (nm, thms) lthy =
     let
       val extern_nm = Name_Space.extern_shortest lthy space nm;
       val {pos, ...} = Name_Space.the_entry space nm;
       val b = make_binding (extern_nm, pos);
       val (_, lthy') =  Local_Theory.note ((b,[]),thms) lthy;
     in lthy' end

in fold add_entry local_facts lthy end;
\<close>

ML \<open>

val _ =
  Outer_Syntax.command @{command_keyword extend_locale} "extend current locale"
    (Parse.opt_target -- (Scan.repeat1 Parse_Spec.context_element) >> (fn (target, (elems)) =>
      (Toplevel.local_theory NONE target (fn lthy =>
      let
        val locale_name = case Named_Target.locale_of lthy of SOME x => x | NONE => error "Not in a locale!"
        val binding = Binding.make (Long_Name.base_name locale_name, Position.none)

        val chunkN = "extchunk_"

        val last_chunk =
          case Long_Name.explode locale_name of
            [_, chunk, _] => (unprefix chunkN chunk |> Int.fromString |> the)
            | [_, _] => 0
            | _ => raise Fail ("Unexpected locale naming scheme:" ^ locale_name)

        val chunk = Int.toString (last_chunk + 1)


        val (next_locale_name, lthy') = lthy
          |> Local_Theory.map_background_naming
               (Name_Space.parent_path #> Name_Space.add_path (chunkN ^ chunk))
          |> Local_Theory.background_theory_result
               (Expression.add_locale_cmd binding binding
                  ([((locale_name,Position.none), (("#",false), (Expression.Positional [],[])))], []) elems
                 ##> Local_Theory.exit_global)
          ||> Local_Theory.restore_background_naming lthy


        val lthy'' = lthy'
          |> Local_Theory.exit_global
          |> Named_Target.init next_locale_name

      in lthy'' end)
      )));

\<close>

locale Internal begin
  definition "internal_const1 = True"
  definition "internal_const2 = False"
end

locale Generic
begin

definition "generic_const = ((\<forall>x :: nat. x \<noteq> x))"

extend_locale
  assumes asm_1: "Internal.internal_const1 = (\<forall>x :: nat. x = x)"

lemma generic_lemma_1: "Internal.internal_const1"
  apply (insert asm_1)
  apply simp
  done

extend_locale
  assumes asm_2: "\<not> Internal.internal_const2"

lemma generic_lemma_2: "generic_const = Internal.internal_const2"
  by (simp add: asm_2 generic_const_def)

extend_locale
  fixes param_const_1 :: nat
  assumes asm_3: "param_const_1 > 0"

lemma generic_lemma_3: "param_const_1 \<noteq> 0"
  by (simp add: asm_3)

extend_locale
  assumes asm_4: "\<not> generic_const"

lemma generic_lemma_4: "generic_const = Internal.internal_const2"
  by (simp add: asm_4 asm_2 generic_lemma_2)

extend_locale
  assumes asm_4: "x = param_const_1 \<Longrightarrow> y > x \<Longrightarrow> y > 1"


end

context Internal begin

lemma internal_lemma1: "internal_const1 = (\<forall>x :: nat. x = x)" by (simp add: internal_const1_def)

lemma internal_lemma2: "\<not> internal_const2" by (simp add: internal_const2_def)

lemma internal_lemma3: "\<not> Generic.generic_const" by (simp add: Generic.generic_const_def)

definition "internal_const3 = (1 :: nat)"

lemma internal_lemma4: "internal_const3 > 0" by (simp add: internal_const3_def)

lemma asm_4: "x = internal_const3 \<Longrightarrow> y > x \<Longrightarrow> y > 1"
  by (simp add: internal_const3_def)

end

interpretation Generic
 where param_const_1 = Internal.internal_const3
  subgoal
  proof -
  interpret Internal .
  show ?thesis
    (* annoyingly, the proof method "fact" no longer has access to facts produced by "interpret" *)
    apply (intro_locales; unfold_locales)
        apply (rule internal_lemma1)
       apply (rule internal_lemma2)
      apply (rule internal_lemma4)
     apply (rule internal_lemma3)
    apply (erule (1) asm_4)
    done
  qed
  done

context Internal begin

lemma internal_lemma5:
  "internal_const3 \<noteq> 0"
  by (rule generic_lemma_3)

end


end
