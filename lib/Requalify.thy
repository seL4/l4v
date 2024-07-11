(*
 * Copyright 2024, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

(*
  Requalify constants, types and facts into the current naming.
  Includes command variants that support implicitly using the L4V_ARCH environment variable.
*)

theory Requalify
imports Main
keywords "requalify_facts" :: thy_decl
     and "requalify_types" :: thy_decl
     and "requalify_consts" :: thy_decl
     and "global_naming" :: thy_decl
     and "arch_requalify_facts" :: thy_decl
     and "arch_requalify_types" :: thy_decl
     and "arch_requalify_consts" :: thy_decl
     and "arch_global_naming" :: thy_decl
begin

ML \<open>

local

fun all_facts_of ctxt =
  Proof_Context.theory_of ctxt
  |> Global_Theory.facts_of
  |> Facts.dest_static false [];

fun tl' (_ :: xs) = xs
  | tl' _ = []

(* Alias binding to fully-qualified name "name" in both global and local context *)
fun bind_alias global_alias_fn local_alias_fn binding (name : string) =
  Local_Theory.declaration {syntax = false, pos = Position.none, pervasive = true} (fn phi =>
    let val binding' = Morphism.binding phi binding;
    in Context.mapping (global_alias_fn binding' name) (local_alias_fn binding' name) end);

(* Instantiate global and local aliasing functions for consts, types and facts *)
val const_alias = bind_alias Sign.const_alias Proof_Context.const_alias;
val type_alias = bind_alias Sign.type_alias Proof_Context.type_alias;
val alias_fact = bind_alias Global_Theory.alias_fact Proof_Context.alias_fact;

(* Locate global fact matching supplied name.
   When we specify a fact name that resolves to a global name, return the normal fact lookup result.
   Note: Locale_Name.fact_name outside the locale resolves to a global name.

   When we are inside a locale, the lookup is more interesting. Supplying "short_name" will result
   in "local.short_name", which we then need to match to some name in the global context. We do
   this by going through *all* the fact names in the current context, searching for matches
   of the form "X.Y.short_name", where we hope X is some theory, and Y is some locale.

   Since "X.Y.short_name" is not sufficiently unique, we must also check that the theorems under
   the discovered name match the ones under "local.short_name". *)
fun global_fact ctxt nm =
let
   val facts = Proof_Context.facts_of ctxt;
   val {name, thms, ...} = (Facts.retrieve (Context.Proof ctxt) facts (nm, Position.none));

   fun matches suffix (global_name, global_thms) =
     suffix = (Long_Name.explode global_name |> tl' |> tl' |> Long_Name.implode)
     andalso eq_list (Thm.equiv_thm (Proof_Context.theory_of ctxt)) (thms, global_thms)
in
  case Long_Name.dest_local name of
    NONE => (name, thms)
  | SOME suffix =>
     (case (find_first (matches suffix) (all_facts_of ctxt)) of
        SOME x => x
      | NONE => raise Fail ("Couldn't find global equivalent of local fact: " ^ nm))
end

val alias = Parse.reserved "aliasing" >> K true
val alias_default = false

(* (aliasing) only *)
val generic_options = Scan.optional (Args.parens alias >> (fn x => (x, ""))) (alias_default, "")

(* e.g. ARM, ARM_A, ARM_H *)
val arch_suffix = ((Parse.reserved "A" || Parse.reserved "H") >> (fn s =>  "_" ^ s))
fun arch_prefix suffix = getenv_strict "L4V_ARCH" ^ suffix

(* ([aliasing][,] [A|H]) in that order *)
val arch_options =
  Scan.optional (
   Args.parens (
     (alias --| Parse.$$$ "," -- arch_suffix)
     || (alias >> (fn x => (x, "")))
     || (arch_suffix >> (fn x => (alias_default, x)))
   )) (alias_default, "")

val arch_global_opts = Scan.optional (Args.parens arch_suffix) ""

in

fun gen_requalify get_proper_nm parse_nm check_parsed_nm alias_fn arch =
let
  val options = if arch then arch_options else generic_options
in
  (Parse.opt_target -- options --  Scan.repeat1 (Parse.position (Scan.ahead parse_nm -- Parse.name))
   >> (fn ((target, (aliasing, arch_suffix)), names) =>
       Toplevel.local_theory NONE target (fn lthy =>
       let
         val global_ctxt = Proof_Context.theory_of lthy |> Proof_Context.init_global

         fun requalify_entry ((entry, orig_name), pos) lthy =
         let
           val name = if arch then arch_prefix arch_suffix ^ "." ^ orig_name else orig_name
           val local_name = get_proper_nm lthy name;
           val _ = check_parsed_nm lthy (entry, (local_name, pos));

           (* Check whether the short (base) name is already available in theory context if no
              locale target is supplied and the "aliasing" option is not supplied.
              Note: currently no name collision warning when exporting into locale *)
           val base_name = Long_Name.base_name name;
           val global_base = try (get_proper_nm global_ctxt) (Long_Name.base_name name);
           val _ = (case (global_base, target, aliasing) of
                      (SOME _, NONE, false) => warning ("Name \"" ^ base_name
                                                        ^ "\" already exists in theory context")
                    | _ => ())

           val b = Binding.make (base_name, pos)
           val lthy' = lthy |> alias_fn b local_name
         in lthy' end
       in fold requalify_entry names lthy end)))
end

local

val get_const_nm = ((fst o dest_Const) oo (Proof_Context.read_const {proper = true, strict = false}))
val get_type_nm = ((fst o dest_Type) oo (Proof_Context.read_type_name {proper = true, strict = false}))
val get_fact_nm = (fst oo global_fact)

(* For a theorem name, we want to additionally make sure that global fact names found by
   global_fact are accessible in the current context. *)
fun check_fact lthy (_, (nm, pos)) = Proof_Context.get_fact lthy (Facts.Named ((nm,pos), NONE))

in

val _ =
  Outer_Syntax.command @{command_keyword requalify_consts} "alias const with current naming"
    (gen_requalify get_const_nm Parse.const (fn lthy => fn (e, _) => get_const_nm lthy e) const_alias
                   false)

val _ =
  Outer_Syntax.command @{command_keyword requalify_types} "alias type with current naming"
    (gen_requalify get_type_nm Parse.typ (fn lthy => fn (e, _) => get_type_nm lthy e) type_alias
                   false)

val _ =
  Outer_Syntax.command @{command_keyword requalify_facts} "alias fact with current naming"
    (gen_requalify get_fact_nm Parse.thm check_fact alias_fact false)

val _ =
  Outer_Syntax.command @{command_keyword global_naming} "change global naming of context block"
    (Parse.binding >> (fn naming =>
      Toplevel.local_theory NONE NONE
        (Local_Theory.map_background_naming (Name_Space.parent_path
                                             #> Name_Space.qualified_path true naming))))

(* Arch variants use the L4V_ARCH variable and an additional A/H option, so that when L4V_ARCH=ARM
   "arch_requalify_consts (H) const" becomes "requalify_consts ARM_H.const"
   This allows them to be used in a architecture-generic theory.

   For consts and types, we don't perform extra checking on the results of Parse.const and Parse.typ
   because their "strings" contain embedded syntax, which means prepending a normal string to them
   causes malformed syntax and YXML exceptions. It shouldn't matter, we are looking up the name and
   checking it's a constant/type anyway. *)

val _ =
  Outer_Syntax.command @{command_keyword arch_requalify_consts}
    "alias const with current naming, but prepend \"($L4V_ARCH)_[A|H].\" using env. variable"
    (gen_requalify get_const_nm Parse.const (fn _ => fn (_, _) => ()) const_alias
                   true)

val _ =
  Outer_Syntax.command @{command_keyword arch_requalify_types}
    "alias type with current naming, but prepend \"($L4V_ARCH)_[A|H].\" using env. variable"
    (gen_requalify get_type_nm Parse.typ (fn _ => fn (_, _) => ()) type_alias
                   true)

val _ =
  Outer_Syntax.command @{command_keyword arch_requalify_facts}
    "alias fact with current naming, but prepend \"($L4V_ARCH)_[A|H].\" using env. variable"
    (gen_requalify get_fact_nm Parse.thm check_fact alias_fact true)

val _ =
  Outer_Syntax.command @{command_keyword arch_global_naming}
    "change global naming of context block to \"($L4V_ARCH)_[A|H]\" using env. variable"
    (arch_global_opts  >> (fn arch_suffix =>
      Toplevel.local_theory NONE NONE
        (Local_Theory.map_background_naming
          (Name_Space.parent_path
           #> Name_Space.qualified_path true (Binding.make (arch_prefix arch_suffix, @{here}))))))

end

end
\<close>

section \<open>Tests and examples\<close>

subsection \<open>Generic\<close>

subsubsection \<open>Exporting types, constants and facts from a locale into the theory context\<close>

locale Requalify_Example1

context Requalify_Example1 begin
typedecl ex1_type
definition "ex1_const \<equiv> undefined :: ex1_type"
end

(* these will all generate errors:
typ ex1_type
term "ex1_const :: ex1_type"
thm ex1_const_def
*)

typ Requalify_Example1.ex1_type
term "Requalify_Example1.ex1_const :: Requalify_Example1.ex1_type"
thm Requalify_Example1.ex1_const_def

(* exporting will make types/consts/facts available *)

requalify_types Requalify_Example1.ex1_type
typ ex1_type

requalify_consts Requalify_Example1.ex1_const
term "ex1_const :: ex1_type"

requalify_facts Requalify_Example1.ex1_const_def
thm ex1_const_def

(* trying to export into theory context that already has that name will result in warnings *)
requalify_types Requalify_Example1.ex1_type
requalify_consts Requalify_Example1.ex1_const
requalify_facts Requalify_Example1.ex1_const_def

(* warnings can be suppressed if naming collision is on purpose, but see caveats in next sections *)
requalify_types (aliasing) Requalify_Example1.ex1_type
requalify_consts (aliasing) Requalify_Example1.ex1_const
requalify_facts (aliasing) Requalify_Example1.ex1_const_def

(* requalification can also occur via interpretation, using internal names, but this is slower *)
context begin interpretation Requalify_Example1 .
requalify_types ex1_type
requalify_consts ex1_const
requalify_facts ex1_const_def
end


subsubsection \<open>Exporting types, constants and facts from a locale into a locale context\<close>

locale Requalify_Example2

(* the target of the export can be a locale (this mode cannot be used from an interpretation) *)

requalify_types (in Requalify_Example2) Requalify_Example1.ex1_type
requalify_consts (in Requalify_Example2) Requalify_Example1.ex1_const
requalify_facts (in Requalify_Example2) Requalify_Example1.ex1_const_def

(* this is equivalent to doing the requalifications in the locale context *)
context Requalify_Example2 begin
requalify_types (in Requalify_Example2) Requalify_Example1.ex1_type
requalify_consts (in Requalify_Example2) Requalify_Example1.ex1_const
requalify_facts (in Requalify_Example2) Requalify_Example1.ex1_const_def
end

typ Requalify_Example2.ex1_type
term "Requalify_Example2.ex1_const :: Requalify_Example2.ex1_type"
thm Requalify_Example2.ex1_const_def

(* unfortunately, there is currently no warning on name collisions into locales *)
requalify_types (in Requalify_Example2) Requalify_Example1.ex1_type (* no warning *)
requalify_consts (in Requalify_Example2) Requalify_Example1.ex1_const (* no warning *)
requalify_facts (in Requalify_Example2) Requalify_Example1.ex1_const_def (* no warning *)


subsubsection \<open>Using global naming to ensure a name prefix within a locale\<close>

locale Requalify_Example_G

context Requalify_Example_G begin global_naming EXAMPLE1
typedecl ex_g_type
definition "ex_g_const \<equiv> undefined :: ex_g_type"
end

(* note the prefixed names in the global context *)
typ EXAMPLE1.ex_g_type
term "EXAMPLE1.ex_g_const :: EXAMPLE1.ex_g_type"
thm EXAMPLE1.ex_g_const_def

(* the locale names will not work, these will all generate errors:
typ Requalify_Example_G.ex_g_type
term "Requalify_Example_G.ex_g_const :: Requalify_Example_G.ex_g_type"
thm Requalify_Example_G.ex_g_const_def
*)

(* Looking up the local unprefixed name inside the locale will work as expected *)
context Requalify_Example_G begin
thm ex_g_const_def
end

(* using the new name, we can export as usual: *)
requalify_types EXAMPLE1.ex_g_type
requalify_consts EXAMPLE1.ex_g_const
requalify_facts EXAMPLE1.ex_g_const_def

(* inside a locale interpretation, the names can be accessed without a prefix *)
context begin interpretation Requalify_Example_G .
requalify_types ex_g_type
requalify_consts ex_g_const
requalify_facts ex_g_const_def
end

(* We can also re-export the name to the same locale in order to make an un-prefixed alias *)
requalify_types (in Requalify_Example_G) EXAMPLE1.ex_g_type
requalify_consts (in Requalify_Example_G) EXAMPLE1.ex_g_const
requalify_facts (in Requalify_Example_G) EXAMPLE1.ex_g_const_def

(* This makes the names available via the locale name as well *)
typ Requalify_Example_G.ex_g_type
term "Requalify_Example_G.ex_g_const :: Requalify_Example_G.ex_g_type"
thm Requalify_Example_G.ex_g_const_def


subsubsection \<open>Managing collisions and global naming\<close>

(* In previous sections we generated collisions by repeatedly exporting the same thing.
   Generally, exporting the same name from a locale into the global context is not advised,
   as it will only cause confusion.

   However, a more realistic example is when global_naming is involved. Let's say we have a
   Fake_Arch locale that's supposed to hide some architecture-specific details, and a name
   prefix of FAKE_BOARD for a specific architecture. It makes more sense with constants and types,
   but those are harder to tell apart in a demo.
*)

lemma requalify_collision:
  "False = False"
  by simp

locale Fake_Arch

context Fake_Arch begin global_naming FAKE_BOARD
lemma requalify_collision:
  "True = True"
  by simp
end

(* If we access the name, we get what we expect: *)
thm requalify_collision (* False = False *)

(* Exporting requalify_collision to the theory context would now be ill-advised, as it would
   make the global name inconvenient to access. What makes more sense is to export it such
   that we can access the architecture specific name under Fake_Arch (and not talk about the
   specific board), while maintaining access to the global name. Let's try: *)

requalify_facts (in Fake_Arch) FAKE_BOARD.requalify_collision

(* global context: good *)
thm requalify_collision (* False = False *)
thm Fake_Arch.requalify_collision (* True = True *)

(* context post-interpretation: we don't have convenient access to the global name anymore *)
context begin interpretation Fake_Arch .
thm requalify_collision (* True = True *)
thm Fake_Arch.requalify_collision (* True = True *)
end

(* This is because whatever name was last interpreted takes precedence. If we want to fix this, we
   need to re-export the global name *from* the Fake_Arch locale.
   By convention we also give it a "global." prefix: *)
context Fake_Arch begin
  context begin global_naming global
  requalify_facts (aliasing) Requalify.requalify_collision
  end
end

(* After this convolution, the names are now consistently available: *)

(* globally *)
thm requalify_collision (* False = False *)
thm global.requalify_collision (* False = False *)
thm Fake_Arch.requalify_collision (* True = True *)

(* when interpreted *)
context begin interpretation Fake_Arch .
thm requalify_collision (* False = False *)
thm global.requalify_collision (* False = False *)
thm Fake_Arch.requalify_collision (* True = True *)
end

(* and in the locale context *)
context Fake_Arch begin
thm requalify_collision (* False = False *)
thm global.requalify_collision (* False = False *)
thm Fake_Arch.requalify_collision (* True = True *)
end


subsection \<open>Architecture-specific (requires L4V_ARCH environment variable set to work)\<close>

(* The above documentation and examples attempted to be somewhat generic. In the seL4 verification
   repository, we have a specific setup:

   * A number of architectures (e.g. ARM, ARM_HYP, RISCV64, X64, AARCH64) parametrised by the
     L4V_ARCH environment variable.
   * An Arch locale for containing architecture-specific definitions, types and proofs, wherein
     global naming wraps the architecture as follows:
     * ($L4V_ARCH)_A for the Abstract spec (e.g. ARM_A)
     * ($L4V_ARCH)_H for the Haskell spec (e.g. ARM_H)
     * as per L4V_ARCH for everything else (e.g. ARM) (though other namespaces may appear in future)

   The arch_requalify and arch_global_naming variants lean on this, by being able to generically
   say something about a requirement each specific architecture needs to fulfill.
*)

context Fake_Arch begin
  arch_global_naming (* equivalent to "global_naming ARM" on ARM *)
  typedecl arch_specific_type
  definition "arch_specific_const \<equiv> undefined :: arch_specific_type"
  lemma arch_specific_lemma: "arch_specific_const = arch_specific_const" by simp

  arch_global_naming (A) (* equivalent to "global_naming ARM_A" on ARM *)
  definition "arch_specific_const_a \<equiv> undefined :: arch_specific_type"

  arch_global_naming (H) (* equivalent to "global_naming ARM_A" on ARM *)
  definition "arch_specific_const_h \<equiv> undefined :: arch_specific_type"
end

(* confirm these are the ARM, ARM_A, and ARM_H prefixes respectively: *)
find_theorems name:arch_specific_const

(* we requalify these prefixed constants without knowing what arch we are on: *)
arch_requalify_types arch_specific_type
arch_requalify_consts arch_specific_const
arch_requalify_facts arch_specific_lemma
arch_requalify_consts (A) arch_specific_const_a
arch_requalify_consts (H) arch_specific_const_h
arch_requalify_consts (H) arch_specific_const_h (* warnings work as usual *)
arch_requalify_consts (aliasing, H) arch_specific_const_h (* warnings suppression *)

(* this has placed all names into the global context *)
typ arch_specific_type
thm arch_specific_lemma
term "arch_specific_const :: arch_specific_type"
term "arch_specific_const_a :: arch_specific_type"
term "arch_specific_const_h :: arch_specific_type"

(* If we wish to create a generic name that does not compete with a global name, we need to export
   into the Arch locale, then fix up the interpretation order of any collisions as described in
   "Managing collisions and global naming" *)
arch_requalify_consts (in Fake_Arch) (A) arch_specific_const_a

(* this now works *)
term Fake_Arch.arch_specific_const_a

(* FIXME: this is dumping a bit much into the global context, might best be moved to a test file.
   Moving to a test file would also allow us to use Arch locale for Arch examples. *)

section "WUT"
(* FIXME: what do I do with these? I understand what they do, but they aren't conducive to
   understanding anything. *)

(* Extra Tests and examples *)


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
