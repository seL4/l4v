(*
 * Copyright 2024, Proofcraft Pty Ltd
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Requalify_Test
imports Lib.Requalify
begin

section \<open>Tests and examples for requalify commands\<close>

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

(* this is equivalent to doing the requalifications in the original locale context *)
context Requalify_Example1 begin
requalify_types (in Requalify_Example2) ex1_type
requalify_consts (in Requalify_Example2) ex1_const
requalify_facts (in Requalify_Example2) ex1_const_def
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
   Arch locale that's supposed to hide some architecture-specific details, and a name
   prefix of BOARD for a specific architecture. Let's also say we have a constant, that has
   both a generic and arch-specific component (the former calling the latter). *)

lemma requalify_collision:
  "False = False"
  by simp

locale Arch

context Arch begin global_naming BOARD

lemma requalify_collision:
  "True = True"
  by simp

definition
  "const_collision \<equiv> 1000 :: nat"

end

definition
  "const_collision \<equiv> 1 + BOARD.const_collision"

(* If we access the names, we get what we expect: *)
thm requalify_collision    (* False = False *)
term const_collision       (* const_collision (global) *)
term BOARD.const_collision (* BOARD.const_collision (arch-specific) *)

(* Exporting requalify_collision and const_collision to the theory context would now be ill-advised,
   as it would make the global names inconvenient to access. What makes more sense is to export them
   such that we can access the architecture specific names under Arch (and not talk about the
   specific board), while maintaining access to the global name. Let's try: *)

requalify_consts (in Arch) BOARD.const_collision
requalify_facts (in Arch) BOARD.requalify_collision

(* global context: good *)
thm requalify_collision (* False = False *)
thm Arch.requalify_collision (* True = True *)
term const_collision (* global *)

(* context post-interpretation: we don't have convenient access to the global names anymore *)
context begin interpretation Arch .
thm requalify_collision (* True = True *)
thm Arch.requalify_collision (* True = True *)
term const_collision (* local.const_collision (arch-specific) *)
term Arch.const_collision (* local.const_collision (arch-specific) *)
end

(* This is because whatever name was last interpreted takes precedence. If we want to fix this, we
   need to re-export the global names *from* the Arch locale.
   By convention we also give them a "global." prefix: *)
context Arch begin
  context begin global_naming global
  requalify_facts (aliasing) Requalify_Test.requalify_collision
  requalify_consts (aliasing) Requalify_Test.const_collision
  end
end

(* After this convolution, the names are now consistently available: *)

(* globally *)
term const_collision (* global.const_collision *)
term global.const_collision (* global.const_collision *)
term Arch.const_collision (* Arch.const_collision *)
thm requalify_collision (* False = False *)
thm global.requalify_collision (* False = False *)
thm Arch.requalify_collision (* True = True *)

(* when interpreted *)
context begin interpretation Arch .
term const_collision (* global.const_collision *)
term global.const_collision (* global.const_collision *)
term Arch.const_collision (* Arch.const_collision *)
thm requalify_collision (* False = False *)
thm global.requalify_collision (* False = False *)
thm Arch.requalify_collision (* True = True *)
end

(* and in the locale context *)
context Arch begin
term const_collision (* global.const_collision *)
term global.const_collision (* global.const_collision *)
term Arch.const_collision (* Arch.const_collision *)
thm requalify_collision (* False = False *)
thm global.requalify_collision (* False = False *)
thm Arch.requalify_collision (* True = True *)
end

(* Unfortunately, using named_theorems temporarily causes some internal fact name reordering.
   Consts are not affected by this. *)

(* when interpreted *)
context begin interpretation Arch .
thm requalify_collision (* False = False as expected*)
named_theorems Some_assms
thm requalify_collision (* REORDERED: should be False = False *)
thm global.requalify_collision (* False = False *)
thm Arch.requalify_collision (* True = True *)
term const_collision (* still global.const_collision *)
end

(* and in the locale context *)
context Arch begin
thm requalify_collision (* False = False as expected*)
named_theorems Some_assms2
thm requalify_collision (* REORDERED: should be False = False *)
thm global.requalify_collision (* False = False *)
thm Arch.requalify_collision (* True = True *)
term const_collision (* still global.const_collision *)
end

(* the effect lasts until the end of the context block containing named_theorems *)
context Arch begin
thm requalify_collision (* WORKS AGAIN: False = False *)
thm global.requalify_collision (* False = False *)
thm Arch.requalify_collision (* True = True *)
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

context Arch begin
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
arch_requalify_consts (in Arch) (A) arch_specific_const_a

(* this now works *)
term Arch.arch_specific_const_a


section "Specific tests"

subsection \<open>Temporary requalification of, hiding of, and re-exposing of constants\<close>

(* This kind of approach can be used for tools such at the C Parser, which are not aware of the Arch
   locale and might need to refer to constants directly in internal annotations. *)

context Arch begin arch_global_naming
datatype vmpage_size =
    ARCHSmallPage
end
arch_requalify_types vmpage_size

context Arch begin global_naming vmpage_size
requalify_consts ARCHSmallPage
end

(* both now visible in generic context *)
typ vmpage_size
term vmpage_size.ARCHSmallPage
term ARCHSmallPage (* note: the direct constructor name is not accessible due to qualified export *)

(* temporary global exposure is done, hide vmpage sizes again *)
hide_const
  vmpage_size.ARCHSmallPage

find_consts name:ARCHSmallPage
(* finds one constant (despite it being hidden), e.g. on ARM:
   Requalify.ARM.vmpage_size.ARMSmallPage :: "vmpage_size"
   but note that this constant is inaccessible from theory scope:
   term Requalify_Test.AARCH64.vmpage_size.ARCHSmallPage
   will result in Inaccessible constant: "Requalify_Test.ARM.vmpage_size.ARCHSmallPage" *)

(* Arch-specific, in actual use replace ARCH with actual architecture such as ARM *)
context Arch begin
term vmpage_size.ARCHSmallPage (* despite being hidden in theory scope, it's still visible in Arch *)
global_naming "ARCH.vmpage_size" requalify_consts ARCHSmallPage
global_naming "ARCH" requalify_consts ARCHSmallPage
end

term ARCH.ARCHSmallPage (* now accessible under specific qualified name *)
term ARCH.vmpage_size.ARCHSmallPage (* now accessible under specific qualified name *)
term Requalify_Test.ARCH.vmpage_size.ARCHSmallPage (* fully qualified name *)
(* but be aware, these are only aliases to the original constant! *)
find_consts name:ARCHSmallPage (* still only Requalify_Test.ARM.vmpage_size.ARCHSmallPage *)


section "Misc tests / usage examples"

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
  and f2: "requalify_test_f Requalify_Locale2.requalify_const Requalify_Test.requalify_const"
  shows "requalify_test_f Requalify_Locale2.requalify_const requalify_const" "requalify_const = undefined"
  apply (rule f1)?
  apply (rule f2)
  apply (simp add: requalify_const_def)
  done

context Requalify_Locale begin

lemma
  assumes f1: "requalify_test_f requalify_const Requalify_Locale2.requalify_const"
  and f2: "requalify_test_f Requalify_Locale2.requalify_const Requalify_Test.requalify_const"
  shows "requalify_test_f Requalify_Locale2.requalify_const requalify_const" "requalify_const = undefined"
  apply (rule f2)?
  apply (rule f1)
  apply (simp add: requalify_const_def)
  done

end

context Requalify_Locale begin global_naming global

requalify_consts Requalify_Test.requalify_const
requalify_types Requalify_Test.requalify_type
requalify_facts Requalify_Test.requalify_const_def

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
