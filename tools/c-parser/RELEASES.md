<!--
  Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

  SPDX-License-Identifier: BSD-2-Clause
-->

# StrictC Releases

## 0.1 Disentangle c-parser tech from seL4 verification effort.

- In particular, use standard word types from HOL-Word rather than seL4-specific word types.

## 0.2: First public release

## 0.3

- Fix for bug in guards attached to switch statement expressions.
- Dependency files (with .d extension) don't include references to /home/michaeln

## 0.4

- All files should now be labelled with correct copyright/licence information.

## 0.5

- The types of C arrays now have size types that are numerals rather
  than ugly `tycopy<n>` names.  Unfortunately, the size 8192 has to be
  an exception to this; the corresponding type is called "ty8192".

## 0.6

- More (all?) files appropriately labelled with copyright/licence information.
- Better introduction to using the system in INSTALL/MANIFEST/README
- Some cleanups in the ctranslation document
- Ctranslation document PDF is part of the release
- Regression tests factorial, list_reverse_norm, list_reverse and
  struct_list_reverse all now build.  List reversal was one of the
  examples discussed in our POPL 2007 paper "Types, bytes and
  separation logic".
- Handling of local variable "default initialisation" is now properly
  non-deterministic. This makes it more apparent that depending on
  uninitialised memory is a bad idea.  However, it is not ideal in
  that it still allows the user to conclue that

    int f(void) { int i; return i - i; }

  returns 0, rather than being undefined behaviour.

## 0.7

- Correct bug caused by pathological programs that have no local
  variables, parameters or returns with attached expressions (every
  function is of type taking-void-returning-void).

## 0.7.1

- Correct bug in Makefile controlling build of standalone parser tool.

# 0.7.2

- Adjust source code to be better compatible with Isabelle 2011, removing
  deprecated commands such as "axclass".
- Ensure that tokenizer tool (in standalone-parser directory) builds
  with Poly as well as mlton.

# 1.0

- Builds with isabelle-2011-1 (VER 109)
- Other minor fixes
  - allow break statements within switch statements even if they don't
    appear at the end of the case. (VER 110)
  - fix Makefiles in tools/{mllex,mlyacc} so that those tools can be
    built independently (VER 111)
  - fix casts from "boolean" expressions (e.g. (x > 2)). (VER 92)
  - ensure that guards on switch statements are subjected to integer
    promotions. (VER 39)
  - fix lexing of certain comments. (VER 105)
  - make size_of on known types automatically simplify (VER 125)
  - generate correct guards for double pointer deref (VER 152)
  - use "type_synonym" rather than "types"

## 1.12.0

- Builds with isabelle-2012 (VER 192)

## 1.12.1

- Fixes a problem with non-ASCII #include filenames (VER 224)

## 1.13.0

- Builds with isabelle-2013 (VER 247)
- Implements the C99 _Bool type (VER 254)

## 1.13.1

- Builds with isabelle-2013-{1,2} (VER 331)
- Handles filenames including spaces (VER 307)
- Allows the const keyword in more places (and completely ignores it) (VER 315)
- Fixes the undefinedness guards on shift operations (VER 332)
- Handles Windows-style newlines in C files (VER 336)
- Allows identifiers with leading underscores if the allow_underscore_idents configuration option is set.  This latter can be done with a line like

      declare [[allow_underscore_idents=true]]

- Fixes guards for some nested pointer-dereferences (VER 345)

## 1.14

- Builds with Isabelle2017
- avoid complex call lvals
- add x64 definitions and support for multiple architectures
- improved performance of automatic modifies-proofs
- improved tracing

## 1.15

- Builds with Isabelle2018
- update documentation
- always attach GCC attributes to vars in the AST

## 1.16

- Builds with Isabelle2019
- added syntax for displaying pointer types (PTR and PTR_COERCE)
- always emit long (type-wrangled) variable names,
  provide short names as abbreviation

## 1.16.1

- Correct license for shorten_names.ML. No code changes.

## 1.17

- Builds with Isabelle2020
- Faster automation for proving packed_type class instances
- Remove unused assumptions from field_lookup rules
- Use python3 in scripts
- Use SPDX identifiers for licensing information

## 1.18

- Builds with Isabelle2021
- improve inline assembly support in modifies proofs
- always use fresh names for generated temporary variables.
  This fixes a problem that could make some function call expressions unprovable. (VER-1389)
- improve compile time performance for functional record update definitions

## 1.19

- Builds with Isabelle2021-1
- setup for AARCH64/ARM64 targets
- AST printing for top-level declarations annotated to make them easier to
  consume in external tools. Annotations take the form:

      ##<decl_type>: <name>

  e.g. `##Function: ctzl`

## 1.20

- Builds with Isabelle2023
- Rearranged library session structure and included more libraries for heap
  reasoning in the release. See e.g. files TypHeapLib.thy and LemmaBucket_C.thy

## 1.21

- Builds with Isabelle2024
- Updated SIMPL from the AFP
- Ensure that umm_types.txt is saved relative to theory file
- If cpp_path is relative, make it relative to the current theory
