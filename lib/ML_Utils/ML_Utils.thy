(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

\<comment>\<open>
  ML_Utils is a collection of 'basic' ML utilities (kind of like @{file
  "~~/src/Pure/library.ML"}, but maintained by Trustworthy Systems). If you
  find yourself implementing:
      - A simple data-structure-shuffling task,
      - Something that shows up in the standard library of other functional
        languages, or
      - Something that's "missing" from the general pattern of an Isabelle ML
        library,
  consider adding it here.
\<close>

theory ML_Utils
imports Main
begin
ML_file "StringExtras.ML"
ML_file "ListExtras.ML"
ML_file "MethodExtras.ML"
ML_file "OptionExtras.ML"
ML_file "ThmExtras.ML"
ML_file "Sum.ML"
ML_file "TermExtras.ML"
end
