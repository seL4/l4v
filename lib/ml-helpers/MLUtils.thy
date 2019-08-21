(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.

 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.

 * @TAG(DATA61_BSD)
 *)

\<comment>\<open>
  MLUtils is a collection of 'basic' ML utilities (kind of like @{file
  "~~/src/Pure/library.ML"}, but maintained by Trustworthy Systems). If you
  find yourself implementing:
      - A simple data-structure-shuffling task,
      - Something that shows up in the standard library of other functional
        languages, or
      - Something that's "missing" from the general pattern of an Isabelle ML
        library,
  consider adding it here.
\<close>

theory MLUtils
imports Main
begin
ML_file "StringExtras.ML"
ML_file "ListExtras.ML"
ML_file "MethodExtras.ML"
ML_file "OptionExtras.ML"
ML_file "Sum.ML"
end
