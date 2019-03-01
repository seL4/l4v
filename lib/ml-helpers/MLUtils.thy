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

  When appropriate, you should consider *extending* an existing signature,
  rather than creating a new one: `String.whatever` is more meaningful than
  `TSStringLib.whatever`, and it doesn't damage the bindings to the "original"
  signature in any way. Look at `String.ML` in this directory for an example.

  Some structures (like `Method`) can't be overridden this way. In these cases
  name the new structure with a `Utils` suffix.
\<close>

theory MLUtils
imports Main
begin
ML_file "String.ML"
ML_file "List.ML"
ML_file "Method.ML"
end
