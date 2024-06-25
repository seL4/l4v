(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *
 * Copyright 2001 John Hurd
 * SPDX-License-Identifier: BSD-3-Clause
 *)

signature STRING_EXTRAS =
sig
  (*
    `split sep s` returns the list of substrings of `s` that are
    separated by `sep`. For example:

    `split ":" "hello:world" = ["hello", "world"]`
    `split "foo" "barbaz" = ["barbaz"]`
  *)
  val split: string -> string -> string list
end

structure StringExtras: STRING_EXTRAS =
struct

\<comment>\<open>
  Copied from @{file "~~/src/Tools/Metis/src/Useful.sml"}.
\<close>
local
  fun match [] l = SOME l
    | match _ [] = NONE
    | match (x :: xs) (y :: ys) = if x = y then match xs ys else NONE;

  fun stringify acc [] = acc
    | stringify acc (h :: t) = stringify (String.implode h :: acc) t;
in
  fun split (sep: string) (s: string) =
      let
        val pat = String.explode sep

        fun div1 prev recent [] = stringify [] (List.rev recent :: prev)
          | div1 prev recent (l as h :: t) =
            case match pat l of
              NONE => div1 prev (h :: recent) t
            | SOME rest => div1 (List.rev recent :: prev) [] rest
      in
        div1 [] [] (String.explode s)
      end;
end;

end;
