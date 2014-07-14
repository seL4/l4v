(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Turning of abbreviation contraction can speed up the display of large terms.
 *
 * usage:
 *   ML_file "l4.verified/lib/show_abbrevs.ML";
 * 
 * To turn them back on:
 *   ML {* show_abbrevs true; *}
 *)

fun show_abbrevs true = (PrintMode.print_mode := List.filter
                           ((curry op<>) "no_abbrevs")
                           (!PrintMode.print_mode))
  | show_abbrevs false = (PrintMode.print_mode := "no_abbrevs"::
                            (!PrintMode.print_mode))

val () = show_abbrevs false;

