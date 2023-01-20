(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

text \<open>
  mk_term: ML antiquotation for building and splicing terms.
\<close>
theory MkTermAntiquote_Tests
imports
  MkTermAntiquote
  Main (* MkTermAntiquote imports only Pure *)
begin

text \<open>
  Basic usage: \<open>@{mk_term "pattern..." (vars, ...)} (args, ...)\<close>

  The vars should match schematic vars in the pattern, and they
  are substituted with the given arguments.

  Template vars can include type vars, and they should be applied
  to type arguments.
\<close>

ML_val \<open>
@{assert} (@{mk_term "?x" (x)} @{term "x::'a"}
           = @{term "x::'a"});

@{assert} (@{mk_term "0::'a::zero" ('a)} @{typ "nat"}
           = @{term "0::nat"});

(* Tuples are used to pass multiple arguments *)
@{assert} (@{mk_term "?xs @ ?ys" (ys, xs)} (@{term "[True]"}, @{term "[False]"})
           = @{term "[False] @ [True]"});
\<close>

text \<open>
  Note that mk_term does not perform full type inference automatically.
  If some argument types are mismatched or too general, the output may
  be inconsistent. This may change in future versions.
\<close>
ML_val \<open>
@{assert} (@{mk_term "?x = ?y" (x, y)} (@{term "0::'a::zero"}, @{term "Suc 0"})
           = (Const (@{const_name HOL.eq}, @{typ "'a::zero \<Rightarrow> 'a \<Rightarrow> bool"}) $
                @{term "0::'a::zero"} $ @{term "Suc 0"}))
\<close>

text \<open>
  Besides static checking, using mk_term also gives a reusable template:
\<close>

ML_val \<open>
let
  val mk_pair: term*term -> term = @{mk_term "(?a, ?b)" (a, b)};
in
   @{assert} (mk_pair (@{term "()"}, @{term "True"}) = @{term "((), True)"});
   @{assert} (mk_pair (@{term "int 1"}, @{term "int 2"})
              = @{term "(int 1, int 2)"})
end;
\<close>

end