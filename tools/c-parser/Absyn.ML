(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)


signature ABSYN =
sig
  include REGION_EXTRAS
  include CTYPE
  include EXPR
  include STMT_DECL
end


structure Absyn : ABSYN =
struct

open RegionExtras
open CType
open Expr
open StmtDecl

end; (* struct *)

(* Local variables: *)
(* mode: sml *)
(* End: *)
