(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
