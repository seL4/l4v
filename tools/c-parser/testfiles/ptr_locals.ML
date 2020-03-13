(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

val result = state "testfiles/ptr_locals.c";

local
      open CalculateState TermsTypes NameGeneration
      val INTINFO ii = std_types_IntInfo
      val int_refname = heapreftype_name "int"
      val intptrrefname = heapreftype_name "int_ptr"
      val int_refty = Type(int_refname, [])
      val intptrrefty = Type(intptrrefname, [])
      val int = #ity ii
      val expected_result =
          [vdecl (global_var "x", int, true),
           refinstance int_refname,
           vdecl (heap_var_name "int", int_refty --> int, true),
           vdecl (global_var "ptr", int_refty, true),
           vdecl (global_var "array", mk_list_type int, true),
           vdecl (local_var "f" return_var_name, int_refty, false),
           refinstance intptrrefname,
           vdecl (heap_var_name "int_ptr", intptrrefty --> int_refty, true),
           vdecl (local_var "f" "p", intptrrefty, false),
           vdecl (local_var "f" "ptrarray", mk_list_type int_refty, false)
           ]
in
val _ = if result = expected_result then print "ptr_locals.c: PASSED\n"
        else print "ptr_locals.c: FAILED\n"
end


(* Local variables: *)
(* mode: sml *)
(* End: *)
