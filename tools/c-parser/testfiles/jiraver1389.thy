(*
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory jiraver1389
imports "CParser.CTranslation"
begin

external_file "jiraver1389.c"
install_C_file "jiraver1389.c"

context jiraver1389
begin

(* Demonstrate correct handling of temporaries across an assignment.
   Earlier versions of the C parser would reuse the same temporary for the
   results of both calls to `ptr`. *)
lemma test_assignment_to_deref_simple:
  "\<exists>assignment.
   test_assignment_to_deref_simple_body = TRY
                 \<acute>ret__ptr_to_unsigned :== CALL ptr(\<acute>p,0);;
                 \<acute>ptr_to_unsigned_eret_2 :== CALL ptr(\<acute>p,1);;
                 assignment
               CATCH SKIP
               END"
  by (rule exI, rule test_assignment_to_deref_simple_body_def[unfolded atomize_eq])

(* Same, but with multiple temporary types. *)
lemma test_assignment_to_deref_complex:
  "\<exists>assignment.
   test_assignment_to_deref_complex_body = TRY
                  \<acute>ret__ptr_to_unsigned :== CALL ptr(\<acute>p,0);;
                  \<acute>ret__int :== CALL intf(1);;
                  \<acute>int_eret_2 :== CALL intf(2);;
                  \<acute>ptr_to_unsigned_eret_2 :== CALL ptr(\<acute>p,3);;
                  \<acute>int_eret_3 :== CALL intf(4);;
                  \<acute>int_eret_4 :== CALL intf(5);;
                  assignment
                CATCH SKIP
                END"
  by (rule exI, rule test_assignment_to_deref_complex_body_def[unfolded atomize_eq])

(* Demonstrates that the branches of short-circuit logical operators may internally use the same
   variable that is used to linearise the expression. This preserves the previous behaviour
   of the C parser in more cases. *)
lemma test_logical_short_circuit_simple:
  "test_logical_short_circuit_simple_body =
   TRY
     \<acute>ret__int :== (if \<acute>i \<noteq> 0 then 1 else 0);;
     IF \<acute>ret__int \<noteq> 0 THEN
       \<acute>ret__int :== CALL intf(0);;
       \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0)
     FI;;
     IF \<acute>ret__int \<noteq> 0 THEN
       SKIP
     ELSE
       \<acute>ret__int :== CALL intf(1);;
       \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0)
     FI;;
     IF \<acute>ret__int \<noteq> 0 THEN
       SKIP
     ELSE
       \<acute>ret__int :== CALL intf(2);;
       \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0);;
       IF \<acute>ret__int \<noteq> 0 THEN
         SKIP
       ELSE
         \<acute>ret__int :== CALL intf(3);;
         \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0);;
         IF \<acute>ret__int \<noteq> 0 THEN
           \<acute>ret__int :== CALL intf(4);;
           \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0)
         FI
       FI;;
       IF \<acute>ret__int \<noteq> 0 THEN
         \<acute>ret__int :== CALL intf(5);;
         \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0)
       FI
     FI;;
     creturn global_exn_var_'_update ret__int_'_update ret__int_';;
     Guard DontReach {} SKIP
   CATCH SKIP
   END"
  by (rule test_logical_short_circuit_simple_body_def[unfolded atomize_eq])

(* The same applies for nested short-circuit logical expressions. *)
lemma test_logical_short_circuit_nested:
  "test_logical_short_circuit_nested_body =
   TRY
     \<acute>ret__int :== (if \<acute>i \<noteq> 0 then 1 else 0);;
     IF \<acute>ret__int \<noteq> 0 THEN
       SKIP
     ELSE
       \<acute>ret__int :== CALL intf(0);;
       \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0)
     FI;;
     \<acute>ret__int :== (if \<not> \<not> \<acute>ret__int \<noteq> 0 then 1 else 0);;
     IF \<acute>ret__int \<noteq> 0 THEN
       SKIP
     ELSE
       \<acute>ret__int :== CALL intf(1);;
       \<acute>ret__int :== (if \<acute>ret__int \<noteq> 0 then 1 else 0)
     FI;;
     creturn global_exn_var_'_update ret__int_'_update ret__int_';;
     Guard DontReach {} SKIP
   CATCH SKIP
   END"
  by (rule test_logical_short_circuit_nested_body_def[unfolded atomize_eq])

(* However, when the short-circuit logical expression is in a context where `ret__int`
   is already used, the C parser now uses a fresh variable to linearise the short-circuit
   logical expression. Previous versions of the C parser would incorrectly reuse `ret__int`. *)
lemma test_logical_short_circuit_subexpression:
  "\<exists>expr.
   test_logical_short_circuit_subexpression_body =
   TRY
     \<acute>ret__int :== CALL intf(0);;
     \<acute>int_eret_2 :== CALL intf(1);;
     \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0);;
     IF \<acute>int_eret_2 \<noteq> 0 THEN
       SKIP
     ELSE
       \<acute>int_eret_2 :== CALL intf(2);;
       \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0)
     FI;;
     expr;;
     Guard DontReach {} SKIP
   CATCH SKIP
   END"
  by (rule exI, rule test_logical_short_circuit_subexpression_body_def[unfolded atomize_eq])

(* Similar demonstration, including a mix of short-circuit logical and conditional operators. *)
lemma test_conditional:
  "test_conditional_body =
   TRY
     \<acute>ret__int :== CALL intf(0);;
     \<acute>int_eret_2 :== CALL intf(1);;
     \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0);;
     IF \<acute>int_eret_2 \<noteq> 0 THEN
       \<acute>int_eret_2 :== CALL intf(2);;
       \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0);;
       IF \<acute>int_eret_2 \<noteq> 0 THEN
         SKIP
       ELSE
         \<acute>int_eret_2 :== CALL intf(3);;
         \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0)
       FI;;
       IF \<acute>int_eret_2 \<noteq> 0 THEN
         \<acute>int_eret_2 :== CALL intf(4);;
         \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0);;
         IF \<acute>int_eret_2 \<noteq> 0 THEN
           \<acute>int_eret_2 :== CALL intf(5);;
           \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0)
         FI;;
         \<acute>int_eret_2 :== \<acute>int_eret_2
       ELSE
         \<acute>int_eret_2 :== CALL intf(6);;
         \<acute>int_eret_2 :== \<acute>int_eret_2
       FI;;
       \<acute>int_eret_2 :== (if \<acute>int_eret_2 \<noteq> 0 then 1 else 0)
     FI;;
     creturn global_exn_var_'_update ret__int_'_update
             (\<lambda>s. UCAST(32 \<rightarrow> 32 signed) (i_' s + SCAST(32 signed \<rightarrow> 32) (ret__int_' s)
                                          + SCAST(32 signed \<rightarrow> 32) (int_eret_2_' s)));;
     Guard DontReach {} SKIP
   CATCH SKIP
   END"
  by (rule test_conditional_body_def[unfolded atomize_eq])

end
end
