/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* Basic undefinedness requirements

   A.  arg2 not too large
         if result is unsigned [A+]: arg2 < 32
         if result is signed   [A-]: arg1 * 2^arg2 < 2^31
   B.  arg2 nonnegative
         if arg2 is unsigned:  - (nothing required)
         if arg2 is signed [B-]: 0 <= arg2
   C.  arg1 nonnegative
         if arg1 is unsigned:  - (nothing required)
         if arg1 is signed [C-]: 0 <= arg1
*/

unsigned f(void)
{
  int i = -1;
  unsigned larg = 4;
  int test1 = (i << 3);       /* [A- = 7, B- = 4, C- = 1] */
  int test2 = (larg << 32);   /* [A+ = 3, B- = 6, C+ = -] */
  int test3 = (i << larg);    /* [A- = 5, B+ = -, C- = 1] */
  int test4 = (larg << larg); /* [A+ = 8, B+ = -, C+ = -] */

  //  1. 0 <= i      (left argument must be non-negative)
  //  2.
  //  3. 32 < 32     (right argument must be less than width of promoted left
  //                  argument's type, when promoted type is unsigned)
  //  4. 0 <= 3      (shift amount must be non-negative)
  //  5. i * 2^larg < 2^31
  //                 (when result is signed, result can't be too large)
  //  6. 0 <= 32     (signed right argument must be non-negative)
  //  7. i * 2^3 < 2^31
  //                 (when result is signed, result can't be too large)
  //  8. larg < 32   (when argument is unsigned, must be < result's width)

  return 3;

}
