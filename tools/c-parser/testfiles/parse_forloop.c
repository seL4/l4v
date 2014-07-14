/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* also tests
   - post-increment and decrement (which are common in for loops)
   - arrays on the heap and stack (treated differently in VCG-land)
*/

int *f(int *i, int c)
{
  unsigned j;
  for (j = 0; j < 4; j++) i[j] = i[j] + c;
  i[0]++;
  return i;
}

int g(int c)
{
  for (unsigned int j = 10; 0 < j; j--)
    /** INVARIANT: "\<lbrace> 0 <= \<acute>j & \<acute>j <= 10 \<rbrace>" */
    {
      c = c + j;
    }
  return c;
}

int h(int c)
{
  int a[10];
  for (unsigned int j = 0; j < 10; j++) a[j] = j;
  a[0] = a[1] + a[2];
  return a[0];
}

int f2(int *a)
{
  int j, res;
  for (j=0,res=0; j < 32; j += 4) { res += a[j]; }
  return res;
}
