/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int global;

int g(int n) { global += n; }

int f(void)
{
  (void)0;
  (void)g(6);
  global + 3;
  return 3;
}

/* following would cause an error */
/*
void h (void)
{
  g(4) + f(5);
}
*/
