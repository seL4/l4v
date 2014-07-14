/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* from ISO/IEC 9899:1999 */

enum hue {chartreuse, burgundy, claret = 20, winedark };

int f(enum hue *cp)
{
  enum hue col;
  int array[claret];
  col = claret;
  array[6] = chartreuse;
  if (*cp != burgundy) return 1;
  else return 2;
}

enum foo {bar,baz} x;
int g(void)
{
  x = bar;
  return x;
}

int h(void)
{
  int array[100] = {[claret] = 10};
  return array[winedark];
}


enum ts20091113 {foo = -10, bar2, baz2 = -60, qux = 1, quux};
