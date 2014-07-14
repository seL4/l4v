/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef struct s {
  int x,y;
  char c;
} s;

int f(void)
{
  unsigned char array[sizeof(s)];
  struct s var1;
  for (int i = 0; i < sizeof(s); i++) array[i] = 1;
  return sizeof (s);
}
