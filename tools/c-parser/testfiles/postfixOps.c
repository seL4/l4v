/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

unsigned char uc;
signed char sc;
unsigned int ui;
int si;
unsigned long ul;
long sl;

signed char *retptr(void)
{
  return &sc;
}

void doit(void)
{
  uc++;
  sc++;
  ui++;
  si++;
  ul++;
  sl++;
  (*retptr())++;
  sl--;
  uc--;
}

