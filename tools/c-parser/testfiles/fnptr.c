/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned f(unsigned x) { return x + 1; }

unsigned g(unsigned);

void callthem(void)
{
  g((int)f);
  g((int)&f);
}

unsigned global1, global2;

void callable1(void)
{
  global1++;
}

void callable2(void)
{
  global2++;
}

int voidcaller(void (*pfn)(void))
{
  pfn();
  return 2;
}

int callvoidcaller(void)
{
  return voidcaller(callable1);
}

int intcallable1(void)
{
  return 3;
}

int intcallable2(void)
{
  return 4;
}

int intcaller(int (*ipfn)(void) /** CALLS intcallable2 */)
{
  return ipfn();
}

int callintcaller(void)
{
  return intcaller(intcallable2);
}
