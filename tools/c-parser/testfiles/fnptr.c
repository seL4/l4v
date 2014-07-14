/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
