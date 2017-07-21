/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int x,y;

int g(int);
int h(int);

int f(void)
{
  if (x < 0) return 1 + g(6);
  else {
    int i = h(x);
    return 7 + i;
  }
}

int g(int i)
{
  x++;
  int local = f();
  return i + local;
}

int h(int i)
{
  y++;
  return i * 2 + y;
}

int atop(int i)
{
  if (i < 0) return g(i);
  else return 3;
}

int fact(int i)
{
  if (i < 2) return 1;
  else return i * fact(i - 1);
}


void rec2(void);
void rec3(void);
void rec4(void);
int rec1(void)
{
  if (x < 0) rec2();
  return 1;
}

void rec2(void)
{
  if (y > x) rec1(); else rec4();
}

void rec3(void)
{
  int tmp = h(x);
  if (x > tmp) rec2();
}

void rec4(void)
{
  rec2();
  rec3();
}



