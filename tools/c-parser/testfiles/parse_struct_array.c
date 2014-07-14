/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#define MAX_SIZE 1024

int globint1, globint2, globintarray[3];

struct s {
  int sz;
  char data[MAX_SIZE];
};

struct s_dataptr {
  int sz;
  char *dataptr;
};

int f(struct s* ptr)
{
  return ptr ? 0 : ptr->sz;
}

struct t {
  int x, y;
};

struct u {
  struct t array[10];
};

struct k {
  unsigned short b;
  char c[1];
};

int g(struct u* uptr, int n, struct k *kptr)
{
  return uptr->array[n].x + (kptr ? kptr->b : 0);
}

struct u globu;
struct k globk1, globk2, globkarray[10];

int h(int *i)
{
  globk2.b++;
  return *i + g(&globu, *i * 2, &globk1);
}

int h1(void)
{
  return g(&globu, 2, globkarray + 6);
}

int j(void)
{
  int i = h(&globint1), j = h(globintarray + 2);
  return i + j;
}

int ts20110511_1(struct s *sptr, int i, int shift)
{
  return ((sptr->data[i]) >> shift);
}

int ts20110511_2(struct s *sptr, int shift)
{
  return ((sptr->sz) >> shift);
}

