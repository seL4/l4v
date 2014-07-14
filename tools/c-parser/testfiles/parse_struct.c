/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct struct1 {
  char c;
  int fld1;
  char fld2;
};

struct charpair {
  char c1;
  char c2;
};

struct allinclusive {
  char c;
  struct charpair p1;
  struct struct1 s;
  int foo;
  };

int firstinc_ptr(struct struct1 *sptr)
{
  if (sptr) { return sptr->fld1 + 1; }
  else return 1;
}

int firstinc(struct struct1 m)
{
  return m.fld1 + 1;
}

struct struct1 *firstptr_ptr(struct struct1 *sptr)
{
  return sptr + 1;
}

int *fldaddr(struct struct1 *sptr)
{
  return &(sptr->fld1);
}

struct allinclusive mkall(int i)
{
  struct allinclusive s;
  s.c = i;
  s.s.c = i + 1;
  s.p1.c1 = i + 2;
  s.p1.c2 = i + 3;
  s.s.fld1 = i + 4;
  s.s.fld2 = i + 5;
  s.foo = i + 6;
  return s;
}


struct voidstar {
  void *vptr;
  int i;
};

struct recursive1;
struct recursive2 {
  struct recursive1 *ptr;
  int fld;
};

struct recursive1 {
  struct recursive2 subfld;
  char c;
};

struct {
  int anonfld1;
  char anonfld2[10];
} anon_global1, anon_global2;

int f(int i)
{
  if (i == 0) return anon_global1.anonfld1;
  else return anon_global2.anonfld1;
}

struct tree20 {
  struct tree20 *array[20];
  void *data;
};

struct tree20 create20(void *init)
{
  struct tree20 s;
  for (int i = 0; i < 20; i++) s.array[i] = 0;
  s.data = init;
  return s;
}

typedef struct monstrous {
  int i,j;
} __attribute__((packed)) monstrous_t;

monstrous_t yikes(void)
{
  return (monstrous_t){.j = 6, .i = 3};
}
