/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

#ifndef COMPILE
#define NULL ((void*)0)
#endif

struct node {
  struct node *l, *r;
  unsigned m, c;
};

/* This is Mehta & Nipkow's version of the algorithm (HOL/Hoare/SchorrWaite.thy). */
void schorr_waite(struct node *root) {
  struct node *t = root, *p = NULL, *q;
  while (p != NULL || (t != NULL && !t->m)) {
    if (t == NULL || t->m) {
      if (p->c) {
        q = t; t = p; p = p->r; t->r = q;
      } else {
        q = t; t = p->r; p->r = p->l; p->l = q; p->c = 1;
      }
    } else {
      q = p; p = t; t = t->l; p->l = q; p->m = 1; p->c = 0;
    }
  }
}


/*
 * An executable specification for graph traversal.
 */
void simple_traverse(struct node *n) {
  if (n == NULL || n->m) {
    return;
  }

  n->m = 1;
  simple_traverse(n->l);
  simple_traverse(n->r);
}

#ifdef COMPILE
#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>
#include <time.h>

void make_graph(unsigned size, unsigned graph[size][2], struct node n[size]) {
  for (unsigned i = 0; i < size; ++i) {
    if (graph[i][0] == size) {
      n[i].l = NULL;
    } else {
      n[i].l = &n[0] + graph[i][0];
    }
    if (graph[i][1] == size) {
      n[i].r = NULL;
    } else {
      n[i].r = &n[0] + graph[i][1];
    }
    n[i].c = n[i].m = 0;
  }
}

int main(void) {
  const unsigned max_size = 1000;
  unsigned graph[max_size][2];

  struct timeval tv;
  if (gettimeofday(&tv, NULL)) {
    return 1;
  }
  unsigned long long t = (unsigned long long)tv.tv_sec * 1000000 + tv.tv_usec;
  const int seed = (t >> 32) ^ t;

  srand(seed);
  unsigned size = rand() % max_size + 1;
  for (unsigned i = 0; i < size; ++i) {
    graph[i][0] = rand() % (size+1);
    graph[i][1] = rand() % (size+1);
  }

  struct node n1[max_size], n2[max_size];
  make_graph(size, graph, n1);
  make_graph(size, graph, n2);

  schorr_waite(n1);
  simple_traverse(n2);

  for (unsigned i = 0; i < size; ++i) {
    if (graph[i][0] == size) {
      assert(n1[i].l == NULL);
      assert(n2[i].l == NULL);
    } else {
      assert(n1[i].l == n1 + graph[i][0]);
      assert(n2[i].l == n2 + graph[i][0]);
    }
    if (graph[i][1] == size) {
      assert(n1[i].r == NULL);
      assert(n2[i].r == NULL);
    } else {
      assert(n1[i].r == n1 + graph[i][1]);
      assert(n2[i].r == n2 + graph[i][1]);
    }
    assert(n1[i].m == n2[i].m);
  }

  return 0;
}
#endif
