/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

struct foo {
  int x, thread_index;
} glob;
struct foo* camkes_get_tls(void)
{
  return &glob;
}
_Noreturn void abort(void);

static int a1;
static int a2;
static int *get(void) __attribute__((__unused__));
static int *get(void) {
  switch (camkes_get_tls()->thread_index) {
  case 1:
    return &a1;
  case 2:
    return &a2;
  default:
    (void)0;
    abort();
  }
}
