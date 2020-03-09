/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef struct {
  int r2, r3;
} seL4_UserContext;

int
useContext(seL4_UserContext *ucptr)
{
  return ucptr->r2 + ucptr->r3;
}
