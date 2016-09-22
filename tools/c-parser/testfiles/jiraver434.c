/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

typedef struct {
  int r2, r3;
} seL4_UserContext;

int
useContext(seL4_UserContext *ucptr)
{
  return ucptr->r2 + ucptr->r3;
}
