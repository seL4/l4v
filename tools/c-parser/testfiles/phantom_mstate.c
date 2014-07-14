/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int x, y;
/** MODIFIES: x [*] */
int machine_proto(void);

/** MODIFIES: phantom_machine_state y */
int proto2(int);

int f(int i)
{
  return i + machine_proto() + proto2(i);
}

int g(void)
{
  y++;
  return x + y;
}

