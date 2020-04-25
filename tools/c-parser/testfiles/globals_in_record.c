/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int zuzu = 1;
int zozo = 1;
int zyzy = 1;

int incz(void) {
    zuzu = zuzu + 1;
    return zuzu;
}

int incp(void) {
    int *pp = &zozo;

    *pp = *pp + 1;
    return *pp;
}

/*
    This gives a global record:
        [|
           global_exn_var_';
           t_hrs_';
           phantom_machine_state_';
           zuzu_';
           ...
        |]
    Note:
    * The program reads and writes zuzu but does not take its address.
      ==> There is an explicit field for zuzu.

    * The program takes the address of zozo.
      ==> There is not an explicit field for zozo
      ==> It is instead modelled in t_hrs_' (see below)

    * The program does not write to zyzy.
      ==> There is not an explicit field for zyzy.
      ==> Nor is it modelled in t_hrs_'
      ==> It does exist as a constant: zyzy == 1

    * t_hrs_' stands for "typed heap representation structure"
      It is a function from addresses to bytes and type tags (which say how
      those bytes are to be interpreted), as described in "Types, Bytes,
      and Separation Logic".
      A variable must be modelled in the heap, to account for the effects
      of aliasing, whenever the address-of (&) operator is used against it.
 */

