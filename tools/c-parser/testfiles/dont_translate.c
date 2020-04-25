/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int x;

/** DONT_TRANSLATE
    MODIFIES: [*]
*/
void scary(void)
{
  volatile int *x = 0xdeadbeef;
  *x = 10;
}

/**
   MODIFIES:
 */
void not_scary(void);

/**
   DONT_TRANSLATE
*/
void not_scary(void)
{
  volatile int *x = 0xdeadbeef;
  *x = 10;
}

void somewhat_scary(void);

/**
   DONT_TRANSLATE
   MODIFIES:
*/
void somewhat_scary(void)
{
  volatile int *x = 0xdeadbeef;
  *x = 10;
}

int f(void)
{
  scary();
  not_scary();
  somewhat_scary();
  return 3;
}
