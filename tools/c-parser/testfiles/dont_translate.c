/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
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
