/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

int g (int n) {
  return n;
}

int
f (int n) {
  switch (n) {
    case 0:
      n++;
      if (n == 1)
        break;
      return 3;
    case 1:
      return 0;
    default:
      break;
  };
  return g (n);
}

