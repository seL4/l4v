/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
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

