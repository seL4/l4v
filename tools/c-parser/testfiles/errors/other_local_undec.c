/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* demonstrates that local variables in one function aren't available to other
   functions */

int f (int n) { return n + 1; }

int g (int m) { return n + m; }

