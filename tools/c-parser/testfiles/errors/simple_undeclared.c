/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* demonstrates that undeclared variables are spotted */

int f(int n) { return m + 1; }
