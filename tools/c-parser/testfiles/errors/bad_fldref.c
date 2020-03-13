/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* references to non-existent fields are caught */

struct s {
  int x;
  int y;
};

int f (struct s r) { return r.z; }
