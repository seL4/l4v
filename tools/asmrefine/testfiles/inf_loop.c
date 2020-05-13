/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

int redundant_global = 3;
int another_redundant_global = 2;

void redundant_fun(int x)
{
    redundant_global = x;
}

void other_f(void)
{
    return;
}

int main_f(void)
{
    while (1) {
        other_f();
    }
}


