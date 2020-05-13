/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

typedef unsigned char uint8_t;
typedef unsigned int uint32_t;

uint8_t foo(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint8_t bar(int a, uint32_t b, uint8_t c)
{
    return foo(1, 2, foo(1, 2, 3));
}

uint32_t foo2(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint32_t bar2(int a, uint32_t b, uint8_t c)
{
    return foo2(a, b, foo2(1, 2, 3));
}

uint8_t foo3(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint8_t bar3(int a, uint32_t b, uint8_t c)
{
    return foo3(1, 2, foo3(1, 2, 3));
}

uint32_t foo4(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint32_t bar4(int a, uint32_t b, uint8_t c)
{
    return foo4(a, b, foo2(1, 2, 3));
}

uint8_t foo5(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint8_t bar5(int a, uint32_t b, uint8_t c)
{
    return foo(1, 2, foo(1, 2, 3));
}

uint32_t foo6(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint32_t bar6(int a, uint32_t b, uint8_t c)
{
    return foo2(a, b, foo2(1, 2, 3));
}

uint8_t foo7(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint8_t bar7(int a, uint32_t b, uint8_t c)
{
    return foo3(1, 2, foo3(1, 2, 3));
}

uint32_t foo8(int a, uint32_t b, uint8_t c)
{
    return a + b + c;
}

uint32_t bar8(int a, uint32_t b, uint8_t c)
{
    return foo4(a, b, foo2(1, 2, 3));
}


