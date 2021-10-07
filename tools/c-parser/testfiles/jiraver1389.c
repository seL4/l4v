/*
 * Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

unsigned *ptr(unsigned *p, unsigned i)
{
  return p + i;
}

int intf(unsigned i)
{
  return i;
}

void test_assignment_to_deref_simple(unsigned *p)
{
  *ptr(p,0u) = *ptr(p,1u);
}

void test_assignment_to_deref_complex(unsigned *p)
{
  *(ptr(p,0u) + intf(1u) + intf(2u)) = *(ptr(p,3u) + intf(4u) + intf(5u));
}

int test_logical_short_circuit_simple(unsigned i)
{
  return (i && intf(0u) || intf(1u)) || (intf(2u) || intf(3u) && intf(4u)) && intf(5u);
}

int test_logical_short_circuit_nested(unsigned i)
{
  return (!!(i || intf(0u))) || intf(1u);
}

int test_logical_short_circuit_subexpression(unsigned i)
{
  return i + intf(0u) + (intf(1u) || intf(2u));
}

int test_conditional(unsigned i)
{
  return i + intf(0u) + (intf(1u) && ((intf(2u) || intf(3u)) ? (intf(4u) && intf(5u)) : intf(6u)));
}
