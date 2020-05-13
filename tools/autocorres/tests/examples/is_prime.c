/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#define SQRT_UINT_MAX 65536

/*
 * Determine if the given number 'n' is prime.
 *
 * We return 0 if 'n' is composite, or non-zero if 'n' is prime.
 */
unsigned is_prime_linear(unsigned n)
{
    /* Numbers less than 2 are not prime. */
    if (n < 2) {
        return 0;
    }

    /* Find the first non-trivial factor of 'n'. */
    for (unsigned i = 2; i < n; i++) {
        if (n % i == 0) {
            return 0;
        }
    }

    /* No factors. */
    return 1;
}

/*
 * Determine if the given number 'n' is prime.
 *
 * We return 0 if 'n' is composite, or non-zero if 'n' is prime.
 *
 * Faster version that 'is_prime'; runs in O(sqrt(n)).
 */
unsigned int is_prime(unsigned int n)
{
    /* Numbers less than 2 are not primes. */
    if (n < 2) {
        return 0;
    }

    /* Find the first non-trivial factor of 'n' or sqrt(UINT_MAX), whichever
     * comes first. */
    /* Find the first non-trivial factor of 'n' less than sqrt(n). */
    for (unsigned i = 2; i < SQRT_UINT_MAX && i * i <= n; i++) {
        if (n % i == 0) {
            return 0;
        }
    }

    /* No factors. */
    return 1;
}

