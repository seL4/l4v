/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

/* http://blog.regehr.org/archives/909 */

long long LONG_MAX = 9223372036854775807L;
long long LONG_MIN = -9223372036854775807L - 1L;

int error = 0;

extern int error;
long str2long(const char *);

long str2long(const char *s) {
    long val = 0;
    int negative = 0;

    if (*s == '-') {
        negative = 1;
        s++;
    }

    if (*s == '\0') {
        error = 1;
        return -1;
    }

    for (;*s != '\0'; s++) {
        if (*s < '0' || *s > '9') {
            /* Non-numeric character; bail out. */
            error = 1;
            return -1;
        } else {
            long d = *s - '0'; /* digit value */

            if (negative) {
                if ((LONG_MIN + d) / 10 > val) {
                    /* We're about to underflow. */
                    error = 1;
                    return -1;
                }
                val = val * 10 - d;
            } else {
                if ((LONG_MAX - d) / 10 < val) {
                    /* We're about to overflow. */
                    error = 1;
                    return -1;
                }
                val = val * 10 + d;
            }
        }
    }
    return val;
}
