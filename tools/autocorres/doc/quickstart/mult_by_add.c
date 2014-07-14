/*
 * Simple loop example.
 */

unsigned mult_by_add(unsigned a, unsigned b)
{
    unsigned result = 0;
    while (a > 0) {
        result += b;
        a--;
    }
    return result;
}

