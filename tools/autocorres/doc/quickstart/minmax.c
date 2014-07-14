#define UINT_MAX (-1u)

/*
 * Simple pure functions.
 */

unsigned min(unsigned a, unsigned b) {
  if (a <= b) {
    return a;
  } else {
    return b;
  }
}

unsigned max(unsigned a, unsigned b) {
  return UINT_MAX - (
      min(UINT_MAX - a, UINT_MAX - b));
}

