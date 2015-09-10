int global;

int __attribute__((__const__)) baz(void) {
  return 3;
}

int __attribute__((const)) qux(void) {
  /* shouldn't fail with "syntax error: deleting  CONST" */
  return 4;
}
