_Noreturn void exit(int i);

unsigned f(unsigned i)
{
  if (i < 0) exit(-1);
  return i * i;
}

_Noreturn void myexit(int i)
{
  exit(i + 1);
}
