int x;

int f(int i)
{
  extern int x;
  return x + i;
}

int g(int i)
{
  return x + i;
}
