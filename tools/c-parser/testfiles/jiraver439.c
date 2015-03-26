unsigned z;

unsigned f(void)
{
  static unsigned x = 0;
  x++;
  return x;
}

unsigned g(void)
{
  z++;
  return z;
}
