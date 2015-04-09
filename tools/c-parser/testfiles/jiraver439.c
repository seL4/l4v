unsigned z;

unsigned f(void)
{
  static unsigned x = 0;
  x++;
  return x;
}

unsigned g1(void)
{
  z++;
  return z;
}

unsigned g2(void)
{
  static unsigned z;
  z++;
  return z;
}

unsigned h1(void)
{
  static unsigned xx = 1;
  return xx;
}

unsigned h2(void)
{
  static unsigned x;
  return x;
}

unsigned h3(unsigned x)
{
  static unsigned xx = 0;
  xx += x;
  return xx;
}
