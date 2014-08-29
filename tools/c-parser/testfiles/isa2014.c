int x, y;

int f(int i)
{
  return i + 1;
}

int g(int *iptr)
{
  return iptr ? *iptr : 0;
}

/** MODIFIES: x */
void ff(int i)
{
  x += i * g(&y);
}
