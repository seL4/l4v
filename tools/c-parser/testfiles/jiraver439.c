int f(void)
{
  static int x = 0;
  x++;
  return x;
}
