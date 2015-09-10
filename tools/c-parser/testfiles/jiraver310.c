struct s {
  struct s *next;
  int data;
};

int * globalptr;

struct s f(int i)
{
  struct s node = {.data = i};
  return node;
}

struct s g(int i)
{
  globalptr = 0;
  return (struct s){.data = i, .next = 0};
}

struct s h(void)
{
  struct s node = {0};
  return node;
}
