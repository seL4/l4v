typedef struct {
  int r2, r3;
} seL4_UserContext;

int
useContext(seL4_UserContext *ucptr)
{
  return ucptr->r2 + ucptr->r3;
}
