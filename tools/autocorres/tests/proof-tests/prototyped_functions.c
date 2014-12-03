
unsigned int moo1(void);

void moo2(void);

void moo3(unsigned int x);

void moo4(void);

unsigned int cow(void)
{
    moo2();
    moo4();
    moo3(moo1());
    return moo1();
}

