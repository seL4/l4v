

struct baz { unsigned int baz_x; };

struct bar {
    struct baz bar_baz;
};

struct foobatbaz {
   struct baz foo_baz;
   struct bar foo_bar;
};


struct foo {
    unsigned int x;
    unsigned int y;
};

struct contains_foo {
    struct foo foov;
    unsigned int z;
};

struct no_foo {
    unsigned int j;
    unsigned int k;
};

int do_something(struct foo *foo, struct contains_foo *contains_foo, struct no_foo *no_foo)
{
    foo->x = 1;
    contains_foo->foov.y = 2;

    no_foo->k = 42;
       
    
    return foo->y;
}
