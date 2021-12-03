
  This is a description of what I have changed so far to make stacks sort-of work in the c-parser, and what is left to be done. When I started, the c-parser had no notion of the stack. The goal is to get the c-parser to a point where it both has a stack, and can reason about pointers to that stack.

  To add the notion of a stact, I create a stack field in the global state record (in `mk_globals_rcd` in `calculate_state.ML`). The stack itself is an abstract datatype (defined `Stack.thy`) which is a sort of inverted list, where the top of the stack is the deepest down, and the root is immediately accessible. Each stack frame also keeps a generation number, which is a number keeping track of the version of the frame currently on the stack. This design allows for safe dereferencing, becuase the abstract stack-pointers keep track of the frame generations on which they were created, and (will, once implemented) ensure that they are the same before continuing.

  The second point to consider is the frames. `frame` is a datatype containing an variant for every function call, and each variant contains a record for that functions local variables. (This is also generated in `calculate_state.ML`.)

Due to these new datatypes, a number of definitions and lemmas need to be created for get and update functions for each variable on this stack. Currently, not all simplification lemmas are generated automatically.

  Currently, these changes sit *alongside* the previous design, where the globalstate contains a variable for each variable name in all functions. (This *is* in fact safe, because when a function call gets processed by SIMPL, the state is copied.) Eventually, the goal is to remove these. This will affect AutoCorres, which relies on this representation to perform its abstraction. I have not thought about how to fix the abstraction after this change is made.
