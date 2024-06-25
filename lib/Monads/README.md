<!--
  Copyright 2023, Proofcraft Pty Ltd
  SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Monad Definitions and Tactics

This session contains definitions of various monads useful in [AutoCorres] and
the [seL4 verification][l4v] for the verification of C programs.

In particular, this session defines:

- a [nondeterministic state monad][nondet] with failure to express stateful
  computation. There is a variation of this monad that also allows computation
  with exceptions (throw/catch).

- a [reader option monad][option] to express computation that can depend on
  state and can fail, but does not change state. It can also be used to express
  projections from the state in preconditions and other state assertions.

- a [trace monad][trace] that stores a set of traces for expressing concurrent
  computation.

- for each of these monads, weakest-precondition lemmas and corresponding tool
  setup.

- for the nondeterministic state monad, additional concepts such as
  wellformedness with respect to failure (`empty_fail`), absence of failure
  (`no_fail`), absence of exceptions (`no_throw`). See its [README][nondet] and
  the respective theories for more details.

- the trace monad has similar concepts where applicable, and its theories follow
  the same structure as that of the nondet monad.

The directory [`wp/`](./wp/) contains proof methods to reason about these monads
in weakest-precondition style. See its [README][wp] for more details.

This session also introduces a [strengthen] method, which is useful for
performing rewriting steps within the complex conclusions that often appear when
working with these monads.

[l4v]: https://github.com/seL4/l4v/
[nondet]: ./nondet/Nondet_README.thy
[option]: ./reader_option/Reader_Option_Monad.thy
[trace]: ./trace/Trace_Monad.thy
[AutoCorres]: ../../tools/autocorres/
[wp]: ./wp/WP_README.thy
[strengthen]: ./Strengthen_Demo.thy
