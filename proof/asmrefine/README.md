Assembly Refinement Proof
=========================

This proof establishes that seL4's compiled binary correctly implements the
[semantics](../../spec/cspec) of its C code. It uses the [binary verification
tool](../../tools/asmrefine/). An earlier version of this proof is described
in the PLDI '13 [paper][1].

  [1]: http://www.nicta.com.au/pub?id=6449  "Translation Validation for a Verified OS Kernel"

Important Theories
------------------

The [`SEL4SimplExport`](SEL4SimplExport.thy) theory, when executed, exports the
kernel's C semantics into the graph refinement language used by the external
graph refinement toolset. The [`SEL4GraphRefine`](SEL4GraphRefine.thy) theory
establishes that this exported graph semantics is a formal refinement of
the kernel's C semantics.

The external graph refinement toolset then proves that the kernel's exported
graph semantics is refined by the compiled binary.

Current Status
--------------

This work is currently in flux. As a result,
[`SEL4GraphRefine`](SEL4GraphRefine.thy) may not be currently complete.

The external graph refinement toolset is also currently in flux. An
earlier version of this toolset is available [here][2].

  [2]: http://ssrg.nicta.com.au/software/TS/graph-refine/

