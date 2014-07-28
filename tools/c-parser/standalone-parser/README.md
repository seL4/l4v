Standalone Isabelle/C Parser
============================

This directory contains a standalone executable build of the Isabelle/C
parser for lightweight testing whether a C program falls into the
verification C subset.

Note that this is only the parser, not the Isabelle translation.
Programs that pass the parse may still fail in translation.


Dependencies
------------

This build works best with the `mlton` compiler, available from

  http://mlton.org

PolyML has worked as well in the past, but may require some additional
setup for 64bit platforms.
