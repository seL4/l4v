<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Python Isabelle Symbols Module

This directory contains Python functionality for translation between Isabelle's
ascii representations (e.g. `\<forall>`) and its unicode representations (e.g.
`∀`). You need to provide it with a copy of Isabelle's internal "symbols" file
that it uses to form translation mappings.

Example usage:

```python
import isasymbols

t = isasymbols.make_translator('/path/to/symbols')
print t.encode('\\<lbrakk>A; B\\<rbrakk> \\<Longrightarrow> A')
```

For anything more complicated, please consult the source.
