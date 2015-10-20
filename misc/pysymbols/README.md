<!--
 Copyright 2015, NICTA

 This software may be distributed and modified according to the terms of
 the BSD 2-Clause license. Note that NO WARRANTY is provided.
 See "LICENSE_BSD2.txt" for details.

 @TAG(NICTA_BSD)
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
