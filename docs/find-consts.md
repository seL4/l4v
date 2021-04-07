<!--
     Copyright 2021, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Using find_consts effectively

The `find_consts` command searches for constants matching the given
criteria. It is similar to [find_theorems][], searching using type patterns
instead of term patterns.

[find_theorems]: find-theorems.md

The basic search criteria are:

  syntax            | find ...
  ------------------|-------------------------------------
  `"type"`          | constants containing this type
  `strict: "type"`  | constants matching this type
  `name: "string"`  | constant with `string` in name
  `- <criterion>`   | constants that do **not** match `<criterion>`

Generally, the `strict` criterion is most useful, followed by `name`,
while a plain type pattern can be used to refine other queries.

Suppose we are searching for a function that extracts the left side of a
sum:

    "_ + _ ⇒ _"

Unfortunately (depending on how deep you are in l4v) this is liable to print
many irrelevant constants whose types merely contain `"_ + _ ⇒ _"` somewhere.
The pattern is good if you want to cast the search net wide, but `l4v` tends to
be too big for that. We can use a strict query instead:

    strict: "_ + _ ⇒ _"

We can also use schematic variables instead of dummy types to make a precise
query:

    strict: "?'a + _ ⇒ ?'a"

Analogously to `find_theorems`, use

    "_ ⇒ foo"

to search for functions that return a given type, or

    "foo ⇒ _"

for functions that take a given type.

As in `find_theorems` you can use `name` and `-name` to restrict to specific
theories or exclude theories

     "_ => _ list" -name: "List."

will find all constants that produce list, but exclude the basic `List` library.
