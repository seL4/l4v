<!--
     Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

The StrictC translation tool
============================

To install, see the file INSTALL in the `src/c-parser` directory.

To use:

1. Use the heap CParser that is created by installation
2. Import the theory CTranslation
3. Load ('install') C files into your theories with the Isar command
   `install_C_file`.

See `docs/ctranslation.pdf` for more information about the options
and C language semantics that this tool provides.

See also the examples in the testfiles directory.  For example,
`breakcontinue.thy` is a fairly involved demonstration of doing things
the hard way.

----------------------------------------------------------------------
The translation tool builds on various open source projects by others.

1. Norbert Schirmer's Simpl language and associated VCG tool.

   Sources for this are found in the Simpl/ directory.  The
   code is covered by an LGPL licence.

   See <https://isa-afp.org/entries/Simpl.html>

2. Code from SML/NJ:
   - an implementation of binary sets (Binaryset.ML)
   - the mllex and mlyacc tools (tools/{mllex,mlyacc})
   - command-line option parsing (standalone-parser/GetOpt)

   This code is covered by SML/NJ's BSD-ish licence.

   See <http://www.smlnj.org>

3. Code from the mlton compiler:
   - regions during lexing and parsing (Region.ML, SourceFile.ML and
     SourcePos.ML)

   This code is governed by a BSD licence.

   See <http://mlton.org>
