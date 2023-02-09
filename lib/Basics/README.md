<!--
  Copyright 2023, Proofcraft Pty Ltd
  SPDX-License-Identifier: CC-BY-SA-4.0
-->

# Basic Library Theories

This session contains basic library theories that are needed in other sessions
of this repository, such as [Monads] or [CParser], but that we do not want to
put into these sessions to avoid circular session dependencies.

Dependencies on `Word_Lib` and the Isabelle distribution (e.g. `HOL-Libary`) are
fine, but avoid introducing any further session dependencies.

[Monads]: ../Monads/
[CParser]: ../../tools/c-parser
