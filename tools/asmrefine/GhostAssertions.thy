theory GhostAssertions

imports "../c-parser/CTranslation"

begin

text {* Some framework constants for adding assertion data to the ghost
state and accessing it. These constants don't do much, but using them
allows the SimplExport mechanism to recognise the intent of ghost state
operations. *}


