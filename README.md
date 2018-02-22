# Coq for Programmers - Programming with Dependent Types

This text is an introduction to programming with dependent types in Coq and
the library contains a lot of useful functions to create real world programs
with Coq.

**Author:** Helmut Brandl (firstname dot lastname at gmx dot net)

**Repository:** http://github.com/hbr/coqlib

**Browse Library:** https://hbr.github.io/coqlib

There are already some excellent introductions to the Coq proof
assistant. E.g. the [Software Foundations](docs/bibliography.md#pierce_sf)
written by Benjamin Pierce, [Certified Programming with Dependent
Types](docs/bibliography.md#chlipala_cpdt) written by Adam Chlipala and
[Interactive Theorem Proving and Program
Development](docs/bibliography.md#bertot_casteran) written by Yves Bertot and
Pierre Casteran.

_Coq for Programmers_ can be seen complementary to the above mentioned
introductions which has been written to show how real world programms can be
written in Coq.

Normally Coq is used by writing some functions and proof properties about
those functions. The proofs are done by using tactics. With that the user has
to learn the language to express functions (Gallina, Coq's term language) and
the tactic language to write proof scripts.

This approach is very convenient to as long as you don't write functions with
strong result types (e.g. an insert function for a balanced tree which
maintains the sorting of elements and a certain balancing or decision
procedures).

In this text we focus on writing proofs by providing proof terms. I.e. we use
the same language (Gallina, Coq's term language) for writing functions and
proofs about properties of these functions. The user has to learn only one
language. Furthermore functions with strong result types can be written
directly.

For those who might be horrified by writing proof terms directly: In many
cases it is not more difficult than proving with tactics. Furthermore the
structure of the proofs is visible.


<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
