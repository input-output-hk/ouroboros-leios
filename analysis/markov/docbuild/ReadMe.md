# Building the documentation

See https://github.com/leanprover/doc-gen4/tree/v4.24.0 for detailed instructions.

1.  In this folder, execute `MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4`.
2.  Also in this folder, execute `lake build Linleios:docs`.
3.  View the documentation at `./.lake/doc/index.html`.
