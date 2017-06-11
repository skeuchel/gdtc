Generic Datatypes à la Carte
============================

This repository contains the source code accompanying the paper

[Keuchel, Steven, and Tom Schrijvers. "Generic datatypes à la carte."
Proceedings of the 9th ACM SIGPLAN workshop on Generic programming. ACM, 2013](http://dl.acm.org/citation.cfm?id=2502491)

which include the GDTC framework and the case-study ported from MTC to GDTC. The
code has been tested with Coq version 8.4pl6; later versions may not work.

Framework
---------

### Functors.v

Contains the general infrastructure for modular datatypes, algebras and
proof algebras.

* code for glueing (mixin) algebras and (mixin) proof-algebras along coproducts
  of functors
* type classes for carrying (mixin) algebras and proof algebras amd (FAlgebra,
  FPAlgebra, FPMixin)
* sub-functor relation (Sub_Functor)
* naturality of injections into super functors (WF_Functor)
* discrimination of distinct sub functors (Distinct_Sub_Functor)
* algebra and mixin delegation (WF_Algebra, WF_Mixin)

### Containers.v

Contains code for the universes of container functors
as well as generic implementation of

* equality
* functorial mappings
* folds
* inductions

includings generic proofs about their properties.

### Polynomial.

Contains code for the universe of polynomal functors and generic equality.


Case Study
----------

### Names.v

General infrastructure for evaluation and typing of expressions. Declarations
for continuity and type-safety and final proofs for continuity and type-safety
from the modular proof algebras.

### PNames.v

Infrastructure for the PHOAS representation.

### Arith.v, Lambda.v, ..

Feature specific declarations, algebras and proof algebras.

### test_A.v, test_AB.v, ..

Fully composed type-safety proofs.
