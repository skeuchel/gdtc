Generic Datatypes à la Carte
============================

Functors.v
----------

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

Containers.v
------------

Contains code for the universes of polynomal functors and container functors
as well as generic implementation of

* equality
* functorial mappings
* folds
* inductions

includings generic proofs about their properties.

Names.v
-------

General infrastructure for evaluation and typing of expressions. Declarations
for continuity and type-safety and final proofs for continuity and type-safety
from the modular proof algebras.

PNames.v
--------
Infrastructure for the PHOAS representation.

Arith.v, Lambda.v, ..
---------------------
Feature specific declarations, algebras and proof algebras.
