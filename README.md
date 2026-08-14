# Simon's Split Theorem and Green's Relations (Lean 4)

Formalization in Lean 4 of the algebraic components behind Simon's Split Theorem,
with a focus on Green's relations.

## Reference Article

- Thomas Colcombet, *The Factorization Forest Theorem*: 
  <https://www.irif.fr/~colcombe/Publications/handbook-fft-colcombet_non-final.pdf>

## What this repository formalizes

- Green's relations: L, R, H, D, J
- Equivalence classes and quotient constructions for Green's relations
- Finite-semigroup structure results (regular D-classes, idempotents, D = J)
- Multiplicative labelings and Ramsey splits
- Special cases of Simon's split theorem: group case, H-class case, and regular D-class case
- The full split theorem construction bounded by ($3*N(S) - 1$)

## Overview

### `Project/GreensRelations/`
Contains the foundational semigroup theory and Green's relations.

* `Basic.lean`
  - The foundational definitions for Green's relations (L, R, H, D, and J) and left/right divisibility over semigroups. 
  - Setoid instances, duality equivalences, equivalence classes as sets, quotient spaces, and notions of regular elements/D-classes.
 
* `MulSeq.lean`
  - Tools for analyzing finite semigroups using iterated multiplication sequences.
  - Structural helper lemmas for intermediate proofs, such as the existence of idempotents in regular L/R-classes.

* `Green.lean`
  - The major structural theorems of Green's relations.
  - Key results like Green's lemma (constructing explicit bijections between H-classes) and characterizations of regular D-classes via idempotents.

* `Finite.lean`
  - Structural theorems regarding Green's relations requiring a finite semigroup, such as the equivalence of D and J, and conditions for H-classes to be subgroups.

* `Order.lean`
  - Defines the natural partial order structures on the quotient types (`GreenLClass`, `GreenRClass`, `GreenJClass`, and `GreenDClass`).

### `Project/SimonSplit/`
Contains the definitions, lemmas, and constructions for Simon's Split Theorem.

* `Basic.lean`
  - Core structures: `MultiplicativeLabeling`, `Split` (normalized and Ramsey).

* `Combine.lean`
  - Lemmas for combining splits.

* `Irregular.lean`
  - Proofs for the irregular cases of the Split Theorem (the irregular D-class case).

* `Regular.lean`
  - Proofs for the regular cases, dealing with group/H-class cases and regular D-class cases using custom colorings.

* `Split.lean`
  - The induction steps for Simon's split theorem, proving that any multiplicative labeling over a finite linear order admits a bounded normalized Ramsey split. Culminates in `simon_word`, which applies this to words.
