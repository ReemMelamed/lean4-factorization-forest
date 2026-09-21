# Simon's Factorization Forest Theorem and Green's Relations (Lean 4)

Formalization in Lean 4 of the algebraic theory of Green's relations, Simon's Split Theorem, the Factorization Forest Theorem, Brown's Lemma, and optimality/complexity bounds.

## Reference Article

- Thomas Colcombet, *The Factorization Forest Theorem*: 
  <https://www.irif.fr/~colcombe/Publications/handbook-fft-colcombet_non-final.pdf>

## What this repository formalizes

- **Green's relations**: $\mathcal{L}, \mathcal{R}, \mathcal{H}, \mathcal{D}, \mathcal{J}$, their setoids, quotient spaces, and partial orders.
- **Finite semigroup structure**: regular $\mathcal{D}$-classes, idempotents, $\mathcal{D} = \mathcal{J}$, and Green's lemma.
- **Multiplicative labelings and Ramsey splits**: normalized and Ramsey splits over linear orders.
- **Simon's Split Theorem**: bounded Ramsey split construction ($3 \cdot N(S) - 1$) dealing with irregular $\mathcal{D}$-classes, $\mathcal{H}$-classes, and regular $\mathcal{D}$-classes.
- **Simon's Factorization Forest Theorem**: constructing unranked Ramsey factorization trees of bounded height ($3 \cdot N(S) - 1$) from Ramsey splits.
- **Brown's Lemma and Algebraic Presentation**: stabilization of subsemigroup closures ($\langle X \rangle_S = X_{3 \cdot N(T)}$) and local finiteness.
- **Optimality and Bounds**:
  - Sub-linear bounds for the truncated addition semigroup ($\lceil \log_2 n \rceil + 2$).
  - Kufleitner's tight lower bound ($3|G| - 1$) for non-trivial groups.
  - Improved bounds ($2|S|$) for aperiodic (group-trivial) semigroups.

## Repository Overview

### `Project/GreensRelations/`
Foundational semigroup theory and Green's relations.

* `Basic.lean`
  - Foundational definitions for Green's relations ($\mathcal{L}, \mathcal{R}, \mathcal{H}, \mathcal{D}, \mathcal{J}$) and divisibility.
  - Setoid instances, duality equivalences, equivalence classes as sets, quotient spaces, and regular elements/$\mathcal{D}$-classes.

* `MulSeq.lean`
  - Analysis of finite semigroups via iterated multiplication sequences.
  - Existence of idempotents in regular $\mathcal{L}$/$\mathcal{R}$-classes.

* `Green.lean`
  - Green's lemma (explicit bijections between $\mathcal{H}$-classes).
  - Characterizations of regular $\mathcal{D}$-classes via idempotents.

* `Finite.lean`
  - Structure theorems requiring a finite semigroup: equivalence of $\mathcal{D}$ and $\mathcal{J}$, and group structure of $\mathcal{H}$-classes containing idempotents.

* `Order.lean`
  - Natural partial order structures on quotient types (`GreenLClass`, `GreenRClass`, `GreenJClass`, and `GreenDClass`).

### `Project/SimonSplit/`
Definitions, lemmas, and constructions for Simon's Split Theorem.

* `Basic.lean`
  - Core structures: `MultiplicativeLabeling`, `Split` (normalized and Ramsey).

* `Combine.lean`
  - Complexity invariants `nSElement` and `nS`.
  - Construction of jump points (`buildXSeq`) and combining local interval splits (`combineSplits_props`).

* `Irregular.lean`
  - Proofs for the irregular $\mathcal{D}$-class case of the Split Theorem.

* `Regular.lean`
  - Proofs for regular cases (group/$\mathcal{H}$-class and regular $\mathcal{D}$-class cases via custom colorings).

* `Split.lean`
  - Inductive steps proving any multiplicative labeling over a finite linear order admits a bounded normalized Ramsey split.
  - `simon_word`: application of Simon's Split Theorem to words.

### `Project/FactorizationTree/`
Unranked ordered factorization trees and Simon's Factorization Forest Theorem.

* `FactorizationTree.lean`
  - Definition of `FactorizationTree` (leaves, binary nodes, idempotent nodes) and their Ramsey property (`IsRamsey`).
  - Conversion of Ramsey splits to Ramsey factorization trees (`split_to_tree_outer`, `split_to_tree_inner`).
  - `factorization_forest_theorem` (Colcombet Theorem 3.4): every non-empty word admits a Ramsey factorization tree of height at most $3 \cdot N(S) - 1$.

### `Project/BrownLemma.lean`
Applications of the Factorization Forest Theorem to semigroup theory.

* `closure_eq_X_seq` (Colcombet Theorem 4.1 / Algebraic Presentation Theorem): the subsemigroup closure sequence stabilizes at $3 \cdot N(T)$.
* `closure_mem_set_family`: Set-Family Fixed Point Theorem.
* `brown_lemma`: Brown's Lemma on local finiteness.

### `Project/Optimality/`
Bounds and optimality results from Section 3.4 of Colcombet (2008).

* `TruncatedAddition.lean`
  - Balanced factorization trees for the truncated addition semigroup $S_n$.
  - Proves the sub-linear upper bound $\lceil \log_2 n \rceil + 2$.

* `Kufleitner.lean`
  - Kufleitner's lower bound of $3|G| - 1$ for non-trivial finite groups (Theorem 3.6).
  - Optimality of Ramsey splits (Corollary 3.7).

* `Aperiodic.lean`
  - Improved upper bound of $2|S|$ for aperiodic (group-free) semigroups (Theorem 3.8).
  - Tightness of the aperiodic bound ($2n - 1$).

## Building the Project

Ensure you have Lean 4 and Lake installed (matching the version in `lean-toolchain`).

```bash
lake build
```
