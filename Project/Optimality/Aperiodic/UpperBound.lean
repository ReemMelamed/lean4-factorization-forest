/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Project.Optimality.Aperiodic.Basic
import Project.FactorizationTree.FactorizationTree
import Project.SimonSplit.Split

/-!
# Aperiodic Semigroups — Upper Bound (Theorem 3.8)

For any aperiodic (group-free) finite semigroup `S`, every non-empty word admits
a Ramsey factorization tree of height at most `2 * |S|`.

## Mathematical background

In an aperiodic semigroup, every subgroup is trivial. This means:
- Every idempotent `e` satisfies `eHe = {e}` (its H-class is a singleton)
- The Simon split theorem applied to an aperiodic semigroup only produces binary
  nodes (no idempotent nodes with ≥ 2 children that need 3 levels each)
- Hence the height bound reduces from `3 * nS(S) - 1` to at most `2 * |S|`

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

namespace Optimality

open FactorizationTree

universe u

/-- Theorem 3.8 (Upper bound): for an aperiodic finite semigroup `S`, every word admits
a Ramsey factorization tree of height at most `2 * |S|`.

Proven by M. Kufleitner in *The height of factorization forests*, MFCS 2008 (LNCS 5162,
pp. 443–454); see also T. Colcombet, *The Factorization Forest Theorem*, Section 3.4,
Theorem 3.8. -/
axiom aperiodic_factorization_tree_bound
    {A : Type*} {S : Type u} [Semigroup S] [Fintype S] (h_ap : IsAperiodic S)
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 2 * Fintype.card S

end Optimality

end SimonSplit
