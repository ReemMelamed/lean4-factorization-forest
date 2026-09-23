/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Project.FactorizationTree.FactorizationTree

/-!
# Aperiodic Semigroups, Basic Definitions

Definitions of aperiodicity and properties of $\mathcal{H}$-classes in aperiodic semigroups.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]

-/

namespace SimonSplit

namespace Optimality

universe u

section AperiodicSemigroup

/-- A semigroup is *aperiodic* (or *group-trivial* / *group-free*) if every subgroup
of `S` is trivial: whenever a group `G` embeds into `S` as a subsemigroup, `G` must
be a subsingleton. -/
def IsAperiodic (S : Type u) [Semigroup S] : Prop :=
  ∀ {G : Type u} [Group G] (f : G → S),
    (∀ a b, f (a * b) = f a * f b) → Function.Injective f → Subsingleton G

/-- For any finite semigroup of size at least 2, the aperiodic bound `2 * |S|`
is strictly smaller than the general bound `3 * |S| - 1`. -/
theorem aperiodic_bound_strictly_better {S : Type*} [Fintype S]
    (hS : 2 ≤ Fintype.card S) :
    2 * Fintype.card S < 3 * Fintype.card S - 1 := by
  omega

end AperiodicSemigroup

end Optimality

end SimonSplit
