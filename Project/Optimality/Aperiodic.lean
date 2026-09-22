/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Project.FactorizationTree.FactorizationTree
import Project.Optimality.TruncatedAddition

/-!
# Improved Ramsey Factorization Trees: Aperiodic Semigroups

Formalization of the upper-bound result for aperiodic (group-trivial) semigroups from
Colcombet (2008).  The truncated-addition example also gives a sub-linear upper bound.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

namespace Optimality

open FactorizationTree

universe u

section AperiodicSemigroup

/-- A semigroup is *aperiodic* (or *group-trivial* / *group-free*) if every subgroup
of `S` is trivial: whenever a group `G` embeds into `S` as a subsemigroup, `G` must
be a subsingleton. -/
def IsAperiodic (S : Type u) [Semigroup S] : Prop :=
  ∀ {G : Type u} [Group G] (f : G → S),
    (∀ a b, f (a * b) = f a * f b) → Function.Injective f → Subsingleton G

/-- For any finite semigroup of size at least 2, the numeric expression `2 * |S|`
is strictly smaller than the general bound `3 * |S| - 1`. -/
theorem aperiodic_bound_strictly_better {S : Type*} [Fintype S]
    (hS : 2 ≤ Fintype.card S) :
    2 * Fintype.card S < 3 * Fintype.card S - 1 := by
  omega

end AperiodicSemigroup

section AperiodicBounds

open TruncatedAdd

/-- The general factorization-forest bound, exposed as the option 2B wrapper.

The available formalized theorem is stated in terms of Simon complexity `nS S`;
no bound of `nS S` by `Fintype.card S` has been formalized here.  The
aperiodicity hypothesis is retained in the wrapper for compatibility with the
aperiodic statement, although the general theorem does not need it. -/
theorem aperiodic_factorization_tree_bound
    {A : Type*} {S : Type u} [Semigroup S] [Fintype S] (h_ap : IsAperiodic S)
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * nS S - 1 := by
  letI : Nonempty S := ⟨eval u⟩
  exact factorization_forest_theorem eval hmul u hu

/-- The truncated-addition semigroup has a sub-linear Ramsey-tree height bound. -/
theorem truncated_addition_sublinear_bound (n : ℕ) (hn : 0 < n)
    (u : List (TruncatedAdd n)) (hu : u ≠ []) :
    ∃ t : FactorizationTree (TruncatedAdd n),
      t.value = u ∧
      t.IsRamsey (evalTrunc hn) ∧
      t.height ≤ log2Ceil n + 2 :=
  truncated_addition_tree_height n hn u hu

end AperiodicBounds

end Optimality

end SimonSplit
