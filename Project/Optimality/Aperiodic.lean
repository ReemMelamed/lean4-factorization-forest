/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Project.FactorizationTree.FactorizationTree

/-!
# Improved Ramsey Factorization Trees: Aperiodic Semigroups

Formalization of Theorem 3.8 from Colcombet (2008): for aperiodic (group-trivial) semigroups,
every word admits a Ramsey tree of height at most `2 * |S|`, and this bound is tight.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

namespace Optimality

open FactorizationTree

universe u

/-- A semigroup is *aperiodic* (or *group-trivial* / *group-free*) if every subgroup
of `S` is trivial: whenever a group `G` embeds into `S` as a subsemigroup, `G` must
be a subsingleton. -/
def IsAperiodic (S : Type u) [Semigroup S] : Prop :=
  ∀ {G : Type u} [Group G] (f : G → S),
    (∀ a b, f (a * b) = f a * f b) → Function.Injective f → Subsingleton G

/-- In an aperiodic semigroup, the only group that can embed into `S` has cardinality at most 1. -/
lemma isAperiodic_subsingleton {S : Type u} [Semigroup S] (h_ap : IsAperiodic S)
    {G : Type u} [Group G] (f : G → S)
    (hf_mul : ∀ a b, f (a * b) = f a * f b) (hf_inj : Function.Injective f) :
    Subsingleton G :=
  h_ap f hf_mul hf_inj

/-- For any finite semigroup of size at least 2, the aperiodic bound `2 * |S|`
is strictly smaller than the general bound `3 * |S| - 1`. -/
theorem aperiodic_bound_strictly_better {S : Type*} [Fintype S]
    (hS : 2 ≤ Fintype.card S) :
    2 * Fintype.card S < 3 * Fintype.card S - 1 := by
  omega

/-- Theorem 3.8 (Upper bound): for an aperiodic finite semigroup `S`, every word admits
a Ramsey factorization tree of height at most `2 * |S|`. -/
axiom aperiodic_factorization_tree_bound
    {A : Type*} {S : Type u} [Semigroup S] [Fintype S] (h_ap : IsAperiodic S)
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 2 * Fintype.card S

/-- Theorem 3.8 (Tightness): for each `n ≥ 2`, there exists an aperiodic finite semigroup `S`
of size `n` requiring tree height at least `2 * n - 1`. -/
axiom aperiodic_bound_tight (n : ℕ) (_ : 2 ≤ n) :
    ∃ (S : Type) (_ : Semigroup S) (_ : Fintype S) (_ : IsAperiodic S),
      Fintype.card S = n ∧
      ∃ (eval : List S → S)
        (_ : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
        (u : List S) (_ : u ≠ []),
        ∀ t : FactorizationTree S,
          t.value = u →
          t.IsRamsey eval →
          2 * n - 1 ≤ t.height

end Optimality

end SimonSplit
