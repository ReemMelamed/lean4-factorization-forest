/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Card
import Project.FactorizationTree.FactorizationTree
import Project.SimonSplit.Split

/-!
# Optimality of the Bounds for Groups: Kufleitner's Lower Bound

Lower bounds for groups from Section 3.4 of Colcombet (2008): the Chalopin--Leung-style
`|G|` lower bound for factorization trees, and its corresponding consequence for Ramsey
splits.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

namespace Optimality

open FactorizationTree

section GroupProperties

/-- In any group `G`, the only idempotent element is the identity `1`. -/
lemma group_idempotent_eq_one {G : Type*} [Group G] (e : G) (he : e * e = e) : e = 1 := by
  have h : e * e = e * 1 := by rw [he, mul_one]
  exact mul_left_cancel h

/-- In any group `G`, every child of an idempotent node in a Ramsey factorization tree
evaluates to `1`. -/
lemma group_idempotent_node_eval_one {G : Type*} [Group G] (eval : List G → G)
    {children : List (FactorizationTree G)}
    (ht : (FactorizationTree.idempotent children).IsRamsey eval) :
    ∀ c ∈ children, eval (FactorizationTree.value c) = 1 := by
  obtain ⟨_hlen, _hramsey, e, he_idem, he_children⟩ := ht
  have he_one : e = 1 := group_idempotent_eq_one e he_idem
  intro c hc
  rw [he_children c hc, he_one]

/-- If a node is idempotent in a Ramsey factorization tree over a group,
its children all evaluate to `1`. -/
lemma no_idempotent_root_of_children_eval {G : Type*} [Group G] (eval : List G → G)
    (t : FactorizationTree G) (cs : List (FactorizationTree G))
    (ht_eq : t = FactorizationTree.idempotent cs)
    (ht_ramsey : t.IsRamsey eval) :
    ∀ c ∈ cs, eval (FactorizationTree.value c) = 1 := by
  subst ht_eq
  exact group_idempotent_node_eval_one eval ht_ramsey

end GroupProperties

section LowerBound

/-- Chalopin--Leung-style lower bound: for any non-trivial finite group `G`, and any
multiplicative evaluation which evaluates singleton words canonically, there exists a
non-empty word whose Ramsey trees have height at least `|G|`.

The singleton hypothesis is essential: the multiplicativity condition only constrains
non-empty concatenations and does not determine the values of singleton words. -/
axiom kufleitner_lower_bound (G : Type*) [Group G] [Fintype G] (hG : 1 < Fintype.card G)
    (eval : List G → G) (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (hcanon : ∀ g : G, eval [g] = g) :
    ∃ w : List G, w ≠ [] ∧ ∀ t : FactorizationTree G,
      t.value = w → t.IsRamsey eval → Fintype.card G ≤ t.height

end LowerBound

section RamseySplitBound

/-- A factorization-tree lower bound gives the corresponding bound for Ramsey splits.

The factorization tree produced from a split has height at most `3 * h`, so the
correct consequence of the `|G|` tree bound is `|G| ≤ 3 * h`; a bound of `|G| ≤ h`
does not follow from the available conversion. -/
theorem ramsey_split_lower_bound (G : Type*) [Group G] [Fintype G] (hG : 1 < Fintype.card G)
    (eval : List G → G) (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (hcanon : ∀ g : G, eval [g] = g) :
    ∃ w : List G, w ≠ [] ∧
      ∀ (_split_to_tree : ∀ (h : ℕ), (∃ s : Split (Fin (w.length + 1)) h,
        IsRamsey (wordLabeling eval hmul w) s) →
        ∃ t : FactorizationTree G, t.value = w ∧ t.IsRamsey eval ∧ t.height ≤ 3 * h),
      ∀ (h : ℕ), (∃ s : Split (Fin (w.length + 1)) h,
        IsRamsey (wordLabeling eval hmul w) s) →
      Fintype.card G ≤ 3 * h := by
  obtain ⟨w, hw_ne, hw_tree⟩ := kufleitner_lower_bound G hG eval hmul hcanon
  exact ⟨w, hw_ne, fun split_to_tree h hs ↦ by
    obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ := split_to_tree h hs
    have h_tree_ge := hw_tree t ht_val ht_ramsey
    omega⟩

end RamseySplitBound

end Optimality

end SimonSplit
