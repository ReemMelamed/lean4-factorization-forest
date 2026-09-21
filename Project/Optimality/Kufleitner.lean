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

Lower bounds for groups from Section 3.4 of Colcombet (2008): Kufleitner's lower bound of
`3|G| - 1` for factorization trees (Theorem 3.6) and `|G|` for Ramsey splits (Corollary 3.7).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

namespace Optimality

open FactorizationTree

/-! ### Algebraic Properties of Groups in Ramsey Factorization Trees -/

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

/-! ### Theorem 3.6 (Kufleitner's Lower Bound) -/

/-- Kufleitner's lower bound (Theorem 3.6): for any non-trivial finite group `G`, there exists
a non-empty word whose Ramsey trees have height at least `3 * |G| - 1`. -/
axiom kufleitner_lower_bound (G : Type*) [Group G] [Fintype G] (hG : 1 < Fintype.card G)
    (eval : List G → G) (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v) :
    ∃ w : List G, w ≠ [] ∧ ∀ t : FactorizationTree G,
      t.value = w → t.IsRamsey eval → 3 * Fintype.card G - 1 ≤ t.height

/-! ### Corollary 3.7 (Optimality of the Bound for Splits) -/

/-- Optimality of Ramsey splits (Corollary 3.7): for any non-trivial finite group `G`,
there exists a word whose Ramsey splits have height at least `|G|`. -/
theorem ramsey_split_lower_bound (G : Type*) [Group G] [Fintype G] (hG : 1 < Fintype.card G)
    (eval : List G → G) (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v) :
    ∃ w : List G, w ≠ [] ∧
      ∀ (_split_to_tree : ∀ (h : ℕ), (∃ s : Split (Fin (w.length + 1)) h,
        IsRamsey (wordLabeling eval hmul w) s) →
        ∃ t : FactorizationTree G, t.value = w ∧ t.IsRamsey eval ∧ t.height ≤ 3 * h),
      ∀ (h : ℕ), (∃ s : Split (Fin (w.length + 1)) h,
        IsRamsey (wordLabeling eval hmul w) s) →
      Fintype.card G ≤ h := by
  obtain ⟨w, hw_ne, hw_tree⟩ := kufleitner_lower_bound G hG eval hmul
  refine ⟨w, hw_ne, ?_⟩
  intro split_to_tree h hs
  by_contra h_lt
  push Not at h_lt
  obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ := split_to_tree h hs
  have h_tree_ge := hw_tree t ht_val ht_ramsey
  have : 3 * h ≤ 3 * (Fintype.card G - 1) := by omega
  omega

end Optimality

end SimonSplit
