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

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

namespace Optimality

open FactorizationTree

section GroupProperties

lemma group_idempotent_eq_one {G : Type*} [Group G] (e : G) (he : e * e = e) : e = 1 := by
  have h : e * e = e * 1 := by rw [he, mul_one]
  exact mul_left_cancel h

lemma group_idempotent_node_eval_one {G : Type*} [Group G] (eval : List G → G)
    {children : List (FactorizationTree G)}
    (ht : (FactorizationTree.idempotent children).IsRamsey eval) :
    ∀ c ∈ children, eval (FactorizationTree.value c) = 1 := by
  obtain ⟨_hlen, _hramsey, e, he_idem, he_children⟩ := ht
  have he_one : e = 1 := group_idempotent_eq_one e he_idem
  intro c hc
  rw [he_children c hc, he_one]

lemma no_idempotent_root_of_children_eval {G : Type*} [Group G] (eval : List G → G)
    (t : FactorizationTree G) (cs : List (FactorizationTree G))
    (ht_eq : t = FactorizationTree.idempotent cs)
    (ht_ramsey : t.IsRamsey eval) :
    ∀ c ∈ cs, eval (FactorizationTree.value c) = 1 := by
  subst ht_eq
  exact group_idempotent_node_eval_one eval ht_ramsey

end GroupProperties

section LowerBound

theorem kufleitner_lower_bound (G : Type*) [Group G] [Fintype G] (hG : 1 < Fintype.card G)
    (eval : List G → G) (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (hcanon : ∀ g : G, eval [g] = g) :
    ∃ w : List G, w ≠ [] ∧ ∀ t : FactorizationTree G,
      t.value = w → t.IsRamsey eval → 3 * Fintype.card G - 1 ≤ t.height := by
    sorry

end LowerBound

section RamseySplitBound

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
