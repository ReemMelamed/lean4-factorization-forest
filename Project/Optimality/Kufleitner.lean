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

/-- Kufleitner's lower bound (Theorem 3.6): for any non-trivial finite group `G`, there exists
a non-empty word whose Ramsey trees have height at least `3 * |G| - 1`.

**Mathematical content (Kufleitner 2008, Colcombet §3.4)**:
The key insight is that in a group G, the only idempotent is the identity `1`.
Therefore in a Ramsey tree, any idempotent node forces all its children to evaluate
to `1`. For the canonical evaluation morphism `eval w = w.prod`, Kufleitner constructs
a word `w_G` such that any Ramsey tree computing it must have height ≥ 3|G| - 1.

The construction proceeds by induction on |G|: pick any non-identity generator g,
build sub-words forcing the tree to repeatedly resolve conflicts between g and its
inverse, requiring 3|G| - 1 levels in the worst case. -/
theorem kufleitner_lower_bound (G : Type*) [Group G] [Fintype G] (hG : 1 < Fintype.card G)
    (eval : List G → G) (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v) :
    ∃ w : List G, w ≠ [] ∧ ∀ t : FactorizationTree G,
      t.value = w → t.IsRamsey eval → 3 * Fintype.card G - 1 ≤ t.height := by
  -- Key helper: eval is multiplicative so eval([g]) is well-defined for any g : G
  -- We pick a non-identity generator to build Kufleitner's word
  obtain ⟨g, hg_ne⟩ : ∃ g : G, g ≠ 1 := by
    by_contra h
    push Not at h
    have : Fintype.card G = 1 := Fintype.card_eq_one_iff.mpr ⟨1, fun x => h x⟩
    omega
  -- Kufleitner's word w_G is built inductively on the group structure.
  -- For a group of order k, w_G has length 3*k - 2 and any Ramsey tree has height ≥ 3*k - 1.
  --
  -- The construction is:
  --   w_{G,g} = w_{G/⟨g⟩, ...} · [g] · [g⁻¹] · w_{G/⟨g⟩, ...}
  -- where the recursion terminates when the quotient is trivial.
  --
  -- The height lower bound follows by induction:
  --   Any Ramsey tree for w_G must have an idempotent node at or above level 3(k-1)-1,
  --   and that node's evaluation (= 1 in a group) forces two sub-trees each needing depth
  --   3(k-1)-1, plus 1 for the binary parent, giving total ≥ 3k-1.
  --
  -- This is a non-trivial inductive proof requiring careful case analysis on tree structure.
  sorry


end LowerBound

section RamseySplitBound

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
  exact ⟨w, hw_ne, fun split_to_tree h hs ↦ by
    by_contra h_lt
    push Not at h_lt
    obtain ⟨t, ht_val, ht_ramsey, ht_height⟩ := split_to_tree h hs
    have h_tree_ge := hw_tree t ht_val ht_ramsey
    have : 3 * h ≤ 3 * (Fintype.card G - 1) := by omega
    omega⟩

end RamseySplitBound

end Optimality

end SimonSplit
