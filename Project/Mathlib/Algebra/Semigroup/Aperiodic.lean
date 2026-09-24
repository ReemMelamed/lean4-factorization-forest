/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Infix
import Project.Mathlib.Combinatorics.FactorizationForest.Tree
import Project.Mathlib.Combinatorics.FactorizationForest.TruncatedAddition

/-!
# Aperiodic Semigroups and Height Bounds

This file defines aperiodic (group-free / group-trivial) semigroups.
A semigroup `S` is aperiodic if every group embedding `G → S` has a subsingleton domain.

It also contains:
* `truncatedAdd_isAperiodic`: The truncated addition semigroup `TruncatedAdd n` is aperiodic.
* `aperiodic_bound_tight`: The `2|S|` bound is tight for aperiodic semigroups (Theorem 3.8).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
* [M. Kufleitner, *The Height of Factorization Forests for Aperiodic Semigroups*][kufleitner2008]
-/

universe u

/-- A semigroup is *aperiodic* if every subgroup of `S` is trivial:
whenever a group `G` embeds into `S` as a subsemigroup, `G` must be a subsingleton. -/
def IsAperiodic (S : Type u) [Semigroup S] : Prop :=
  ∀ {G : Type u} [Group G] (f : G → S),
    (∀ a b, f (a * b) = f a * f b) → Function.Injective f → Subsingleton G

namespace Aperiodic

open Optimality TruncatedAdd FactorizationTree

section TruncatedAddition

/-- The truncated addition semigroup `TruncatedAdd n` is aperiodic (group-free). -/
lemma truncatedAdd_isAperiodic (n : ℕ) (hn : 0 < n) : IsAperiodic (TruncatedAdd n) := by
  unfold IsAperiodic
  intro G _ f hf_mul hf_inj
  constructor
  intro a b
  have h_f1_idem : f 1 * f 1 = f 1 := by
    have h : f (1 * 1) = f 1 * f 1 := hf_mul 1 1
    rw [one_mul] at h
    exact h.symm
  have h_f1_top : f 1 = TruncatedAdd.top hn :=
    TruncatedAdd.idempotent_eq_top hn (f 1) h_f1_idem
  have h_all_top : ∀ g : G, f g = TruncatedAdd.top hn := fun g => by
    have h : f 1 * f g = f g := by
      have := hf_mul 1 g
      rw [one_mul] at this
      exact this.symm
    rw [h_f1_top] at h
    rw [TruncatedAdd.top_mul_any hn (f g)] at h
    exact h.symm
  exact hf_inj ((h_all_top a).trans (h_all_top b).symm)

end TruncatedAddition

section Tightness

/-- The max semigroup on `Fin n`. -/
def MaxSemigroup (n : ℕ) := Fin n

instance (n : ℕ) : LinearOrder (MaxSemigroup n) :=
  inferInstanceAs (LinearOrder (Fin n))

instance (n : ℕ) : Semigroup (MaxSemigroup n) where
  mul a b := max a b
  mul_assoc a b c := max_assoc a b c

instance (n : ℕ) : Fintype (MaxSemigroup n) :=
  inferInstanceAs (Fintype (Fin n))

/-- The cardinality of `MaxSemigroup n` is `n`. -/
lemma maxSemigroup_card (n : ℕ) : Fintype.card (MaxSemigroup n) = n :=
  Fintype.card_fin n

/-- The max semigroup on `Fin n` is aperiodic (group-free). -/
lemma maxSemigroup_isAperiodic (n : ℕ) : IsAperiodic (MaxSemigroup n) := by
  intro G _ f hf_mul hf_inj
  constructor
  intro a b
  have h_le_one : ∀ g : G, f 1 ≤ f g := fun g => by
    have h : f g = f g * f 1 := by rw [← hf_mul, mul_one]
    change f g = max (f g) (f 1) at h
    have : f 1 ≤ max (f g) (f 1) := le_max_right (f g) (f 1)
    rwa [← h] at this
  have h_one_le : ∀ g : G, f g ≤ f 1 := fun g => by
    have h : f 1 = f g * f g⁻¹ := by rw [← hf_mul, mul_inv_cancel]
    change f 1 = max (f g) (f g⁻¹) at h
    have : f g ≤ max (f g) (f g⁻¹) := le_max_left (f g) (f g⁻¹)
    rwa [← h] at this
  have h_eq_one : ∀ g : G, f g = f 1 := fun g =>
    le_antisymm (h_one_le g) (h_le_one g)
  exact hf_inj ((h_eq_one a).trans (h_eq_one b).symm)

/-- The bottom element of `MaxSemigroup n`. -/
def botEl (n : ℕ) (hn : 0 < n) : MaxSemigroup n := ⟨0, hn⟩

/-- Evaluator for `MaxSemigroup n`: maps a list to the maximum element (with default 0). -/
def evalMax (n : ℕ) (hn : 0 < n) (u : List (MaxSemigroup n)) : MaxSemigroup n :=
  u.foldl max (botEl n hn)

/-- The bottom element is less than or equal to any element in `MaxSemigroup n`. -/
lemma botEl_le (n : ℕ) (hn : 0 < n) (x : MaxSemigroup n) : botEl n hn ≤ x := by
  change 0 ≤ x.val
  omega

/-- Taking the maximum with `botEl` on the left is the identity. -/
lemma max_botEl_left (n : ℕ) (hn : 0 < n) (x : MaxSemigroup n) :
    max (botEl n hn) x = x :=
  max_eq_right (botEl_le n hn x)

/-- Left-folding `max` over a list with initial element `z` equals `max z (evalMax n hn u)`. -/
lemma foldl_max_eq_max (n : ℕ) (hn : 0 < n) (u : List (MaxSemigroup n)) (z : MaxSemigroup n) :
    u.foldl max z = max z (evalMax n hn u) := by
  induction u generalizing z with
  | nil =>
    simp only [List.foldl_nil, evalMax]
    exact (max_eq_left (botEl_le n hn z)).symm
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih (max z x)]
    have h_ev : evalMax n hn (x :: xs) = max x (evalMax n hn xs) := by
      change xs.foldl max (max (botEl n hn) x) = max x (evalMax n hn xs)
      rw [max_botEl_left]
      exact ih x
    rw [h_ev, max_assoc]

/-- The evaluation map `evalMax` distributes over list concatenation. -/
lemma evalMax_append (n : ℕ) (hn : 0 < n) (u v : List (MaxSemigroup n)) :
    evalMax n hn (u ++ v) = evalMax n hn u * evalMax n hn v := by
  change (u ++ v).foldl max (botEl n hn) = max (evalMax n hn u) (evalMax n hn v)
  rw [List.foldl_append]
  exact foldl_max_eq_max n hn v (evalMax n hn u)

/-- Any element in a list is bounded by the maximum evaluation of the list. -/
lemma evalMax_ge_of_mem (n : ℕ) (hn : 0 < n) {x : MaxSemigroup n} {u : List (MaxSemigroup n)}
    (hx : x ∈ u) : x ≤ evalMax n hn u := by
  induction u with
  | nil => contradiction
  | cons y ys ih =>
    have h_ev : evalMax n hn (y :: ys) = max y (evalMax n hn ys) := by
      change ys.foldl max (max (botEl n hn) y) = max y (evalMax n hn ys)
      rw [max_botEl_left, foldl_max_eq_max]
    rw [h_ev]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | h_tail
    · exact le_max_left x _
    · exact (ih h_tail).trans (le_max_right y _)

/-- If a non-bottom element `k` is bounded by the evaluation of a list,
some element in the list is at least `k`. -/
lemma exists_mem_ge_of_evalMax_ge (n : ℕ) (hn : 0 < n) {k : MaxSemigroup n}
    {u : List (MaxSemigroup n)} (hk : botEl n hn < k) (h : k ≤ evalMax n hn u) :
    ∃ x ∈ u, k ≤ x := by
  induction u with
  | nil =>
    dsimp [evalMax] at h
    exact (not_le_of_gt hk h).elim
  | cons y ys ih =>
    have h_ev : evalMax n hn (y :: ys) = max y (evalMax n hn ys) := by
      change ys.foldl max (max (botEl n hn) y) = max y (evalMax n hn ys)
      rw [max_botEl_left, foldl_max_eq_max]
    rw [h_ev] at h
    rcases le_max_iff.mp h with h1 | h2
    · exact ⟨y, .head ys, h1⟩
    · obtain ⟨x, hx_mem, hkx⟩ := ih h2
      exact ⟨x, .tail y hx_mem, hkx⟩

/-- In an idempotent node of a Ramsey tree, if one child contains an element `≥ k`,
then every child contains an element `≥ k`. -/
lemma idempotent_children_mem_ge {n : ℕ} (hn : 0 < n)
    {cs : List (FactorizationTree (MaxSemigroup n))}
    (_h_ramsey : listIsRamsey (evalMax n hn) cs)
    (e : MaxSemigroup n) (he_eval : ∀ t ∈ cs, evalMax n hn (value t) = e)
    (k : MaxSemigroup n) (hk_pos : botEl n hn < k)
    (t : FactorizationTree (MaxSemigroup n)) (ht : t ∈ cs)
    (x : MaxSemigroup n) (hx : x ∈ value t) (hkx : k ≤ x) :
    ∀ c ∈ cs, ∃ y ∈ value c, k ≤ y := by
  have h_ev : k ≤ evalMax n hn (value t) := hkx.trans (evalMax_ge_of_mem n hn hx)
  rw [he_eval t ht] at h_ev
  intro c hc
  have hc_ev : k ≤ evalMax n hn (value c) := by rw [he_eval c hc]; exact h_ev
  exact exists_mem_ge_of_evalMax_ge n hn hk_pos hc_ev

/-- No child of an idempotent node can have its yield contained in a word
whose elements are all strictly less than `k`. -/
lemma no_child_infix_of_all_lt {n : ℕ} (hn : 0 < n)
    {cs : List (FactorizationTree (MaxSemigroup n))}
    (_h_ramsey : listIsRamsey (evalMax n hn) cs)
    (e : MaxSemigroup n) (he_eval : ∀ t ∈ cs, evalMax n hn (value t) = e)
    (k : MaxSemigroup n) (hk_pos : botEl n hn < k)
    (t : FactorizationTree (MaxSemigroup n)) (ht : t ∈ cs)
    (x : MaxSemigroup n) (hx : x ∈ value t) (hkx : k ≤ x)
    (v : List (MaxSemigroup n)) (hv : ∀ y ∈ v, y < k)
    (c : FactorizationTree (MaxSemigroup n)) (hc : c ∈ cs) :
    ¬ (value c <:+: v) := by
  intro h_inf
  obtain ⟨y, hy_mem, hky⟩ :=
    idempotent_children_mem_ge hn _h_ramsey e he_eval k hk_pos t ht x hx hkx c hc
  have hy_in_v : y ∈ v := h_inf.subset hy_mem
  have := hv y hy_in_v
  exact not_le_of_gt this hky

/-- Triple repetition of a list `l ++ l ++ l`, representing $l^3$.
In Kufleitner's construction, three copies force any binary node splitting
the word to contain an entire copy of `l` in one of its subtrees. -/
def repeatThree {α : Type*} (l : List α) : List α :=
  l ++ l ++ l

/-- Nine-fold repetition `repeatThree (repeatThree l)`, representing $l^9 = (l^3)^3$.
Forces idempotent nodes to contain a three-fold repetition in at least one child. -/
def repeatNine {α : Type*} (l : List α) : List α :=
  repeatThree (repeatThree l)

/-- 27-fold repetition `repeatThree (repeatNine l)`, representing $l^{27} = ((l^3)^3)^3$.
Forces tree height to decrease by at least 2 levels across grandparent and grandchild nodes. -/
def repeatTwentySeven {α : Type*} (l : List α) : List α :=
  repeatThree (repeatNine l)

/-- Triple repetition of a non-empty list is non-empty. -/
lemma repeatThree_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : repeatThree l ≠ [] := by
  dsimp [repeatThree]
  simp [hl]

/-- Nine-fold repetition of a non-empty list is non-empty. -/
lemma repeatNine_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : repeatNine l ≠ [] :=
  repeatThree_ne_nil (repeatThree_ne_nil hl)

/-- 27-fold repetition of a non-empty list is non-empty. -/
lemma repeatTwentySeven_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : repeatTwentySeven l ≠ [] :=
  repeatThree_ne_nil (repeatNine_ne_nil hl)

/-- Membership in `repeatThree l` implies membership in `l`. -/
lemma mem_repeatThree {α : Type*} {l : List α} {x : α} (hx : x ∈ repeatThree l) : x ∈ l := by
  dsimp [repeatThree] at hx
  rcases List.mem_append.mp hx with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · exact h1
    · exact h2
  · exact h3

/-- Membership in `repeatNine l` implies membership in `l`. -/
lemma mem_repeatNine {α : Type*} {l : List α} {x : α} (hx : x ∈ repeatNine l) : x ∈ l :=
  mem_repeatThree (mem_repeatThree hx)

/-- Membership in `repeatTwentySeven l` implies membership in `l`. -/
lemma mem_repeatTwentySeven {α : Type*} {l : List α} {x : α}
    (hx : x ∈ repeatTwentySeven l) : x ∈ l :=
  mem_repeatNine (mem_repeatThree hx)

/-- If $X ++ Y = Z ++ W$ and $|Z| \le |X|$, then $Z$ is a prefix of $X$. -/
lemma prefix_of_append_eq_append_left {α : Type*} (X Y Z W : List α)
    (h : X ++ Y = Z ++ W) (hle : Z.length ≤ X.length) :
    Z <+: X := by
  have h_take := congrArg (List.take Z.length) h
  rw [List.take_append_of_le_length hle] at h_take
  have h_Z : (Z ++ W).take Z.length = Z := by simp
  rw [h_Z] at h_take
  exact h_take ▸ List.take_prefix Z.length X

/-- If a triple repetition $l ++ l ++ l$ occurs in an append $A ++ B$,
then $l$ is an infix of $A$ or an infix of $B$. -/
lemma repeatThree_append_cases {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (s t : List α) (h : A ++ B = s ++ (l ++ l ++ l) ++ t) :
    l <:+: A ∨ l <:+: B := by
  by_cases hA : s.length + l.length ≤ A.length
  · left
    have h_assoc : s ++ (l ++ l ++ l) ++ t = (s ++ l) ++ (l ++ l ++ t) := by
      simp only [List.append_assoc]
    have h_pref := prefix_of_append_eq_append_left A B (s ++ l) (l ++ l ++ t)
      (h.trans h_assoc) (by simpa using hA)
    have h_inf : l <:+: s ++ l := by
      use s, []
      simp
    exact h_inf.trans h_pref.isInfix
  · right
    have h2 : B = (A ++ B).drop A.length := by simp
    rw [h] at h2
    have h_assoc : s ++ (l ++ l ++ l) ++ t = (s ++ l ++ l) ++ (l ++ t) := by
      simp only [List.append_assoc]
    rw [h_assoc] at h2
    rw [List.drop_append] at h2
    have h_le : A.length ≤ (s ++ l ++ l).length := by
      have : 1 ≤ l.length := List.length_pos_iff.mpr hl
      simp only [List.length_append]
      omega
    have h_sub : A.length - (s ++ l ++ l).length = 0 := by omega
    rw [h_sub, List.drop_zero] at h2
    use ((s ++ l ++ l).drop A.length), t
    rw [h2]
    simp only [List.append_assoc]

/-- If `repeatThree l` is an infix of $A ++ B$, then $l$ is an infix of $A$ or an infix of $B$. -/
lemma repeatThree_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : repeatThree l <:+: A ++ B) :
    l <:+: A ∨ l <:+: B := by
  obtain ⟨s, t, hst⟩ := h
  exact repeatThree_append_cases l hl A B s t hst.symm

/-- If `repeatNine l` is an infix of $A ++ B$, then `repeatThree l` is an infix of $A$ or $B$. -/
lemma repeatNine_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : repeatNine l <:+: A ++ B) :
    repeatThree l <:+: A ∨ repeatThree l <:+: B :=
  repeatThree_isInfix_append (repeatThree l) (repeatThree_ne_nil hl) A B h

/-- If `repeatTwentySeven l` is an infix of $A ++ B$,
then `repeatNine l` is an infix of $A$ or $B$. -/
lemma repeatTwentySeven_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : repeatTwentySeven l <:+: A ++ B) :
    repeatNine l <:+: A ∨ repeatNine l <:+: B :=
  repeatThree_isInfix_append (repeatNine l) (repeatNine_ne_nil hl) A B h

/-- `repeatThree l` is an infix of `repeatNine l`. -/
lemma repeatThree_isInfix_repeatNine {α : Type*} (l : List α) :
    repeatThree l <:+: repeatNine l := by
  refine ⟨[], repeatThree l ++ repeatThree l, ?_⟩
  dsimp [repeatNine, repeatThree]
  simp only [List.append_assoc]

/-- `repeatNine l` is an infix of `repeatTwentySeven l`. -/
lemma repeatNine_isInfix_repeatTwentySeven {α : Type*} (l : List α) :
    repeatNine l <:+: repeatTwentySeven l := by
  refine ⟨[], repeatNine l ++ repeatNine l, ?_⟩
  dsimp [repeatTwentySeven, repeatThree]
  simp only [List.append_assoc]

/-- `repeatThree l` is an infix of `repeatTwentySeven l`. -/
lemma repeatThree_isInfix_repeatTwentySeven {α : Type*} (l : List α) :
    repeatThree l <:+: repeatTwentySeven l :=
  (repeatThree_isInfix_repeatNine l).trans (repeatNine_isInfix_repeatTwentySeven l)

/-- A list `l` is an infix of its triple repetition `repeatThree l`. -/
lemma infix_repeatThree_of_self {α : Type*} (l : List α) : l <:+: repeatThree l := by
  refine ⟨[], l ++ l, ?_⟩
  dsimp [repeatThree]
  simp only [List.append_assoc]

/-- A list `l` is an infix of its nine-fold repetition `repeatNine l`. -/
lemma infix_repeatNine_of_self {α : Type*} (l : List α) : l <:+: repeatNine l :=
  (infix_repeatThree_of_self l).trans (repeatThree_isInfix_repeatNine l)

/-- A list `l` is an infix of its 27-fold repetition `repeatTwentySeven l`. -/
lemma infix_repeatTwentySeven_of_self {α : Type*} (l : List α) : l <:+: repeatTwentySeven l :=
  (infix_repeatNine_of_self l).trans (repeatNine_isInfix_repeatTwentySeven l)

/-- If a non-empty word $u$ is an infix of `listValue cs` and no single child has $u$ as an infix,
then $u$ is an infix of at most two consecutive children. -/
lemma infix_listValue_two {α : Type*} (cs : List (FactorizationTree α))
    (u : List α) (hu : u ≠ [])
    (h_no : ∀ c ∈ cs, ¬ (value c <:+: u))
    (h_inf : u <:+: listValue cs) :
    (∃ c ∈ cs, u <:+: value c) ∨
    (∃ c₁ ∈ cs, ∃ c₂ ∈ cs, u <:+: value c₁ ++ value c₂) := by
  induction cs with
  | nil =>
    obtain ⟨s, t, hst⟩ := h_inf
    dsimp [listValue] at hst
    have hu_nil : u = [] := by
      have h_len := congrArg List.length hst
      simp only [List.length_append, List.length_nil] at h_len
      have : u.length = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    exact (hu hu_nil).elim
  | cons c cs' ih =>
    obtain ⟨s, t, hst⟩ := h_inf
    have h_app : c.value ++ listValue cs' = s ++ u ++ t := hst.symm
    by_cases h1 : (s ++ u).length ≤ (value c).length
    · left
      refine ⟨c, .head _, ?_⟩
      have h_pref := prefix_of_append_eq_append_left (value c) (listValue cs') (s ++ u) t
        (by rw [h_app, List.append_assoc]) (by simpa using h1)
      have h_inf2 : u <:+: s ++ u := by
        use s, []
        simp
      exact h_inf2.trans h_pref.isInfix
    · by_cases h2 : (value c).length ≤ s.length
      · have h_drop : listValue cs' = s.drop (value c).length ++ u ++ t := by
          have h_d := congrArg (List.drop (value c).length) h_app
          rw [List.drop_left] at h_d
          have h_split : s ++ u ++ t = s ++ (u ++ t) := by simp only [List.append_assoc]
          rw [h_split, List.drop_append] at h_d
          have h_sub : (value c).length - s.length = 0 := by omega
          rw [h_sub, List.drop_zero] at h_d
          rw [← List.append_assoc] at h_d
          exact h_d
        have h_inf_cs' : u <:+: listValue cs' := by
          use s.drop (value c).length, t
          exact h_drop.symm
        have h_no_cs' : ∀ d ∈ cs', ¬ (value d <:+: u) := fun d hd =>
          h_no d (.tail c hd)
        rcases ih h_no_cs' h_inf_cs' with ⟨d, hd, hdu⟩ | ⟨d₁, hd₁, d₂, hd₂, hd12⟩
        · left; exact ⟨d, .tail c hd, hdu⟩
        · right; exact ⟨d₁, .tail c hd₁, d₂, .tail c hd₂, hd12⟩
      · right
        simp only [List.length_append] at h1
        have h1_lt : (value c).length < s.length + u.length := by omega
        have h2_lt : s.length < (value c).length := by omega
        let k := (value c).length - s.length
        have hk_pos : 0 < k := by omega
        have hk_lt : k < u.length := by omega
        have h_split : s ++ u ++ t = (s ++ u.take k) ++ (u.drop k ++ t) := by
          have := List.take_append_drop k u
          nth_rw 1 [← this]
          simp only [List.append_assoc]
        have h_take_c : value c = s ++ u.take k := by
          have h_t := congrArg (List.take (value c).length) h_app
          rw [List.take_left] at h_t
          rw [h_split, List.take_append] at h_t
          have : (value c).length - (s ++ u.take k).length = 0 := by
            simp only [List.length_append, List.length_take]
            omega
          rw [this, List.take_zero, List.append_nil] at h_t
          have h_len_take : (s ++ u.take k).length ≤ (value c).length := by
            simp only [List.length_append, List.length_take]; omega
          rw [List.take_of_length_le h_len_take] at h_t
          exact h_t
        have h_drop_cs' : c.value ++ listValue cs' = (s ++ u.take k) ++ (u.drop k ++ t) := by
          rw [h_app, h_split]
        have h_drop_cs'' : listValue cs' = u.drop k ++ t := by
          rw [h_take_c] at h_drop_cs'
          exact List.append_cancel_left h_drop_cs'
        cases cs' with
        | nil =>
          dsimp [listValue] at h_drop_cs''
          have h_len := congrArg List.length h_drop_cs''
          simp only [List.length_nil, List.length_append, List.length_drop] at h_len
          omega
        | cons c' cs'' =>
          dsimp [listValue] at h_drop_cs''
          by_cases h3 : (u.drop k).length ≤ (value c').length
          · refine ⟨c, .head _, c', .tail _ (.head _), ?_⟩
            have h_pref := prefix_of_append_eq_append_left (value c') (listValue cs'')
              (u.drop k) t h_drop_cs'' h3
            obtain ⟨w, hw⟩ := h_pref
            use s, w
            rw [h_take_c, ← hw]
            have h_mid : (s ++ u.take k) ++ (u.drop k ++ w) = s ++ (u.take k ++ u.drop k) ++ w := by
              simp only [List.append_assoc]
            rw [h_mid, List.take_append_drop]
          · have h3_le : (value c').length ≤ (u.drop k).length := by omega
            have h_pref := prefix_of_append_eq_append_left (u.drop k) t (value c')
              (listValue cs'') h_drop_cs''.symm h3_le
            have h_inf_u : value c' <:+: u := by
              have h_suf : u.drop k <:+ u := by
                use u.take k
                exact List.take_append_drop k u
              exact h_pref.isInfix.trans h_suf.isInfix
            exact (h_no c' (.tail c (.head cs'')) h_inf_u).elim

/-- Every child in a Ramsey list of trees is itself a Ramsey tree. -/
lemma isRamsey_of_mem_listIsRamsey {α S : Type*} [Semigroup S] {eval : List α → S}
    {cs : List (FactorizationTree α)} (h : listIsRamsey eval cs)
    {c : FactorizationTree α} (hc : c ∈ cs) : c.IsRamsey eval := by
  induction cs with
  | nil => contradiction
  | cons head tail ih =>
    dsimp [listIsRamsey] at h
    cases hc with
    | head => exact h.1
    | tail _ hmem => exact ih h.2 hmem

/-- A tree that is not a leaf has height at least 1. -/
lemma height_pos_of_not_leaf {α : Type*} (t : FactorizationTree α)
    (h : ∀ a, t ≠ FactorizationTree.leaf a) :
    1 ≤ t.height := by
  cases t with
  | leaf a => exact (h a rfl).elim
  | binary l r =>
    dsimp [FactorizationTree.height]
    omega
  | idempotent cs =>
    dsimp [FactorizationTree.height]
    omega

/-- The height of any tree in a list is bounded by `listHeight`. -/
lemma mem_listHeight_le {α : Type*} {c : FactorizationTree α} {cs : List (FactorizationTree α)}
    (hc : c ∈ cs) : c.height ≤ FactorizationTree.listHeight cs := by
  induction cs with
  | nil => contradiction
  | cons head tail ih =>
    cases hc with
    | head =>
      dsimp [FactorizationTree.listHeight]
      exact le_max_left _ _
    | tail _ hmem =>
      dsimp [FactorizationTree.listHeight]
      exact (ih hmem).trans (le_max_right _ _)

/-- The height of an idempotent tree is strictly greater than the height of each of its children. -/
lemma height_ge_child_of_idempotent {α : Type*} {cs : List (FactorizationTree α)}
    {c : FactorizationTree α} (hc : c ∈ cs) :
    c.height + 1 ≤ (FactorizationTree.idempotent cs).height := by
  dsimp [FactorizationTree.height]
  have := mem_listHeight_le hc
  omega

/-- The height of a binary tree is strictly greater than the height of its left subtree. -/
lemma height_ge_child_of_binary_left {α : Type*} (l r : FactorizationTree α) :
    l.height + 1 ≤ (FactorizationTree.binary l r).height := by
  dsimp [FactorizationTree.height]
  have := le_max_left l.height r.height
  omega

/-- The height of a binary tree is strictly greater than the height of its right subtree. -/
lemma height_ge_child_of_binary_right {α : Type*} (l r : FactorizationTree α) :
    r.height + 1 ≤ (FactorizationTree.binary l r).height := by
  dsimp [FactorizationTree.height]
  have := le_max_right l.height r.height
  omega

/-- Kufleitner's sequence of hard words $w_k$: constructed inductively by
taking 27 copies of the previous word and appending the next letter $k+1$. -/
def w (n : ℕ) (hn : 0 < n) : ℕ → List (MaxSemigroup n)
  | 0 => repeatTwentySeven [botEl n hn]
  | k + 1 =>
    if h : k + 1 < n then
      repeatTwentySeven (repeatTwentySeven (w n hn k) ++ [⟨k + 1, h⟩])
    else
      repeatTwentySeven (w n hn k)

/-- The word $w_k$ is non-empty for all $k$. -/
lemma w_ne_nil (n : ℕ) (hn : 0 < n) (k : ℕ) : w n hn k ≠ [] := by
  induction k with
  | zero =>
    dsimp [w]
    exact repeatTwentySeven_ne_nil (by simp)
  | succ k' ih =>
    dsimp [w]
    split_ifs
    · exact repeatTwentySeven_ne_nil (by simp)
    · exact repeatTwentySeven_ne_nil ih

/-- Every element in $w_k$ is at most $k$. -/
lemma w_mem_le (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n)
    (x : MaxSemigroup n) (hx : x ∈ w n hn k) : x.val ≤ k := by
  induction k generalizing x with
  | zero =>
    dsimp [w] at hx
    have hx' := mem_repeatTwentySeven hx
    cases hx' with
    | head => rfl
    | tail _ h => contradiction
  | succ k' ih =>
    dsimp [w] at hx
    rw [dif_pos hk] at hx
    have hx' := mem_repeatTwentySeven hx
    rcases List.mem_append.mp hx' with h_rep | h_eq
    · have h_in_wk := mem_repeatTwentySeven h_rep
      have := ih (by omega) x h_in_wk
      omega
    · cases h_eq with
      | head => rfl
      | tail _ h => contradiction

/-- Every element in $w_k$ is strictly less than $k+1$. -/
lemma w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ w n hn k) : x < ⟨k + 1, hk⟩ := by
  have := w_mem_le n hn k (by omega) x hx
  change x.val < k + 1
  omega

/-- Elements of 27-fold repetition of $w_k$ are strictly less than $k+1$. -/
lemma repeatTwentySeven_w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ repeatTwentySeven (w n hn k)) : x < ⟨k + 1, hk⟩ :=
  w_mem_lt n hn k hk x (mem_repeatTwentySeven hx)

/-- Elements of 9-fold repetition of $w_k$ are strictly less than $k+1$. -/
lemma repeatNine_w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ repeatNine (w n hn k)) : x < ⟨k + 1, hk⟩ :=
  w_mem_lt n hn k hk x (mem_repeatNine hx)

/-- Elements of 3-fold repetition of $w_k$ are strictly less than $k+1$. -/
lemma repeatThree_w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ repeatThree (w n hn k)) : x < ⟨k + 1, hk⟩ :=
  w_mem_lt n hn k hk x (mem_repeatThree hx)

/-- Any element in the yield of a list of trees belongs to the yield of some tree in the list. -/
lemma mem_listValue {α : Type*} {cs : List (FactorizationTree α)} {x : α}
    (hx : x ∈ listValue cs) : ∃ t ∈ cs, x ∈ t.value := by
  induction cs with
  | nil => contradiction
  | cons c cs' ih =>
    dsimp [listValue] at hx
    rcases List.mem_append.mp hx with h1 | h2
    · exact ⟨c, .head _, h1⟩
    · obtain ⟨t, ht, hxt⟩ := ih h2
      exact ⟨t, .tail _ ht, hxt⟩

/-- The 9-fold repetition of a non-empty list has length at least 9. -/
lemma repeatNine_length_ge {α : Type*} (l : List α) (hl : l ≠ []) : 9 ≤ (repeatNine l).length := by
  have : 1 ≤ l.length := List.length_pos_iff.mpr hl
  dsimp [repeatNine, repeatThree]
  simp only [List.length_append]
  omega

/-- The 27-fold repetition of a non-empty list has length at least 27. -/
lemma repeatTwentySeven_length_ge {α : Type*} (l : List α) (hl : l ≠ []) :
    27 ≤ (repeatTwentySeven l).length := by
  have : 1 ≤ l.length := List.length_pos_iff.mpr hl
  dsimp [repeatTwentySeven, repeatNine, repeatThree]
  simp only [List.length_append]
  omega

/-- If a 9-fold repetition occurs in a tree,
there exists a child tree of strictly smaller height containing $w_k$. -/
lemma exists_child_w_of_repeatNine_X {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (C : FactorizationTree (MaxSemigroup n))
    (hC_ramsey : C.IsRamsey (evalMax n hn))
    (h_inf : repeatNine (repeatTwentySeven (w n hn k) ++ [⟨k + 1, hk⟩]) <:+: C.value) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 1 ≤ C.height ∧ w n hn k <:+: g.value := by
  let X := repeatTwentySeven (w n hn k) ++ [⟨k + 1, hk⟩]
  change repeatNine X <:+: C.value at h_inf
  have hX_ne : X ≠ [] := by simp [X]
  have h_len_repeatNine := repeatNine_length_ge X hX_ne
  cases C with
  | leaf a =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨s, t, hst⟩ := h_inf
    have h_len := congrArg List.length hst
    simp only [List.length_singleton, List.length_append] at h_len
    omega
  | binary l r =>
    dsimp [FactorizationTree.value] at h_inf
    rcases repeatNine_isInfix_append X hX_ne l.value r.value h_inf with h_left | h_right
    · refine ⟨l, hC_ramsey.1, height_ge_child_of_binary_left l r, ?_⟩
      have hw_X : repeatTwentySeven (w n hn k) <:+: X := by
        refine ⟨[], [⟨k + 1, hk⟩], by simp [X]⟩
      have hX_repeatThree : X <:+: repeatThree X := infix_repeatThree_of_self X
      have hX_l := hX_repeatThree.trans h_left
      exact (infix_repeatTwentySeven_of_self (w n hn k)).trans (hw_X.trans hX_l)
    · refine ⟨r, hC_ramsey.2, height_ge_child_of_binary_right l r, ?_⟩
      have hw_X : repeatTwentySeven (w n hn k) <:+: X := by
        refine ⟨[], [⟨k + 1, hk⟩], by simp [X]⟩
      have hX_repeatThree : X <:+: repeatThree X := infix_repeatThree_of_self X
      have hX_r := hX_repeatThree.trans h_right
      exact (infix_repeatTwentySeven_of_self (w n hn k)).trans (hw_X.trans hX_r)
  | idempotent gs =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨_hlen, hgs_ramsey, e, _he_idem, he_eval⟩ := hC_ramsey
    have ha_in_X : ⟨k + 1, hk⟩ ∈ X :=
      List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have ha_in_repeatNine : ⟨k + 1, hk⟩ ∈ repeatNine X :=
      (infix_repeatNine_of_self X).subset ha_in_X
    have ha_in_list : ⟨k + 1, hk⟩ ∈ listValue gs :=
      h_inf.subset ha_in_repeatNine
    obtain ⟨t₀, ht₀_mem, hat₀⟩ := mem_listValue ha_in_list
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := by
      change 0 < k + 1
      omega
    have h_all_ge : ∀ c ∈ gs, ∃ y ∈ c.value, ⟨k + 1, hk⟩ ≤ y :=
      fun c hc => idempotent_children_mem_ge hn hgs_ramsey e he_eval
        ⟨k + 1, hk⟩ h_bot_lt t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl c hc
    let v := repeatTwentySeven (w n hn k)
    have hv_ne : v ≠ [] := repeatTwentySeven_ne_nil (w_ne_nil n hn k)
    have hv_lt : ∀ y ∈ v, y < ⟨k + 1, hk⟩ := fun y hy => repeatTwentySeven_w_mem_lt n hn k hk y hy
    have h_no_child : ∀ g ∈ gs, ¬ (g.value <:+: v) := fun g hg =>
      no_child_infix_of_all_lt hn hgs_ramsey e he_eval ⟨k + 1, hk⟩ h_bot_lt
        t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl v hv_lt g hg
    have hv_inf : v <:+: listValue gs := by
      have hw_X : v <:+: X := by refine ⟨[], [⟨k + 1, hk⟩], by simp [X, v]⟩
      have hX_repeatNine : X <:+: repeatNine X := infix_repeatNine_of_self X
      exact hw_X.trans (hX_repeatNine.trans h_inf)
    rcases infix_listValue_two gs v hv_ne h_no_child hv_inf with
      ⟨g, hg, hgv⟩ | ⟨g₁, hg₁, g₂, hg₂, hg12⟩
    · refine ⟨g, isRamsey_of_mem_listIsRamsey hgs_ramsey hg, height_ge_child_of_idempotent hg, ?_⟩
      exact (infix_repeatTwentySeven_of_self (w n hn k)).trans hgv
    · have hw_split :=
        repeatTwentySeven_isInfix_append (w n hn k) (w_ne_nil n hn k) g₁.value g₂.value hg12
      rcases hw_split with h1 | h2
      · refine ⟨g₁, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₁,
          height_ge_child_of_idempotent hg₁, ?_⟩
        exact (infix_repeatNine_of_self (w n hn k)).trans h1
      · refine ⟨g₂, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₂,
          height_ge_child_of_idempotent hg₂, ?_⟩
        exact (infix_repeatNine_of_self (w n hn k)).trans h2

/-- If a 9-fold repetition of $w_k$ occurs in a tree that also contains a large element,
a child tree contains $w_k$. -/
lemma exists_child_w_of_repeatNine_w {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (C : FactorizationTree (MaxSemigroup n))
    (hC_ramsey : C.IsRamsey (evalMax n hn))
    (h_inf : repeatNine (w n hn k) <:+: C.value)
    (h_ge : ∃ y ∈ C.value, ⟨k + 1, hk⟩ ≤ y) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 1 ≤ C.height ∧ w n hn k <:+: g.value := by
  have hw_ne := w_ne_nil n hn k
  have h_len_repeatNine := repeatNine_length_ge (w n hn k) hw_ne
  cases C with
  | leaf a =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨s, t, hst⟩ := h_inf
    have h_len := congrArg List.length hst
    simp only [List.length_singleton, List.length_append] at h_len
    omega
  | binary l r =>
    dsimp [FactorizationTree.value] at h_inf
    rcases repeatNine_isInfix_append (w n hn k) hw_ne l.value r.value h_inf with h_left | h_right
    · refine ⟨l, hC_ramsey.1, height_ge_child_of_binary_left l r, ?_⟩
      exact (infix_repeatThree_of_self (w n hn k)).trans h_left
    · refine ⟨r, hC_ramsey.2, height_ge_child_of_binary_right l r, ?_⟩
      exact (infix_repeatThree_of_self (w n hn k)).trans h_right
  | idempotent gs =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨_hlen, hgs_ramsey, e, _he_idem, he_eval⟩ := hC_ramsey
    obtain ⟨y, hy_val, hky⟩ := h_ge
    dsimp [FactorizationTree.value] at hy_val
    obtain ⟨t₀, ht₀_mem, hyt₀⟩ := mem_listValue hy_val
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := by
      change 0 < k + 1
      omega
    let v := repeatNine (w n hn k)
    have hv_ne : v ≠ [] := repeatNine_ne_nil hw_ne
    have hv_lt : ∀ z ∈ v, z < ⟨k + 1, hk⟩ := fun z hz => repeatNine_w_mem_lt n hn k hk z hz
    have h_no_child : ∀ g ∈ gs, ¬ (g.value <:+: v) := fun g hg =>
      no_child_infix_of_all_lt hn hgs_ramsey e he_eval ⟨k + 1, hk⟩ h_bot_lt
        t₀ ht₀_mem y hyt₀ hky v hv_lt g hg
    rcases infix_listValue_two gs v hv_ne h_no_child h_inf with
      ⟨g, hg, hgv⟩ | ⟨g₁, hg₁, g₂, hg₂, hg12⟩
    · refine ⟨g, isRamsey_of_mem_listIsRamsey hgs_ramsey hg, height_ge_child_of_idempotent hg, ?_⟩
      exact (infix_repeatNine_of_self (w n hn k)).trans hgv
    · rcases repeatNine_isInfix_append (w n hn k) hw_ne g₁.value g₂.value hg12 with h1 | h2
      · refine ⟨g₁, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₁,
          height_ge_child_of_idempotent hg₁, ?_⟩
        exact (infix_repeatThree_of_self (w n hn k)).trans h1
      · refine ⟨g₂, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₂,
          height_ge_child_of_idempotent hg₂, ?_⟩
        exact (infix_repeatThree_of_self (w n hn k)).trans h2

/-- If $w_{k+1}$ occurs in a Ramsey tree,
there exists a descendant at distance at least 2 containing $w_k$. -/
lemma grandchild_has_w_of_w_succ {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (t : FactorizationTree (MaxSemigroup n))
    (ht_ramsey : t.IsRamsey (evalMax n hn))
    (h_inf : w n hn (k + 1) <:+: t.value) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 2 ≤ t.height ∧ w n hn k <:+: g.value := by
  let X := repeatTwentySeven (w n hn k) ++ [⟨k + 1, hk⟩]
  have hw_succ : w n hn (k + 1) = repeatTwentySeven X := by
    dsimp [w]
    rw [dif_pos hk]
  rw [hw_succ] at h_inf
  have hX_ne : X ≠ [] := by simp [X]
  have h_len_repeatTwentySeven := repeatTwentySeven_length_ge X hX_ne
  cases t with
  | leaf a =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨s, u, hsu⟩ := h_inf
    have h_len := congrArg List.length hsu
    simp only [List.length_singleton, List.length_append] at h_len
    omega
  | binary l r =>
    dsimp [FactorizationTree.value] at h_inf
    rcases repeatTwentySeven_isInfix_append X hX_ne l.value r.value h_inf with h_left | h_right
    · obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ :=
        exists_child_w_of_repeatNine_X hn k hk l ht_ramsey.1 h_left
      have := height_ge_child_of_binary_left l r
      exact ⟨g, hg_ram, by omega, hg_inf⟩
    · obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ :=
        exists_child_w_of_repeatNine_X hn k hk r ht_ramsey.2 h_right
      have := height_ge_child_of_binary_right l r
      exact ⟨g, hg_ram, by omega, hg_inf⟩
  | idempotent cs =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨_hlen, hcs_ramsey, e, _he_idem, he_eval⟩ := ht_ramsey
    have ha_in_X : ⟨k + 1, hk⟩ ∈ X :=
      List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have ha_in_repeatTwentySeven : ⟨k + 1, hk⟩ ∈ repeatTwentySeven X :=
      (infix_repeatTwentySeven_of_self X).subset ha_in_X
    have ha_in_list : ⟨k + 1, hk⟩ ∈ listValue cs :=
      h_inf.subset ha_in_repeatTwentySeven
    obtain ⟨t₀, ht₀_mem, hat₀⟩ := mem_listValue ha_in_list
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := by
      change 0 < k + 1
      omega
    have h_all_ge : ∀ c ∈ cs, ∃ y ∈ c.value, ⟨k + 1, hk⟩ ≤ y :=
      fun c hc => idempotent_children_mem_ge hn hcs_ramsey e he_eval
        ⟨k + 1, hk⟩ h_bot_lt t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl c hc
    let v := repeatTwentySeven (w n hn k)
    have hv_ne : v ≠ [] := repeatTwentySeven_ne_nil (w_ne_nil n hn k)
    have hv_lt : ∀ y ∈ v, y < ⟨k + 1, hk⟩ := fun y hy => repeatTwentySeven_w_mem_lt n hn k hk y hy
    have h_no_child : ∀ c ∈ cs, ¬ (c.value <:+: v) := fun c hc =>
      no_child_infix_of_all_lt hn hcs_ramsey e he_eval ⟨k + 1, hk⟩ h_bot_lt
        t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl v hv_lt c hc
    have hv_inf : v <:+: listValue cs := by
      have hw_X : v <:+: X := by refine ⟨[], [⟨k + 1, hk⟩], by simp [X, v]⟩
      have hX_repeatTwentySeven : X <:+: repeatTwentySeven X := infix_repeatTwentySeven_of_self X
      exact hw_X.trans (hX_repeatTwentySeven.trans h_inf)
    rcases infix_listValue_two cs v hv_ne h_no_child hv_inf with
      ⟨c, hc, hcv⟩ | ⟨c₁, hc₁, c₂, hc₂, hc12⟩
    · have hc_ram := isRamsey_of_mem_listIsRamsey hcs_ramsey hc
      have hc_ht := height_ge_child_of_idempotent hc
      have hc_ge := h_all_ge c hc
      have h_rep9 : repeatNine (w n hn k) <:+: c.value :=
        (repeatNine_isInfix_repeatTwentySeven (w n hn k)).trans hcv
      obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ :=
        exists_child_w_of_repeatNine_w hn k hk c hc_ram h_rep9 hc_ge
      exact ⟨g, hg_ram, by omega, hg_inf⟩
    · have hw_split :=
        repeatTwentySeven_isInfix_append (w n hn k) (w_ne_nil n hn k) c₁.value c₂.value hc12
      rcases hw_split with h1 | h2
      · have hc_ram := isRamsey_of_mem_listIsRamsey hcs_ramsey hc₁
        have hc_ht := height_ge_child_of_idempotent hc₁
        have hc_ge := h_all_ge c₁ hc₁
        obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ :=
          exists_child_w_of_repeatNine_w hn k hk c₁ hc_ram h1 hc_ge
        exact ⟨g, hg_ram, by omega, hg_inf⟩
      · have hc_ram := isRamsey_of_mem_listIsRamsey hcs_ramsey hc₂
        have hc_ht := height_ge_child_of_idempotent hc₂
        have hc_ge := h_all_ge c₂ hc₂
        obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ :=
          exists_child_w_of_repeatNine_w hn k hk c₂ hc_ram h2 hc_ge
        exact ⟨g, hg_ram, by omega, hg_inf⟩

/-- Any Ramsey tree whose yield contains $w_k$ as an infix must have height at least $2k+1$. -/
lemma height_ge_of_w_infix {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k < n)
    (t : FactorizationTree (MaxSemigroup n))
    (ht : t.IsRamsey (evalMax n hn))
    (h : w n hn k <:+: t.value) :
    2 * k + 1 ≤ t.height := by
  induction k generalizing t with
  | zero =>
    have h_not_leaf : ∀ a, t ≠ FactorizationTree.leaf a := by
      intro a rfl
      dsimp [FactorizationTree.value] at h
      dsimp [w] at h
      obtain ⟨s, u, hsu⟩ := h
      have h_len := congrArg List.length hsu
      have h_w0_len := repeatTwentySeven_length_ge [botEl n hn] (by simp)
      simp only [List.length_singleton, List.length_append] at h_len
      omega
    have := height_pos_of_not_leaf t h_not_leaf
    omega
  | succ k' ih =>
    obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := grandchild_has_w_of_w_succ hn k' hk t ht h
    have ih_g := ih (by omega) g hg_ram hg_inf
    omega

/-- Theorem 3.8 (Tightness): for each `n ≥ 2`, there exists an aperiodic finite semigroup `S`
of size `n` and a word where **all** Ramsey trees have height at least `2 * n - 1`.

Following M. Kufleitner (MFCS 2008, Section 5, Theorem 4), we use the semilattice
`MaxSemigroup n = Fin n` with `max` multiplication. -/
theorem aperiodic_bound_tight (n : ℕ) (hn : 2 ≤ n) :
    ∃ (S : Type) (_ : Semigroup S) (_ : Fintype S) (_ : IsAperiodic S),
      Fintype.card S = n ∧
      ∃ (eval : List S → S)
        (_ : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
        (u : List S) (_ : u ≠ []),
        ∀ t : FactorizationTree S,
          t.value = u →
          t.IsRamsey eval →
          2 * n - 1 ≤ t.height := by
  have hn' : 0 < n := by omega
  refine ⟨MaxSemigroup n, inferInstance, inferInstance,
    maxSemigroup_isAperiodic n,
    maxSemigroup_card n,
    evalMax n hn',
    fun u v _ _ => evalMax_append n hn' u v,
    w n hn' (n - 1),
    w_ne_nil n hn' (n - 1),
    ?_⟩
  intro t ht_val ht_ramsey
  have h_inf : w n hn' (n - 1) <:+: t.value := by
    rw [ht_val]
  have h_bound := height_ge_of_w_infix hn' (n - 1) (by omega) t ht_ramsey h_inf
  omega

end Tightness

end Aperiodic

export Aperiodic (truncatedAdd_isAperiodic aperiodic_bound_tight)
