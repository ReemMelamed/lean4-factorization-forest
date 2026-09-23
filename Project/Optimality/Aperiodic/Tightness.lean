/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Project.Optimality.Aperiodic.Basic
import Project.Optimality.TruncatedAddition
import Project.FactorizationTree.FactorizationTree
import Mathlib.Data.List.Infix

/-!
# Aperiodic Semigroups — Tightness of the Bound (Theorem 3.8)

For each `n ≥ 2`, the aperiodic bound `2 * n` is tight: there exists an aperiodic semigroup
of size `n` requiring Ramsey trees of height at least `2 * n - 1`.

## Main results

* `truncatedAdd_isAperiodic`: The truncated addition semigroup `TruncatedAdd n` is aperiodic.
* `aperiodic_bound_tight`: The 2|S| bound is tight.

## Proof of aperiodicity

For any group G with homomorphism f : G → TruncatedAdd n:
- f(1_G) is idempotent (since f(1·1) = f(1)·f(1)), so f(1_G) = top n (the unique idempotent)
- For any g : G, f(1_G) * f(g) = f(g), but top n * x = n = top n for ALL x (since n + x ≥ n + 1)
- Therefore f(g) = top n for all g, so f is constant and can only be injective if G is trivial

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

namespace Optimality

open FactorizationTree TruncatedAdd

/-- The max semigroup on `Fin n`. -/
def MaxSemigroup (n : ℕ) := Fin n

instance (n : ℕ) : LinearOrder (MaxSemigroup n) :=
  inferInstanceAs (LinearOrder (Fin n))

instance (n : ℕ) : Semigroup (MaxSemigroup n) where
  mul a b := max a b
  mul_assoc a b c := max_assoc a b c

instance (n : ℕ) : Fintype (MaxSemigroup n) :=
  inferInstanceAs (Fintype (Fin n))

lemma maxSemigroup_card (n : ℕ) : Fintype.card (MaxSemigroup n) = n :=
  Fintype.card_fin n

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

lemma botEl_le (n : ℕ) (hn : 0 < n) (x : MaxSemigroup n) : botEl n hn ≤ x := by
  change 0 ≤ x.val
  omega

lemma max_botEl_left (n : ℕ) (hn : 0 < n) (x : MaxSemigroup n) :
    max (botEl n hn) x = x :=
  max_eq_right (botEl_le n hn x)

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

lemma evalMax_append (n : ℕ) (hn : 0 < n) (u v : List (MaxSemigroup n)) :
    evalMax n hn (u ++ v) = evalMax n hn u * evalMax n hn v := by
  change (u ++ v).foldl max (botEl n hn) = max (evalMax n hn u) (evalMax n hn v)
  rw [List.foldl_append]
  exact foldl_max_eq_max n hn v (evalMax n hn u)

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

def rep3 {α : Type*} (l : List α) : List α :=
  l ++ l ++ l

def rep9 {α : Type*} (l : List α) : List α :=
  rep3 (rep3 l)

def rep27 {α : Type*} (l : List α) : List α :=
  rep3 (rep9 l)

lemma rep3_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : rep3 l ≠ [] := by
  dsimp [rep3]
  simp [hl]

lemma rep9_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : rep9 l ≠ [] :=
  rep3_ne_nil (rep3_ne_nil hl)

lemma rep27_ne_nil {α : Type*} {l : List α} (hl : l ≠ []) : rep27 l ≠ [] :=
  rep3_ne_nil (rep9_ne_nil hl)

lemma mem_rep3 {α : Type*} {l : List α} {x : α} (hx : x ∈ rep3 l) : x ∈ l := by
  dsimp [rep3] at hx
  rcases List.mem_append.mp hx with h12 | h3
  · rcases List.mem_append.mp h12 with h1 | h2
    · exact h1
    · exact h2
  · exact h3

lemma mem_rep9 {α : Type*} {l : List α} {x : α} (hx : x ∈ rep9 l) : x ∈ l :=
  mem_rep3 (mem_rep3 hx)

lemma mem_rep27 {α : Type*} {l : List α} {x : α} (hx : x ∈ rep27 l) : x ∈ l :=
  mem_rep9 (mem_rep3 hx)

lemma prefix_of_append_eq_append_left {α : Type*} (X Y Z W : List α)
    (h : X ++ Y = Z ++ W) (hle : Z.length ≤ X.length) :
    Z <+: X := by
  have h_take := congrArg (List.take Z.length) h
  rw [List.take_append_of_le_length hle] at h_take
  have h_Z : (Z ++ W).take Z.length = Z := by simp
  rw [h_Z] at h_take
  exact h_take ▸ List.take_prefix Z.length X

lemma rep3_append_cases {α : Type*} (l : List α) (hl : l ≠ [])
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

lemma rep3_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : rep3 l <:+: A ++ B) :
    l <:+: A ∨ l <:+: B := by
  obtain ⟨s, t, hst⟩ := h
  exact rep3_append_cases l hl A B s t hst.symm

lemma rep9_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : rep9 l <:+: A ++ B) :
    rep3 l <:+: A ∨ rep3 l <:+: B :=
  rep3_isInfix_append (rep3 l) (rep3_ne_nil hl) A B h

lemma rep27_isInfix_append {α : Type*} (l : List α) (hl : l ≠ [])
    (A B : List α) (h : rep27 l <:+: A ++ B) :
    rep9 l <:+: A ∨ rep9 l <:+: B :=
  rep3_isInfix_append (rep9 l) (rep9_ne_nil hl) A B h

lemma rep3_isInfix_rep9 {α : Type*} (l : List α) : rep3 l <:+: rep9 l := by
  refine ⟨[], rep3 l ++ rep3 l, ?_⟩
  dsimp [rep9, rep3]
  simp only [List.append_assoc]

lemma rep9_isInfix_rep27 {α : Type*} (l : List α) : rep9 l <:+: rep27 l := by
  refine ⟨[], rep9 l ++ rep9 l, ?_⟩
  dsimp [rep27, rep3]
  simp only [List.append_assoc]

lemma rep3_isInfix_rep27 {α : Type*} (l : List α) : rep3 l <:+: rep27 l :=
  (rep3_isInfix_rep9 l).trans (rep9_isInfix_rep27 l)

lemma infix_rep3_of_self {α : Type*} (l : List α) : l <:+: rep3 l := by
  refine ⟨[], l ++ l, ?_⟩
  dsimp [rep3]
  simp only [List.append_assoc]

lemma infix_rep9_of_self {α : Type*} (l : List α) : l <:+: rep9 l :=
  (infix_rep3_of_self l).trans (rep3_isInfix_rep9 l)

lemma infix_rep27_of_self {α : Type*} (l : List α) : l <:+: rep27 l :=
  (infix_rep9_of_self l).trans (rep9_isInfix_rep27 l)

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

lemma height_ge_child_of_idempotent {α : Type*} {cs : List (FactorizationTree α)}
    {c : FactorizationTree α} (hc : c ∈ cs) :
    c.height + 1 ≤ (FactorizationTree.idempotent cs).height := by
  dsimp [FactorizationTree.height]
  have := mem_listHeight_le hc
  omega

lemma height_ge_child_of_binary_left {α : Type*} (l r : FactorizationTree α) :
    l.height + 1 ≤ (FactorizationTree.binary l r).height := by
  dsimp [FactorizationTree.height]
  have := le_max_left l.height r.height
  omega

lemma height_ge_child_of_binary_right {α : Type*} (l r : FactorizationTree α) :
    r.height + 1 ≤ (FactorizationTree.binary l r).height := by
  dsimp [FactorizationTree.height]
  have := le_max_right l.height r.height
  omega

def w (n : ℕ) (hn : 0 < n) : ℕ → List (MaxSemigroup n)
  | 0 => rep27 [botEl n hn]
  | k + 1 =>
    if h : k + 1 < n then
      rep27 (rep27 (w n hn k) ++ [⟨k + 1, h⟩])
    else
      rep27 (w n hn k)

lemma w_ne_nil (n : ℕ) (hn : 0 < n) (k : ℕ) : w n hn k ≠ [] := by
  induction k with
  | zero =>
    dsimp [w]
    exact rep27_ne_nil (by simp)
  | succ k' ih =>
    dsimp [w]
    split_ifs
    · exact rep27_ne_nil (by simp)
    · exact rep27_ne_nil ih

lemma w_mem_le (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k < n)
    (x : MaxSemigroup n) (hx : x ∈ w n hn k) : x.val ≤ k := by
  induction k generalizing x with
  | zero =>
    dsimp [w] at hx
    have hx' := mem_rep27 hx
    cases hx' with
    | head => rfl
    | tail _ h => contradiction
  | succ k' ih =>
    dsimp [w] at hx
    rw [dif_pos hk] at hx
    have hx' := mem_rep27 hx
    rcases List.mem_append.mp hx' with h_rep | h_eq
    · have h_in_wk := mem_rep27 h_rep
      have := ih (by omega) x h_in_wk
      omega
    · cases h_eq with
      | head => rfl
      | tail _ h => contradiction

lemma w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ w n hn k) : x < ⟨k + 1, hk⟩ := by
  have := w_mem_le n hn k (by omega) x hx
  change x.val < k + 1
  omega

lemma rep27_w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ rep27 (w n hn k)) : x < ⟨k + 1, hk⟩ :=
  w_mem_lt n hn k hk x (mem_rep27 hx)

lemma rep9_w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ rep9 (w n hn k)) : x < ⟨k + 1, hk⟩ :=
  w_mem_lt n hn k hk x (mem_rep9 hx)

lemma rep3_w_mem_lt (n : ℕ) (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (x : MaxSemigroup n) (hx : x ∈ rep3 (w n hn k)) : x < ⟨k + 1, hk⟩ :=
  w_mem_lt n hn k hk x (mem_rep3 hx)

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

lemma rep9_length_ge {α : Type*} (l : List α) (hl : l ≠ []) : 9 ≤ (rep9 l).length := by
  have : 1 ≤ l.length := List.length_pos_iff.mpr hl
  dsimp [rep9, rep3]
  simp only [List.length_append]
  omega

lemma rep27_length_ge {α : Type*} (l : List α) (hl : l ≠ []) : 27 ≤ (rep27 l).length := by
  have : 1 ≤ l.length := List.length_pos_iff.mpr hl
  dsimp [rep27, rep9, rep3]
  simp only [List.length_append]
  omega

lemma exists_child_w_of_rep9_X {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (C : FactorizationTree (MaxSemigroup n))
    (hC_ramsey : C.IsRamsey (evalMax n hn))
    (h_inf : rep9 (rep27 (w n hn k) ++ [⟨k + 1, hk⟩]) <:+: C.value) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 1 ≤ C.height ∧ w n hn k <:+: g.value := by
  let X := rep27 (w n hn k) ++ [⟨k + 1, hk⟩]
  change rep9 X <:+: C.value at h_inf
  have hX_ne : X ≠ [] := by simp [X]
  have h_len_rep9 := rep9_length_ge X hX_ne
  cases C with
  | leaf a =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨s, t, hst⟩ := h_inf
    have h_len := congrArg List.length hst
    simp only [List.length_singleton, List.length_append] at h_len
    omega
  | binary l r =>
    dsimp [FactorizationTree.value] at h_inf
    rcases rep9_isInfix_append X hX_ne l.value r.value h_inf with h_left | h_right
    · refine ⟨l, hC_ramsey.1, height_ge_child_of_binary_left l r, ?_⟩
      have hw_X : rep27 (w n hn k) <:+: X := by
        refine ⟨[], [⟨k + 1, hk⟩], by simp [X]⟩
      have hX_rep3 : X <:+: rep3 X := infix_rep3_of_self X
      exact (infix_rep27_of_self (w n hn k)).trans (hw_X.trans (hX_rep3.trans h_left))
    · refine ⟨r, hC_ramsey.2, height_ge_child_of_binary_right l r, ?_⟩
      have hw_X : rep27 (w n hn k) <:+: X := by
        refine ⟨[], [⟨k + 1, hk⟩], by simp [X]⟩
      have hX_rep3 : X <:+: rep3 X := infix_rep3_of_self X
      exact (infix_rep27_of_self (w n hn k)).trans (hw_X.trans (hX_rep3.trans h_right))
  | idempotent gs =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨_hlen, hgs_ramsey, e, _he_idem, he_eval⟩ := hC_ramsey
    have ha_in_X : ⟨k + 1, hk⟩ ∈ X :=
      List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have ha_in_rep9 : ⟨k + 1, hk⟩ ∈ rep9 X :=
      (infix_rep9_of_self X).subset ha_in_X
    have ha_in_list : ⟨k + 1, hk⟩ ∈ listValue gs :=
      h_inf.subset ha_in_rep9
    obtain ⟨t₀, ht₀_mem, hat₀⟩ := mem_listValue ha_in_list
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := by
      change 0 < k + 1
      omega
    have h_all_ge : ∀ c ∈ gs, ∃ y ∈ c.value, ⟨k + 1, hk⟩ ≤ y :=
      fun c hc => idempotent_children_mem_ge hn hgs_ramsey e he_eval
        ⟨k + 1, hk⟩ h_bot_lt t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl c hc
    let v := rep27 (w n hn k)
    have hv_ne : v ≠ [] := rep27_ne_nil (w_ne_nil n hn k)
    have hv_lt : ∀ y ∈ v, y < ⟨k + 1, hk⟩ := fun y hy => rep27_w_mem_lt n hn k hk y hy
    have h_no_child : ∀ g ∈ gs, ¬ (g.value <:+: v) := fun g hg =>
      no_child_infix_of_all_lt hn hgs_ramsey e he_eval ⟨k + 1, hk⟩ h_bot_lt
        t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl v hv_lt g hg
    have hv_inf : v <:+: listValue gs := by
      have hw_X : v <:+: X := by refine ⟨[], [⟨k + 1, hk⟩], by simp [X, v]⟩
      have hX_rep9 : X <:+: rep9 X := infix_rep9_of_self X
      exact hw_X.trans (hX_rep9.trans h_inf)
    rcases infix_listValue_two gs v hv_ne h_no_child hv_inf with
      ⟨g, hg, hgv⟩ | ⟨g₁, hg₁, g₂, hg₂, hg12⟩
    · refine ⟨g, isRamsey_of_mem_listIsRamsey hgs_ramsey hg, height_ge_child_of_idempotent hg, ?_⟩
      exact (infix_rep27_of_self (w n hn k)).trans hgv
    · rcases rep27_isInfix_append (w n hn k) (w_ne_nil n hn k) g₁.value g₂.value hg12 with h1 | h2
      · refine ⟨g₁, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₁,
          height_ge_child_of_idempotent hg₁, ?_⟩
        exact (infix_rep9_of_self (w n hn k)).trans h1
      · refine ⟨g₂, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₂,
          height_ge_child_of_idempotent hg₂, ?_⟩
        exact (infix_rep9_of_self (w n hn k)).trans h2

lemma exists_child_w_of_rep9_w {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (C : FactorizationTree (MaxSemigroup n))
    (hC_ramsey : C.IsRamsey (evalMax n hn))
    (h_inf : rep9 (w n hn k) <:+: C.value)
    (h_ge : ∃ y ∈ C.value, ⟨k + 1, hk⟩ ≤ y) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 1 ≤ C.height ∧ w n hn k <:+: g.value := by
  have hw_ne := w_ne_nil n hn k
  have h_len_rep9 := rep9_length_ge (w n hn k) hw_ne
  cases C with
  | leaf a =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨s, t, hst⟩ := h_inf
    have h_len := congrArg List.length hst
    simp only [List.length_singleton, List.length_append] at h_len
    omega
  | binary l r =>
    dsimp [FactorizationTree.value] at h_inf
    rcases rep9_isInfix_append (w n hn k) hw_ne l.value r.value h_inf with h_left | h_right
    · refine ⟨l, hC_ramsey.1, height_ge_child_of_binary_left l r, ?_⟩
      exact (infix_rep3_of_self (w n hn k)).trans h_left
    · refine ⟨r, hC_ramsey.2, height_ge_child_of_binary_right l r, ?_⟩
      exact (infix_rep3_of_self (w n hn k)).trans h_right
  | idempotent gs =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨_hlen, hgs_ramsey, e, _he_idem, he_eval⟩ := hC_ramsey
    obtain ⟨y, hy_val, hky⟩ := h_ge
    dsimp [FactorizationTree.value] at hy_val
    obtain ⟨t₀, ht₀_mem, hyt₀⟩ := mem_listValue hy_val
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := by
      change 0 < k + 1
      omega
    let v := rep9 (w n hn k)
    have hv_ne : v ≠ [] := rep9_ne_nil hw_ne
    have hv_lt : ∀ z ∈ v, z < ⟨k + 1, hk⟩ := fun z hz => rep9_w_mem_lt n hn k hk z hz
    have h_no_child : ∀ g ∈ gs, ¬ (g.value <:+: v) := fun g hg =>
      no_child_infix_of_all_lt hn hgs_ramsey e he_eval ⟨k + 1, hk⟩ h_bot_lt
        t₀ ht₀_mem y hyt₀ hky v hv_lt g hg
    rcases infix_listValue_two gs v hv_ne h_no_child h_inf with
      ⟨g, hg, hgv⟩ | ⟨g₁, hg₁, g₂, hg₂, hg12⟩
    · refine ⟨g, isRamsey_of_mem_listIsRamsey hgs_ramsey hg, height_ge_child_of_idempotent hg, ?_⟩
      exact (infix_rep9_of_self (w n hn k)).trans hgv
    · rcases rep9_isInfix_append (w n hn k) hw_ne g₁.value g₂.value hg12 with h1 | h2
      · refine ⟨g₁, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₁,
          height_ge_child_of_idempotent hg₁, ?_⟩
        exact (infix_rep3_of_self (w n hn k)).trans h1
      · refine ⟨g₂, isRamsey_of_mem_listIsRamsey hgs_ramsey hg₂,
          height_ge_child_of_idempotent hg₂, ?_⟩
        exact (infix_rep3_of_self (w n hn k)).trans h2

lemma grandchild_has_w_of_w_succ {n : ℕ} (hn : 0 < n) (k : ℕ) (hk : k + 1 < n)
    (t : FactorizationTree (MaxSemigroup n))
    (ht_ramsey : t.IsRamsey (evalMax n hn))
    (h_inf : w n hn (k + 1) <:+: t.value) :
    ∃ g : FactorizationTree (MaxSemigroup n),
      g.IsRamsey (evalMax n hn) ∧ g.height + 2 ≤ t.height ∧ w n hn k <:+: g.value := by
  let X := rep27 (w n hn k) ++ [⟨k + 1, hk⟩]
  have hw_succ : w n hn (k + 1) = rep27 X := by
    dsimp [w]
    rw [dif_pos hk]
  rw [hw_succ] at h_inf
  have hX_ne : X ≠ [] := by simp [X]
  have h_len_rep27 := rep27_length_ge X hX_ne
  cases t with
  | leaf a =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨s, u, hsu⟩ := h_inf
    have h_len := congrArg List.length hsu
    simp only [List.length_singleton, List.length_append] at h_len
    omega
  | binary l r =>
    dsimp [FactorizationTree.value] at h_inf
    rcases rep27_isInfix_append X hX_ne l.value r.value h_inf with h_left | h_right
    · obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_rep9_X hn k hk l ht_ramsey.1 h_left
      have := height_ge_child_of_binary_left l r
      exact ⟨g, hg_ram, by omega, hg_inf⟩
    · obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_rep9_X hn k hk r ht_ramsey.2 h_right
      have := height_ge_child_of_binary_right l r
      exact ⟨g, hg_ram, by omega, hg_inf⟩
  | idempotent cs =>
    dsimp [FactorizationTree.value] at h_inf
    obtain ⟨_hlen, hcs_ramsey, e, _he_idem, he_eval⟩ := ht_ramsey
    have ha_in_X : ⟨k + 1, hk⟩ ∈ X :=
      List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have ha_in_rep27 : ⟨k + 1, hk⟩ ∈ rep27 X :=
      (infix_rep27_of_self X).subset ha_in_X
    have ha_in_list : ⟨k + 1, hk⟩ ∈ listValue cs :=
      h_inf.subset ha_in_rep27
    obtain ⟨t₀, ht₀_mem, hat₀⟩ := mem_listValue ha_in_list
    have h_bot_lt : botEl n hn < ⟨k + 1, hk⟩ := by
      change 0 < k + 1
      omega
    have h_all_ge : ∀ c ∈ cs, ∃ y ∈ c.value, ⟨k + 1, hk⟩ ≤ y :=
      fun c hc => idempotent_children_mem_ge hn hcs_ramsey e he_eval
        ⟨k + 1, hk⟩ h_bot_lt t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl c hc
    let v := rep27 (w n hn k)
    have hv_ne : v ≠ [] := rep27_ne_nil (w_ne_nil n hn k)
    have hv_lt : ∀ y ∈ v, y < ⟨k + 1, hk⟩ := fun y hy => rep27_w_mem_lt n hn k hk y hy
    have h_no_child : ∀ c ∈ cs, ¬ (c.value <:+: v) := fun c hc =>
      no_child_infix_of_all_lt hn hcs_ramsey e he_eval ⟨k + 1, hk⟩ h_bot_lt
        t₀ ht₀_mem ⟨k + 1, hk⟩ hat₀ le_rfl v hv_lt c hc
    have hv_inf : v <:+: listValue cs := by
      have hw_X : v <:+: X := by refine ⟨[], [⟨k + 1, hk⟩], by simp [X, v]⟩
      have hX_rep27 : X <:+: rep27 X := infix_rep27_of_self X
      exact hw_X.trans (hX_rep27.trans h_inf)
    rcases infix_listValue_two cs v hv_ne h_no_child hv_inf with
      ⟨c, hc, hcv⟩ | ⟨c₁, hc₁, c₂, hc₂, hc12⟩
    · have hc_ram := isRamsey_of_mem_listIsRamsey hcs_ramsey hc
      have hc_ht := height_ge_child_of_idempotent hc
      have hc_ge := h_all_ge c hc
      have h_rep9 : rep9 (w n hn k) <:+: c.value :=
        (rep9_isInfix_rep27 (w n hn k)).trans hcv
      obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_rep9_w hn k hk c hc_ram h_rep9 hc_ge
      exact ⟨g, hg_ram, by omega, hg_inf⟩
    · rcases rep27_isInfix_append (w n hn k) (w_ne_nil n hn k) c₁.value c₂.value hc12 with h1 | h2
      · have hc_ram := isRamsey_of_mem_listIsRamsey hcs_ramsey hc₁
        have hc_ht := height_ge_child_of_idempotent hc₁
        have hc_ge := h_all_ge c₁ hc₁
        obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_rep9_w hn k hk c₁ hc_ram h1 hc_ge
        exact ⟨g, hg_ram, by omega, hg_inf⟩
      · have hc_ram := isRamsey_of_mem_listIsRamsey hcs_ramsey hc₂
        have hc_ht := height_ge_child_of_idempotent hc₂
        have hc_ge := h_all_ge c₂ hc₂
        obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := exists_child_w_of_rep9_w hn k hk c₂ hc_ram h2 hc_ge
        exact ⟨g, hg_ram, by omega, hg_inf⟩

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
      have h_w0_len := rep27_length_ge [botEl n hn] (by simp)
      simp only [List.length_singleton, List.length_append] at h_len
      omega
    have := height_pos_of_not_leaf t h_not_leaf
    omega
  | succ k' ih =>
    obtain ⟨g, hg_ram, hg_ht, hg_inf⟩ := grandchild_has_w_of_w_succ hn k' hk t ht h
    have ih_g := ih (by omega) g hg_ram hg_inf
    omega

/-- The unique idempotent in `TruncatedAdd n` is `top n`. -/
lemma truncatedAdd_idempotent_eq_top {n : ℕ} (hn : 0 < n)
    (x : TruncatedAdd n) (hx : x * x = x) : x = top hn := by
  ext
  have h := congrArg TruncatedAdd.val hx
  rw [mul_val] at h
  simp only [top_val]
  have hpos : 0 < x.val := x.pos
  have hle  : x.val ≤ n     := x.le
  omega

/-- Left-multiplication by `top n` returns `top n` for any element. -/
lemma top_mul_any {n : ℕ} (hn : 0 < n) (x : TruncatedAdd n) :
    top hn * x = top hn := by
  ext
  simp only [mul_val, top_val]
  have hpos : 0 < x.val := x.pos
  omega

/-- The truncated addition semigroup `TruncatedAdd n` is aperiodic (group-free). -/
lemma truncatedAdd_isAperiodic (n : ℕ) (hn : 0 < n) : IsAperiodic (TruncatedAdd n) := by
  unfold IsAperiodic
  intro G _ f hf_mul hf_inj
  constructor
  intro a b
  -- Step 1: f(1_G) is idempotent in TruncatedAdd n
  have h_f1_idem : f 1 * f 1 = f 1 := by
    have h : f (1 * 1) = f 1 * f 1 := hf_mul 1 1
    rw [one_mul] at h
    exact h.symm
  -- Step 2: f(1_G) = top n (the unique idempotent)
  have h_f1_top : f 1 = top hn :=
    truncatedAdd_idempotent_eq_top hn (f 1) h_f1_idem
  -- Step 3: For any g : G, left-multiply by f(1_G) = top n
  --   f(1_G) * f(g) = top n * f(g) = top n
  --   But also f(1_G) * f(g) = f(1_G * g) = f(g)
  --   Therefore f(g) = top n
  have h_all_top : ∀ g : G, f g = top hn := fun g => by
    have h : f 1 * f g = f g := by
      have := hf_mul 1 g
      rw [one_mul] at this
      exact this.symm
    rw [h_f1_top] at h
    rw [top_mul_any hn (f g)] at h
    exact h.symm
  -- Step 4: f(a) = f(b) for all a b, so by injectivity a = b
  exact hf_inj ((h_all_top a).trans (h_all_top b).symm)

/-- `TruncatedAdd n` has exactly `n` elements. -/
noncomputable def truncatedAddEquivFin (n : ℕ) (_hn : 0 < n) : TruncatedAdd n ≃ Fin n where
  toFun x   := ⟨x.val - 1, by have := x.pos; have := x.le; omega⟩
  invFun j  := ⟨j.val + 1, by omega, by omega⟩
  left_inv  x := by
    ext
    dsimp
    have := x.pos
    omega
  right_inv j := by
    ext
    dsimp

lemma truncatedAdd_card_eq (n : ℕ) (hn : 0 < n) : Fintype.card (TruncatedAdd n) = n := by
  rw [Fintype.card_congr (truncatedAddEquivFin n hn)]
  exact Fintype.card_fin n

/-- The `evalTrunc` function is a semigroup homomorphism from non-empty lists. -/
lemma evalTrunc_hmul (hn : 0 < n) (u v : List (TruncatedAdd n))
    (hu : u ≠ []) (hv : v ≠ []) :
    evalTrunc hn (u ++ v) = evalTrunc hn u * evalTrunc hn v := by
  ext
  have h_ne : u ++ v ≠ [] := by simp [hu]
  rw [evalTrunc_val hn h_ne,
      mul_val,
      evalTrunc_val hn hu,
      evalTrunc_val hn hv]
  simp [List.map_append, List.sum_append]
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

end Optimality

end SimonSplit
