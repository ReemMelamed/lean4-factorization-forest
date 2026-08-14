/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Project.FactorizationForest.Split

/-!
# The Factorization Forest Theorem — Tree Construction

This file contains the algorithmic machinery for constructing a factorization
tree from a word and a Ramsey split, and the main theorem that asserts the
correctness and height bound of the construction.

## Main Definitions

* `splitIndices s` — the list of indices in `Fin (n+1)` assigned the maximum
  rank by the split `s`.
* `partitionIndices idxs` — consecutive pairs from a sorted list.
* `restrictSplit`, `lowerSplitInterior` — helpers for restricting and lowering
  splits on sub-intervals.
* `buildInnerFactorizationTree` — builds a tree from a word using inner cuts.
* `buildFactorizationTree` — wraps `buildInnerFactorizationTree` using the full
  split.
* `nary_tree_structure` — builds the top-level tree structure from prefix,
  middle (n-ary), and suffix parts.

## Main Results

* `buildTree_word_eq` — the constructed tree spans exactly the input word.
* `buildTree_height_bound` — the tree height is at most `3 * h - 1`.
* `buildTree_isRamsey` — the constructed tree is a Ramsey tree (proof pending).
* `factorization_forest` — the main theorem: every word has a factorization
  forest of bounded height.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace FactorizationForest

variable {A : Type*}

-- ---------------------------------------------------------------------------
-- Section 1: Index Partitioning Lemmas
-- ---------------------------------------------------------------------------

/-- The list of indices in `Fin (n+1)` that are assigned the maximum rank by
the split `s`. These are the "cut points" used to form the n-ary node. -/
def splitIndices {n h : ℕ} [Nonempty (Fin h)]
    (s : Split (Fin (n + 1)) h) : List (Fin (n + 1)) :=
  let max_val := Finset.max' Finset.univ Finset.univ_nonempty
  (List.finRange (n + 1)).filter (fun i => s i = max_val)

/-- Adjacent pairs from a list of indices, used to form the children of the
n-ary node. For a list `[i₀, i₁, i₂, …]`, this produces
`[(i₀, i₁), (i₁, i₂), …]`. -/
def partitionIndices {n : ℕ} : List (Fin (n + 1)) →
    List (Fin (n + 1) × Fin (n + 1))
| [] => []
| _ :: [] => []
| i :: j :: rest => (i, j) :: partitionIndices (j :: rest)

/-- Key properties of pairs produced by `partitionIndices`:
- Both elements of a pair appear in the original list.
- The first element is strictly less than the second.
- If the gap `j.val - i.val = n`, then the list maps to `[0, n]`.
- No element of the original list lies strictly between `i` and `j` in a pair. -/
lemma partitionIndices_props {n : ℕ} {l : List (Fin (n + 1))}
    {i j : Fin (n + 1)}
    (hs : List.Pairwise (· < ·) l)
    (h : (i, j) ∈ partitionIndices l) :
    i ∈ l ∧ j ∈ l ∧ i < j ∧
    (j.val - i.val = n → l.map (·.val) = [0, n]) ∧
    (∀ k ∈ l, ¬(i < k ∧ k < j)) := by
  induction l with
  | nil => contradiction
  | cons a l' ih =>
    cases l' with
    | nil => contradiction
    | cons b l'' =>
      unfold partitionIndices at h
      simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h_tail
      · have hab : i < j := List.pairwise_cons.1 hs |>.1 j (by simp)
        exact ⟨by simp, by simp, hab,
          fun _ ↦ by
            cases l'' with
            | nil =>
              have h_eqs : i.val = 0 ∧ j.val = n := by omega
              simp [h_eqs]
            | cons c l''' =>
              have hjc : j < c :=
                List.pairwise_cons.1
                  (List.pairwise_cons.1 hs |>.2) |>.1 c (by simp)
              omega,
          fun k hk ↦ by
            simp only [List.mem_cons] at hk
            rcases hk with rfl | rfl | hk
            · omega
            · omega
            · have hjk : j < k :=
                List.pairwise_cons.1
                  (List.pairwise_cons.1 hs |>.2) |>.1 k hk
              omega⟩
      · obtain ⟨hi, hj, hij, h_len, h_adj⟩ :=
            ih (List.pairwise_cons.1 hs |>.2) h_tail
        exact ⟨by simp [hi], by simp [hj], hij,
          fun h_eq_n ↦ by
            have hab : a < b := List.pairwise_cons.1 hs |>.1 b (by simp)
            have hb_zero : b.val = 0 := by injection h_len h_eq_n
            omega,
          fun k hk ↦ by
            rcases List.mem_cons.1 hk with rfl | hk
            · have hki : k < i :=
                  List.pairwise_cons.1 hs |>.1 i (by simp [hi])
              omega
            · exact h_adj k hk⟩

/-- All consecutive pairs produced by `partitionIndices (List.finRange (n+1))`
have difference exactly 1 (they are truly adjacent indices). -/
lemma partitionIndices_finRange_diff {n : ℕ}
    (x : Fin (n + 1) × Fin (n + 1))
    (hx : x ∈ partitionIndices (List.finRange (n + 1))) :
    x.2.val - x.1.val = 1 := by
  have h_props := partitionIndices_props
    (List.sortedLT_finRange _ |>.pairwise) hx
  rcases h_props with ⟨h_in1, h_in2, h_lt, h_len, h_between⟩
  have h_eq : x.2.val = x.1.val + 1 := by
    by_contra h_neq
    have h_mid_val : x.1.val + 1 < x.2.val := by omega
    have h_mid_lt : x.1.val + 1 < n + 1 := by omega
    have h_mid_in : (⟨x.1.val + 1, h_mid_lt⟩ : Fin (n + 1)) ∈
        List.finRange (n + 1) := List.mem_finRange _
    have h_contra := h_between ⟨x.1.val + 1, h_mid_lt⟩ h_mid_in
    simp at h_contra
    grind
  omega



/-- The slices produced by `partitionIndices` concatenate to the sub-list
between the first and last element (general version without boundary
conditions). -/
lemma flatten_partitionIndices_take_drop_gen {A : Type*} (u : List A)
    {n : ℕ}
    (idxs : List (Fin (n + 1))) (h_not_empty : idxs ≠ [])
    (h_sorted : List.Pairwise (· < ·) idxs) :
    (List.map (fun x : Fin (n + 1) × Fin (n + 1) ↦
      List.take (x.2.val - x.1.val) (List.drop x.1.val u))
      (partitionIndices idxs)).flatten =
    (List.drop (idxs.head h_not_empty).val u).take
      ((idxs.getLast h_not_empty).val - (idxs.head h_not_empty).val) := by
  induction idxs with
  | nil => contradiction
  | cons i1 idxs' ih =>
    cases idxs' with
    | nil =>
      simp only [partitionIndices, List.map_nil, List.flatten_nil,
        List.head_cons]
      have h_zero : (i1.val - i1.val) = 0 := by omega
      simp [h_zero]
    | cons i2 idxs'' =>
      have h_sorted_tail : List.Pairwise (· < ·) (i2 :: idxs'') :=
        List.pairwise_cons.1 h_sorted |>.2
      have h_not_empty_tail : i2 :: idxs'' ≠ [] := by simp
      have ih' := ih h_not_empty_tail h_sorted_tail
      have h_i1_lt_i2 : i1 < i2 :=
        List.pairwise_cons.1 h_sorted |>.1 i2 (by simp)
      simp only [partitionIndices, List.map_cons, List.flatten_cons]
      rw [ih']
      have h_head : (List.head (i2 :: idxs'') h_not_empty_tail) = i2 := rfl
      rw [h_head]
      have h_drop : List.drop i2.val u =
          List.drop (i2.val - i1.val) (List.drop i1.val u) := by
        rw [List.drop_drop]; congr 1; omega
      rw [h_drop]
      have h_append := take_append_take_drop (List.drop i1.val u)
        (i2.val - i1.val)
        ((List.getLast (i2 :: idxs'') h_not_empty_tail).val - i2.val)
      rw [h_append]
      have h_head2 : List.head (i1 :: i2 :: idxs'') h_not_empty = i1 := rfl
      rw [h_head2]
      have h_last : List.getLast (i1 :: i2 :: idxs'') h_not_empty =
          List.getLast (i2 :: idxs'') h_not_empty_tail := rfl
      rw [h_last]
      congr 1
      have h_i2_le_last : i2.val ≤
          (List.getLast (i2 :: idxs'') h_not_empty_tail).val :=
        idxs_le_getLast (i2 :: idxs'') h_not_empty_tail h_sorted_tail
          i2 (List.Mem.head _)
      omega

/-- The slices produced by `partitionIndices` starting at 0 and ending at
`u.length` concatenate to recover `u`. -/
lemma flatten_partitionIndices_take_drop {A : Type*} (u : List A)
    {n : ℕ} (h_len : u.length = n)
    (idxs : List (Fin (n + 1))) (h_not_empty : idxs ≠ [])
    (h_sorted : List.Pairwise (· < ·) idxs)
    (h_first : (idxs.head h_not_empty).val = 0)
    (h_last : (idxs.getLast h_not_empty).val = u.length) :
    (List.map (fun x : Fin (n + 1) × Fin (n + 1) =>
      List.take (x.2.val - x.1.val)
      (List.drop x.1.val u)) (partitionIndices idxs)).flatten = u := by
  rw [flatten_partitionIndices_take_drop_gen u idxs h_not_empty h_sorted]
  rw [h_first, h_last]
  simp [h_len]

/-- The `splitIndices` list is pairwise strictly increasing. -/
lemma splitIndices_sorted {n h : ℕ} [Nonempty (Fin h)]
    (s : Split (Fin (n + 1)) h) :
    List.Pairwise (· < ·) (splitIndices s) := by
  unfold splitIndices
  exact List.Pairwise.filter _ (List.sortedLT_finRange _ |>.pairwise)

-- ---------------------------------------------------------------------------
-- Section 2: Split Restriction and Lowering
-- ---------------------------------------------------------------------------

/-- Restricts a split on `Fin (n+1)` to the sub-interval `[i, i+len]`,
producing a split on `Fin (len+1)`. -/
def restrictSplit {n h : ℕ} (s : Split (Fin (n + 1)) h)
    (i len : ℕ) (h_bound : i + len ≤ n) :
    Split (Fin (len + 1)) h :=
  fun k => s ⟨i + k.val, by omega⟩

/-- Lowers a split whose values are all strictly below `h - 1` into a split
taking values in `Fin (h - 1)`. -/
def lowerSplitInterior {n h : ℕ} (s : Split (Fin (n + 1)) h)
    (h_interior : ∀ i : Fin (n + 1), (s i).val < h - 1) :
    Split (Fin (n + 1)) (h - 1) :=
  fun i => ⟨(s i).val, h_interior i⟩

/-- Auxiliary lemma: pairs in `partitionIndices (splitIndices s)` correspond
to valid, strict sub-intervals of `u`. -/
lemma h_valid_of_mem_partitionIndices {A : Type*} {n h : ℕ}
    [Nonempty (Fin h)]
    (u : List A) (h_len : u.length = n)
    (s : Split (Fin (n + 1)) h)
    (h_idxs : ¬(splitIndices s).map (·.val) = [0, n])
    (i j : Fin (n + 1))
    (mem : (i, j) ∈ partitionIndices (splitIndices s)) :
    let w := List.take (j.val - i.val) (List.drop i.val u)
    w.length < u.length ∧ i.val + w.length ≤ u.length ∧ w ≠ [] := by
  intro w
  have h_sorted := splitIndices_sorted s
  have h_props := partitionIndices_props h_sorted mem
  have h_ij : i.val < j.val := h_props.2.2.1
  have h_w_len : w.length = j.val - i.val := by
    dsimp [w]
    rw [List.length_take, List.length_drop]
    omega
  have h_w_ne : w ≠ [] := by
    rw [← List.length_pos_iff, h_w_len]; omega
  have h_le : i.val + w.length ≤ u.length := by
    rw [h_w_len]; omega
  have h_lt : w.length < u.length := by
    rw [h_w_len]
    by_contra h_not_lt
    have h_n : j.val - i.val = n := by omega
    have h_contra := h_props.2.2.2.1 h_n
    contradiction
  exact ⟨h_lt, h_le, h_w_ne⟩

-- ---------------------------------------------------------------------------

-- ---------------------------------------------------------------------------
-- Section 3: Inner Split Helpers
-- ---------------------------------------------------------------------------

/-- The type of inner splits: splits indexed by `Fin (u.length - 1)` (the
positions of internal cuts, not including the endpoints). -/
abbrev InnerSplit (u : List A) (h : ℕ) := Split (Fin (u.length - 1)) h

/-- Maps an inner cut index `i : Fin (u.length - 1)` to the corresponding
index `i + 1 : Fin (u.length + 1)` in the full domain. -/
def mapInnerCut {u : List A} (i : Fin (u.length - 1)) :
    Fin (u.length + 1) :=
  ⟨i.val + 1, by omega⟩

/-- Restricts an inner split on `u` to an inner split on a subword `w`,
starting at position `start` (relative to `u`). -/
def restrictInnerSplit {u w : List A} {h : ℕ} (s : InnerSplit u h)
    (start : ℕ) (h_len : w.length ≤ u.length)
    (h_start : start + w.length ≤ u.length) : InnerSplit w h :=
  fun i => s ⟨start + i.val, by omega⟩

/-- Lowers an inner split on `w` whose values are all strictly below `h'`
into a split taking values in `Fin h'`. -/
def lowerInnerSplit {w : List A} {h h' : ℕ} (s : InnerSplit w h)
    (h_lt : ∀ i, (s i).val < h') : InnerSplit w h' :=
  fun i => ⟨(s i).val, h_lt i⟩

-- ---------------------------------------------------------------------------
-- Section 4: buildInnerFactorizationTree
-- ---------------------------------------------------------------------------

lemma max_pos_of_not_mem {n h : ℕ} (s : Split (Fin n) h) (max_val : Fin h)
    (h_max : ∀ i, s i ≤ max_val)
    (i : Fin n)
    (h_neq : s i ≠ max_val) :
    0 < max_val.val := by
  have : s i < max_val := lt_of_le_of_ne (h_max i) h_neq
  omega

lemma exists_not_of_filter_length_lt {α} (l : List α) (p : α → Bool)
    (h_lt : (l.filter p).length < l.length) :
    ∃ x ∈ l, p x = false := by
  by_contra h_contra
  push Not at h_contra
  have h_eq : l.filter p = l := List.filter_eq_self.mpr fun x hx => by
    have h_not_false := h_contra x hx
    cases h_px : p x
    · exact False.elim (h_not_false h_px)
    · rfl
  rw [h_eq] at h_lt
  omega

/-- Builds a factorization tree for the word `u` using the inner split `s`.

The construction works by induction on `(h, u.length)`:
- If `u.length ≤ 2`, return a leaf or a binary of two leaves directly.
- Otherwise, find the maximum rank value and collect all inner indices `i`
  with `s i = max_val`. These become the "cut points".
- The portion of `u` between the first and last cut point is wrapped in an
  n-ary node (`list_to_nary`).
- The prefix (before the first cut) and suffix (after the last cut) are
  handled by recursive calls with a strictly smaller split. -/
def buildInnerFactorizationTree {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : InnerSplit u h) : FactorizationTree A :=
  if _h_len : u.length ≤ 2 then
    if _h_len2 : u.length = 1 then
      FactorizationTree.leaf (u.head hu)
    else
      have h_len2 : u.length = 2 := by
        have h_pos := List.length_pos_of_ne_nil hu; omega
      let (u1, u2) := (u.head hu, u.getLast (by omega))
      FactorizationTree.binary
        (FactorizationTree.leaf u1) (FactorizationTree.leaf u2) u 1
  else
    have h_nonempty : Nonempty (Fin (u.length - 1)) :=
      ⟨⟨0, by omega⟩⟩
    let max_val := Finset.max' (Finset.univ.image s) (by simp)
    let inner_idxs :=
      (List.finRange (u.length - 1)).filter (fun i => s i = max_val)
    let idxs := inner_idxs.map mapInnerCut
    if h_idxs : idxs = [] then
      FactorizationTree.leaf (u.head hu)
    else if h_const : inner_idxs.length = u.length - 1 then
      FactorizationTree.nary (u.map FactorizationTree.leaf) u 1
    else
      let children := (partitionIndices idxs).map fun ⟨i, j⟩ =>
        let w := (u.drop i.val).take (j.val - i.val)
        if h_valid : w.length ≤ 2 then
          if h_w1 : w.length = 1 then
            have hw_ne : w ≠ [] := fun h => by simp_all
            FactorizationTree.leaf (w.head hw_ne)
          else if h_w2 : w.length = 2 then
            have hw_ne : w ≠ [] := fun h => by simp_all
            let (w1, w2) := (w.head hw_ne, w.getLast hw_ne)
            FactorizationTree.binary
              (FactorizationTree.leaf w1) (FactorizationTree.leaf w2) w 1
          else
            FactorizationTree.leaf (u.head hu)
        else
          have h_w_len_ge_3 : 3 ≤ w.length := by omega
          have hw_ne : w ≠ [] := fun h => by simp_all
          if h_start : i.val ≤ u.length ∧ i.val + w.length ≤ u.length
          then
            let s_w := restrictInnerSplit s (i.val - 1) (by omega)
              (by omega)
            if h_interior : ∀ idx : Fin (w.length - 1),
                (s_w idx).val < max_val.val then
              have h_max_pos_strict : 0 < max_val.val := by
                have h_idx : 0 < w.length - 1 := by omega
                have h_lt := h_interior ⟨0, h_idx⟩
                omega
              have h_ne : Nonempty (Fin max_val.val) := ⟨⟨0, h_max_pos_strict⟩⟩
              buildInnerFactorizationTree eval w hw_ne
                (lowerInnerSplit s_w h_interior)
            else
              FactorizationTree.leaf (u.head hu)
          else
            FactorizationTree.leaf (u.head hu)
      let k_pre := (idxs.head h_idxs).val
      let k := (idxs.getLast h_idxs).val
      let max_h_children :=
        (children.map FactorizationTree.height).foldl max 0
      let t_mid := list_to_nary children
        ((u.drop k_pre).take (k - k_pre))
        (max_h_children + 1)
        (FactorizationTree.leaf (u.head hu))
      let t_pre : FactorizationTree A :=
        let w_pre := u.take k_pre
        if h_pre_len : w_pre.length ≤ 2 then
          if h_pre_1 : w_pre.length = 1 then
            have hw_ne : w_pre ≠ [] := fun h => by simp_all
            FactorizationTree.leaf (w_pre.head hw_ne)
          else if h_pre_2 : w_pre.length = 2 then
            have hw_ne : w_pre ≠ [] := fun h => by simp_all
            let (p1, p2) := (w_pre.head hw_ne, w_pre.getLast hw_ne)
            FactorizationTree.binary
              (FactorizationTree.leaf p1)
              (FactorizationTree.leaf p2) w_pre 1
          else
            FactorizationTree.leaf (u.head hu)
        else
          have hw_ne : w_pre ≠ [] := fun h => by simp_all
          if h_start : 0 + w_pre.length ≤ u.length then
            let s_pre := restrictInnerSplit s 0 (by omega) (by omega)
            if h_interior : ∀ idx : Fin (w_pre.length - 1),
                (s_pre idx).val < max_val.val then
              have h_max_pos_strict : 0 < max_val.val := by
                have h_idx : 0 < w_pre.length - 1 := by omega
                have h_lt := h_interior ⟨0, h_idx⟩
                omega
              have h_ne : Nonempty (Fin max_val.val) := ⟨⟨0, h_max_pos_strict⟩⟩
              buildInnerFactorizationTree eval w_pre hw_ne
                (lowerInnerSplit s_pre h_interior)
            else
              FactorizationTree.leaf (u.head hu)
          else
            FactorizationTree.leaf (u.head hu)
      let t_suf : FactorizationTree A :=
        let w_suf := (u.drop k).take (u.length - k)
        if h_suf_len : w_suf.length ≤ 2 then
          if h_suf_1 : w_suf.length = 1 then
            have hw_ne : w_suf ≠ [] := fun h => by simp_all
            FactorizationTree.leaf (w_suf.head hw_ne)
          else if h_suf_2 : w_suf.length = 2 then
            have hw_ne : w_suf ≠ [] := fun h => by simp_all
            let (s1, s2) := (w_suf.head hw_ne, w_suf.getLast hw_ne)
            FactorizationTree.binary
              (FactorizationTree.leaf s1)
              (FactorizationTree.leaf s2) w_suf 1
          else
            FactorizationTree.leaf (u.head hu)
        else
          have hw_ne : w_suf ≠ [] := fun h => by simp_all
          if h_start : k + w_suf.length ≤ u.length then
            let s_suf := restrictInnerSplit s k (by omega) (by omega)
            if h_interior : ∀ idx : Fin (w_suf.length - 1),
                (s_suf idx).val < max_val.val then
              have h_max_pos_strict : 0 < max_val.val := by
                have h_idx : 0 < w_suf.length - 1 := by omega
                have h_lt := h_interior ⟨0, h_idx⟩
                omega
              have h_ne : Nonempty (Fin max_val.val) := ⟨⟨0, h_max_pos_strict⟩⟩
              buildInnerFactorizationTree eval w_suf hw_ne
                (lowerInnerSplit s_suf h_interior)
            else
              FactorizationTree.leaf (u.head hu)
          else
            FactorizationTree.leaf (u.head hu)
      let t_pre_mid := FactorizationTree.binary t_pre t_mid
        (u.take k) (max t_pre.height t_mid.height + 1)
      FactorizationTree.binary t_pre_mid t_suf u
        (max t_pre_mid.height t_suf.height + 1)
termination_by (h, u.length)

-- ---------------------------------------------------------------------------
-- Section 5: Height Bound Auxiliary Lemmas
-- ---------------------------------------------------------------------------



lemma pairwise_lt_finRange (n : ℕ) : (List.finRange n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  simp only [List.get_finRange]
  exact hij

lemma head_le_of_pairwise_lt_mem {n : ℕ} (l : List (Fin n))
    (h_sorted : l.Pairwise (· < ·)) (hne : l ≠ []) (x : Fin n) (hx : x ∈ l) :
    (l.head hne).val ≤ x.val := by
  cases l with
  | nil => contradiction
  | cons a as =>
    cases hx with
    | head _ => exact le_refl _
    | tail _ hx_tail =>
      have h_rel : ∀ y ∈ as, a < y := (List.pairwise_cons.1 h_sorted).1
      exact le_of_lt (h_rel x hx_tail)

lemma mem_le_getLast_of_pairwise_lt {n : ℕ} (l : List (Fin n))
    (h_sorted : l.Pairwise (· < ·)) (hne : l ≠ []) (x : Fin n) (hx : x ∈ l) :
    x.val ≤ (l.getLast hne).val := by
  induction l generalizing x with
  | nil =>
    contradiction
  | cons a as ih =>
    cases as with
    | nil =>
      cases hx with
      | head _ => exact le_refl _
      | tail _ h => contradiction
    | cons b bs =>
      cases hx with
      | head _ =>
        have h_rel : ∀ y ∈ b :: bs, a < y := (List.pairwise_cons.1 h_sorted).1
        have h_getLast_mem : (b :: bs).getLast (by simp) ∈ b :: bs := List.getLast_mem (by simp)
        have h_lt := h_rel ((b :: bs).getLast (by simp)) h_getLast_mem
        have h_eq : (b :: bs).getLast (by simp) = (a :: b :: bs).getLast hne := by rfl
        rw [←h_eq]
        exact le_of_lt h_lt
      | tail _ hx_tail =>
        have h_sorted_tail : (b :: bs).Pairwise (· < ·) := (List.pairwise_cons.1 h_sorted).2
        have h_ih := ih h_sorted_tail (by simp) x hx_tail
        have h_eq : (b :: bs).getLast (by simp) = (a :: b :: bs).getLast hne := by rfl
        rw [←h_eq]
        exact h_ih

lemma h_interior_pre_aux {n h : ℕ} (s : Split (Fin n) h)
    (max_val : Fin h)
    (h_max : ∀ i, s i ≤ max_val)
    (inner_idxs : List (Fin n))
    (h_inner_idxs : inner_idxs = (List.finRange n).filter (fun i => decide (s i = max_val)))
    (h_ne : inner_idxs ≠ [])
    (idx : ℕ)
    (h_idx : idx < (inner_idxs.head h_ne).val) :
    (s ⟨idx, by omega⟩).val < max_val.val := by
  have h_le := h_max ⟨idx, by omega⟩
  have h_eq_or_lt := eq_or_lt_of_le h_le
  rcases h_eq_or_lt with h_eq | h_lt
  · have h_mem : ⟨idx, by omega⟩ ∈ inner_idxs := by
      subst h_inner_idxs
      rw [List.mem_filter]
      exact ⟨List.mem_finRange _, by simp [h_eq]⟩
    have h_sorted : inner_idxs.Pairwise (· < ·) := by
      subst h_inner_idxs
      exact List.Pairwise.filter _ (pairwise_lt_finRange _)
    have h_contra : (inner_idxs.head h_ne).val ≤ idx :=
      head_le_of_pairwise_lt_mem inner_idxs h_sorted h_ne ⟨idx, _⟩ h_mem
    omega
  · exact h_lt

lemma h_interior_suf_aux {n h : ℕ} (s : Split (Fin n) h)
    (max_val : Fin h)
    (h_max : ∀ i, s i ≤ max_val)
    (inner_idxs : List (Fin n))
    (h_inner_idxs : inner_idxs = (List.finRange n).filter (fun i => decide (s i = max_val)))
    (h_ne : inner_idxs ≠ [])
    (idx : ℕ)
    (h_idx : (inner_idxs.getLast h_ne).val < idx)
    (h_idx_lt : idx < n) :
    (s ⟨idx, h_idx_lt⟩).val < max_val.val := by
  have h_le := h_max ⟨idx, h_idx_lt⟩
  have h_eq_or_lt := eq_or_lt_of_le h_le
  rcases h_eq_or_lt with h_eq | h_lt
  · have h_mem : ⟨idx, h_idx_lt⟩ ∈ inner_idxs := by
      subst h_inner_idxs
      rw [List.mem_filter]
      exact ⟨List.mem_finRange _, by simp [h_eq]⟩
    have h_sorted : inner_idxs.Pairwise (· < ·) := by
      subst h_inner_idxs
      exact List.Pairwise.filter _ (pairwise_lt_finRange _)
    have h_contra : idx ≤ (inner_idxs.getLast h_ne).val :=
      mem_le_getLast_of_pairwise_lt inner_idxs h_sorted h_ne ⟨idx, h_idx_lt⟩ h_mem
    omega
  · exact h_lt

lemma h_interior_mid_aux {A : Type*} {u : List A} {h : ℕ} (s : Split (Fin (u.length - 1)) h)
    (max_val : Fin h)
    (h_max : ∀ i, s i ≤ max_val)
    (inner_idxs : List (Fin (u.length - 1)))
    (h_inner_idxs : inner_idxs = (List.finRange (u.length - 1)).filter
    (fun i => decide (s i = max_val)))
    (idxs : List (Fin (u.length + 1)))
    (h_idxs : idxs = inner_idxs.map mapInnerCut)
    (i j : Fin (u.length + 1))
    (h_part : (i, j) ∈ partitionIndices idxs)
    (idx : ℕ)
    (h_idx_gt : i.val ≤ idx)
    (h_idx_lt : idx < j.val - 1) :
    (s ⟨idx, by omega⟩).val < max_val.val := by
  have h_le := h_max ⟨idx, by omega⟩
  have h_eq_or_lt := eq_or_lt_of_le h_le
  rcases h_eq_or_lt with h_eq | h_lt
  · have h_mem_inner : ⟨idx, by omega⟩ ∈ inner_idxs := by
      subst h_inner_idxs
      rw [List.mem_filter]
      exact ⟨List.mem_finRange _, by simp [h_eq]⟩
    have h_mem_idxs : (⟨idx + 1, by omega⟩ : Fin (u.length + 1)) ∈ idxs := by
      subst h_idxs
      rw [List.mem_map]
      exact ⟨⟨idx, by omega⟩, h_mem_inner, rfl⟩
    have h_sorted_idxs : idxs.Pairwise (· < ·) := by
      subst h_idxs
      have h_sorted_inner : inner_idxs.Pairwise (· < ·) := by
        subst h_inner_idxs
        exact List.Pairwise.filter _ (pairwise_lt_finRange _)
      exact List.Pairwise.map _ (fun _ _ h => by simp [mapInnerCut]; omega) h_sorted_inner
    have h_props := partitionIndices_props h_sorted_idxs h_part
    have h_contra := h_props.2.2.2.2 ⟨idx + 1, by omega⟩ h_mem_idxs
    have h_i_lt : i < ⟨idx + 1, by omega⟩ := by grind
    have h_lt_j : (⟨idx + 1, by omega⟩ : Fin (u.length + 1)) < j := by grind
    exact nomatch (h_contra ⟨h_i_lt, h_lt_j⟩)
  · exact h_lt

lemma my_bound_helper {hp hm hs h h_height : ℕ}
  (h_pre : hp ≤ 3 * h - 1)
  (h_mid : hm ≤ 3 * h)
  (h_suf : hs ≤ 3 * h - 1)
  (h_bound : h ≤ h_height - 1)
  (h_pos : 0 < h) :
  max (max hp hm + 1) hs + 1 ≤ 3 * h_height - 1 := by omega

lemma my_foldl_max_le {α : Type*} (l : List α) (f : α → ℕ) (bound : ℕ)
    (h_zero : 0 ≤ bound)
    (h_all : ∀ x ∈ l, f x ≤ bound) :
    (l.map f).foldl max 0 ≤ bound := by
  revert h_zero
  generalize 0 = acc
  intro h_acc
  induction l generalizing acc with
  | nil => exact h_acc
  | cons a as ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · intro x hx
      exact h_all x (List.mem_cons_of_mem _ hx)
    · have h_a := h_all a (by simp)
      simp only [max_le_iff]
      omega

/-- The height bound `3 * h - 1` holds for `buildInnerFactorizationTree`. -/
lemma buildInnerTree_height_bound {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : InnerSplit u h) :
    (buildInnerFactorizationTree eval u hu s).height ≤ 3 * h - 1 := by
  induction h, ‹Nonempty (Fin h)›, u, hu, s
      using buildInnerFactorizationTree.induct eval
  case case1 h_height inst u hu s h_len h_len1 =>
    unfold buildInnerFactorizationTree
    dsimp only
    rw [dif_pos h_len, dif_pos h_len1]
    simp only [height_leaf]
    omega
  case case2 h_height inst u hu s h_len h_not_len1 h_len2 u1 u2 h_head_last =>
    unfold buildInnerFactorizationTree
    dsimp only
    rw [dif_pos h_len, dif_neg h_not_len1]
    have : 1 ≤ h_height := by rcases inst with ⟨⟨_, _⟩⟩; omega
    simp only [height_binary]
    omega
  case case3 h_height inst =>
    unfold buildInnerFactorizationTree
    dsimp only
    split_ifs
    all_goals simp_all [height_leaf]
  case case4 h_height inst u hu s h_not_len h_nonempty max_val inner_idxs idxs h_idxs_ne h_const =>
    unfold buildInnerFactorizationTree
    dsimp only
    rw [dif_neg h_not_len, dif_neg h_idxs_ne, dif_pos h_const]
    simp only [height_nary]
    have : 1 ≤ h_height := by rcases inst with ⟨⟨_, _⟩⟩; omega
    omega
  case case5 =>
    rename_i h_height inst u hu s h_not_len h_nonempty max_val
      inner_idxs idxs h_idxs_ne h_const k_pre k ih3 ih2 ih1
    have h_max_pos_strict : 0 < max_val.val := by
      have h_len_le : inner_idxs.length ≤ u.length - 1 := by
        have h1 :=
          List.length_filter_le (fun i => decide (s i = max_val)) (List.finRange (u.length - 1))
        rw [List.length_finRange] at h1
        exact h1
      have h_lt : inner_idxs.length < u.length - 1 := lt_of_le_of_ne h_len_le h_const
      have h_lt' : ((List.finRange (u.length - 1)).filter
        (fun i => decide (s i = max_val))).length < (List.finRange (u.length - 1)).length := by
        have h_len : (List.finRange (u.length - 1)).length = u.length - 1 := List.length_finRange
        rw [h_len]
        exact h_lt
      have h_ex := exists_not_of_filter_length_lt _ _ h_lt'
      rcases h_ex with ⟨i, _, h_false⟩
      have h_neq : s i ≠ max_val := by
        intro h_eq
        have : decide (s i = max_val) = true := decide_eq_true h_eq
        rw [this] at h_false
        contradiction
      have h_max : ∀ i, s i ≤ max_val :=
        fun j => Finset.le_max' _ _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      exact max_pos_of_not_mem s max_val h_max i h_neq
    unfold buildInnerFactorizationTree
    dsimp only
    rw [dif_neg h_not_len, dif_neg h_idxs_ne, dif_neg h_const]
    simp only [height_binary]
    apply my_bound_helper (h := max_val.val) (h_pos := h_max_pos_strict)
    · split_ifs
      all_goals {
        try apply ih2 <;> assumption
        try simp only [height_leaf, height_binary]
        try omega
        try grind
      }
    · apply le_trans (list_to_nary_height_le _ _ _ _)
      apply le_trans (b := 3 * max_val.val - 1 + 1)
      · apply Nat.add_le_add_right
        apply my_foldl_max_le
        · omega
        · intro x hx
          rw [List.mem_map] at hx
          rcases hx with ⟨⟨i, j⟩, h_part, rfl⟩
          split_ifs
          all_goals {
            try apply ih3 i j <;> assumption
            try simp only [height_leaf, height_binary]
            try omega
          }
      · omega
    · split_ifs
      all_goals {
        try apply ih1 <;> assumption
        try simp only [height_leaf, height_binary]
        try omega
      }
    · have : max_val.val < h_height := max_val.isLt
      omega

-- ---------------------------------------------------------------------------
-- Section 6: buildFactorizationTree
-- ---------------------------------------------------------------------------

/-- Wraps `buildInnerFactorizationTree` using the full split `s` on
`Fin (u.length + 1)`. The inner split is obtained by restricting `s` to
internal positions `⟨i + 1, …⟩`. -/
def buildFactorizationTree {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h) : FactorizationTree A :=
  buildInnerFactorizationTree eval u hu (fun i => s ⟨i.val + 1, by omega⟩)

-- ---------------------------------------------------------------------------
-- Section 7: Word Equality Theorem
-- ---------------------------------------------------------------------------

/-- The word of `buildInnerFactorizationTree eval u hu s` is `u`. -/
lemma buildInnerTree_word_eq {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : InnerSplit u h) :
    (buildInnerFactorizationTree eval u hu s).word = u := by
  induction h, ‹Nonempty (Fin h)›, u, hu, s
      using buildInnerFactorizationTree.induct eval
  case case1 =>
    unfold buildInnerFactorizationTree
    dsimp only
    split_ifs; simp_all
  case case2 =>
    unfold buildInnerFactorizationTree
    dsimp only
    split_ifs; simp_all
  case case3 =>
    rename_i h_height inst u hu s h_not_len h_nonempty max_val
      inner_idxs idxs h_idxs_eq
    have h_impossible : False := by
      have h_max_mem : max_val ∈ Finset.image s Finset.univ :=
        Finset.max'_mem _ _
      rcases Finset.mem_image.mp h_max_mem with ⟨i, _, hi_eq⟩
      have hi_inner : i ∈ inner_idxs := by simp [inner_idxs, hi_eq]
      have h_inner_nil : inner_idxs = [] :=
        List.map_eq_nil_iff.mp h_idxs_eq
      rw [h_inner_nil] at hi_inner
      cases hi_inner
    exact nomatch h_impossible
  case case4 =>
    rename_i h_height inst u hu s h_not_len h_nonempty max_val inner_idxs idxs h_idxs_ne h_const
    unfold buildInnerFactorizationTree
    dsimp only
    rw [dif_neg h_not_len, dif_neg h_idxs_ne, dif_pos h_const]
  case case5 =>
    rename_i h_height inst u hu s h_not_len h_nonempty max_val
      inner_idxs idxs h_idxs_ne h_const k_pre k ih3 ih2 ih1
    unfold buildInnerFactorizationTree
    dsimp only
    rw [dif_neg h_not_len, dif_neg h_idxs_ne, dif_neg h_const]

/-- **The constructed tree spans the input word**: the word of
`buildFactorizationTree eval u hu s` is `u`. -/
theorem buildTree_word_eq {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h) :
    (buildFactorizationTree eval u hu s).word = u := by
  unfold buildFactorizationTree
  exact buildInnerTree_word_eq eval u hu _

-- ---------------------------------------------------------------------------
-- Section 8: nary_tree_structure
-- ---------------------------------------------------------------------------

/-- The top-level tree structure combining prefix, n-ary middle, and suffix
parts. The branching logic optimizes away empty prefix/suffix parts:
- If `k = u.length` (suffix is empty), omit the suffix.
- If `k_pre = 0` (prefix is empty), omit the prefix.
- If `k_pre = k` (no children), use just the prefix or suffix. -/
def nary_tree_structure (u : List A) (hu : u ≠ [])
    (k k_pre : ℕ)
    (t_pre t_suf : FactorizationTree A)
    (children : List (FactorizationTree A)) : FactorizationTree A :=
  let max_h_children :=
    (children.map FactorizationTree.height).foldl max 0
  let w_mid := (u.drop k_pre).take (k - k_pre)
  let t_mid := list_to_nary children w_mid (max_h_children + 1)
    (FactorizationTree.leaf (u.head hu))
  if _ : k = u.length then
    if _ : k_pre = 0 then
      t_mid
    else
      if _ : k_pre = k then
        t_pre
      else
        FactorizationTree.binary t_pre t_mid u
          (max t_pre.height t_mid.height + 1)
  else
    if _ : k_pre = 0 then
      if _ : k_pre = k then
        t_suf
      else
        FactorizationTree.binary t_mid t_suf u
          (max t_mid.height t_suf.height + 1)
    else
      if _ : k_pre = k then
        FactorizationTree.binary t_pre t_suf u
          (max t_pre.height t_suf.height + 1)
      else
        let t_pre_mid := FactorizationTree.binary t_pre t_mid (u.take k)
          (max t_pre.height t_mid.height + 1)
        FactorizationTree.binary t_pre_mid t_suf u
          (max t_pre_mid.height t_suf.height + 1)

/-- The height of `nary_tree_structure` is bounded by the maximum of the
part heights plus 3. -/
lemma nary_tree_structure_height_bound (u : List A) (hu : u ≠ [])
    (k k_pre : ℕ)
    (t_pre t_suf : FactorizationTree A)
    (children : List (FactorizationTree A))
    (bound : ℕ)
    (h_pre : t_pre.height ≤ bound + 1)
    (h_suf : t_suf.height ≤ bound + 1)
    (h_children : ∀ c ∈ children, c.height ≤ bound) :
    (nary_tree_structure u hu k k_pre t_pre t_suf children).height ≤
    bound + 3 := by
  unfold nary_tree_structure
  have h_max_children :
      (children.map FactorizationTree.height).foldl max 0 ≤ bound :=
    foldl_max_bound children bound h_children
  have h_mid_le : (list_to_nary children ((u.drop k_pre).take (k - k_pre))
      ((children.map FactorizationTree.height).foldl max 0 + 1)
      (FactorizationTree.leaf (u.head hu))).height ≤ bound + 1 := by
    have := list_to_nary_height_le children
      ((u.drop k_pre).take (k - k_pre))
      ((children.map FactorizationTree.height).foldl max 0 + 1)
      (FactorizationTree.leaf (u.head hu))
    omega
  split_ifs
  · exact h_mid_le.trans (by omega)
  · exact h_pre.trans (by omega)
  · simp (config := { zeta := true }); omega
  · exact h_suf.trans (by omega)
  · simp (config := { zeta := true }); omega
  · simp (config := { zeta := true }); omega
  · simp (config := { zeta := true }); omega

-- ---------------------------------------------------------------------------
-- Section 9: Invariance Under Split Embedding
-- ---------------------------------------------------------------------------

/-- `buildInnerFactorizationTree` is invariant under strictly monotone
embeddings of the split codomain: if `s2 = f ∘ s1` for a strictly monotone
`f`, then the two trees built are equal. -/
lemma buildInnerTree_invariant {A S : Type*} [Semigroup S]
    {h1 h2 : ℕ} [Nonempty (Fin h1)] [Nonempty (Fin h2)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s1 : InnerSplit u h1) (s2 : InnerSplit u h2)
    (f : Fin h1 → Fin h2) (hf_mono : StrictMono f)
    (h_eq : ∀ i, s2 i = f (s1 i)) :
    buildInnerFactorizationTree eval u hu s1 =
    buildInnerFactorizationTree eval u hu s2 := by
  revert h_eq hf_mono f s2
  revert h2
  induction h1, ‹Nonempty (Fin h1)›, u, hu, s1
      using buildInnerFactorizationTree.induct eval
  case case1 =>
    intro h2 inst2 s2 f hf_mono h_eq
    unfold buildInnerFactorizationTree
    dsimp only
    split_ifs; rfl
  case case2 =>
    intro h2 inst2 s2 f hf_mono h_eq
    unfold buildInnerFactorizationTree
    dsimp only
    split_ifs; rfl
  case case3 =>
    rename_i h_height inst u' hu' s1' h_not_len h_nonempty max_val1
      inner_idxs1 idxs1 h_idxs_eq
    intro h2 inst2 s2 f hf_mono h_eq
    have h_impossible : False := by
      have h_max_mem : max_val1 ∈ Finset.image s1' Finset.univ :=
        Finset.max'_mem _ _
      rcases Finset.mem_image.mp h_max_mem with ⟨i, _, hi_eq⟩
      have hi_inner : i ∈ inner_idxs1 := by simp [inner_idxs1, hi_eq]
      have h_inner_nil : inner_idxs1 = [] :=
        List.map_eq_nil_iff.mp h_idxs_eq
      rw [h_inner_nil] at hi_inner
      cases hi_inner
    exact nomatch h_impossible
  case case4 =>
    rename_i h_height inst u' hu' s1' h_not_len h_nonempty max_val1 inner_idxs1 idxs1 h_idxs_ne
      h_const
    intro h2 inst2 s2 f hf_mono h_eq
    unfold buildInnerFactorizationTree
    dsimp only
    have h_nonempty_s1 : (Finset.image s1' Finset.univ).Nonempty := Finset.univ_nonempty.image s1'
    have h_nonempty_s2 : (Finset.image s2 Finset.univ).Nonempty := Finset.univ_nonempty.image s2
    have h_max_val : ∀ h_proof, (Finset.image s2 Finset.univ).max' h_proof = f max_val1 := by
      intro h_proof
      rw [Finset.max'_eq_iff]
      constructor
      · have h_m1 := Finset.max'_mem (Finset.image s1' Finset.univ) (by simp)
        rcases Finset.mem_image.mp h_m1 with ⟨i, _, hi⟩
        apply Finset.mem_image.mpr
        use i, Finset.mem_univ _
        rw [h_eq, hi]
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨i, _, hi⟩
        rw [← hi, h_eq]
        have h_le := Finset.le_max' (Finset.image s1' Finset.univ) (s1' i)
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        exact hf_mono.monotone h_le
    have h_inner_idxs : List.filter
        (fun i => decide (s2 i = (Finset.image s2 Finset.univ).max' h_nonempty_s2)) (List.finRange (u'.length - 1)) = inner_idxs1 := by
      change _ = List.filter (fun i => decide (s1' i = max_val1)) (List.finRange (u'.length - 1))
      congr 1
      funext i
      rw [h_max_val h_nonempty_s2, h_eq]
      simp only [hf_mono.injective.eq_iff]
    have h_inner1_eq : List.filter
        (fun i => decide (s1' i = (Finset.image s1' Finset.univ).max' h_nonempty_s1)) (List.finRange (u'.length - 1)) = inner_idxs1 := rfl
    have h_idxs_ne2 : (List.map mapInnerCut inner_idxs1) ≠ [] := h_idxs_ne
    have h_const2 : inner_idxs1.length = u'.length - 1 := h_const
    simp only [h_inner_idxs, h_inner1_eq, dif_neg h_not_len, dif_neg h_idxs_ne2, dif_pos h_const2]
  case case5 =>
    rename_i h_height inst u' hu' s1' h_not_len h_nonempty max_val1
      inner_idxs1 idxs1 h_idxs_ne h_const k_pre1 k1 ih3 ih2 ih1
    intro h2 inst2 s2 f hf_mono h_eq
    unfold buildInnerFactorizationTree
    dsimp only
    have h_nonempty_s1 : (Finset.image s1' Finset.univ).Nonempty := Finset.univ_nonempty.image s1'
    have h_nonempty_s2 : (Finset.image s2 Finset.univ).Nonempty := Finset.univ_nonempty.image s2
    have h_max_val : ∀ h_proof, (Finset.image s2 Finset.univ).max' h_proof =
        f max_val1 := by
      intro h_proof
      rw [Finset.max'_eq_iff]
      constructor
      · have h_m1 := Finset.max'_mem (Finset.image s1' Finset.univ)
            (by simp)
        rcases Finset.mem_image.mp h_m1 with ⟨i, _, hi⟩
        apply Finset.mem_image.mpr
        use i, Finset.mem_univ _
        rw [h_eq, hi]
      · intro y hy
        rcases Finset.mem_image.mp hy with ⟨i, _, hi⟩
        rw [← hi, h_eq]
        have h_le := Finset.le_max'
          (Finset.image s1' Finset.univ) (s1' i)
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        exact hf_mono.monotone h_le
    have h_inner_idxs : ∀ h_proof, List.filter
        (fun i => decide (s2 i = (Finset.image s2 Finset.univ).max' h_proof)) (List.finRange (u'.length - 1)) = inner_idxs1 := by
      intro h_proof
      change _ = List.filter (fun i => decide (s1' i = max_val1)) (List.finRange (u'.length - 1))
      congr 1
      funext i
      rw [h_max_val h_proof, h_eq]
      simp only [hf_mono.injective.eq_iff]
    have h_inner1_eq : ∀ h_proof, List.filter
        (fun i => decide (s1' i = (Finset.image s1' Finset.univ).max' h_proof)) (List.finRange (u'.length - 1)) = inner_idxs1 := fun _ => rfl
    have h_idxs_ne2 : (List.map mapInnerCut inner_idxs1) ≠ [] := h_idxs_ne
    have h_const2 : ¬ (inner_idxs1.length = u'.length - 1) := h_const

    simp only [h_inner_idxs, h_inner1_eq, dif_neg h_not_len, dif_neg h_idxs_ne2, dif_neg h_const2]

    let max_val2 := (Finset.image s2 Finset.univ).max' h_nonempty_s2
    have h_max_eq : max_val2 = f max_val1 := h_max_val h_nonempty_s2
    -- Define the restricted strictly monotone function for the recursive calls
    let f' : Fin max_val1.val → Fin max_val2.val := fun x => ⟨(f ⟨x.val, by omega⟩).val, by
      have h2 : (f ⟨x.val, by omega⟩).val < (f max_val1).val := hf_mono (by exact x.isLt)
      rw [← h_max_eq] at h2
      exact h2
    ⟩
    have hf'_mono : StrictMono f' := by
      intro x y hxy
      exact hf_mono hxy

    have h_int_eq : ∀ offset (w : List A) h_len h_start h_proof,
        (∀ idx : Fin (w.length - 1), (restrictInnerSplit s2 offset h_len h_start idx).val <
          ((Finset.image s2 Finset.univ).max' h_proof).val) =
        (∀ idx : Fin (w.length - 1), (restrictInnerSplit s1' offset h_len h_start idx).val < max_val1.val) := by
      intro offset w h_len h_start h_proof
      apply propext
      constructor
      · intro h_int idx
        have h1 := h_int idx
        rw [restrictInnerSplit] at h1
        have h_s2 : s2 ⟨offset + idx.val, by omega⟩ = f (s1' ⟨offset + idx.val, by omega⟩) := h_eq _
        have h_mv : (Finset.image s2 Finset.univ).max' h_proof = f max_val1 := h_max_val _
        rw [h_s2, h_mv] at h1
        exact hf_mono.lt_iff_lt.mp h1
      · intro h_int idx
        have h1 := h_int idx
        rw [restrictInnerSplit]
        have h_s2 : s2 ⟨offset + idx.val, by omega⟩ = f (s1' ⟨offset + idx.val, by omega⟩) := h_eq _
        have h_mv : (Finset.image s2 Finset.univ).max' h_proof = f max_val1 := h_max_val _
        rw [h_s2, h_mv]
        exact hf_mono h1

    have h_pre_eq := fun h_pre_len h_start h_interior =>
      have h_idx_lt : 0 < (u'.take k_pre1).length - 1 := by omega
      have h_lt := h_interior ⟨0, h_idx_lt⟩
      have h_max1_pos : 0 < max_val1.val := by omega
      have : Nonempty (Fin max_val2.val) := ⟨f' ⟨0, h_max1_pos⟩⟩
      ih2 h_pre_len h_start h_interior
        (lowerInnerSplit (restrictInnerSplit s2 0 (by omega) (by omega)) ((h_int_eq 0 (u'.take k_pre1) (by omega) (by omega) h_nonempty_s2).mpr h_interior))
        f' hf'_mono (fun idx => by
          apply Fin.ext
          dsimp [restrictInnerSplit, f', lowerInnerSplit]
          exact congr_arg Fin.val (h_eq ⟨0 + idx.val, by
            have := idx.isLt
            omega
          ⟩)
        )

    have h_suf_eq := fun h_suf_len h_start h_interior =>
      have h_idx_lt : 0 < ((u'.drop k1).take (u'.length - k1)).length - 1 := by omega
      have h_lt := h_interior ⟨0, h_idx_lt⟩
      have h_max1_pos : 0 < max_val1.val := by omega
      have : Nonempty (Fin max_val2.val) := ⟨f' ⟨0, h_max1_pos⟩⟩
      ih1 h_suf_len h_start h_interior
        (lowerInnerSplit (restrictInnerSplit s2 k1 (by omega) (by omega)) ((h_int_eq k1 ((u'.drop k1).take (u'.length - k1)) (by omega) (by omega) h_nonempty_s2).mpr h_interior))
        f' hf'_mono (fun idx => by
          apply Fin.ext
          dsimp [restrictInnerSplit, f', lowerInnerSplit]
          exact congr_arg Fin.val (h_eq ⟨k1 + idx.val, by
            have := idx.isLt
            omega
          ⟩)
        )

    have h_mid_eq := fun (i j : Fin (u'.length + 1)) (h_part : (i, j) ∈ partitionIndices idxs1) h_len h_start h_interior =>
      have h_idx_lt : 0 < ((u'.drop i.val).take (j.val - i.val)).length - 1 := by omega
      have h_lt := h_interior ⟨0, h_idx_lt⟩
      have h_max1_pos : 0 < max_val1.val := by omega
      have : Nonempty (Fin max_val2.val) := ⟨f' ⟨0, h_max1_pos⟩⟩
      ih3 i j h_len h_start h_interior
        (lowerInnerSplit (restrictInnerSplit s2 (i.val - 1) (by omega) (by omega)) ((h_int_eq (i.val - 1) ((u'.drop i.val).take (j.val - i.val)) (by omega) (by omega) h_nonempty_s2).mpr h_interior))
        f' hf'_mono (fun idx => by
          apply Fin.ext
          dsimp [restrictInnerSplit, f', lowerInnerSplit]
          exact congr_arg Fin.val (h_eq ⟨(i.val - 1) + idx.val, by
            have := idx.isLt
            omega
          ⟩)
        )

    have binary_eq_height : ∀ {t1 t1' t2 t2' : FactorizationTree A} {w w' : List A},
      t1 = t1' → t2 = t2' → w = w' →
      FactorizationTree.binary t1 t2 w (max t1.height t2.height + 1) =
      FactorizationTree.binary t1' t2' w' (max t1'.height t2'.height + 1) := by
      intro _ _ _ _ _ _ ht1 ht2 hw; rw [ht1, ht2, hw]

    have list_to_nary_eq_height : ∀ {l1 l2 : List (FactorizationTree A)} {w w' : List A} {dl dl' : FactorizationTree A},
      l1 = l2 → w = w' → dl = dl' →
      list_to_nary l1 w (List.foldl max 0 (List.map FactorizationTree.height l1) + 1) dl =
      list_to_nary l2 w' (List.foldl max 0 (List.map FactorizationTree.height l2) + 1) dl' := by
      intro _ _ _ _ _ _ hl hw hdl; rw [hl, hw, hdl]

    have map_eq : ∀ {α β} {f g : α → β} {l : List α},
      (∀ x ∈ l, f x = g x) → List.map f l = List.map g l := by
      intro _ _ _ _ _ h; apply List.map_congr_left h

    have h_rw_pre1 : ∀ h_proof h_ne, ((List.map mapInnerCut (List.filter (fun i => decide (s1' i = (Finset.image s1' Finset.univ).max' h_proof)) (List.finRange (u'.length - 1)))).head h_ne) = idxs1.head h_idxs_ne := by
      intro h_proof h_ne; congr 1
    have h_rw_pre2 : ∀ h_proof h_ne, ((List.map mapInnerCut (List.filter (fun i => decide (s2 i = (Finset.image s2 Finset.univ).max' h_proof)) (List.finRange (u'.length - 1)))).head h_ne) = idxs1.head h_idxs_ne := by
      intro h_proof h_ne; have h_eq := h_inner_idxs h_proof; revert h_ne; rw [h_eq]; intro h_ne; congr 1
    have h_rw1 : ∀ h_proof h_ne, ((List.map mapInnerCut (List.filter (fun i => decide (s1' i = (Finset.image s1' Finset.univ).max' h_proof)) (List.finRange (u'.length - 1)))).getLast h_ne) = idxs1.getLast h_idxs_ne := by
      intro h_proof h_ne; congr 1
    have h_rw2 : ∀ h_proof h_ne, ((List.map mapInnerCut (List.filter (fun i => decide (s2 i = (Finset.image s2 Finset.univ).max' h_proof)) (List.finRange (u'.length - 1)))).getLast h_ne) = idxs1.getLast h_idxs_ne := by
      intro h_proof h_ne; have h_eq := h_inner_idxs h_proof; revert h_ne; rw [h_eq]; intro h_ne; congr 1

    have h_max1_val_eq : ∀ h_proof, ((Finset.image s1' Finset.univ).max' h_proof).val = max_val1.val := fun _ => rfl

    simp only [h_max1_val_eq, h_int_eq]

    apply binary_eq_height
    · -- t_pre_mid
      apply binary_eq_height
      · -- t_pre
        simp only [h_rw_pre1, h_rw_pre2]
        split_ifs
        all_goals {
          first
          | rfl
          | exact h_pre_eq (by assumption) (by assumption) (by assumption)
        }
      · -- t_mid
        apply list_to_nary_eq_height
        · -- l1 = l2
          apply map_eq
          intro x hx
          split_ifs
          all_goals {
            first
            | rfl
            | exact h_mid_eq x.1 x.2 hx (by assumption) (by assumption) (by assumption)
          }
        · rfl
        · rfl
      · rfl
    · -- t_suf
      simp only [h_rw1, h_rw2]
      split_ifs
      all_goals {
        first
        | rfl
        | exact h_suf_eq (by assumption) (by assumption) (by assumption)
      }
    · rfl

-- ---------------------------------------------------------------------------
-- Section 10: Height Bound for Children
-- ---------------------------------------------------------------------------

/-- When a split is uniformly strictly below `h' - 1`, the constructed tree
height is bounded by `3 * (h' - 1) - 1`. -/
lemma buildTree_child_height_bound {A S : Type*} [Semigroup S]
    {h' : ℕ} (_ : h' ≠ 1) [Nonempty (Fin h')]
    (eval : List A → S) (w : List A) (hw : w ≠ [])
    (s_w : Split (Fin (w.length + 1)) h')
    (h_no_max : ∀ i, (s_w i).val < h' - 1)
    (ih : ∀ [Nonempty (Fin (h' - 1))] (u : List A) (hu : u ≠ [])
        (s : Split (Fin (u.length + 1)) (h' - 1)),
      (buildFactorizationTree eval u hu s).height ≤ 3 * (h' - 1) - 1) :
    (buildFactorizationTree eval w hw s_w).height ≤ 3 * (h' - 1) - 1 := by
  have h_ne : Nonempty (Fin (h' - 1)) :=
    ⟨⟨(s_w ⟨0, by omega⟩).val, h_no_max _⟩⟩
  let s_lower : Split (Fin (w.length + 1)) (h' - 1) :=
    fun i => ⟨(s_w i).val, h_no_max i⟩
  have h_eq :
      buildFactorizationTree eval w hw s_w =
      buildFactorizationTree eval w hw s_lower := by
    unfold buildFactorizationTree
    apply Eq.symm
    apply buildInnerTree_invariant eval w hw
      (fun i => s_lower ⟨i.val + 1, by omega⟩)
      (fun i => s_w ⟨i.val + 1, by omega⟩)
      (fun x => ⟨x.val, by omega⟩)
    · intro a b hab
      simp only [Fin.lt_def] at hab ⊢
      exact hab
    · intro i; rfl
  rw [h_eq]
  exact ih w hw s_lower

/-- `buildFactorizationTree` on a word of length 1 produces a tree of height 0. -/
lemma buildTree_height_zero_of_len_one {A S : Type*} [Semigroup S]
    {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h)
    (h_len : u.length = 1) :
    (buildFactorizationTree eval u hu s).height = 0 := by
  unfold buildFactorizationTree buildInnerFactorizationTree
  dsimp only
  rw [dif_pos (by omega), dif_pos h_len]
  rfl

/-- `buildFactorizationTree` on a word of length ≤ 2 produces a tree of
height ≤ 1. -/
lemma buildTree_height_le_one_of_len_le_two {A S : Type*} [Semigroup S]
    {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h)
    (h_len : u.length ≤ 2) :
    (buildFactorizationTree eval u hu s).height ≤ 1 := by
  unfold buildFactorizationTree buildInnerFactorizationTree
  dsimp only
  rw [dif_pos h_len]
  split_ifs
  · exact Nat.zero_le 1
  · rfl

/-- **Height bound**: the height of the tree produced by
`buildFactorizationTree eval u hu s` is at most `3 * h - 1`. -/
theorem buildTree_height_bound {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h) :
    (buildFactorizationTree eval u hu s).height ≤ 3 * h - 1 := by
  unfold buildFactorizationTree
  exact buildInnerTree_height_bound eval u hu _

/-- `buildFactorizationTree` with a split of size 1 produces a tree of
height ≤ 2. -/
lemma buildTree_height_bound_one {A S : Type*} [Semigroup S]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) 1) :
    (buildFactorizationTree eval u hu s).height ≤ 2 :=
  buildTree_height_bound eval u hu s

-- ---------------------------------------------------------------------------
-- Section 11: The Ramsey Property
-- ---------------------------------------------------------------------------

/-- Extracts the common idempotent value from a set of indices in `splitIndices`
that includes at least three points `i0 < i1 < i2`. All pairs within the index
set evaluate to the same idempotent element under the word labeling. -/
lemma extract_idempotent {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (idxs : List (Fin (u.length + 1)))
    (h_idxs : ∀ i ∈ idxs,
      s i = Finset.max' Finset.univ Finset.univ_nonempty)
    (i0 i1 i2 : Fin (u.length + 1))
    (hi0_mem : i0 ∈ idxs) (hi1_mem : i1 ∈ idxs) (hi2_mem : i2 ∈ idxs)
    (hlt01 : i0 < i1) (hlt12 : i1 < i2) :
    let L := wordLabeling eval hmul u
    let e := L.σ i0 i1
    e * e = e ∧ ∀ j0 j1, j0 ∈ idxs → j1 ∈ idxs → j0 < j1 →
      L.σ j0 j1 = e := by
  intros L e
  have mk_rel : ∀ a b, a ∈ idxs → b ∈ idxs → a < b →
      SplitRelation s a b := by
    intro a b ha hb hab
    dsimp [SplitRelation]
    exact ⟨by rw [h_idxs a ha, h_idxs b hb],
      fun z hz_ge hz_le ↦ by
        have h_s_min :
            s (min a b) = Finset.max' Finset.univ Finset.univ_nonempty := by
          rw [min_eq_left (le_of_lt hab), h_idxs a ha]
        rw [h_s_min]
        exact Finset.le_max' _ _ (Finset.mem_univ _)⟩
  constructor
  · exact hs_ramsey.left i0 i1 i2 hlt01 hlt12
      (mk_rel i0 i1 hi0_mem hi1_mem hlt01)
      (mk_rel i1 i2 hi1_mem hi2_mem hlt12)
  · intros j0 j1 h_j0_mem h_j1_mem hlt_j
    have h_rel_cross : SplitRelation s i0 j0 := by
      dsimp [SplitRelation]
      exact ⟨by rw [h_idxs i0 hi0_mem, h_idxs j0 h_j0_mem],
        fun z h_i0_le_z h_z_le_j0 ↦ by
          have h_s_min :
              s (min i0 j0) =
              Finset.max' Finset.univ Finset.univ_nonempty := by
            obtain h_le | h_le := le_total i0 j0 <;>
              simp only [min_eq_left h_le, min_eq_right h_le,
                h_idxs i0 hi0_mem, h_idxs j0 h_j0_mem]
          exact h_s_min ▸ Finset.le_max' _ _ (Finset.mem_univ _)⟩
    exact (hs_ramsey.right i0 i1 j0 j1 hlt01 hlt_j
      (mk_rel i0 i1 hi0_mem hi1_mem hlt01)
      (mk_rel j0 j1 h_j0_mem h_j1_mem hlt_j) h_rel_cross).symm



/-- A split relation on a restricted sub-interval lifts to a split relation
on the full domain (with indices shifted by `i`). -/
lemma shift_split_relation {n h : ℕ} (s : Split (Fin (n + 1)) h)
    {i len : ℕ} (h_bound : i + len ≤ n) (x y : Fin (len + 1))
    (hsr : SplitRelation (restrictSplit s i len h_bound) x y) :
    SplitRelation s ⟨i + x.val, by omega⟩ ⟨i + y.val, by omega⟩ := by
  exact ⟨hsr.1, fun z hz_ge hz_le ↦ by
    have h_rel_le := hsr.2
    rcases le_total x y with hxy | hxy
    · have hixy :
          (⟨i + x.val, by omega⟩ : Fin (n + 1)) ≤
          ⟨i + y.val, by omega⟩ :=
        Fin.le_iff_val_le_val.mpr
          (by have hxy_val := Fin.le_iff_val_le_val.mp hxy; grind)
      rw [min_eq_left hxy, max_eq_right hxy] at h_rel_le
      rw [min_eq_left hixy] at hz_ge ⊢
      rw [max_eq_right hixy] at hz_le
      have hi_le_z : i ≤ z.val := by
        have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge; grind
      let zw : Fin (len + 1) := ⟨z.val - i, by
        have hz_le_val := Fin.le_iff_val_le_val.mp hz_le
        have hy_lt := y.isLt
        simp; grind⟩
      have hx_zw : x ≤ zw := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]
        have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge
        simp; grind)
      have hzw_y : zw ≤ y := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]
        have hz_le_val := Fin.le_iff_val_le_val.mp hz_le
        simp; grind)
      have h_res := h_rel_le zw hx_zw hzw_y
      rw [(Fin.ext (by dsimp [zw]; omega) :
          z = (⟨i + zw.val, by dsimp [zw]; omega⟩ : Fin (n + 1)))]
      exact h_res
    · have hyx : y ≤ x := by omega
      have hiyx :
          (⟨i + y.val, by omega⟩ : Fin (n + 1)) ≤
          ⟨i + x.val, by omega⟩ :=
        Fin.le_iff_val_le_val.mpr
          (by have hxy_val := Fin.le_iff_val_le_val.mp hxy; grind)
      rw [min_eq_right hxy, max_eq_left hxy] at h_rel_le
      rw [min_eq_right hiyx] at hz_ge ⊢
      rw [max_eq_left hiyx] at hz_le
      have hi_le_z : i ≤ z.val := by
        have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge; grind
      let zw : Fin (len + 1) := ⟨z.val - i, by
        have hz_le_val := Fin.le_iff_val_le_val.mp hz_le
        have hx_lt := x.isLt
        simp; grind⟩
      have hy_zw : y ≤ zw := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]
        have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge
        simp; grind)
      have hzw_x : zw ≤ x := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]
        have hz_le_val := Fin.le_iff_val_le_val.mp hz_le
        simp; grind)
      have h_res := h_rel_le zw hy_zw hzw_x
      rw [(Fin.ext (by dsimp [zw]; omega) :
          z = (⟨i + zw.val, by dsimp [zw]; omega⟩ : Fin (n + 1)))]
      exact h_res⟩

/-- A restricted split inherits the Ramsey property from the full split,
restricted to the corresponding sub-word. -/
lemma restrictSplit_ramsey {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (i : ℕ) (w : List A) (h_bound : i + w.length ≤ u.length)
    (hw : ∃ j, w = (u.drop i).take (j - i) := by exact ⟨_, rfl⟩) :
    IsRamsey (wordLabeling eval hmul w)
      (restrictSplit s i w.length h_bound) := by
  constructor
  · intros x y z hxy hyz hsr_xy hsr_yz
    have hx_b : i + x.val < u.length + 1 := by omega
    have hy_b : i + y.val < u.length + 1 := by omega
    have hz_b : i + z.val < u.length + 1 := by omega
    have hxy_shift :
        (⟨i + x.val, hx_b⟩ : Fin (u.length + 1)) <
        ⟨i + y.val, hy_b⟩ := by
      simp only [Fin.mk_lt_mk]; omega
    have hyz_shift :
        (⟨i + y.val, hy_b⟩ : Fin (u.length + 1)) <
        ⟨i + z.val, hz_b⟩ := by
      simp only [Fin.mk_lt_mk]; omega
    have h_eval := hs_ramsey.1 _ _ _ hxy_shift hyz_shift
      (shift_split_relation s h_bound x y hsr_xy)
      (shift_split_relation s h_bound y z hsr_yz)
    dsimp [wordLabeling] at h_eval ⊢
    rw [chunk_eq hw x y (le_of_lt hxy)]
    have h_sub : (i + y.val) - (i + x.val) = y.val - x.val := by omega
    have h_eval_eq :
        (u.drop (i + x.val)).take (i + y.val - (i + x.val)) =
        (u.drop (i + x.val)).take (y.val - x.val) := by rw [h_sub]
    rw [h_eval_eq] at h_eval
    exact h_eval
  · intros x y p q hxy hpq h_rel_xy h_rel_pq h_rel_xp
    have hx_b : i + x.val < u.length + 1 := by omega
    have hy_b : i + y.val < u.length + 1 := by omega
    have hp_b : i + p.val < u.length + 1 := by omega
    have hq_b : i + q.val < u.length + 1 := by omega
    have hxy_shift :
        (⟨i + x.val, hx_b⟩ : Fin (u.length + 1)) <
        ⟨i + y.val, hy_b⟩ := by simp; omega
    have hpq_shift :
        (⟨i + p.val, hp_b⟩ : Fin (u.length + 1)) <
        ⟨i + q.val, hq_b⟩ := by simp; omega
    have h_eval := hs_ramsey.2 _ _ _ _ hxy_shift hpq_shift
      (shift_split_relation s h_bound x y h_rel_xy)
      (shift_split_relation s h_bound p q h_rel_pq)
      (shift_split_relation s h_bound x p h_rel_xp)
    dsimp [wordLabeling] at h_eval ⊢
    simp only [chunk_eq hw x y (le_of_lt hxy),
      chunk_eq hw p q (le_of_lt hpq)]
    have h_sub1 : (i + y.val) - (i + x.val) = y.val - x.val := by omega
    have h_sub2 : (i + q.val) - (i + p.val) = q.val - p.val := by omega
    have h_eval_eq1 :
        (u.drop (i + x.val)).take (i + y.val - (i + x.val)) =
        (u.drop (i + x.val)).take (y.val - x.val) := by rw [h_sub1]
    have h_eval_eq2 :
        (u.drop (i + p.val)).take (i + q.val - (i + p.val)) =
        (u.drop (i + p.val)).take (q.val - p.val) := by rw [h_sub2]
    simp only [h_eval_eq1, h_eval_eq2] at h_eval
    exact h_eval

/-- Lowering the interior of a split (below `h - 1`) preserves the Ramsey
property, since the split relation is unchanged by a value-preserving map. -/
lemma lowerSplitInterior_ramsey {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)] [Nonempty (Fin (h - 1))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) (_ : 1 < h)
    (h_interior : ∀ i : Fin (u.length + 1), (s i).val < h - 1) :
    IsRamsey (wordLabeling eval hmul u)
      (lowerSplitInterior s h_interior) := by
  have h_rel_eq : ∀ x y,
      SplitRelation (lowerSplitInterior s h_interior) x y ↔
      SplitRelation s x y := by
    intro x y
    dsimp [SplitRelation, lowerSplitInterior]
    constructor
    · rintro ⟨h_s_eq, h_s_le⟩
      have h_s_eq_val := congrArg Fin.val h_s_eq
      exact ⟨Fin.ext h_s_eq_val, fun z hx_le_z hz_le_y ↦
        Fin.le_iff_val_le_val.mpr
          (Fin.le_iff_val_le_val.mp (h_s_le z hx_le_z hz_le_y))⟩
    · rintro ⟨h_s_eq, h_s_le⟩
      have h_s_eq_val := congrArg Fin.val h_s_eq
      exact ⟨Fin.ext h_s_eq_val, fun z hx_le_z hz_le_y ↦
        Fin.le_iff_val_le_val.mpr
          (Fin.le_iff_val_le_val.mp (h_s_le z hx_le_z hz_le_y))⟩
  exact ⟨fun x y z hxy hyz h_rel_xy h_rel_yz ↦
      hs_ramsey.1 x y z hxy hyz
        ((h_rel_eq x y).mp h_rel_xy) ((h_rel_eq y z).mp h_rel_yz),
    fun x y p q hxy hpq h_rel_xy h_rel_pq h_rel_xp ↦
      hs_ramsey.2 x y p q hxy hpq ((h_rel_eq x y).mp h_rel_xy)
        ((h_rel_eq p q).mp h_rel_pq) ((h_rel_eq x p).mp h_rel_xp)⟩

/-- The n-ary children of a Ramsey tree all evaluate to the same idempotent,
provided the children were built from a Ramsey split and the index list
includes at least 4 elements (giving at least 3 children). -/
lemma nary_children_ramsey {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (children : List (FactorizationTree A))
    (h_children : ((partitionIndices (splitIndices s)).map
        fun ⟨i, j⟩ =>
        let w_len := j.val - i.val
        let w := (u.drop i.val).take w_len
        if h_valid : w.length < u.length ∧
            i.val + w.length ≤ u.length ∧
            w ≠ [] then
          let s_w : Split (Fin (w.length + 1)) h :=
            restrictSplit s i.val w.length (by exact h_valid.2.1)
          buildFactorizationTree eval w (by exact h_valid.2.2) s_w
        else
          FactorizationTree.leaf (u.head hu)) = children)
    (h_at_least_3 : children.length ≥ 3)
    (h_not_idxs : (splitIndices s).map (·.val) ≠ [0, u.length]) :
    ∃ (e : S), e * e = e ∧
      ∀ c ∈ children, eval (FactorizationTree.word c) = e := by
  generalize h_idx_eq : splitIndices s = idxs at h_children ⊢
  have h_idxs : ∀ i ∈ idxs,
      s i = Finset.max' Finset.univ Finset.univ_nonempty := by
    intro i hi
    rw [← h_idx_eq] at hi
    unfold splitIndices at hi
    rw [List.mem_filter] at hi
    exact of_decide_eq_true hi.right
  have h_len_idxs : idxs.length ≥ 4 := by
    have h_map_len : (partitionIndices idxs).length = children.length := by
      have h_map_len2 :
          (((partitionIndices idxs).map _).length) = children.length :=
        congrArg List.length h_children
      rwa [List.length_map] at h_map_len2
    have h_part_len : ∀ {n} (l : List (Fin (n + 1))),
        (partitionIndices l).length = l.length - 1 := by
      intro n l
      induction l with
      | nil => rfl
      | cons a l' ih =>
        cases l'
        · rfl
        · simp [partitionIndices, ih]
    rw [h_part_len] at h_map_len
    omega
  rcases idxs with _ | ⟨i0, _ | ⟨i1, _ | ⟨i2, rest⟩⟩⟩
  · nomatch h_len_idxs
  · nomatch h_len_idxs
  · nomatch h_len_idxs
  · have h_sorted : List.Pairwise (· < ·) (i0 :: i1 :: i2 :: rest) := by
      rw [← h_idx_eq]
      unfold splitIndices
      exact List.Pairwise.filter _
        (List.sortedLT_finRange (u.length + 1) |>.pairwise)
    have hlt01 : i0 < i1 :=
      List.pairwise_cons.1 h_sorted |>.1 i1 (by simp)
    have hlt12 : i1 < i2 :=
      List.pairwise_cons.1
        (List.pairwise_cons.1 h_sorted |>.2) |>.1 i2 (by simp)
    have ⟨hi0_mem, hi1_mem, hi2_mem⟩ :
        i0 ∈ i0 :: i1 :: i2 :: rest ∧
        i1 ∈ i0 :: i1 :: i2 :: rest ∧
        i2 ∈ i0 :: i1 :: i2 :: rest := by simp
    obtain ⟨h_ee, h_all_pairs⟩ :=
      extract_idempotent eval hmul u s hs_ramsey
        (i0 :: i1 :: i2 :: rest) h_idxs i0 i1 i2
        hi0_mem hi1_mem hi2_mem hlt01 hlt12
    use (wordLabeling eval hmul u).σ i0 i1
    constructor
    · exact h_ee
    · intro c hc
      simp only [← h_children, List.mem_map, Prod.exists] at hc
      rcases hc with ⟨j0, j1, hj_mem, hc_eq⟩
      simp only [← hc_eq]
      split
      · rename_i h_valid
        obtain ⟨h_j0_mem, h_j1_mem, h_j_lt, _, _⟩ :=
          partitionIndices_props h_sorted hj_mem
        rw [buildTree_word_eq]
        have h_σ := h_all_pairs j0 j1 h_j0_mem h_j1_mem h_j_lt
        dsimp [wordLabeling, MultiplicativeLabeling.σ] at h_σ ⊢
        exact h_σ
      · rename_i h_valid_false
        obtain ⟨_, _, _, hj_len, _⟩ :=
          partitionIndices_props h_sorted hj_mem
        have h_len : j1.val - j0.val < u.length := by
          by_contra h_ge
          have h_eq_u : j1.val - j0.val = u.length := by omega
          exact h_not_idxs (h_idx_eq.symm ▸ hj_len h_eq_u)
        have h_valid_true :
            ((u.drop j0.val).take (j1.val - j0.val)).length < u.length ∧
            j0.val + ((u.drop j0.val).take (j1.val - j0.val)).length ≤
              u.length ∧
            ((u.drop j0.val).take (j1.val - j0.val)) ≠ [] := by
          have h_take_len :
              ((u.drop j0.val).take (j1.val - j0.val)).length =
              j1.val - j0.val := by
            rw [List.length_take, List.length_drop]
            exact min_eq_left (by omega)
          exact ⟨by omega, by omega, by
            rw [← List.length_pos_iff, h_take_len]; omega⟩
        exact nomatch (h_valid_false h_valid_true)

/-- The `nary_tree_structure` construction produces a Ramsey tree, given that
the prefix, suffix, and children are all Ramsey. -/
lemma nary_control_flow_ramsey {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (u : List A) (hu : u ≠ [])
    (k k_pre : ℕ)
    (t_pre t_suf : FactorizationTree A)
    (children : List (FactorizationTree A)) :
    k ≤ u.length →
    k_pre ≤ k →
    IsRamseyTree eval t_pre →
    IsRamseyTree eval t_suf →
    (∀ c ∈ children, IsRamseyTree eval c) →
    (∃ e, e * e = e ∧ ∀ c ∈ children, eval c.word = e) →
    t_pre.word = u.take k_pre →
    t_suf.word = (u.drop k).take (u.length - k) →
    List.flatten (children.map FactorizationTree.word) =
      (u.drop k_pre).take (k - k_pre) →
    children.length ≥ 3 →
    IsRamseyTree eval
      (nary_tree_structure u hu k k_pre t_pre t_suf children) := by
  intros h_k_le h_pre_le h_pre_ramsey h_suf_ramsey h_children_ramsey
    h_e h_pre_word h_suf_word h_children_word h_children_len
  unfold nary_tree_structure
  have h_mid_ramsey : IsRamseyTree eval
      (list_to_nary children ((u.drop k_pre).take (k - k_pre))
        ((children.map FactorizationTree.height).foldl max 0 + 1)
        (FactorizationTree.leaf (u.head hu))) := by
    rw [list_to_nary_of_len_ge_3 _ _ _ _ h_children_len]
    apply IsRamseyTree.nary _ _ _ h_children_len h_children_ramsey
      h_e h_children_word.symm
    intro c hc
    have h_mem : c.height ∈ children.map FactorizationTree.height := by
      simp only [List.mem_map]
      exact ⟨c, hc, rfl⟩
    have h_le_max : c.height ≤
        (children.map FactorizationTree.height).foldl max 0 :=
      foldl_max_mem _ _ h_mem
    omega
  split_ifs
  · exact h_mid_ramsey
  · exact h_pre_ramsey
  · rename_i h_k_full h_k_zero h_k_eq_pre
    apply IsRamseyTree.binary
    · exact h_pre_ramsey
    · exact h_mid_ramsey
    · rw [h_pre_word, list_to_nary_word_eq]
      have h_take := take_append_take_drop u k_pre (k - k_pre)
      have h_sum : k_pre + (k - k_pre) = k := by omega
      rw [h_sum] at h_take
      have h_k_eq : u.take k = u := by rw [h_k_full, List.take_length]
      rw [h_take, h_k_eq]
    · omega
    · omega
  · exact h_suf_ramsey
  · rename_i h_k_full h_k_zero h_k_eq_pre
    apply IsRamseyTree.binary
    · exact h_mid_ramsey
    · exact h_suf_ramsey
    · rw [h_suf_word, list_to_nary_word_eq]
      rw [h_k_zero]
      have h_sub : k - 0 = k := by omega
      rw [h_sub, List.drop_zero]
      have h_take : u.take k ++ u.drop k = u := List.take_append_drop k u
      have h_len : u.length - k = (u.drop k).length := by simp
      have h_take_all : (u.drop k).take (u.length - k) = u.drop k := by
        rw [h_len, List.take_length]
      rw [h_take_all, h_take]
    · omega
    · omega
  · rename_i h_k_full h_k_zero h_k_eq_pre
    apply IsRamseyTree.binary
    · exact h_pre_ramsey
    · exact h_suf_ramsey
    · rw [h_pre_word, h_suf_word]
      rw [h_k_eq_pre]
      have h_len : u.length - k = (u.drop k).length := by simp
      have h_take_all : (u.drop k).take (u.length - k) = u.drop k := by
        rw [h_len, List.take_length]
      rw [h_take_all, List.take_append_drop k u]
    · omega
    · omega
  · rename_i h_k_full h_k_zero h_k_eq_pre
    apply IsRamseyTree.binary
    · apply IsRamseyTree.binary
      · exact h_pre_ramsey
      · exact h_mid_ramsey
      · rw [h_pre_word, list_to_nary_word_eq]
        have h_take := take_append_take_drop u k_pre (k - k_pre)
        have h_sum : k_pre + (k - k_pre) = k := by omega
        rw [h_sum] at h_take
        exact h_take.symm
      · omega
      · omega
    · exact h_suf_ramsey
    · rw [h_suf_word]
      have h_len : u.length - k = (u.drop k).length := by simp
      have h_take_all : (u.drop k).take (u.length - k) = u.drop k := by
        rw [h_len, List.take_length]
      rw [h_take_all, List.take_append_drop k u]
    · omega
    · omega

-- ---------------------------------------------------------------------------
-- Section 12: Main Theorems
-- ---------------------------------------------------------------------------

/-- **The constructed tree is a Ramsey tree** (proof pending — key step is
showing that all n-ary nodes evaluate to the same idempotent, which follows
from the Ramsey property of the split). -/
theorem buildTree_isRamsey {A S : Type*} [Semigroup S] {h : ℕ}
    [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h)
    (_hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    IsRamseyTree eval (buildFactorizationTree eval u hu s) := by
  -- Proof sketch:
  -- 1. Base cases (u.length ≤ 2 and idxs = []):
  --    - Leaves and binary of two leaves are trivially Ramsey.
  -- 2. Inductive step (case 4):
  --    - t_pre, t_mid, t_suf are built recursively — Ramsey by IH.
  --    - t_mid = list_to_nary children; the children evaluate to the
  --      same idempotent by `nary_children_ramsey`.
  --    - Combining them with binary nodes preserves the Ramsey property.
  sorry

/-- **Existence of a Ramsey factorization tree**: given a Ramsey split, one
can construct a factorization tree of bounded height that spans the word. -/
theorem exists_factorizationTree_of_split {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) {h : ℕ} [Nonempty (Fin h)]
    (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    ∃ (t : FactorizationTree A), t.word = u ∧
      t.height ≤ 3 * h - 1 ∧ IsRamseyTree eval t :=
  ⟨buildFactorizationTree eval u hu s,
    buildTree_word_eq eval u hu s,
    buildTree_height_bound eval u hu s,
    buildTree_isRamsey eval hmul u hu s hs_ramsey⟩

/-- **Simon's Factorization Forest Theorem**: every word `u` over a finite
semigroup `S` admits a factorization tree of height at most `3 * nS S - 1`.
This is the main theorem of the file, combining Simon's split theorem
(`simon_word`) with the tree construction (`exists_factorizationTree_of_split`). -/
theorem factorization_forest {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty (Fin (nS S))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ (t : FactorizationTree A), t.word = u ∧
      t.height ≤ 3 * (nS S) - 1 ∧ IsRamseyTree eval t :=
  let ⟨s, _, hs_ramsey⟩ := simon_word eval hmul u
  exists_factorizationTree_of_split eval hmul u hu s hs_ramsey

end FactorizationForest
