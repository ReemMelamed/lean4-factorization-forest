/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Project.FactorizationForest.Split

/-!
# The Factorization Forest Theorem

## References
* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace FactorizationForest

/-- Indices in `Fin (n+1)` that receive the maximal split rank. -/
def splitIndices {n h : ℕ} [Nonempty (Fin h)]
    (s : Split (Fin (n + 1)) h) : List (Fin (n + 1)) :=
  let max_val := Finset.max' Finset.univ Finset.univ_nonempty
  (List.finRange (n + 1)).filter (fun i => s i = max_val)

/-- Adjacent pairs from a list of indices. -/
def partitionIndices {n : ℕ} : List (Fin (n + 1)) → List (Fin (n + 1) × Fin (n + 1))
| [] => []
| _ :: [] => []
| i :: j :: rest => (i, j) :: partitionIndices (j :: rest)

/-- Properties of pairs from `partitionIndices`:
both elements are in the list, they are strictly ordered,
and no list element lies strictly between them. -/
lemma partitionIndices_props {n : ℕ} {l : List (Fin (n + 1))} {i j : Fin (n + 1)}
    (hs : List.Pairwise (· < ·) l) (h : (i, j) ∈ partitionIndices l) :
    i ∈ l ∧ j ∈ l ∧ i < j ∧ (j.val - i.val = n → l.map (·.val) = [0, n]) ∧
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
                List.pairwise_cons.1 (List.pairwise_cons.1 hs |>.2) |>.1 c (by simp)
              omega,
          fun k hk ↦ by
            simp only [List.mem_cons] at hk
            rcases hk with rfl | rfl | hk
            · omega
            · omega
            · have hjk : j < k := List.pairwise_cons.1 (List.pairwise_cons.1 hs |>.2) |>.1 k hk
              omega⟩
      · obtain ⟨hi, hj, hij, h_len, h_adj⟩ := ih (List.pairwise_cons.1 hs |>.2) h_tail
        exact ⟨by simp [hi], by simp [hj], hij,
          fun h_eq_n ↦ by
            have hab : a < b := List.pairwise_cons.1 hs |>.1 b (by simp)
            have hb_zero : b.val = 0 := by injection h_len h_eq_n
            omega,
          fun k hk ↦ by
            rcases List.mem_cons.1 hk with rfl | hk
            · have hki : k < i := List.pairwise_cons.1 hs |>.1 i (by simp [hi])
              omega
            · exact h_adj k hk⟩

/-- Taking the first `x` elements and then `y` elements
from the remainder gives the first `x + y` elements. -/
lemma take_append_take_drop {A : Type*} : (L : List A) → (x y : ℕ) →
    L.take x ++ (L.drop x).take y = L.take (x + y)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: l, x' + 1, y => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, Nat.succ_add]
    rw [take_append_take_drop l x' y]

/-- Elements of a sorted non-empty list of indices are bounded above by the last element. -/
lemma idxs_le_getLast {n : ℕ} (L : List (Fin (n + 1)))
  (hL : L ≠ []) (h_sort : List.Pairwise (· < ·) L) :
    ∀ x ∈ L, x.val ≤ (L.getLast hL).val := fun x hx ↦ by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  have h_last_eq : L.getLast hL = L.get ⟨L.length - 1, by grind⟩ := by grind
  rw [h_last_eq]
  have h_pw := List.pairwise_iff_get.mp h_sort
  if h_eq : i.val = L.length - 1 then
    have h_i_eq : i = ⟨L.length - 1, by omega⟩ := Fin.ext h_eq
    grind
  else
    have h_lt : i.val < L.length - 1 := by omega
    have h_get_lt : L.get i < L.get ⟨L.length - 1, by omega⟩ := h_pw i ⟨L.length - 1, by omega⟩ h_lt
    have h_val_lt : (L.get i).val < (L.get ⟨L.length - 1, by omega⟩).val := h_get_lt
    omega

/-- Elements of a sorted non-empty list of indices are bounded below by the first element. -/
lemma head_le_idxs {n : ℕ} (L : List (Fin (n + 1)))
  (hL : L ≠ []) (h_sort : List.Pairwise (· < ·) L) :
    ∀ x ∈ L, (L.head hL).val ≤ x.val := fun x hx ↦ by
  cases L with
  | nil => contradiction
  | cons a l =>
    simp only [List.head_cons]
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · omega
    · have h_all : ∀ y ∈ l, a < y := List.pairwise_cons.1 h_sort |>.1
      have h_lt := h_all x hx
      omega

/-- A generalized version of `flatten_partitionIndices_take_drop` without boundary conditions. -/
lemma flatten_partitionIndices_take_drop_gen {A : Type*} (u : List A) {n : ℕ}
    (idxs : List (Fin (n + 1))) (h_not_empty : idxs ≠ [])
    (h_sorted : List.Pairwise (· < ·) idxs) :
    (List.map (fun x : Fin (n + 1) × Fin (n + 1) ↦
      List.take (x.2.val - x.1.val) (List.drop x.1.val u)) (partitionIndices idxs)).flatten =
    (List.drop (idxs.head h_not_empty).val u).take
      ((idxs.getLast h_not_empty).val - (idxs.head h_not_empty).val) := by
  induction idxs with
  | nil => contradiction
  | cons i1 idxs' ih =>
    cases idxs' with
    | nil =>
      simp only [partitionIndices, List.map_nil, List.flatten_nil, List.head_cons]
      have h_zero : (i1.val - i1.val) = 0 := by omega
      simp [h_zero]
    | cons i2 idxs'' =>
      have h_sorted_tail : List.Pairwise (· < ·) (i2 :: idxs'') :=
        List.pairwise_cons.1 h_sorted |>.2
      have h_not_empty_tail : i2 :: idxs'' ≠ [] := by simp
      have ih' := ih h_not_empty_tail h_sorted_tail
      have h_i1_lt_i2 : i1 < i2 := List.pairwise_cons.1 h_sorted |>.1 i2 (by simp)
      simp only [partitionIndices, List.map_cons, List.flatten_cons]
      rw [ih']
      have h_head : (List.head (i2 :: idxs'') h_not_empty_tail) = i2 := rfl
      rw [h_head]
      have h_drop : List.drop i2.val u = List.drop (i2.val - i1.val) (List.drop i1.val u) := by
        rw [List.drop_drop]
        congr 1
        omega
      rw [h_drop]
      have h_append := take_append_take_drop (List.drop i1.val u) (i2.val - i1.val)
        ((List.getLast (i2 :: idxs'') h_not_empty_tail).val - i2.val)
      rw [h_append]
      have h_head2 : List.head (i1 :: i2 :: idxs'') h_not_empty = i1 := rfl
      rw [h_head2]
      have h_last : List.getLast (i1 :: i2 :: idxs'') h_not_empty = List.getLast
        (i2 :: idxs'') h_not_empty_tail := rfl
      rw [h_last]
      congr 1
      have h_i2_le_last : i2.val ≤ (List.getLast (i2 :: idxs'') h_not_empty_tail).val := by
        apply idxs_le_getLast (i2 :: idxs'') h_not_empty_tail h_sorted_tail
        exact List.Mem.head _
      omega

/-- Slicing a list at indices given by `partitionIndices`
and concatenating the slices recovers the original list. -/
lemma flatten_partitionIndices_take_drop {A : Type*} (u : List A) {n : ℕ} (h_len : u.length = n)
    (idxs : List (Fin (n + 1))) (h_not_empty : idxs ≠ [])
    (h_sorted : List.Pairwise (· < ·) idxs)
    (h_first : (idxs.head h_not_empty).val = 0)
    (h_last : (idxs.getLast h_not_empty).val = u.length) :
    (List.map (fun x : Fin (n + 1) × Fin (n + 1) => List.take (x.2.val - x.1.val)
    (List.drop x.1.val u)) (partitionIndices idxs)).flatten = u := by
  rw [flatten_partitionIndices_take_drop_gen u idxs h_not_empty h_sorted]
  rw [h_first, h_last]
  simp [h_len]

/-- The split indices are sorted in increasing order. -/
lemma splitIndices_sorted {n h : ℕ} [Nonempty (Fin h)]
  (s : Split (Fin (n + 1)) h) : List.Pairwise (· < ·) (splitIndices s) := by
  unfold splitIndices
  exact List.Pairwise.filter _ (List.sortedLT_finRange _ |>.pairwise)

/-- Restricts a split to a sub-interval `[i, i + len]`. -/
def restrictSplit {n h : ℕ} (s : Split (Fin (n + 1)) h) (i len : ℕ) (h_bound : i + len ≤ n) :
    Split (Fin (len + 1)) h :=
  fun k => s ⟨i + k.val, by omega⟩

/-- Lowers a split whose values are all strictly below `h - 1` into `Fin (h - 1)`. -/
def lowerSplitInterior {n h : ℕ} (s : Split (Fin (n + 1)) h)
    (h_interior : ∀ i : Fin (n + 1), (s i).val < h - 1) : Split (Fin (n + 1)) (h - 1) :=
  fun i => ⟨(s i).val, h_interior i⟩

/-- Auxiliary lemma to prove that the intervals from `partitionIndices` are valid subwords. -/
lemma h_valid_of_mem_partitionIndices {A : Type*} {n h : ℕ} [Nonempty (Fin h)]
    (u : List A) (h_len : u.length = n)
    (s : Split (Fin (n + 1)) h)
    (h_idxs : ¬(splitIndices s).map (·.val) = [0, n])
    (i j : Fin (n + 1))
    (mem : (i, j) ∈ partitionIndices (splitIndices s)) :
    let w := List.take (j.val - i.val) (List.drop i.val u);
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
    rw [← List.length_pos_iff, h_w_len]
    omega
  have h_le : i.val + w.length ≤ u.length := by
    rw [h_w_len]
    omega
  have h_lt : w.length < u.length := by
    rw [h_w_len]
    by_contra h_not_lt
    have h_n : j.val - i.val = n := by omega
    have h_contra := h_props.2.2.2.1 h_n
    contradiction
  exact ⟨h_lt, h_le, h_w_ne⟩

/-- Recursively builds a factorization tree from a word and a split function. -/
def buildFactorizationTree {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ [])
    (s : Split (Fin (u.length + 1)) h) : FactorizationTree A :=
  if _h_len : u.length ≤ 2 then
    if _h_len2 : u.length = 1 then
      FactorizationTree.leaf (u.head hu)
    else
      have h_len2 : u.length = 2 := by have h_pos := List.length_pos_of_ne_nil hu; omega
      let (u1, u2) := (u.head hu, u.getLast (by omega))
      FactorizationTree.binary (FactorizationTree.leaf u1) (FactorizationTree.leaf u2) u 1
  else
    let idxs := splitIndices s
    if h_idxs : idxs.map (·.val) = [0, u.length] then
      if hh : 1 < h then
        have h_nonempty : Nonempty (Fin (h - 1)) := ⟨⟨0, by omega⟩⟩
        let w := (u.drop 1).take (u.length - 2)
        have h_len_w : w.length = u.length - 2 := by
          rw [List.length_take, List.length_drop]
          omega
        have hw : w ≠ [] := by
          intro h
          have h_w_len_zero : w.length = 0 := congrArg List.length h
          omega
        have h_bound : 1 + w.length ≤ u.length := by omega
        let s_w := restrictSplit s 1 w.length h_bound
        have h_interior : ∀ i : Fin (w.length + 1), (s_w i).val < h - 1 := by
          intro i
          let j_val := 1 + i.val
          have h_max_val : (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = h - 1 := by
            have h_eq :
              (Finset.max' Finset.univ Finset.univ_nonempty : Fin h) = ⟨h - 1, by omega⟩ := by
              rw [Finset.max'_eq_iff]
              exact ⟨Finset.mem_univ _, fun b _ ↦ Fin.le_iff_val_le_val.mpr (by grind)⟩
            exact congrArg Fin.val h_eq
          have h_not_max : (s_w i).val ≠ h - 1 := by
            intro h_eq
            have h_s_eq : s ⟨j_val, by omega⟩ = Finset.max' Finset.univ Finset.univ_nonempty := by
              apply Fin.ext
              exact h_max_val ▸ h_eq
            have h_in_idxs : ⟨j_val, by omega⟩ ∈ splitIndices s := by
              simp [splitIndices, h_s_eq]
            have h_map : j_val ∈ (splitIndices s).map (·.val) := List.mem_map_of_mem h_in_idxs
            rw [h_idxs] at h_map
            simp at h_map
            omega
          have h_lt := (s_w i).isLt
          omega
        let t_w := buildFactorizationTree eval w hw (lowerSplitInterior s_w h_interior)
        let last_val := u.getLast (by omega)
        FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
          (FactorizationTree.binary t_w (FactorizationTree.leaf last_val)
            (w ++ [last_val]) (t_w.height + 1)) u (t_w.height + 2)
      else
        FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
          (FactorizationTree.leaf (u.head hu)) u 0
    else
      let children := (partitionIndices idxs).map fun ⟨i, j⟩ =>
        let w := (u.drop i.val).take (j.val - i.val)
        if h_valid : w.length < u.length ∧ i.val + w.length ≤ u.length ∧ w ≠ [] then
          buildFactorizationTree eval w h_valid.2.2 (restrictSplit s i.val w.length h_valid.2.1)
        else
          FactorizationTree.leaf (u.head hu)
      let max_h_children := (children.map FactorizationTree.height).foldl max 0
      if h_empty : idxs = [] then
        have h_interior : ∀ i : Fin (u.length + 1), (s i).val < h - 1 := by
          intro i
          have h_max_val : (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = h - 1 := by
            have h_eq :
              (Finset.max' Finset.univ Finset.univ_nonempty : Fin h) = ⟨h - 1, by grind⟩ := by
              rw [Finset.max'_eq_iff]
              exact ⟨Finset.mem_univ _, fun b _ ↦ Fin.le_iff_val_le_val.mpr (by grind)⟩
            exact congrArg Fin.val h_eq
          have h_not_max : s i ≠ Finset.max' Finset.univ Finset.univ_nonempty := by
            intro heq
            have h_in : i ∈ idxs := by
              dsimp [idxs, splitIndices]
              simp only [List.mem_filter, List.mem_finRange, true_and]
              apply decide_eq_true heq
            rw [h_empty] at h_in
            contradiction
          have h_lt := (s i).isLt
          omega
        have hh : Nonempty (Fin (h - 1)) := by
          if h_eq_one : h = 1 then
            have h_max_zero :
              (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = 0 := by omega
            have h_all_max : ∀ x : Fin (u.length + 1),
              s x = Finset.max' Finset.univ Finset.univ_nonempty := by
              intro x
              have hs := (s x).isLt
              apply Fin.ext
              omega
            have h_first_in : (⟨0, by omega⟩ : Fin (u.length + 1)) ∈ idxs := by
              dsimp [idxs, splitIndices]
              simp only [List.mem_filter, List.mem_finRange, true_and]
              simp [h_all_max _]
            rw [h_empty] at h_first_in
            contradiction
          else
            have h_pos : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
            exact ⟨⟨0, by omega⟩⟩
        have h_lt_h : h - 1 < h := by obtain ⟨⟨_, hlt⟩⟩ := hh; omega
        buildFactorizationTree eval u hu (lowerSplitInterior s h_interior)
      else
        let k := (idxs.getLast h_empty).val
        let k_pre := (idxs.head h_empty).val
        let t_suf : FactorizationTree A :=
          if h_k_full : k = u.length then
            FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
            (FactorizationTree.leaf (u.head hu)) ((u.drop k).take (u.length - k)) 0
          else
            let suf_len := u.length - k
            let char_k := u.get ⟨k, by omega⟩
            let suf_rest_len := suf_len - 1
            if h_rest : suf_rest_len = 0 then
              FactorizationTree.binary (FactorizationTree.leaf char_k)
              (FactorizationTree.leaf char_k) ((u.drop k).take suf_len) 0
            else
              let w_rest := (u.drop (k + 1)).take suf_rest_len
              have h_w_rest_ne : w_rest ≠ [] := by
                intro h_empty_w
                have h_len_zero : w_rest.length = 0 := by simp [h_empty_w]
                have h_len_eq : w_rest.length = suf_rest_len := by
                  dsimp [w_rest, suf_rest_len, suf_len]
                  rw [List.length_take, List.length_drop]
                  omega
                omega
              have h_w_rest_len : w_rest.length < u.length := by
                dsimp [w_rest, suf_rest_len, suf_len]
                rw [List.length_take, List.length_drop]
                omega
              let s_suf := restrictSplit s (k + 1) w_rest.length (by
                dsimp [w_rest, suf_rest_len, suf_len]
                rw [List.length_take, List.length_drop]
                omega)
              have h_interior : ∀ i : Fin (w_rest.length + 1), (s_suf i).val < h - 1 := by
                intro i
                have h_max_val :
                  (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = h - 1 := by
                  have h_eq :
                    (Finset.max' Finset.univ Finset.univ_nonempty : Fin h) = ⟨h - 1, by grind⟩ := by
                    rw [Finset.max'_eq_iff]
                    exact ⟨Finset.mem_univ _, fun b _ ↦ Fin.le_iff_val_le_val.mpr (by grind)⟩
                  exact congrArg Fin.val h_eq
                have h_not_max : s_suf i ≠ Finset.max' Finset.univ Finset.univ_nonempty := by
                  intro heq
                  have h_lt : k + 1 + i.val < u.length + 1 := by
                    have hi : i.val < w_rest.length + 1 := i.isLt
                    have h_len : w_rest.length = suf_rest_len := by
                      dsimp [w_rest, suf_rest_len, suf_len]
                      rw [List.length_take, List.length_drop]
                      omega
                    omega
                  have h_in : (⟨k + 1 + i.val, h_lt⟩ : Fin (u.length + 1)) ∈ idxs := by
                    dsimp [idxs, splitIndices]
                    simp only [List.mem_filter, List.mem_finRange, true_and]
                    apply decide_eq_true
                    have h_eq_s : s ⟨k + 1 + i.val, h_lt⟩ = s_suf i := by
                      dsimp [s_suf, restrictSplit]
                    rw [h_eq_s]
                    exact heq
                  have h_k_last : (⟨k + 1 + i.val, h_lt⟩ : Fin (u.length + 1)).val ≤ k := by
                    apply idxs_le_getLast idxs h_empty (splitIndices_sorted s)
                    exact h_in
                  grind
                have h_lt := (s_suf i).isLt
                omega
              have hh : Nonempty (Fin (h - 1)) := by
                if h_eq_one : h = 1 then
                  have h_max_zero :
                    (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = 0 := by omega
                  have h_all_max : ∀ x :
                    Fin (u.length + 1), s x = Finset.max' Finset.univ Finset.univ_nonempty := by
                    intro x
                    have hs := (s x).isLt
                    apply Fin.ext
                    omega
                  have h_last_in : (⟨u.length, by omega⟩ : Fin (u.length + 1)) ∈ idxs := by
                    dsimp [idxs, splitIndices]
                    simp only [List.mem_filter, List.mem_finRange, true_and]
                    simp [h_all_max _]
                  have h_s := splitIndices_sorted s
                  have h_le : u.length ≤ k := idxs_le_getLast idxs h_empty h_s _ h_last_in
                  omega
                else
                  have h_pos : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
                  exact ⟨⟨0, by omega⟩⟩
              have h_lt_h : h - 1 < h := by obtain ⟨⟨_, hlt⟩⟩ := hh; omega
              let t_suf_rest :=
                buildFactorizationTree eval w_rest h_w_rest_ne (lowerSplitInterior s_suf h_interior)
              let suf_w := (u.drop k).take suf_len
              (FactorizationTree.leaf char_k).binary t_suf_rest
                suf_w (max 1 t_suf_rest.height + 1)
        let t_pre : FactorizationTree A :=
          if h_k_zero : k_pre = 0 then
            FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
              (FactorizationTree.leaf (u.head hu)) (u.take k_pre) 0
          else
            let pre_len := k_pre
            let char_pre := u.get ⟨k_pre - 1, by omega⟩
            let pre_rest_len := pre_len - 1
            if h_rest : pre_rest_len = 0 then
              FactorizationTree.binary (FactorizationTree.leaf char_pre)
                (FactorizationTree.leaf char_pre) (u.take pre_len) 0
            else
              let w_rest := u.take pre_rest_len
              have h_w_rest_ne : w_rest ≠ [] := by
                intro h_empty_w
                have h_len_zero : w_rest.length = 0 := by simp [h_empty_w]
                have h_len_eq : w_rest.length = pre_rest_len := by
                  dsimp [w_rest, pre_rest_len, pre_len]
                  rw [List.length_take]
                  omega
                omega
              have h_w_rest_len : w_rest.length < u.length := by
                dsimp [w_rest, pre_rest_len, pre_len]
                rw [List.length_take]
                omega
              let s_pre := restrictSplit s 0 w_rest.length (by
                dsimp [w_rest, pre_rest_len, pre_len]
                rw [List.length_take]
                omega)
              have h_interior : ∀ i : Fin (w_rest.length + 1), (s_pre i).val < h - 1 := by
                intro i
                have h_max_val :
                  (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = h - 1 := by
                  have h_eq :
                    (Finset.max' Finset.univ Finset.univ_nonempty : Fin h) = ⟨h - 1, by grind⟩ := by
                    rw [Finset.max'_eq_iff]
                    exact ⟨Finset.mem_univ _, fun b _ ↦ Fin.le_iff_val_le_val.mpr (by grind)⟩
                  exact congrArg Fin.val h_eq
                have h_not_max : s_pre i ≠ Finset.max' Finset.univ Finset.univ_nonempty := by
                  intro heq
                  have h_lt : i.val < u.length + 1 := by
                    have hi : i.val < w_rest.length + 1 := i.isLt
                    have h_len : w_rest.length = pre_rest_len := by
                      dsimp [w_rest, pre_rest_len, pre_len]
                      rw [List.length_take]
                      omega
                    omega
                  have h_in : (⟨i.val, h_lt⟩ : Fin (u.length + 1)) ∈ idxs := by
                    dsimp [idxs, splitIndices]
                    simp only [List.mem_filter, List.mem_finRange, true_and]
                    apply decide_eq_true
                    have h_eq_s : s ⟨i.val, h_lt⟩ = s_pre i := by
                      dsimp [s_pre, restrictSplit]
                      congr 1
                      apply Fin.ext
                      grind
                    rw [h_eq_s]
                    exact heq
                  have h_head_le : k_pre ≤ (⟨i.val, h_lt⟩ : Fin (u.length + 1)).val := by
                    apply head_le_idxs idxs h_empty (splitIndices_sorted s)
                    exact h_in
                  grind
                have h_lt := (s_pre i).isLt
                omega
              have hh : Nonempty (Fin (h - 1)) := by
                if h_eq_one : h = 1 then
                  have h_max_zero :
                    (Finset.max' Finset.univ Finset.univ_nonempty : Fin h).val = 0 := by omega
                  have h_all_max : ∀ x :
                    Fin (u.length + 1), s x = Finset.max' Finset.univ Finset.univ_nonempty := by
                    intro x
                    have hs := (s x).isLt
                    apply Fin.ext
                    omega
                  have h_first_in : (⟨0, by omega⟩ : Fin (u.length + 1)) ∈ idxs := by
                    dsimp [idxs, splitIndices]
                    simp only [List.mem_filter, List.mem_finRange, true_and]
                    simp [h_all_max _]
                  have h_s := splitIndices_sorted s
                  have h_le : k_pre ≤ 0 := head_le_idxs idxs h_empty h_s _ h_first_in
                  omega
                else
                  have h_pos : 0 < h := Fin.pos_iff_nonempty.mpr inferInstance
                  exact ⟨⟨0, by omega⟩⟩
              have h_lt_h : h - 1 < h := by obtain ⟨⟨_, hlt⟩⟩ := hh; omega
              let t_pre_rest :=
                buildFactorizationTree eval w_rest h_w_rest_ne (lowerSplitInterior s_pre h_interior)
              let pre_w := u.take pre_len
              t_pre_rest.binary (FactorizationTree.leaf char_pre)
                pre_w (max t_pre_rest.height 1 + 1)
        if h_k_full : k = u.length then
          if h_k_zero : k_pre = 0 then
            match children with
            | [] => FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
                      (FactorizationTree.leaf (u.head hu)) u 0
            | [c] => FactorizationTree.binary c c u (max_h_children + 1)
            | [c1, c2] => FactorizationTree.binary c1 c2 u (max_h_children + 1)
            | c1::c2::c3::rest => FactorizationTree.nary children u (max_h_children + 1)
          else
            if h_k_eq_pre : k_pre = k then
              t_pre
            else
              match children with
              | [] => FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
                        (FactorizationTree.leaf (u.head hu)) u 0
              | [c] => FactorizationTree.binary t_pre c u (max t_pre.height c.height + 1)
              | c1::c2::rest =>
                FactorizationTree.nary (t_pre :: children) u
                  (max t_pre.height max_h_children + 1)
        else
          if h_k_zero : k_pre = 0 then
            if h_k_eq_pre : k_pre = k then
              t_suf
            else
              match children with
              | [] => FactorizationTree.binary (FactorizationTree.leaf (u.head hu))
                        (FactorizationTree.leaf (u.head hu)) u 0
              | [c] => FactorizationTree.binary c t_suf u (max c.height t_suf.height + 1)
              | c1::c2::rest =>
                FactorizationTree.nary (children ++ [t_suf]) u
                  (max max_h_children t_suf.height + 1)
          else
            if h_k_eq_pre : k_pre = k then
              FactorizationTree.binary t_pre t_suf u (max t_pre.height t_suf.height + 1)
            else
              FactorizationTree.nary (t_pre :: children ++ [t_suf]) u
                (max t_pre.height (max max_h_children t_suf.height) + 1)
termination_by (h, u.length)
decreasing_by
  all_goals
    simp_wf
    first
    | exact Prod.Lex.left _ _ (by omega)
    | exact Prod.Lex.right _ (by first | exact h_valid.1 | grind)

/-- The word of a leaf node is the singleton list containing its label. -/
@[simp] lemma word_leaf {A} (a : A) :
  (FactorizationTree.leaf a).word = [a] := rfl
/-- The word of a binary node is the word provided at its construction. -/
@[simp] lemma word_binary {A} (l r : FactorizationTree A) (w : List A) (h : ℕ) :
  (FactorizationTree.binary l r w h).word = w := rfl
/-- The word of an n-ary node is the word provided at its construction. -/
@[simp] lemma word_nary {A} (cs : List (FactorizationTree A)) (w : List A) (h : ℕ) :
  (FactorizationTree.nary cs w h).word = w := rfl

/-- The height of a leaf node is 0. -/
@[simp] lemma height_leaf {A} (a : A) :
  (FactorizationTree.leaf a).height = 0 := rfl

/-- The height of a binary node is the height provided at its construction. -/
@[simp] lemma height_binary {A} (l r : FactorizationTree A) (w : List A) (h : ℕ) :
  (FactorizationTree.binary l r w h).height = h := rfl

/-- The height of an n-ary node is the height provided at its construction. -/
@[simp] lemma height_nary {A} (cs : List (FactorizationTree A)) (w : List A) (h : ℕ) :
  (FactorizationTree.nary cs w h).height = h := rfl

/-- A word of length 1 is equal to the singleton list containing its head. -/
@[simp] lemma word_leaf_eq {A} (u : List A) (hu : u ≠ []) (h : u.length = 1) : [u.head hu] = u := by
  cases u with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil => rfl
    | cons _ _ => simp at h

lemma word_ite {A} (c : Prop) [Decidable c] (t f : FactorizationTree A) :
  (if c then t else f).word = if c then t.word else f.word := by
  split <;> rfl

lemma word_dite {A} (c : Prop) [Decidable c] (t : c → FactorizationTree A)
    (f : ¬c → FactorizationTree A) :
  (dite c t f).word = dite c (fun h => (t h).word) (fun h => (f h).word) := by
  split <;> rfl

lemma match_children_word_eq1 {A : Type*} (children : List (FactorizationTree A)) (u : List A)
    (hu : u ≠ []) (max_h_children : ℕ) :
  (match children with
  | [] => (FactorizationTree.leaf (u.head hu)).binary (FactorizationTree.leaf (u.head hu)) u 0
  | [c] => c.binary c u (max_h_children + 1)
  | [c1, c2] => c1.binary c2 u (max_h_children + 1)
  | _ :: _ :: _ :: _ => FactorizationTree.nary children u (max_h_children + 1)).word = u := by
  match children with
  | [] => rfl
  | [_] => rfl
  | [_, _] => rfl
  | _ :: _ :: _ :: _ => rfl

lemma match_children_word_eq2 {A : Type*} (children : List (FactorizationTree A)) (u : List A)
    (hu : u ≠ []) (max_h_children : ℕ) (t_pre : FactorizationTree A) :
  (match children with
  | [] => (FactorizationTree.leaf (u.head hu)).binary (FactorizationTree.leaf (u.head hu)) u 0
  | [c] => t_pre.binary c u (max t_pre.height c.height + 1)
  | _ :: _ :: _ => FactorizationTree.nary
    (t_pre :: children) u (max t_pre.height max_h_children + 1)).word = u := by
  match children with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

lemma match_children_word_eq3 {A : Type*} (children : List (FactorizationTree A)) (u : List A)
    (hu : u ≠ []) (max_h_children : ℕ) (t_suf : FactorizationTree A) :
  (match children with
  | [] => (FactorizationTree.leaf (u.head hu)).binary (FactorizationTree.leaf (u.head hu)) u 0
  | [c] => c.binary t_suf u (max c.height t_suf.height + 1)
  | _ :: _ :: _ => FactorizationTree.nary
    (children ++ [t_suf]) u (max max_h_children t_suf.height + 1)).word = u := by
  match children with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- The tree built by `buildFactorizationTree` has the original word as its word. -/
theorem buildTree_word_eq {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h) :
    (buildFactorizationTree eval u hu s).word = u := by
  let P := fun (h_val : ℕ) => ∀ [Nonempty (Fin h_val)] (u : List A) (hu : u ≠ [])
    (s' : Split (Fin (u.length + 1)) h_val),
    (buildFactorizationTree eval u hu s').word = u
  have H_P : P h := by
    clear u hu s
    induction h using Nat.strong_induction_on with | h h' ih =>
    intro h_nonempty u hu s'
    have h_pos : 0 < h' := by
      have ⟨⟨_, hlt⟩⟩ := h_nonempty
      omega
    rw [buildFactorizationTree]
    split
    · split
      · exact word_leaf_eq u hu ‹u.length = 1›
      · rfl
    · simp only [word_ite, word_dite, match_children_word_eq1,
        match_children_word_eq2, match_children_word_eq3, dite_eq_ite, ite_self]
      by_cases h_idxs : (splitIndices s').map (fun x : Fin (u.length + 1) => (x:ℕ)) = [0, u.length]
      · simp only [h_idxs, if_true]
      · simp only [h_idxs, if_false]
        by_cases h_empty : splitIndices s' = []
        · simp only [h_empty, dite_true]
          haveI inst : Nonempty (Fin (h' - 1)) := by
            if h_eq_one : h' = 1 then
              have h_max_zero :
                (Finset.max' Finset.univ Finset.univ_nonempty : Fin h').val = 0 := by omega
              have h_all_max : ∀ x : Fin (u.length + 1),
                s' x = Finset.max' Finset.univ Finset.univ_nonempty := by
                intro x
                have hs := (s' x).isLt
                apply Fin.ext
                omega
              have h_first_in : (⟨0, by omega⟩ : Fin (u.length + 1)) ∈ splitIndices s' := by
                dsimp [splitIndices]
                simp only [List.mem_filter, List.mem_finRange, true_and]
                simp [h_all_max _]
              rw [h_empty] at h_first_in
              contradiction
            else
              exact ⟨⟨0, by omega⟩⟩
          exact ih (h' - 1) (by omega) u hu _
        · simp only [h_empty, dite_false]
          split_ifs
          all_goals
            simp_all [FactorizationTree.word]
  exact H_P u hu s

/-- Auxiliary lemma to add 1 to both sides of an inequality with subtraction. -/
lemma plus_one_le {a b : ℕ} (h : a ≤ b - 1) (hb : 0 < b) : a + 1 ≤ b := by omega

/-- The `foldl max` of tree heights is bounded by any uniform upper bound on the children. -/
lemma foldl_max_bound {A : Type*}
    (children : List (FactorizationTree A))
    (bound : ℕ)
    (h_bound : ∀ c ∈ children,
      c.height ≤ bound) :
    (children.map FactorizationTree.height).foldl
      max 0 ≤ bound := by
  have h_fold : ∀ (l : List (FactorizationTree A)) (init : ℕ), init ≤ bound →
      (∀ c ∈ l, c.height ≤ bound) → (l.map FactorizationTree.height).foldl max init ≤ bound := by
    intro l
    induction l with
    | nil =>
      intro init h_init _
      exact h_init
    | cons hd tl ih =>
      intro init h_init h_all
      apply ih
      · have h_hd : hd.height ≤ bound := h_all hd (by simp)
        omega
      · intro c hc
        exact h_all c (by simp [hc])
  exact h_fold children 0 (by omega) h_bound

/-- The height of the tree built by `buildFactorizationTree` is at most `3 * h - 1`. -/
theorem buildTree_height_bound {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S) (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h) :
    (buildFactorizationTree eval u hu s).height ≤ 3 * h - 1 := by
  let P := fun (h_val : ℕ) => ∀ [Nonempty (Fin h_val)] (u : List A) (hu : u ≠ [])
    (s' : Split (Fin (u.length + 1)) h_val),
    (buildFactorizationTree eval u hu s').height ≤ 3 * h_val - 1
  have H_P : P h := by
    induction h using Nat.strong_induction_on with | h h' ih =>
    intro h_nonempty u hu s'
    have h_pos : 0 < h' := by
      have ⟨⟨_, hlt⟩⟩ := h_nonempty
      omega
    rw [buildFactorizationTree]
    sorry
  exact H_P u hu s

/-- Extracts the idempotent from a Ramsey tree whose split indices cover the entire word. -/
lemma extract_idempotent {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (idxs : List (Fin (u.length + 1)))
    (h_idxs : ∀ i ∈ idxs, s i = Finset.max' Finset.univ Finset.univ_nonempty)
    (i0 i1 i2 : Fin (u.length + 1))
    (hi0_mem : i0 ∈ idxs) (hi1_mem : i1 ∈ idxs) (hi2_mem : i2 ∈ idxs)
    (hlt01 : i0 < i1) (hlt12 : i1 < i2) :
    let L := wordLabeling eval hmul u
    let e := L.σ i0 i1
    e * e = e ∧ ∀ j0 j1, j0 ∈ idxs → j1 ∈ idxs → j0 < j1 → L.σ j0 j1 = e := by
  intros L e
  have mk_rel : ∀ a b, a ∈ idxs → b ∈ idxs → a < b → SplitRelation s a b := by
    intro a b ha hb hab
    dsimp [SplitRelation]
    exact ⟨by rw [h_idxs a ha, h_idxs b hb], fun z hz_ge hz_le ↦ by
      have h_s_min : s (min a b) = Finset.max' Finset.univ Finset.univ_nonempty := by
        rw [min_eq_left (le_of_lt hab), h_idxs a ha]
      rw [h_s_min]
      exact Finset.le_max' _ _ (Finset.mem_univ _)⟩
  constructor
  · exact hs_ramsey.left i0 i1 i2 hlt01 hlt12 (mk_rel i0 i1 hi0_mem hi1_mem hlt01)
      (mk_rel i1 i2 hi1_mem hi2_mem hlt12)
  · intros j0 j1 h_j0_mem h_j1_mem hlt_j
    have h_rel_cross : SplitRelation s i0 j0 := by
      dsimp [SplitRelation]
      exact ⟨by rw [h_idxs i0 hi0_mem, h_idxs j0 h_j0_mem], fun z h_i0_le_z h_z_le_j0 ↦ by
        have h_s_min : s (min i0 j0) = Finset.max' Finset.univ Finset.univ_nonempty := by
          obtain h_le | h_le := le_total i0 j0 <;>
            simp only [min_eq_left h_le, min_eq_right h_le, h_idxs i0 hi0_mem, h_idxs j0 h_j0_mem]
        exact h_s_min ▸ Finset.le_max' _ _ (Finset.mem_univ _)⟩
    exact (hs_ramsey.right i0 i1 j0 j1 hlt01 hlt_j (mk_rel i0 i1 hi0_mem hi1_mem hlt01)
      (mk_rel j0 j1 h_j0_mem h_j1_mem hlt_j) h_rel_cross).symm

/-- A chunk of a word equals the corresponding sublist. -/
lemma chunk_eq {A : Type*} {u w : List A} {i : ℕ} (hw : ∃ j, w = (u.drop i).take (j - i))
    (x y : Fin (w.length + 1)) (hxy : x ≤ y) :
    (w.drop x.val).take (y.val - x.val) =
    (u.drop (i + x.val)).take (y.val - x.val) := by
  rcases hw with ⟨j, rfl⟩
  have h_ylt := y.isLt
  have h_len : ((u.drop i).take (j - i)).length = min (j - i) (u.drop i).length := List.length_take
  have h_min : min (y.val - x.val) (j - i - x.val) = y.val - x.val := by omega
  simp only [List.drop_take, List.drop_drop, List.take_take, h_min]

/-- A split relation on a restricted sub-interval lifts
to a split relation on the original domain. -/
lemma shift_split_relation {n h : ℕ} (s : Split (Fin (n + 1)) h)
    {i len : ℕ} (h_bound : i + len ≤ n) (x y : Fin (len + 1))
    (hsr : SplitRelation (restrictSplit s i len h_bound) x y) :
    SplitRelation s ⟨i + x.val, by omega⟩ ⟨i + y.val, by omega⟩ := by
  exact ⟨hsr.1, fun z hz_ge hz_le ↦ by
    have h_rel_le := hsr.2
    rcases le_total x y with hxy | hxy
    · have hixy : (⟨i + x.val, by omega⟩ : Fin (n + 1)) ≤ ⟨i + y.val, by omega⟩ :=
        Fin.le_iff_val_le_val.mpr (by have hxy_val := Fin.le_iff_val_le_val.mp hxy; grind)
      rw [min_eq_left hxy, max_eq_right hxy] at h_rel_le
      rw [min_eq_left hixy] at hz_ge ⊢
      rw [max_eq_right hixy] at hz_le
      have hi_le_z : i ≤ z.val := by
        have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge
        grind
      let zw : Fin (len + 1) := ⟨z.val - i, by
        have hz_le_val := Fin.le_iff_val_le_val.mp hz_le; have hy_lt := y.isLt; simp; grind⟩
      have hx_zw : x ≤ zw := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge; simp; grind)
      have hzw_y : zw ≤ y := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have hz_le_val := Fin.le_iff_val_le_val.mp hz_le; simp; grind)
      have h_res := h_rel_le zw hx_zw hzw_y
      rw [(Fin.ext (by dsimp [zw]; omega) : z = (⟨i + zw.val, by dsimp [zw]; omega⟩ : Fin (n + 1)))]
      exact h_res
    · have hyx : y ≤ x := by omega
      have hiyx : (⟨i + y.val, by omega⟩ : Fin (n + 1)) ≤ ⟨i + x.val, by omega⟩ :=
        Fin.le_iff_val_le_val.mpr (by have hxy_val := Fin.le_iff_val_le_val.mp hxy; grind)
      rw [min_eq_right hxy, max_eq_left hxy] at h_rel_le
      rw [min_eq_right hiyx] at hz_ge ⊢
      rw [max_eq_left hiyx] at hz_le
      have hi_le_z : i ≤ z.val := by
        have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge
        grind
      let zw : Fin (len + 1) := ⟨z.val - i, by
        have hz_le_val := Fin.le_iff_val_le_val.mp hz_le; have hx_lt := x.isLt; simp; grind⟩
      have hy_zw : y ≤ zw := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have hz_ge_val := Fin.le_iff_val_le_val.mp hz_ge; simp; grind)
      have hzw_x : zw ≤ x := Fin.le_iff_val_le_val.mpr (by
        dsimp [zw]; have hz_le_val := Fin.le_iff_val_le_val.mp hz_le; simp; grind)
      have h_res := h_rel_le zw hy_zw hzw_x
      rw [(Fin.ext (by dsimp [zw]; omega) : z = (⟨i + zw.val, by dsimp [zw]; omega⟩ : Fin (n + 1)))]
      exact h_res⟩

/-- A restricted split preserves the Ramsey property on the corresponding sub-word. -/
lemma restrictSplit_ramsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (i : ℕ) (w : List A) (h_bound : i + w.length ≤ u.length)
    (hw : ∃ j, w = (u.drop i).take (j - i) := by exact ⟨_, rfl⟩) :
    IsRamsey (wordLabeling eval hmul w) (restrictSplit s i w.length h_bound) := by
  constructor
  · intros x y z hxy hyz hsr_xy hsr_yz
    have hx_b : i + x.val < u.length + 1 := by omega
    have hy_b : i + y.val < u.length + 1 := by omega
    have hz_b : i + z.val < u.length + 1 := by omega
    have hxy_shift : (⟨i + x.val, hx_b⟩ : Fin (u.length + 1)) < ⟨i + y.val, hy_b⟩ := by
      simp only [Fin.mk_lt_mk]
      omega
    have hyz_shift : (⟨i + y.val, hy_b⟩ : Fin (u.length + 1)) < ⟨i + z.val, hz_b⟩ := by
      simp only [Fin.mk_lt_mk]
      omega
    have h_eval := hs_ramsey.1 _ _ _ hxy_shift hyz_shift
      (shift_split_relation s h_bound x y hsr_xy) (shift_split_relation s h_bound y z hsr_yz)
    dsimp [wordLabeling] at h_eval ⊢
    rw [chunk_eq hw x y (le_of_lt hxy)]
    have h_sub : (i + y.val) - (i + x.val) = y.val - x.val := by omega
    have h_eval_eq : (u.drop (i + x.val)).take (i + y.val - (i + x.val)) =
                     (u.drop (i + x.val)).take (y.val - x.val) := by rw [h_sub]
    rw [h_eval_eq] at h_eval
    exact h_eval
  · intros x y p q hxy hpq h_rel_xy h_rel_pq h_rel_xp
    have hx_b : i + x.val < u.length + 1 := by omega
    have hy_b : i + y.val < u.length + 1 := by omega
    have hp_b : i + p.val < u.length + 1 := by omega
    have hq_b : i + q.val < u.length + 1 := by omega
    have hxy_shift : (⟨i + x.val, hx_b⟩ : Fin (u.length + 1)) < ⟨i + y.val, hy_b⟩ := by
      simp
      omega
    have hpq_shift : (⟨i + p.val, hp_b⟩ : Fin (u.length + 1)) < ⟨i + q.val, hq_b⟩ := by
      simp
      omega
    have h_eval := hs_ramsey.2 _ _ _ _ hxy_shift hpq_shift
      (shift_split_relation s h_bound x y h_rel_xy)
      (shift_split_relation s h_bound p q h_rel_pq)
      (shift_split_relation s h_bound x p h_rel_xp)
    dsimp [wordLabeling] at h_eval ⊢
    simp only [chunk_eq hw x y (le_of_lt hxy), chunk_eq hw p q (le_of_lt hpq)]
    have h_sub1 : (i + y.val) - (i + x.val) = y.val - x.val := by omega
    have h_sub2 : (i + q.val) - (i + p.val) = q.val - p.val := by omega
    have h_eval_eq1 : (u.drop (i + x.val)).take (i + y.val - (i + x.val)) =
                      (u.drop (i + x.val)).take (y.val - x.val) := by rw [h_sub1]
    have h_eval_eq2 : (u.drop (i + p.val)).take (i + q.val - (i + p.val)) =
                      (u.drop (i + p.val)).take (q.val - p.val) := by rw [h_sub2]
    simp only [h_eval_eq1, h_eval_eq2] at h_eval
    exact h_eval

/-- Lowering the interior of a split preserves the Ramsey property. -/
lemma lowerSplitInterior_ramsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    [Nonempty (Fin (h - 1))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) (_ : 1 < h)
    (h_interior : ∀ i : Fin (u.length + 1), (s i).val < h - 1) :
    IsRamsey (wordLabeling eval hmul u) (lowerSplitInterior s h_interior) := by
  have h_rel_eq : ∀ x y,
      SplitRelation (lowerSplitInterior s h_interior) x y ↔ SplitRelation s x y := by
    intro x y
    dsimp [SplitRelation, lowerSplitInterior]
    constructor
    · rintro ⟨h_s_eq, h_s_le⟩
      have h_s_eq_val := congrArg Fin.val h_s_eq
      exact ⟨Fin.ext h_s_eq_val, fun z hx_le_z hz_le_y ↦
        Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp (h_s_le z hx_le_z hz_le_y))⟩
    · rintro ⟨h_s_eq, h_s_le⟩
      have h_s_eq_val := congrArg Fin.val h_s_eq
      exact ⟨Fin.ext h_s_eq_val, fun z hx_le_z hz_le_y ↦
        Fin.le_iff_val_le_val.mpr (Fin.le_iff_val_le_val.mp (h_s_le z hx_le_z hz_le_y))⟩
  exact ⟨fun x y z hxy hyz h_rel_xy h_rel_yz => hs_ramsey.1 x y z hxy hyz
           ((h_rel_eq x y).mp h_rel_xy) ((h_rel_eq y z).mp h_rel_yz),
         fun x y p q hxy hpq h_rel_xy h_rel_pq h_rel_xp =>
           hs_ramsey.2 x y p q hxy hpq ((h_rel_eq x y).mp h_rel_xy)
             ((h_rel_eq p q).mp h_rel_pq) ((h_rel_eq x p).mp h_rel_xp)⟩

/-- Children of an n-ary node in a Ramsey tree all evaluate to the same idempotent. -/
lemma nary_children_ramsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s)
    (children : List (FactorizationTree A))
    (h_children : ((partitionIndices (splitIndices s)).map fun ⟨i, j⟩ =>
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
    ∃ (e : S), e * e = e ∧ ∀ c ∈ children, eval (FactorizationTree.word c) = e := by
  generalize h_idx_eq : splitIndices s = idxs at h_children ⊢
  have h_idxs : ∀ i ∈ idxs, s i = Finset.max' Finset.univ Finset.univ_nonempty := by
    intro i hi
    rw [← h_idx_eq] at hi
    unfold splitIndices at hi
    rw [List.mem_filter] at hi
    exact of_decide_eq_true hi.right
  have h_len_idxs : idxs.length ≥ 4 := by
    have h_map_len : (partitionIndices idxs).length = children.length := by
      have h_map_len2 : (((partitionIndices idxs).map _).length) = children.length :=
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
      exact List.Pairwise.filter _ (List.sortedLT_finRange (u.length + 1) |>.pairwise)
    have hlt01 : i0 < i1 := List.pairwise_cons.1 h_sorted |>.1 i1 (by simp)
    have hlt12 : i1 < i2 :=
      List.pairwise_cons.1 (List.pairwise_cons.1 h_sorted |>.2) |>.1 i2 (by simp)
    have ⟨hi0_mem, hi1_mem, hi2_mem⟩ : i0 ∈ i0 :: i1 :: i2 :: rest
      ∧ i1 ∈ i0 :: i1 :: i2 :: rest ∧ i2 ∈ i0 :: i1 :: i2 :: rest := by simp
    obtain ⟨h_ee, h_all_pairs⟩ :=
      extract_idempotent eval hmul u s hs_ramsey (i0 :: i1 :: i2 :: rest) h_idxs i0 i1 i2
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
        obtain ⟨h_j0_mem, h_j1_mem, h_j_lt, _, _⟩ := partitionIndices_props h_sorted hj_mem
        rw [buildTree_word_eq]
        have h_σ := h_all_pairs j0 j1 h_j0_mem h_j1_mem h_j_lt
        dsimp [wordLabeling, MultiplicativeLabeling.σ] at h_σ ⊢
        exact h_σ
      · rename_i h_valid_false
        obtain ⟨_, _, _, hj_len, _⟩ := partitionIndices_props h_sorted hj_mem
        have h_len : j1.val - j0.val < u.length := by
          by_contra h_ge
          push Not at h_ge
          have h_eq_u : j1.val - j0.val = u.length := by omega
          exact h_not_idxs (h_idx_eq.symm ▸ hj_len h_eq_u)
        have h_valid_true : ((u.drop j0.val).take (j1.val - j0.val)).length < u.length ∧
            j0.val + ((u.drop j0.val).take (j1.val - j0.val)).length ≤ u.length ∧
            ((u.drop j0.val).take (j1.val - j0.val)) ≠ [] := by
          have h_take_len : ((u.drop j0.val).take (j1.val - j0.val)).length = j1.val - j0.val := by
            rw [List.length_take, List.length_drop]
            exact min_eq_left (by omega)
          exact ⟨by omega, by omega, by
            rw [← List.length_pos_iff, h_take_len]
            omega⟩
        nomatch h_valid_false h_valid_true

lemma list_drop_length_sub_one {A} (u : List A) (hu : u ≠ []) :
  u.drop (u.length - 1) = [u.getLast hu] := by
  induction u with
  | nil => contradiction
  | cons head tail ih =>
    match tail with
    | [] => rfl
    | head2 :: tail2 =>
      have h_tail_ne : head2 :: tail2 ≠ [] := by simp
      exact ih h_tail_ne

lemma word_decomp {A} (u : List A) (hu : u ≠ []) (h_len : 2 < u.length) :
  u = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++ [u.getLast hu] := by
  have h3 : u.drop 1 = (u.drop 1).take (u.length - 2) ++ (u.drop 1).drop (u.length - 2) :=
    (List.take_append_drop (u.length - 2) (u.drop 1)).symm
  have h4 : (u.drop 1).drop (u.length - 2) = [u.getLast hu] := by
    rw [List.drop_drop]
    have hd2 : 1 + (u.length - 2) = u.length - 1 := by omega
    rw [hd2]
    exact list_drop_length_sub_one u hu
  calc u
    _ = u.take 1 ++ u.drop 1 := (List.take_append_drop 1 u).symm
    _ = [u.head hu] ++ u.drop 1 := by
      have h2 : u.take 1 = [u.head hu] := by
        match u with
        | [] => contradiction
        | a :: tl => rfl
      rw [h2]
    _ = [u.head hu] ++ ((u.drop 1).take (u.length - 2) ++ (u.drop 1).drop (u.length - 2)) := by
      exact congrArg (fun x => [u.head hu] ++ x) h3
    _ = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++ (u.drop 1).drop (u.length - 2) := by
      rw [List.append_assoc]
    _ = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++ [u.getLast hu] := by rw [h4]

/-- The tree built by `buildFactorizationTree` satisfies the Ramsey property. -/
theorem buildTree_isRamsey {A S : Type*} [Semigroup S] {h : ℕ} [Nonempty (Fin h)]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    IsRamseyTree eval (buildFactorizationTree eval u hu s) := by
  let P := fun (h_val : ℕ) => ∀ [Nonempty (Fin h_val)] (u : List A)
    (hu : u ≠ []) (s' : Split (Fin (u.length + 1)) h_val),
    IsRamsey (wordLabeling eval hmul u) s' →
    IsRamseyTree eval (buildFactorizationTree eval u hu s')
  have H_P : P h := by
    clear u hu s hs_ramsey
    induction h using Nat.strong_induction_on with | h h' ih =>
    intro h_nonempty u hu s' hs_ramsey'
    rw [buildFactorizationTree]
    split
    · -- u.length <= 2
      split
      · -- length = 1
        exact IsRamseyTree.leaf _
      · -- length = 2
        rename_i h_len _h_len2
        have h_len2 : u.length = 2 := by have h_pos := List.length_pos_of_ne_nil hu; omega
        apply IsRamseyTree.binary
        · exact IsRamseyTree.leaf _
        · exact IsRamseyTree.leaf _
        · -- word equality: u = [u.head hu] ++ [u.getLast (by omega)]
          have h_word : u = [u.head hu] ++ [u.getLast (by omega)] := by
            rcases u with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
            · contradiction
            · contradiction
            · rfl
            · simp at h_len2
          exact h_word
        · exact Nat.le_refl 1
        · exact Nat.le_refl 1
    · -- u.length > 2
      rename_i h_len
      by_cases h_idxs : (splitIndices s').map (fun x : Fin (u.length + 1) => (x:ℕ)) = [0, u.length]
      · simp only [h_idxs, dite_true]
        split_ifs with hh
        · -- Sub-case: 1 < h' → binary of head and (binary t_w (leaf last))
          have h_nonempty_1 : Nonempty (Fin (h' - 1)) := ⟨⟨0, by omega⟩⟩
          set w := (u.drop 1).take (u.length - 2) with h_w_def
          have h_len_w : w.length = u.length - 2 := by
            rw [List.length_take, List.length_drop]; omega
          have hw : w ≠ [] := by
            intro heq
            have hlen : w.length = 0 := by rw [heq, List.length_nil]
            omega
          have h_bound : 1 + w.length ≤ u.length := by omega
          set s_w := restrictSplit s' 1 w.length h_bound
          have h_interior : ∀ i : Fin (w.length + 1), (s_w i).val < h' - 1 := by
            intro i
            let j_val := 1 + i.val
            have h_max_val :
              (Finset.max' Finset.univ Finset.univ_nonempty : Fin h').val = h' - 1 := by
              have h_eq :
                (Finset.max' Finset.univ Finset.univ_nonempty : Fin h') = ⟨h' - 1, by grind⟩ := by
                rw [Finset.max'_eq_iff]
                exact ⟨Finset.mem_univ _, fun y _ => Fin.le_iff_val_le_val.mpr (by grind)⟩
              exact congrArg Fin.val h_eq
            have h_not_max : (s_w i).val ≠ h' - 1 := by
              intro h_eq
              have h_s_eq :
                s' ⟨j_val, by omega⟩ = Finset.max' Finset.univ Finset.univ_nonempty := by
                apply Fin.ext; exact h_max_val ▸ h_eq
              have h_in_idxs : ⟨j_val, by omega⟩ ∈ splitIndices s' := by
                simp [splitIndices, h_s_eq]
              have h_map : j_val ∈ (splitIndices s').map (·.val) :=
                List.mem_map_of_mem h_in_idxs
              rw [h_idxs] at h_map; simp at h_map; omega
            have h_lt := (s_w i).isLt; omega
          -- t_w is the recursive subtree
          set t_w := buildFactorizationTree eval w hw (lowerSplitInterior s_w h_interior)
          set last_val := u.getLast (by omega : u ≠ [])
          -- Prove IsRamseyTree for t_w by induction hypothesis
          have h_ramsey_w : IsRamsey (wordLabeling eval hmul w)
            (lowerSplitInterior s_w h_interior) :=
            lowerSplitInterior_ramsey eval hmul w s_w
              (restrictSplit_ramsey eval hmul u s' hs_ramsey' 1 w h_bound) hh h_interior
          have ih_t_w : IsRamseyTree eval t_w :=
            ih (h' - 1) (by omega) w hw (lowerSplitInterior s_w h_interior) h_ramsey_w
          -- Apply binary constructor for the outer node
          apply IsRamseyTree.binary
          · exact IsRamseyTree.leaf _
          · -- Apply binary constructor for the inner node (t_w, leaf last_val)
            apply IsRamseyTree.binary
            · exact ih_t_w
            · exact IsRamseyTree.leaf _
            · -- word: w ++ [last_val] = t_w.word ++ (leaf last_val).word
              change w ++ [last_val] = t_w.word ++ [last_val]
              have h_w_eq : t_w.word = w :=
                buildTree_word_eq eval w hw (lowerSplitInterior s_w h_interior)
              rw [h_w_eq]
            · -- t_w.height + 1 ≤ t_w.height + 1
              exact Nat.le_refl _
            · -- 0 + 1 ≤ t_w.height + 1
              exact Nat.one_le_iff_ne_zero.mpr (by simp)
          · -- word: u = [u.head hu] ++ (w ++ [last_val])
            have h_outer_word : u = [u.head hu] ++ (w ++ [last_val]) := by
              have hw_def' : w = (u.drop 1).take (u.length - 2) := h_w_def
              have hu_decomp := word_decomp u hu (by omega)
              rw [hw_def']
              exact hu_decomp
            exact h_outer_word
          · -- (leaf (u.head hu)).height + 1 = 0 + 1 ≤ t_w.height + 2
            have : (FactorizationTree.leaf (u.head hu)).height = 0 := rfl
            omega
          · -- (binary t_w (leaf last_val) ...).height + 1 = t_w.height + 2
            have : (FactorizationTree.binary t_w (FactorizationTree.leaf last_val)
              (w ++ [last_val]) (t_w.height + 1)).height = t_w.height + 1 := rfl
            grind
        · exfalso
          have h_h1 : h' = 1 := by grind
          have h_all_max : ∀ x :
            Fin (u.length + 1), s' x = Finset.max' Finset.univ Finset.univ_nonempty := by
            intro x
            have hs := (s' x).isLt
            apply Fin.ext
            omega
          have h_all_in : ∀ i : Fin (u.length + 1), i ∈ splitIndices s' := by
            intro i
            simp [splitIndices, h_all_max i]
          have h_map_len : ((splitIndices s').map (·.val)).length = u.length + 1 := by
            simp only [splitIndices, List.length_map]
            have h_filter : (List.finRange (u.length + 1)).filter
              (fun i => decide
              (s' i = Finset.max' Finset.univ Finset.univ_nonempty)) = List.finRange
              (u.length + 1) := by
              apply List.filter_eq_self.mpr
              intro a _
              simp [h_all_max a]
            rw [h_filter, List.length_finRange]
          have h_len_eq : ((splitIndices s').map (·.val)).length = [0, u.length].length := by
            rw [h_idxs]
          rw [h_map_len] at h_len_eq
          simp at h_len_eq
          omega
      · simp only [h_idxs, dite_false]
        by_cases h_empty : splitIndices s' = []
        · simp only [h_empty, dite_true]
          haveI inst : Nonempty (Fin (h' - 1)) := by
            by_contra h_not_ne
            simp only [not_nonempty_iff] at h_not_ne
            have h_h1 : h' = 1 := by
              have : ¬ (h' - 1 > 0) := by
                intro h_gt
                have h_fin : Fin (h' - 1) := ⟨0, h_gt⟩
                exact IsEmpty.false h_fin
              grind
            have h_all_max : ∀ x :
              Fin (u.length + 1), s' x = Finset.max' Finset.univ Finset.univ_nonempty := by
              intro x; apply Fin.ext
              have := (s' x).isLt; omega
            have h_first_in : (⟨0, by omega⟩ : Fin (u.length + 1)) ∈ splitIndices s' := by
              simp [splitIndices, h_all_max _]
            rw [h_empty] at h_first_in
            contradiction
          have h_interior : ∀ i : Fin (u.length + 1), (s' i).val < h' - 1 := by
            intro i
            have h_max_val :
              (Finset.max' Finset.univ Finset.univ_nonempty : Fin h').val = h' - 1 := by
              have h_eq :
                (Finset.max' Finset.univ Finset.univ_nonempty : Fin h') = ⟨h' - 1, by grind⟩ := by
                rw [Finset.max'_eq_iff]
                exact ⟨Finset.mem_univ _, fun y _ => Fin.le_iff_val_le_val.mpr (by grind)⟩
              exact congrArg Fin.val h_eq
            have h_not_max : s' i ≠ Finset.max' Finset.univ Finset.univ_nonempty := by
              intro heq
              have h_in : i ∈ splitIndices s' := by simp [splitIndices, heq]
              rw [h_empty] at h_in; contradiction
            have h_lt := (s' i).isLt; omega
          have h_1 : 1 < h' := by
            rcases inst with ⟨⟨_, hlt⟩⟩; omega
          have h_ramsey_lower :
            IsRamsey (wordLabeling eval hmul u) (lowerSplitInterior s' h_interior) :=
            lowerSplitInterior_ramsey eval hmul u s' hs_ramsey' h_1 h_interior
          exact ih (h' - 1) (by omega) u hu (lowerSplitInterior s' h_interior) h_ramsey_lower
        · -- Sub-case: n-ary split (splitIndices s' ≠ [0, u.length] and ≠ [])
          -- This branch involves destructing the output of buildFactorizationTree
          exact sorry
  exact H_P u hu s hs_ramsey

/-- Given a Ramsey split, one can construct a factorization tree with bounded height. -/
theorem exists_factorizationTree_of_split {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) {h : ℕ} [Nonempty (Fin h)]
    (s : Split (Fin (u.length + 1)) h)
    (hs_ramsey : IsRamsey (wordLabeling eval hmul u) s) :
    ∃ (t : FactorizationTree A), t.word = u ∧
      t.height ≤ 3 * h - 1 ∧ IsRamseyTree eval t := by
  use buildFactorizationTree eval u hu s
  exact ⟨buildTree_word_eq eval u hu s,
         buildTree_height_bound eval u hu s,
         buildTree_isRamsey eval hmul u hu s hs_ramsey⟩

/-- **Simon's Factorization Forest Theorem:**
Every word over a finite semigroup admits a
factorization tree of height at most `3 * nS S`. -/
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
