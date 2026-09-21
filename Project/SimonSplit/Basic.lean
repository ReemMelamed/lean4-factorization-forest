/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Max
import Project.GreensRelations.Order

/-!
# Simon's Split Theorem — Basic Definitions

Core structures and definitions for Simon's Split Theorem, including multiplicative
labelings, splits, Ramsey condition, and Green's relation invariants.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

section SplitDefinitions

variable {S α : Type*} [Semigroup S] [LinearOrder α]

variable {h : ℕ}

/-- A multiplicative labeling over a linearly ordered type `α` into a semigroup
`S`, satisfying the property that `σ x y * σ y z = σ x z` for all `x < y < z`.
This models the evaluation of subwords in a factorization. -/
structure MultiplicativeLabeling (S α : Type*) [Semigroup S] [LinearOrder α] where
  /-- The labeling function, mapping a pair of indices to a semigroup element. -/
  σ : α → α → S
  /-- Multiplicativity: adjacent subwords multiply together correctly. -/
  prop : ∀ x y z : α, x < y → y < z → σ x y * σ y z = σ x z

/-- A split is a function assigning each element of `α` a bounded integer rank
in `Fin h`. The rank encodes the "level" at which an element participates in the
factorization forest construction. -/
abbrev Split (α : Type*) (h : ℕ) := α → Fin h

/-- `SplitRelation s x y` holds when `x` and `y` have the same rank under `s`,
and every element `z` between them (in the linear order) has a rank at most
equal to that of the minimum of `x` and `y`. -/
abbrev SplitRelation (s : Split α h) (x y : α) : Prop :=
  s x = s y ∧ ∀ z, min x y ≤ z → z ≤ max x y → s z ≤ s (min x y)

/-- A split function is normalized if the minimal element of `α` receives the
maximal possible rank `Finset.max' Finset.univ`. This normalization ensures
the split is compatible with the inductive structure of the proof. -/
abbrev IsNormalized [Fintype α] [Nonempty α] [Nonempty (Fin h)]
    (s : Split α h) : Prop :=
  let min_α := Finset.min' Finset.univ Finset.univ_nonempty
  s min_α = Finset.max' Finset.univ Finset.univ_nonempty

/-- `IsRamsey L s` holds if adjacent split-related points evaluate to idempotents and
cross-related points evaluate uniformly. -/
abbrev IsRamsey (L : MultiplicativeLabeling S α) (s : Split α h) : Prop :=
  (∀ x y z : α, x < y → y < z → SplitRelation s x y → SplitRelation s y z →
    L.σ x y * L.σ x y = L.σ x y) ∧
  (∀ x y u v : α, x < y → u < v →
    SplitRelation s x y → SplitRelation s u v → SplitRelation s x u →
    L.σ x y = L.σ u v)

end SplitDefinitions

section WordDefinitions

/-- Multiplicative labeling mapping `(i, j)` to `eval(u[i..j])`. -/
abbrev wordLabeling {A S : Type*} [Semigroup S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) : MultiplicativeLabeling S (Fin (u.length + 1)) where
  σ := fun i j => eval ((u.drop i.val).take (j.val - i.val))
  prop := by
    intros x y z hxy hyz
    let u_xy := (u.drop x.val).take (y.val - x.val)
    let u_yz := (u.drop y.val).take (z.val - y.val)
    let u_xz := (u.drop x.val).take (z.val - x.val)
    have not_empty_xy_yz : u_xy ≠ [] ∧ u_yz ≠ [] := by
      simp [u_xy, u_yz]
      omega
    have concat_xy_yz_eq_xz : u_xy ++ u_yz = u_xz := by
      have index_diff_eq : z.val - x.val = (y.val - x.val) + (z.val - y.val) := by
        omega
      have drop_eq_nested_drop :
          u.drop y.val = (u.drop x.val).drop (y.val - x.val) := by
        simp
        grind
      grind
    grind

end WordDefinitions

section nD

variable {S : Type*} [Semigroup S] [Fintype S]

open Classical in
/-- Number of elements in `D` in the `H`-class of some idempotent, or 1 if non-regular. -/
noncomputable abbrev nD (D : Set S) : ℕ :=
  if IsRegularDClass D then
    (Finset.univ.filter (fun x ↦
      x ∈ D ∧ ∃ e ∈ D, e * e = e ∧ IsGreenH x e
    )).card
  else
    1

open Classical in
/-- The value `nD D` is strictly positive for any Green's `D`-class `D`. -/
theorem nD_pos (D : Set S) (hD : ∃ x, D = IsGreenD.eqvClass x) : 0 < nD D := by
  dsimp [nD]
  split_ifs with hReg
  · obtain ⟨e, heD, he_idem⟩ :=
        (isRegularDClass_iff_exists_idempotent D hD).mp hReg
    exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, heD, e, heD, he_idem, IsGreenH.refl _⟩⟩
  · decide

end nD

section LabelingProperties

variable {S : Type*} [Semigroup S]

/-- The set of elements of `S` whose Green's `J`-class is at least as large as
that of `a`, i.e., `b` such that `a ≤_J b`. Used to bound the image of a
multiplicative labeling during the induction in Simon's theorem. -/
abbrev jUp (a : S) : Set S := { b | GreenJClass.mk a ≤ GreenJClass.mk b }

/-- States that all strictly ordered pairs `(x, y)` under the labeling `σ`
map into the set `U`. This is the hypothesis that the labeling takes values
in the relevant J-upward closure. -/
abbrev labelingIn {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (U : Set S) : Prop :=
  ∀ x y : α, x < y → σ.σ x y ∈ U

/-- Factors are J-greater than or equal to the product containing them. -/
lemma labeling_factor_le_J {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (u v w x : α)
    (huv : u ≤ v) (hvw : v < w) (hwx : w ≤ x) :
    GreenJClass.mk (σ.σ u x) ≤ GreenJClass.mk (σ.σ v w) := by
  rcases huv.eq_or_lt with rfl | h_uv
  · rcases hwx.eq_or_lt with rfl | h_wx
    · exact le_rfl
    · exact (σ.prop u w x hvw h_wx).symm ▸
        (IsGreenJRel.mul_right (σ.σ w x) rfl : GreenJClass.mk _ ≤ _)
  · rcases hwx.eq_or_lt with rfl | h_wx
    · exact (σ.prop u v w h_uv hvw).symm ▸
        (IsGreenJRel.mul_left (σ.σ u v) rfl : GreenJClass.mk _ ≤ _)
    · exact (σ.prop u v x h_uv (hvw.trans h_wx)).symm ▸
          (σ.prop v w x hvw h_wx).symm ▸
          le_trans
            (IsGreenJRel.mul_left (σ.σ u v) rfl : GreenJClass.mk _ ≤ _)
            (IsGreenJRel.mul_right (σ.σ w x) rfl : GreenJClass.mk _ ≤ _)

variable [Finite S]

/-- If a prefix product is `D`-related to `a`, the extended product is also `D`-related to `a`. -/
lemma isGreenD_of_prefix (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (h_img : labelingIn σ (jUp a))
    (u v w : α) (huv : u < v) (hvw : v ≤ w) (hD : IsGreenD (σ.σ u v) a) :
    IsGreenD (σ.σ u w) a := by
  rcases hvw.eq_or_lt with rfl | hvw_lt
  · exact hD
  · exact isGreenD_of_isGreenJ (GreenJClass.mk_eq_mk_iff.mp (le_antisymm
      (GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD hD) ▸
        labeling_factor_le_J σ u u v w le_rfl huv hvw)
      (h_img u w (huv.trans hvw_lt))))

end LabelingProperties

section GeneralUtility

/-- Taking the first `x` elements and then `y` elements from the remainder
gives the same result as taking the first `x + y` elements. -/
lemma take_append_take_drop {A : Type*} : (L : List A) → (x y : ℕ) →
    L.take x ++ (L.drop x).take y = L.take (x + y)
  | [], _, _ => by simp
  | _ :: _, 0, _ => by simp
  | _ :: l, x' + 1, y => by
    simp only [List.take_succ_cons, List.drop_succ_cons,
      List.cons_append, Nat.succ_add]
    rw [take_append_take_drop l x' y]

/-- In a sorted non-empty list, every element is at most the last element. -/
lemma idxs_le_getLast {n : ℕ} (L : List (Fin (n + 1)))
    (hL : L ≠ []) (h_sort : List.Pairwise (· < ·) L) :
    ∀ x ∈ L, x.val ≤ (L.getLast hL).val := fun x hx ↦ by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hx
  have h_last_eq : L.getLast hL = L.get ⟨L.length - 1, by grind⟩ := by
    grind
  rw [h_last_eq]
  have h_pw := List.pairwise_iff_get.mp h_sort
  if h_eq : i.val = L.length - 1 then
    have h_i_eq : i = ⟨L.length - 1, by omega⟩ := Fin.ext h_eq
    grind
  else
    have h_lt : i.val < L.length - 1 := by omega
    have h_get_lt : L.get i < L.get ⟨L.length - 1, by omega⟩ :=
      h_pw i ⟨L.length - 1, by omega⟩ h_lt
    have h_val_lt : (L.get i).val <
        (L.get ⟨L.length - 1, by omega⟩).val := h_get_lt
    omega

/-- In a sorted non-empty list, the head is at most every element. -/
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

/-- Helper: `u.drop (u.length - 1) = [u.getLast hu]`. -/
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

/-- Decomposition of a word of length > 2 into head + middle + last. -/
lemma word_decomp {A} (u : List A) (hu : u ≠ []) (h_len : 2 < u.length) :
    u = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++
    [u.getLast hu] := by
  have h3 : u.drop 1 =
      (u.drop 1).take (u.length - 2) ++ (u.drop 1).drop (u.length - 2) :=
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
    _ = [u.head hu] ++ ((u.drop 1).take (u.length - 2) ++
          (u.drop 1).drop (u.length - 2)) := by
        exact congrArg (fun x => [u.head hu] ++ x) h3
    _ = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++
          (u.drop 1).drop (u.length - 2) := by rw [List.append_assoc]
    _ = [u.head hu] ++ (u.drop 1).take (u.length - 2) ++
          [u.getLast hu] := by rw [h4]

/-- A sub-word extracted as `(u.drop i).take (j - i)` has the same evaluation
as the corresponding sublist of `u`. -/
lemma chunk_eq {A : Type*} {u w : List A} {i : ℕ}
    (hw : ∃ j, w = (u.drop i).take (j - i))
    (x y : Fin (w.length + 1)) (hxy : x ≤ y) :
    (w.drop x.val).take (y.val - x.val) =
    (u.drop (i + x.val)).take (y.val - x.val) := by
  rcases hw with ⟨j, rfl⟩
  have h_ylt := y.isLt
  have h_len : ((u.drop i).take (j - i)).length =
      min (j - i) (u.drop i).length := List.length_take
  have h_min : min (y.val - x.val) (j - i - x.val) = y.val - x.val := by
    omega
  simp only [List.drop_take, List.drop_drop, List.take_take, h_min]

/-- If every element of a list of natural numbers is ≤ k and the accumulator
is ≤ k, then `foldl max acc l ≤ k`. -/
lemma foldl_max_le (l : List ℕ) (acc k : ℕ) (h_acc : acc ≤ k)
    (h_le : ∀ x ∈ l, x ≤ k) :
    List.foldl max acc l ≤ k := by
  induction l generalizing acc with
  | nil => exact h_acc
  | cons x xs ih =>
    apply ih
    · exact max_le h_acc (h_le x List.mem_cons_self)
    · intro y hy
      exact h_le y (List.mem_cons_of_mem x hy)

/-- `foldl max` is monotone in the initial accumulator. -/
private lemma foldl_max_mono (l : List ℕ) (a b : ℕ) (hab : a ≤ b) :
    l.foldl max a ≤ l.foldl max b := by
  induction l generalizing a b with
  | nil => exact hab
  | cons hd tl ih => exact ih (max a hd) (max b hd) (by omega)

/-- The initial accumulator is at most `foldl max init l`. -/
private lemma le_foldl_max_init (l : List ℕ) (init : ℕ) :
    init ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => exact le_refl init
  | cons hd tl ih =>
    calc init ≤ max init hd := le_max_left _ _
    _ ≤ List.foldl max (max init hd) tl := ih (max init hd)

/-- Any element of a list is at most `foldl max 0` of that list. -/
lemma foldl_max_mem (l : List ℕ) (x : ℕ) (hx : x ∈ l) :
    x ≤ l.foldl max 0 := by
  induction l with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hx with
    | inl h_eq =>
      rw [h_eq]
      exact le_trans (by omega : hd ≤ max 0 hd)
        (le_foldl_max_init tl (max 0 hd))
    | inr h_mem =>
      exact le_trans (ih h_mem)
        (foldl_max_mono tl 0 (max 0 hd) (by omega))

/-- A subtype of `α` representing elements strictly between `xs[i]` and
`xs[i+1]` (or between `xs[i]` and +∞ if `i` is the last index).
Used to restrict the inductive hypothesis to proper sub-intervals. -/
abbrev OpenIntervalType {α : Type*} [LinearOrder α] (xs : List α) (i : ℕ) :=
  { y : α // ∃ (hi_lt : i < xs.length),
    xs.get ⟨i, hi_lt⟩ < y ∧
    ∀ (h_next_lt : i + 1 < xs.length), y < xs.get ⟨i + 1, h_next_lt⟩ }

/-- A strictly increasing sequence covering a domain bounds any element `x`
either at one of the sequence points or within a consecutive interval.
This is the key covering lemma used in the split combination construction. -/
lemma list_interval_covers {α : Type*} [LinearOrder α] (x : α) :
    ∀ (xs : List α), x ∉ xs →
    (∃ y ∈ xs, y < x) →
    ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < x ∧
      ∀ (hi_succ_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, hi_succ_lt⟩
| [], _, ⟨_, hy, _⟩ => nomatch hy
| a :: tail, h_not_in, h_lb => by
  by_cases h_tail : ∃ y ∈ tail, y < x
  · obtain ⟨i, hi, hlt, hgt⟩ :=
        list_interval_covers x tail (fun h => h_not_in (List.Mem.tail _ h)) h_tail
    exact ⟨i + 1, by simp; omega, hlt, fun h => hgt (by simp at h; omega)⟩
  · grind

/-- An element in an open interval `OpenIntervalType xs i` is never a member
of the sequence `xs` itself (since it is strictly between two consecutive
sequence points, while the sequence is strictly monotone). -/
lemma not_mem_of_openInterval {α : Type*} [LinearOrder α] {xs : List α}
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length),
      i < j → xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (i : ℕ) (z : α)
    (h_in : ∃ (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < z ∧ ∀ (hi_succ_lt : i + 1 < xs.length),
      z < xs.get ⟨i + 1, hi_succ_lt⟩) : z ∉ xs := by
  intro hz_mem
  obtain ⟨j, hz_eq⟩ := List.mem_iff_get.mp hz_mem
  grind

/-- Two open intervals defined by the same strictly increasing sequence are
disjoint: if an element `x` lies in both interval `i` and interval `k`,
then `i = k`. -/
lemma openInterval_unique {α : Type*} [LinearOrder α] (xs : List α)
    (h_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length)
      (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (x : α) (i k : ℕ) (hi : i < xs.length) (hk : k < xs.length)
    (hlt_i : xs.get ⟨i, hi⟩ < x)
    (hgt_i : ∀ h_next_lt : i + 1 < xs.length,
      x < xs.get ⟨i + 1, h_next_lt⟩)
    (hlt_k : xs.get ⟨k, hk⟩ < x)
    (hgt_k : ∀ h_next_lt : k + 1 < xs.length,
      x < xs.get ⟨k + 1, h_next_lt⟩) :
    i = k := by
  rcases lt_trichotomy i k with h | rfl | h <;>
    first | exfalso; grind | rfl

end GeneralUtility

end SimonSplit
