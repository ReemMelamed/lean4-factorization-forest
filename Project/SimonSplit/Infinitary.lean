/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Project.SimonSplit.Split

/-!
# Infinitary Simon's Theorem over ℕ

Formalization of the infinitary variant of Simon's Factorization Forest Theorem
for the linear order ⟨ℕ, <⟩ (Colcombet 2008, Section 3.5, Theorem 3.9).

## Main result

`simon_split_infinitary_nat`: For any multiplicative labeling `σ : MultiplicativeLabeling S ℕ`
with values in a finite semigroup `S`, there exists a Ramsey split `s : ℕ → Fin (nS S)`.

## Proof sketch

The proof uses compactness of the product space `ℕ → Fin (nS S)` (which is compact
as a product of finite discrete spaces by Tychonoff's theorem):

1. **Finite restrictions**: For each `n : ℕ`, restrict `σ` to `Fin (n+1)` and obtain
   a Ramsey split `s_n : Fin (n+1) → Fin (nS S)` from Simon's split theorem
   (already proved in `SimonSplit/Split.lean`).

2. **Compactness**: The space `ℕ → Fin (nS S)` is compact (product of finite types).
   The sequence `(s_n)` (extended trivially to all of ℕ) has a cluster point `s`.

3. **Ramsey condition preserved**: For any finite set of indices `x < y < z`,
   the Ramsey conditions hold for `s_n` when `n ≥ z`. By the cluster point
   property, they hold for `s` as well.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

open scoped Topology

namespace SimonSplit

/-- If a split `s_N` on `Fin (N + 1)` agrees with a split `s` on `ℕ` up to `max x y`,
then the split relation `SplitRelation s x y` is inherited by `s_N`. -/
lemma splitRelation_of_agree {n : ℕ} {N : ℕ} (s : Split ℕ n) (s_N : Split (Fin (N + 1)) n)
    {x y : ℕ} (hx : x < N + 1) (hy : y < N + 1) (hmax : max x y ≤ N)
    (h_agree : ∀ (k : ℕ) (hk : k ≤ max x y), s_N ⟨k, Nat.lt_succ_of_le (hk.trans hmax)⟩ = s k)
    (hsr : SplitRelation s x y) :
    SplitRelation s_N ⟨x, hx⟩ ⟨y, hy⟩ := by
  let x' : Fin (N + 1) := ⟨x, hx⟩
  let y' : Fin (N + 1) := ⟨y, hy⟩
  change SplitRelation s_N x' y'
  constructor
  · have hx_eq : s_N x' = s x := by
      have : x' = ⟨x, Nat.lt_succ_of_le ((le_max_left x y).trans hmax)⟩ := rfl
      rw [this]
      exact h_agree x (le_max_left x y)
    have hy_eq : s_N y' = s y := by
      have : y' = ⟨y, Nat.lt_succ_of_le ((le_max_right x y).trans hmax)⟩ := rfl
      rw [this]
      exact h_agree y (le_max_right x y)
    rw [hx_eq, hy_eq, hsr.1]
  · intro w hw1 hw2
    have hw1_val : min x y ≤ w.val := by
      rcases le_total x y with hle | hle
      · rw [min_eq_left hle]
        have : min x' y' = x' := min_eq_left (Fin.le_def.mpr hle)
        rw [this] at hw1
        exact Fin.le_def.mp hw1
      · rw [min_eq_right hle]
        have : min x' y' = y' := min_eq_right (Fin.le_def.mpr hle)
        rw [this] at hw1
        exact Fin.le_def.mp hw1
    have hw2_val : w.val ≤ max x y := by
      rcases le_total x y with hle | hle
      · rw [max_eq_right hle]
        have : max x' y' = y' := max_eq_right (Fin.le_def.mpr hle)
        rw [this] at hw2
        exact Fin.le_def.mp hw2
      · rw [max_eq_left hle]
        have : max x' y' = x' := max_eq_left (Fin.le_def.mpr hle)
        rw [this] at hw2
        exact Fin.le_def.mp hw2
    have hw_eq : s_N w = s w.val := by
      have hw_w : w = ⟨w.val, Nat.lt_succ_of_le (hw2_val.trans hmax)⟩ := Fin.ext rfl
      rw [hw_w]
      exact h_agree w.val hw2_val
    have hmin_eq : s_N (min x' y') = s (min x y) := by
      rcases le_total x y with hle | hle
      · have : min x' y' = x' := min_eq_left (Fin.le_def.mpr hle)
        rw [this, min_eq_left hle]
        have : x' = ⟨x, Nat.lt_succ_of_le ((le_max_left x y).trans hmax)⟩ := rfl
        rw [this]
        exact h_agree x (le_max_left x y)
      · have : min x' y' = y' := min_eq_right (Fin.le_def.mpr hle)
        rw [this, min_eq_right hle]
        have : y' = ⟨y, Nat.lt_succ_of_le ((le_max_right x y).trans hmax)⟩ := rfl
        rw [this]
        exact h_agree y (le_max_right x y)
    rw [hw_eq, hmin_eq]
    exact hsr.2 w.val hw1_val hw2_val

section SimonSplitInfinitary

variable {S : Type*} [Semigroup S] [Fintype S]
variable [Nonempty (Fin (nS S))]
variable (σ : MultiplicativeLabeling S ℕ)

/-- Restricts a multiplicative labeling on `ℕ` to `Fin (N + 1)`. -/
def restrictLabeling (N : ℕ) : MultiplicativeLabeling S (Fin (N + 1)) where
  σ := fun i j => σ.σ i.val j.val
  prop := fun x y z hxy hyz => σ.prop x.val y.val z.val hxy hyz

/-- A choice of Ramsey split on `Fin (N + 1)` guaranteed by Simon's split theorem. -/
noncomputable def s_N (N : ℕ) : Split (Fin (N + 1)) (nS S) :=
  (simon_split (restrictLabeling σ N)).choose

lemma isRamsey_s_N (N : ℕ) : IsRamsey (restrictLabeling σ N) (s_N σ N) :=
  (simon_split (restrictLabeling σ N)).choose_spec.2

/-- Extension of `s_N` to all of `ℕ` by a default value outside `[0, N]`. -/
noncomputable def f_N (N : ℕ) : ℕ → Fin (nS S) :=
  fun k =>
    if hk : k ≤ N then
      s_N σ N ⟨k, Nat.lt_succ_of_le hk⟩
    else
      Classical.choice inferInstance

lemma f_N_eq {N k : ℕ} (hk : k ≤ N) :
    f_N σ N k = s_N σ N ⟨k, Nat.lt_succ_of_le hk⟩ :=
  dif_pos hk

/-- By compactness of `ℕ → Fin (nS S)`, the sequence `(f_N)` has a cluster point. -/
lemma exists_clusterPt :
    ∃ s : ℕ → Fin (nS S), MapClusterPt s Filter.atTop (f_N σ) := by
  have : CompactSpace (ℕ → Fin (nS S)) := inferInstance
  have : Filter.NeBot (Filter.atTop : Filter ℕ) := Filter.atTop_neBot
  obtain ⟨s, -, hs⟩ := IsCompact.exists_mapClusterPt isCompact_univ
    (f := Filter.atTop) (u := f_N σ)
    (show Filter.map (f_N σ) Filter.atTop ≤ Filter.principal Set.univ by simp)
  exact ⟨s, hs⟩

/-- Since `s` is a cluster point, for any finite bound `M`, there is `N ≥ M`
such that `f_N` coincides with `s` on `[0, M]`. -/
lemma exists_coinciding_N (s : ℕ → Fin (nS S))
    (hs : MapClusterPt s Filter.atTop (f_N σ)) (M : ℕ) :
    ∃ N, M ≤ N ∧ ∀ k ≤ M, f_N σ N k = s k := by
  have hU : Set.pi (Set.Iic M) (fun k => {s k}) ∈ 𝓝 s :=
    set_pi_mem_nhds (Set.finite_Iic M) (fun k _ => (isOpen_discrete _).mem_nhds rfl)
  have hfreq := mapClusterPt_iff_frequently.mp hs _ hU
  obtain ⟨N, hMN, hNmem⟩ := Filter.frequently_atTop.mp hfreq M
  exact ⟨N, hMN, fun k hk => hNmem k hk⟩

/-- The infinitary Simon's split theorem for ℕ:
for any multiplicative labeling `σ` over ℕ into a finite semigroup `S`,
there exists a Ramsey split of size `nS S`.

**Proof strategy**: Use compactness of `ℕ → Fin (nS S)` (Tychonoff) to extract
a limit point from the sequence of finite Ramsey splits guaranteed by `simon_split`.
The Ramsey condition is preserved at the limit since it involves only finitely many
indices at a time. -/
theorem simon_split_infinitary_nat :
    ∃ s : Split ℕ (nS S), IsRamsey σ s := by
  obtain ⟨s, hs⟩ := exists_clusterPt σ
  refine ⟨s, ?_, ?_⟩
  · intro x y z hxy hyz hsr_xy hsr_yz
    obtain ⟨N, hMN, h_fN⟩ := exists_coinciding_N σ s hs z
    have hxN : x < N + 1 := by omega
    have hyN : y < N + 1 := by omega
    have hzN : z < N + 1 := by omega
    have h_agree : ∀ (k : ℕ) (hk : k ≤ z), s_N σ N ⟨k, Nat.lt_succ_of_le (hk.trans hMN)⟩ = s k := by
      intro k hk
      have hkN : k ≤ N := hk.trans hMN
      have := h_fN k hk
      rw [f_N_eq σ hkN] at this
      exact this
    have hsr_N_xy : SplitRelation (s_N σ N) ⟨x, hxN⟩ ⟨y, hyN⟩ :=
      splitRelation_of_agree s (s_N σ N) hxN hyN (by omega)
        (fun k _ ↦ h_agree k (by omega)) hsr_xy
    have hsr_N_yz : SplitRelation (s_N σ N) ⟨y, hyN⟩ ⟨z, hzN⟩ :=
      splitRelation_of_agree s (s_N σ N) hyN hzN (by omega)
        (fun k _ ↦ h_agree k (by omega)) hsr_yz
    have hram := (isRamsey_s_N σ N).1 ⟨x, hxN⟩ ⟨y, hyN⟩ ⟨z, hzN⟩
      (Fin.lt_def.mpr hxy) (Fin.lt_def.mpr hyz) hsr_N_xy hsr_N_yz
    exact hram
  · intro x y u v hxy huv hsr_xy hsr_uv hsr_xu
    let M := max y v
    obtain ⟨N, hMN, h_fN⟩ := exists_coinciding_N σ s hs M
    have hxN : x < N + 1 := by omega
    have hyN : y < N + 1 := by omega
    have huN : u < N + 1 := by omega
    have hvN : v < N + 1 := by omega
    have h_agree : ∀ (k : ℕ) (hk : k ≤ M), s_N σ N ⟨k, Nat.lt_succ_of_le (hk.trans hMN)⟩ = s k := by
      intro k hk
      have hkN : k ≤ N := hk.trans hMN
      have := h_fN k hk
      rw [f_N_eq σ hkN] at this
      exact this
    have hsr_N_xy : SplitRelation (s_N σ N) ⟨x, hxN⟩ ⟨y, hyN⟩ :=
      splitRelation_of_agree s (s_N σ N) hxN hyN (by omega)
        (fun k _ ↦ h_agree k (by omega)) hsr_xy
    have hsr_N_uv : SplitRelation (s_N σ N) ⟨u, huN⟩ ⟨v, hvN⟩ :=
      splitRelation_of_agree s (s_N σ N) huN hvN (by omega)
        (fun k _ ↦ h_agree k (by omega)) hsr_uv
    have hsr_N_xu : SplitRelation (s_N σ N) ⟨x, hxN⟩ ⟨u, huN⟩ :=
      splitRelation_of_agree s (s_N σ N) hxN huN (by omega)
        (fun k _ ↦ h_agree k (by omega)) hsr_xu
    have hram := (isRamsey_s_N σ N).2 ⟨x, hxN⟩ ⟨y, hyN⟩ ⟨u, huN⟩ ⟨v, hvN⟩
      (Fin.lt_def.mpr hxy) (Fin.lt_def.mpr huv) hsr_N_xy hsr_N_uv hsr_N_xu
    exact hram

end SimonSplitInfinitary

end SimonSplit
