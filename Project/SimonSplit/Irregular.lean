/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Project.SimonSplit.Combine

/-!
# Simon's Split Theorem — Irregular `D`-Class Case

Constructs the Simon split (`simon_split_irregular_case`) for the case where the `D`-class
is irregular, using the fact that the sequence length is at most 2.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace SimonSplit

section LabelingProperties

variable {S : Type*} [Semigroup S]

/-- If an irregular `D`-class contains elements from a multiplicative sequence,
it cannot contain three consecutive products in that sequence. -/
lemma irregular_d_class_no_three_seq [Finite S] (a : S) {α : Type*} [LinearOrder α]
    (σ : MultiplicativeLabeling S α) (x y z : α)
    (h_img : labelingIn σ (jUp a))
    (h_xy : x < y) (h_yz : y < z)
    (h_d1 : IsGreenD (σ.σ x y) a)
    (h_d2 : IsGreenD (σ.σ y z) a) :
    IsRegularDClass (IsGreenD.eqvClass a) :=
  have h_xz_le_xy : GreenJClass.mk (σ.σ x z) ≤ GreenJClass.mk (σ.σ x y) :=
    σ.prop x y z h_xy h_yz ▸ IsGreenJRel.mul_right (σ.σ y z) rfl
  have h_xz_le_a : GreenJClass.mk (σ.σ x z) ≤ GreenJClass.mk a :=
    GreenJClass.mk_eq_mk_iff.mpr (isGreenJ_of_isGreenD h_d1) ▸ h_xz_le_xy
  have h_D_xz_a : IsGreenD (σ.σ x y * σ.σ y z) a :=
    (σ.prop x y z h_xy h_yz).symm ▸ isGreenD_of_isGreenJ
      (GreenJClass.mk_eq_mk_iff.mp (le_antisymm h_xz_le_a (h_img x z (lt_trans h_xy h_yz))))
  (isRegularDClass_iff_exists_idempotent (IsGreenD.eqvClass a) ⟨a, rfl⟩).mpr (
    let ⟨e, he_D, he_idem, _⟩ :=
      (mul_mem_isGreenD_eqvClass_properties ⟨a, rfl⟩ _ _ h_d1 h_d2 h_D_xz_a).2
    ⟨e, he_D, he_idem⟩
  )

end LabelingProperties

section SplitConstruction

/-- A specialized version of `combineSplits` for irregular `D`-classes.
All sequence-point elements receive the maximum rank `nSElement a - 1`,
preventing overlap with the interval ranks. -/
noncomputable abbrev irregularSplits {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a)) :
    Split α (nSElement a) :=
  combineSplits a xs
    (fun _ => ⟨nSElement a - 1, by have h_pos := nSElement_pos a; omega⟩) sY

/-- Proves the normalization and Ramsey properties for `irregularSplits`.
This is the main interface lemma for the irregular `D`-class case, delegating
to `combineSplits_props`. -/
lemma irregularSplits_props {α S : Type*}
    [LinearOrder α] [Fintype α] [Nonempty α] [Semigroup S] [Fintype S]
    (a : S) (xs : List α)
    (σ : MultiplicativeLabeling S α)
    (σ_Y : ∀ (i : ℕ), MultiplicativeLabeling S (OpenIntervalType xs i))
    (sY : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      Split (OpenIntervalType xs i) (nSElement a))
    (hsY_ramsey : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      IsRamsey (σ_Y i) (sY i))
    (h_min_head : xs.head? = some (Finset.min' (Finset.univ : Finset α)
      Finset.univ_nonempty))
    (h_max_val : (Finset.max' (Finset.univ : Finset (Fin (nSElement a)))
      Finset.univ_nonempty).val = nSElement a - 1)
    (h_σ_Y : ∀ i x y, (σ_Y i).σ x y = σ.σ x.val y.val)
    (h_cov : ∀ x, x ∉ xs → ∃ (i : ℕ) (hi_lt : i < xs.length),
      xs.get ⟨i, hi_lt⟩ < x ∧
      ∀ (h_next_lt : i + 1 < xs.length), x < xs.get ⟨i + 1, h_next_lt⟩)
    (hsY_strict : ∀ (i : ℕ) [Nonempty (OpenIntervalType xs i)],
      ∀ z : OpenIntervalType xs i, (sY i z).val < nSElement a - 1)
    (h_xs_mono : ∀ (i j : ℕ) (hi_lt : i < xs.length) (hj_lt : j < xs.length), i < j →
      xs.get ⟨i, hi_lt⟩ < xs.get ⟨j, hj_lt⟩)
    (h_xs_len : xs.length ≤ 2)
    (h_interval_ramsey : ∀ x y, x ∉ xs → x < y →
      SplitRelation (irregularSplits a xs sY) x y →
      ∃ (i : ℕ) (x_val y_val : OpenIntervalType xs i),
        x_val.val = x ∧ y_val.val = y ∧
        SplitRelation (@sY i ⟨x_val⟩) x_val y_val) :
    IsNormalized (irregularSplits a xs sY) ∧
    IsRamsey σ (irregularSplits a xs sY) := by
  exact combineSplits_props a xs (nSElement a - 1) σ σ_Y
    (fun _ ↦ ⟨nSElement a - 1, by have h_pos := nSElement_pos a; omega⟩)
    sY hsY_ramsey h_σ_Y h_cov hsY_strict
    (h_rankX_ge := fun x hx ↦ by dsimp only; omega)
    (h_xs_mono := h_xs_mono)
    (h_interval_ramsey := h_interval_ramsey)
    (h_X_ramsey_1 := fun x y z hx hy hz hlt_xy hlt_yz _ _ ↦ by
      rcases List.mem_iff_get.mp hx with ⟨⟨ix, hix⟩, rfl⟩
      rcases List.mem_iff_get.mp hy with ⟨⟨iy, hiy⟩, rfl⟩
      rcases List.mem_iff_get.mp hz with ⟨⟨iz, hiz⟩, rfl⟩
      have h_ix_lt_iy : ix < iy := by
        contrapose! hlt_xy
        rcases hlt_xy.eq_or_lt with rfl | h
        · exact le_rfl
        · exact (h_xs_mono iy ix hiy hix h).le
      have h_iy_lt_iz : iy < iz := by
        contrapose! hlt_yz
        rcases hlt_yz.eq_or_lt with rfl | h
        · exact le_rfl
        · exact (h_xs_mono iz iy hiz hiy h).le
      omega)
    (h_X_ramsey_2 := fun x y u v hx hy hu hv hlt_xy hlt_uv _ _ _ ↦ by
      rcases List.mem_iff_get.mp hx with ⟨⟨ix, hix⟩, rfl⟩
      rcases List.mem_iff_get.mp hy with ⟨⟨iy, hiy⟩, rfl⟩
      rcases List.mem_iff_get.mp hu with ⟨⟨iu, hiu⟩, rfl⟩
      rcases List.mem_iff_get.mp hv with ⟨⟨iv, hiv⟩, rfl⟩
      have h_ix_lt_iy : ix < iy := by
        contrapose! hlt_xy
        rcases hlt_xy.eq_or_lt with rfl | h
        · exact le_rfl
        · exact (h_xs_mono iy ix hiy hix h).le
      have h_iu_lt_iv : iu < iv := by
        contrapose! hlt_uv
        rcases hlt_uv.eq_or_lt with rfl | h
        · exact le_rfl
        · exact (h_xs_mono iv iu hiv hiu h).le
      have h_ix : ix = iu := by omega
      have h_iy : iy = iv := by omega
      exact congrArg₂ σ.σ (congrArg xs.get (Fin.ext h_ix))
        (congrArg xs.get (Fin.ext h_iy)))
    (h_min_norm := by
      have h_min_in : (Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty) ∈ xs := by
        cases xs with
        | nil => cases h_min_head
        | cons hd tl => injection h_min_head with h; exact h ▸ List.Mem.head _
      grind)
    (h_max_val := h_max_val)

/-- Constructs a normalized Ramsey split when the `D`-class of `a` is irregular. -/
lemma simon_split_irregular_case {S : Type*} [Semigroup S] [Fintype S]
    (a : S) {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α) (_h_img : labelingIn σ (jUp a))
    (_h_not_reg : ¬ IsRegularDClass (IsGreenD.eqvClass a))
    (ih : ∀ b : S, nSElement b < nSElement a →
    ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
    (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
    ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
  classical
  let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let xs := buildXSeq a σ x₀
  have h_x0_in : x₀ ∈ xs := by
    change x₀ ∈ buildXSeq a σ x₀; rw [buildXSeq]; split_ifs <;> exact List.Mem.head _
  let σ_Y (i : ℕ) : MultiplicativeLabeling S (OpenIntervalType xs i) :=
    ⟨fun x y ↦ σ.σ x.val y.val, fun x y z hx hy ↦ σ.prop x.val y.val z.val hx hy⟩
  have h_sY_ex : ∀ i [Nonempty (OpenIntervalType xs i)],
      ∃ (s : Split (OpenIntervalType xs i) (nSElement a)),
        IsRamsey (σ_Y i) s ∧ ∀ z, (s z).val < nSElement a - nD (IsGreenD.eqvClass a) :=
    build_interval_splits_of_ih a σ _h_img x₀ xs (buildXSeq_properties a σ _h_img x₀).2.2.2
      (buildXSeq_properties a σ _h_img x₀).2.2.1 ih
  choose sY hsY_ramsey hsY_strict using h_sY_ex
  have h_xs_len : xs.length ≤ 2 := by
    by_contra h_len
    have h_eval0 : buildXSeq a σ x₀ = if h : (Finset.univ.filter
        (fun z ↦ x₀ < z ∧ IsGreenD (σ.σ x₀ z) a)).Nonempty then x₀ ::
        buildXSeq a σ (Finset.min' _ h) else [x₀] := by rw [buildXSeq]
    have h_c0 : (Finset.univ.filter (fun z ↦ x₀ < z ∧ IsGreenD (σ.σ x₀ z) a)).Nonempty := by
      by_contra hn
      have : xs.length = 1 := by
        change (buildXSeq a σ x₀).length = 1
        rw [h_eval0, dif_neg hn]
        rfl
      omega
    let x1 := Finset.min' _ h_c0
    have h_x1_p : x₀ < x1 ∧ IsGreenD (σ.σ x₀ x1) a :=
      (Finset.mem_filter.mp (Finset.min'_mem _ h_c0)).2
    have h_bw1 : xs = x₀ :: buildXSeq a σ x1 := by
      change buildXSeq a σ x₀ = _
      rw [h_eval0, dif_pos h_c0]
    have h_eval1 : buildXSeq a σ x1 = if h : (Finset.univ.filter
        (fun z ↦ x1 < z ∧ IsGreenD (σ.σ x1 z) a)).Nonempty then x1 ::
        buildXSeq a σ (Finset.min' _ h) else [x1] := by rw [buildXSeq]
    have h_c1 : (Finset.univ.filter (fun z ↦ x1 < z ∧ IsGreenD (σ.σ x1 z) a)).Nonempty := by
      by_contra hn
      have : xs.length = 2 := by rw [h_bw1, h_eval1, dif_neg hn]; rfl
      omega
    let x2 := Finset.min' _ h_c1
    have h_x2_p : x1 < x2 ∧ IsGreenD (σ.σ x1 x2) a :=
      (Finset.mem_filter.mp (Finset.min'_mem _ h_c1)).2
    exact _h_not_reg (irregular_d_class_no_three_seq a σ x₀ x1 x2 _h_img
      h_x1_p.1 h_x2_p.1 h_x1_p.2 h_x2_p.2)
  exact ⟨irregularSplits a xs sY, irregularSplits_props a xs σ σ_Y sY hsY_ramsey
    (h_xs_mono := (buildXSeq_properties a σ _h_img x₀).2.2.2) (h_xs_len := h_xs_len)
    (h_min_head := by change (buildXSeq a σ x₀).head? = _; rw [buildXSeq]; split_ifs <;> rfl)
    (h_max_val := by
      have hm : Finset.max' (Finset.univ : Finset (Fin (nSElement a))) Finset.univ_nonempty =
          ⟨nSElement a - 1, Nat.sub_lt (nSElement_pos a) (by decide)⟩ := by
        rw [Finset.max'_eq_iff]
        exact ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt w.isLt)⟩
      exact congrArg Fin.val hm)
    (h_σ_Y := fun _ _ _ ↦ rfl)
    (h_cov := fun x hx ↦ buildXSeq_covers a σ x₀ x (Finset.min'_le _ _ (Finset.mem_univ x)) hx)
    (hsY_strict := fun i _ z ↦ by
      have h_strict := hsY_strict i z
      simp only [nD, if_neg _h_not_reg] at h_strict
      omega)
    (h_interval_ramsey := combineSplits_interval_ramsey a xs
      (fun _ ↦ ⟨nSElement a - 1, by have h_pos := nSElement_pos a; omega⟩)
      sY (nSElement a - 1) (buildXSeq_properties a σ _h_img x₀).2.2.2
      (fun x hx ↦ buildXSeq_covers a σ x₀ x (Finset.min'_le _ _ (Finset.mem_univ x)) hx)
      (fun i _ z ↦ by
        have h_strict := hsY_strict i z
        simp only [nD, if_neg _h_not_reg] at h_strict
        omega)
      (by intro x; dsimp only; omega))⟩

end SplitConstruction

end SimonSplit
