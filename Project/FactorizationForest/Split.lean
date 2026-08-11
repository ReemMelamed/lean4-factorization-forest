/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Project.FactorizationForest.Regular
import Project.FactorizationForest.Irregular

/-!
# The Factorization Forest Theorem — Simon's Split Theorem

This file assembles the two cases (regular and irregular D-class) into the
main Simon split theorem `simon_split`, and applies it to word labelings in
`simon_word`.

## Main Results

* `simon_split_induction_aux` — the induction step: any labeling into `jUp a`
  (with Simon complexity ≤ n) admits a normalized Ramsey split of size
  `nSElement a`.
* `simon_split_induction` — the induction step without the auxiliary bound.
* `simon_split` — **Simon's Theorem**: every multiplicative labeling over a
  finite linearly ordered type admits a normalized Ramsey split.
* `simon_word` — Simon's split theorem applied to word labelings.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace FactorizationForest

-- ---------------------------------------------------------------------------
-- Section 1: Simon's Split Induction
-- ---------------------------------------------------------------------------

section SimonSplit

variable {S : Type*} [Semigroup S] [Fintype S]

/-- Auxiliary induction step for Simon's split theorem. For each element
`a : S` with `nSElement a ≤ n`, and for each multiplicative labeling `σ`
taking values in `jUp a`, there exists a normalized Ramsey split of size
`nSElement a`.
The proof proceeds by strong induction on `n` and branches on whether the
D-class of `a` is regular or irregular, delegating to
`simon_split_regular_case` or `simon_split_irregular_case` respectively. -/
lemma simon_split_induction_aux {S : Type*} [Semigroup S] [Fintype S]
    (n : ℕ) :
    ∀ (a : S) (_hn : nSElement a ≤ n)
    {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (_h_img : labelingIn σ (jUp a)),
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro a _ α _ _ _ σ h_img
    have ih : ∀ b : S, nSElement b < nSElement a →
        ∀ (xs : List α) (i : ℕ) [Nonempty (OpenIntervalType xs i)]
        (σ_β : MultiplicativeLabeling S (OpenIntervalType xs i)), labelingIn σ_β (jUp b) →
        ∃ (s : Split (OpenIntervalType xs i) (nSElement b)), IsNormalized s ∧ IsRamsey σ_β s :=
      fun b _ xs i _ σ_β h_img_β ↦ ihn (nSElement b) (by omega) b le_rfl σ_β h_img_β
    by_cases h_reg : IsRegularDClass (IsGreenD.eqvClass a)
    · exact simon_split_regular_case a σ h_img h_reg ih
    · exact simon_split_irregular_case a σ h_img h_reg ih

/-- Simon's split induction step: for any element `a : S` and any
multiplicative labeling `σ` into `jUp a`, there exists a normalized Ramsey
split of size `nSElement a`. -/
lemma simon_split_induction (a : S) {α : Type*} [LinearOrder α]
    [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (h_img : labelingIn σ (jUp a)) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s :=
  simon_split_induction_aux (nSElement a) a le_rfl σ h_img

/-- **Simon's Theorem (Split Form)**: every multiplicative labeling `σ` over a
non-empty finite linear order into a finite semigroup `S` admits a normalized
Ramsey split of size `nS S`.
The proof applies `simon_split_induction` to the element `σ(x₀, y₀)` where
`x₀` and `y₀` are the minimum and maximum of the domain, and then shifts the
split ranks to fit into `Fin (nS S)`. -/
theorem simon_split {S α : Type*} [Semigroup S] [Fintype S]
    [LinearOrder α] [Fintype α] [Nonempty α] [Nonempty (Fin (nS S))]
    (σ : MultiplicativeLabeling S α) :
    ∃ (s : Split α (nS S)), IsNormalized s ∧ IsRamsey σ s := by
  let x₀ := Finset.min' (Finset.univ : Finset α) Finset.univ_nonempty
  let y₀ := Finset.max' (Finset.univ : Finset α) Finset.univ_nonempty
  let a := σ.σ x₀ y₀
  have ha : labelingIn σ (jUp a) := fun x y hlt ↦ by
    have h_x0_le : x₀ ≤ x := Finset.min'_le _ _ (Finset.mem_univ _)
    have h_le_y0 : y ≤ y₀ := Finset.le_max' _ _ (Finset.mem_univ _)
    change IsGreenJRel (σ.σ x₀ y₀) (σ.σ x y)
    rcases h_x0_le.eq_or_lt with rfl | h_x0_lt
    · rcases h_le_y0.eq_or_lt with rfl | h_lt_y0
      · exact IsGreenJRel.refl _
      · exact IsGreenJRel.mul_right (σ.σ y y₀) (σ.prop _ y y₀ hlt h_lt_y0).symm
    · rcases h_le_y0.eq_or_lt with rfl | h_lt_y0
      · exact IsGreenJRel.mul_left (σ.σ x₀ x) (σ.prop x₀ x _ h_x0_lt hlt).symm
      · exact IsGreenJRel.mul_both (σ.σ x₀ x) (σ.σ y y₀)
          (by rw [← σ.prop x₀ y y₀ (h_x0_lt.trans hlt) h_lt_y0, ← σ.prop x₀ x y h_x0_lt hlt])
  obtain ⟨s_a, h_norm, h_ramsey⟩ := simon_split_induction a σ ha
  have h_le : nSElement a ≤ nS S := by
    unfold nS
    have h_ne : (Finset.univ.image (fun (x : S) ↦ nSElement x)).Nonempty :=
      ⟨nSElement a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
    exact (dif_pos h_ne).symm ▸ Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  let Δ := nS S - nSElement a
  let s : Split α (nS S) := fun x ↦ ⟨(s_a x).val + Δ, by have h_bound := (s_a x).isLt; omega⟩
  have hsr_iff : ∀ u v, SplitRelation s u v ↔ SplitRelation s_a u v := by
    intro u v
    have h_eq : s u = s v ↔ s_a u = s_a v := by
      rw [Fin.ext_iff, Fin.ext_iff]
      change (s_a u).val + Δ = (s_a v).val + Δ ↔ (s_a u).val = (s_a v).val
      exact ⟨fun h ↦ by omega, fun h ↦ by omega⟩
    have h_le : ∀ z, s z ≤ s (min u v) ↔ s_a z ≤ s_a (min u v) := by
      intro z
      rw [Fin.le_iff_val_le_val, Fin.le_iff_val_le_val]
      change (s_a z).val + Δ ≤ (s_a (min u v)).val + Δ ↔ (s_a z).val ≤ (s_a (min u v)).val
      exact ⟨fun h ↦ by omega, fun h ↦ by omega⟩
    exact ⟨fun h ↦ ⟨h_eq.mp h.1, fun z hz_ge hz_le ↦ (h_le z).mp (h.2 z hz_ge hz_le)⟩,
           fun h ↦ ⟨h_eq.mpr h.1, fun z hz_ge hz_le ↦ (h_le z).mpr (h.2 z hz_ge hz_le)⟩⟩
  exact ⟨s, by
      ext; simp only [h_norm, s]
      have h_max_a : (Finset.max' Finset.univ Finset.univ_nonempty : Fin (nSElement a)).val
          = nSElement a - 1 :=
        congrArg Fin.val ((Finset.max'_eq_iff _ _
          (⟨nSElement a - 1, by have h_pos : 0 < nSElement a := nSElement_pos a; omega⟩ :
          Fin (nSElement a))).mpr ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr
          (Nat.le_pred_of_lt w.isLt)⟩)
      have h_max_S : (Finset.max' Finset.univ Finset.univ_nonempty : Fin (nS S)).val = nS S - 1 :=
        congrArg Fin.val ((Finset.max'_eq_iff _ _
          (⟨nS S - 1, by have h_pos : 0 < nS S := Fin.pos_iff_nonempty.mpr inferInstance; omega⟩ :
          Fin (nS S))).mpr ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr
          (Nat.le_pred_of_lt w.isLt)⟩)
      have h_pos_a : 0 < nSElement a := nSElement_pos a
      omega,
    fun x y z hxy hyz hsr_xy hsr_yz ↦
      h_ramsey.1 x y z hxy hyz ((hsr_iff x y).mp hsr_xy) ((hsr_iff y z).mp hsr_yz),
    fun x y u v hxy huv hsr_xy hsr_uv hsr_xu ↦
      h_ramsey.2 x y u v hxy huv ((hsr_iff x y).mp hsr_xy)
        ((hsr_iff u v).mp hsr_uv) ((hsr_iff x u).mp hsr_xu)⟩

end SimonSplit

-- ---------------------------------------------------------------------------
-- Section 2: Application to Word Labelings
-- ---------------------------------------------------------------------------

section SimonWord

/-- **Simon's split theorem for words**: for any word `u` over an alphabet
`A` and any homomorphism `eval` from `A*` to a finite semigroup `S`, there
exists a normalized Ramsey split of `Fin (u.length + 1)` of size `nS S`.
This is the form of Simon's theorem used to construct factorization trees. -/
theorem simon_word {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty (Fin (nS S))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) :
    ∃ s : Split (Fin (u.length + 1)) (nS S),
      IsNormalized s ∧ IsRamsey (wordLabeling eval hmul u) s :=
  simon_split (wordLabeling eval hmul u)

end SimonWord

end FactorizationForest
