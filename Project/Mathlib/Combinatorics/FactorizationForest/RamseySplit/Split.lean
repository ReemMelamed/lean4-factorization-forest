/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Project.Mathlib.Combinatorics.FactorizationForest.RamseySplit.Regular
import Project.Mathlib.Combinatorics.FactorizationForest.RamseySplit.Irregular

/-!
# Simon's Split Theorem

Assembles the regular and irregular cases to prove Simon's Split Theorem (`simon_split`),
and applies it to word labelings (`simon_word`).

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

namespace RamseySplit

open GreensRelations

section SplitTheorem

variable {S : Type*} [Semigroup S] [Fintype S]

/-- Induction step for Simon's split theorem,
branching on whether the `D`-class of `a` is regular. -/
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
    · exact ramsey_split_regular_case a σ h_img h_reg ih
    · exact ramsey_split_irregular_case a σ h_img h_reg ih

/-- Simon's split induction step: for any element `a : S` and any
multiplicative labeling `σ` into `jUp a`, there exists a normalized Ramsey
split of size `nSElement a`. -/
lemma simon_split_induction (a : S) {α : Type*} [LinearOrder α]
    [Fintype α] [Nonempty α]
    (σ : MultiplicativeLabeling S α)
    (h_img : labelingIn σ (jUp a)) :
    ∃ (s : Split α (nSElement a)), IsNormalized s ∧ IsRamsey σ s :=
  simon_split_induction_aux (nSElement a) a le_rfl σ h_img

/-- Simon's Theorem (Split Form): every multiplicative labeling admits a normalized Ramsey split. -/
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
      · exact .of_eq rfl
      · exact .mul_right (σ.σ y y₀) (σ.prop _ y y₀ hlt h_lt_y0).symm
    · rcases h_le_y0.eq_or_lt with rfl | h_lt_y0
      · exact .mul_left (σ.σ x₀ x) (σ.prop x₀ x _ h_x0_lt hlt).symm
      · exact .mul_both (σ.σ x₀ x) (σ.σ y y₀)
          (by rw [← σ.prop x₀ y y₀ (h_x0_lt.trans hlt) h_lt_y0, ← σ.prop x₀ x y h_x0_lt hlt])
  obtain ⟨s_a, h_norm, h_ramsey⟩ := simon_split_induction a σ ha
  have h_le : nSElement a ≤ nS S := by
    dsimp [nS]
    have h_ne : (Finset.univ.image (fun (x : S) ↦ nSElement x)).Nonempty :=
      ⟨nSElement a, Finset.mem_image_of_mem _ (Finset.mem_univ a)⟩
    rw [dif_pos h_ne]
    exact Finset.le_max' _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  let Δ := nS S - nSElement a
  let s : Split α (nS S) := fun x ↦ ⟨(s_a x).val + Δ, by have := (s_a x).isLt; omega⟩
  have hsr_iff : ∀ u v, SplitRelation s u v ↔ SplitRelation s_a u v := fun u v ↦ by
    simp only [SplitRelation, Fin.ext_iff, Fin.le_iff_val_le_val, s]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨by omega, fun z hz1 hz2 ↦ by have := h2 z hz1 hz2; omega⟩,
      fun ⟨h1, h2⟩ ↦ ⟨by omega, fun z hz1 hz2 ↦ by have := h2 z hz1 hz2; omega⟩⟩
  exact ⟨s, by
      ext
      simp only [h_norm, s]
      have h_max_a : (Finset.max' Finset.univ Finset.univ_nonempty : Fin (nSElement a)).val
          = nSElement a - 1 :=
        congrArg Fin.val ((Finset.max'_eq_iff _ _
          (⟨nSElement a - 1, by have := nSElement_pos a; omega⟩ : Fin (nSElement a))).mpr
          ⟨Finset.mem_univ _, fun w _ ↦ Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt w.isLt)⟩)
      have h_max_S : (Finset.max' Finset.univ Finset.univ_nonempty : Fin (nS S)).val = nS S - 1 :=
        congrArg Fin.val ((Finset.max'_eq_iff _ _
          (⟨nS S - 1, by have : 0 < nS S := Fin.pos_iff_nonempty.mpr inferInstance; omega⟩ :
          Fin (nS S))).mpr ⟨Finset.mem_univ _, fun w _ ↦
          Fin.le_iff_val_le_val.mpr (Nat.le_pred_of_lt w.isLt)⟩)
      have : 0 < nSElement a := nSElement_pos a
      omega,
    fun x y z hxy hyz hsr_xy hsr_yz ↦
      h_ramsey.1 x y z hxy hyz ((hsr_iff x y).mp hsr_xy) ((hsr_iff y z).mp hsr_yz),
    fun x y u v hxy huv hsr_xy hsr_uv hsr_xu ↦
      h_ramsey.2 x y u v hxy huv ((hsr_iff x y).mp hsr_xy)
        ((hsr_iff u v).mp hsr_uv) ((hsr_iff x u).mp hsr_xu)⟩

end SplitTheorem

section SimonWord

/-- Simon's split theorem for words: every word admits a normalized Ramsey split of size `nS S`. -/
theorem simon_word {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty (Fin (nS S))]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) :
    ∃ s : Split (Fin (u.length + 1)) (nS S),
      IsNormalized s ∧ IsRamsey (wordLabeling eval hmul u) s :=
  simon_split (wordLabeling eval hmul u)

end SimonWord

end RamseySplit
