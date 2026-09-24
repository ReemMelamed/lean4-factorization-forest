/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Opposite
import Mathlib.Data.Finite.Defs

/-!
# Opposite Semigroup Divisibility and Finiteness Lemmas

Helper lemmas connecting divisibility and finiteness in a semigroup `S` with its opposite `Sᵐᵒᵖ`.

## References

* [T. Colcombet, *The Factorization Forest Theorem*][colcombet2008]
-/

variable {S : Type*} [Semigroup S]

open MulOpposite

-- TODO: Upstream to Mathlib.Algebra.Group.Opposite
/-- Right divisibility in the opposite semigroup is equivalent to left divisibility. -/
lemma op_rightDvd_op_iff {a b : S} :
    RightDvd (op a) (op b) ↔ a ∣ b :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨unop c, op_injective (by simp [hc])⟩,
   fun ⟨c, hc⟩ ↦ ⟨op c, by simp [hc]⟩⟩

-- TODO: Upstream to Mathlib.Algebra.Group.Opposite
/-- Left divisibility in the opposite semigroup is equivalent to right divisibility. -/
lemma op_dvd_op_iff {a b : S} :
    op a ∣ op b ↔ RightDvd a b :=
  ⟨fun ⟨c, hc⟩ ↦ ⟨unop c, op_injective (by simp [hc])⟩,
   fun ⟨c, hc⟩ ↦ ⟨op c, by simp [hc]⟩⟩

-- TODO: Upstream to Mathlib.Algebra.Group.Opposite
/-- The opposite semigroup construction gives an equivalence between `S` and `Sᵐᵒᵖ`
  that preserves Green's relations, so finiteness of `S` implies finiteness of `Sᵐᵒᵖ`. -/
instance instFiniteMulOpposite [Finite S] : Finite Sᵐᵒᵖ :=
  Finite.of_equiv S MulOpposite.opEquiv
