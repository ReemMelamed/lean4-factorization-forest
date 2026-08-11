import Mathlib

def test1 (n : ℕ) (h : List.finRange (n + 1) ≠ []) : (List.head (List.finRange (n + 1)) h).val = 0 := by
  rfl
