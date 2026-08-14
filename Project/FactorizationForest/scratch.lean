import Mathlib

lemma my_bound_helper {hp hm hs h h_height : ℕ}
  (h_pre : hp ≤ 3 * h - 1)
  (h_mid : hm ≤ 3 * h)
  (h_suf : hs ≤ 3 * h - 1)
  (h_bound : h ≤ h_height - 1) :
  max (max hp hm + 1) hs + 1 ≤ 3 * h_height - 1 := by
  revert h_pre h_mid h_suf h_bound
  simp only [Nat.max_def]
  split_ifs <;> omega
