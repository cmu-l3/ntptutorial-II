import Mathlib.Data.Real.Basic

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b, mul_assoc b a c]
