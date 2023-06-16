import Mathlib

theorem self_inv_of_squares_id[Group G] :(∀ x : G, x * x = 1) →
  ∀ x : G, x⁻¹ = x := by
  intro h x
  apply inv_eq_of_mul_eq_one_right
  apply h
  


theorem commutative_of_squares_id[Group G] :(∀ x : G, x * x = 1) →
  ∀ x y : G, x * y = y * x := by
  intro h
  intro x y
  have rel_xy := self_inv_of_squares_id h (y * x)
  simp at rel_xy
  simp [self_inv_of_squares_id h] at rel_xy
  assumption

#check mul_left_cancel

