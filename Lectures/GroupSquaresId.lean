import Mathlib
/-!
## A Group theory theorem

Since this is a workshop on Groups and Computations, we prove a theorem about groups. Namely, we show that if the square of every element is the identity, then the group is commutative.
-/


#check inv_eq_of_mul_eq_one_right -- ∀ {G : Type u_1} [inst : DivisionMonoid G] {a b : G}, a * b = 1 → a⁻¹ = b

theorem self_inv_of_squares_id[Group G] :(∀ x : G, x * x = 1) →
  ∀ x : G, x⁻¹ = x := by sorry
  


theorem commutative_of_squares_id[Group G] :(∀ x : G, x * x = 1) →
  ∀ x y : G, x * y = y * x := by
  sorry

#check mul_left_cancel

