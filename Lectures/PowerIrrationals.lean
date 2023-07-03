import Mathlib
/-!
# A Noncomputable function

An interesting example of a non-constructive proof is the following:

**Theorem:** There exist irrational numbers $a$ and $b$ such that $a^b$ is rational.
**Proof:** Let `b = √2`. If `b^b` is rational, then we can take `a = b`. Otherwise, we can take `a = √2^{√2}`, so `a^b=2`.

We can prove this in Lean. But a function that returns such a pair of numbers has to be defined as `noncomputable` in Lean.
-/

#check Real.rpow_add -- ∀ (x : ℝ) (y z : ℝ), x ^ (y + z) = x ^ y * x ^ z
#check Real.rpow_mul -- ∀ {x : ℝ}, 0 ≤ x → ∀ (y z : ℝ), x ^ (y * z) = (x ^ y) ^ z
#check Real.mul_self_sqrt -- ∀ {x : ℝ}, 0 ≤ x → Real.sqrt x * Real.sqrt x = x
#check Real.sqrt_pos -- ∀ {x : ℝ}, 0 < Real.sqrt x ↔ 0 < x

/--
An auxiliary lemma that (√2^√2)^√2 = 2. 
-/
theorem sq2_pow_twice : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
  have two_nonneg : (2 : ℝ) ≥ 0 := by norm_cast
  have sq2_pos : (Real.sqrt 2) > 0 := by simp [Real.sqrt_pos]
  have sq2_nonneg : (Real.sqrt 2) ≥ 0 := by
    apply Real.sqrt_nonneg
  rw [← Real.rpow_mul sq2_nonneg, Real.mul_self_sqrt two_nonneg]
  have lm := Real.rpow_add sq2_pos 1 1
  have one_plus_one : (1: ℝ) + (1: ℝ) = 2 := by norm_num
  rw [one_plus_one] at lm
  rw [lm]
  simp [Real.rpow_one]
  apply  Real.mul_self_sqrt
  exact two_nonneg

#check irrational_sqrt_two -- Irrational (Real.sqrt 2)
#check irrational_iff_ne_rational -- ∀ (x : ℝ), Irrational x ↔ ∀ (a b : ℤ), x ≠ ↑a / ↑b

/-- 
There exist irrational numbers `a` and `b` such that `a^b` is rational. 
-/
theorem exists_irrationals_pow_rational :
  ∃ a b : ℝ, (Irrational a) ∧ (Irrational b) ∧ ¬ (Irrational (a ^ b)) := by
    sorry

#check Classical.choice -- {α : Sort u} → Nonempty α → α

/-- 
Function giving a pair of irrational numbers `a` and `b` such that `a^b` is rational, together with a proof of their irrationality.
-/
def irrationalPairWithRationalPower : 
    {ab : ℝ × ℝ  // 
      Irrational ab.1 ∧ Irrational ab.2 ∧ ¬ Irrational (ab.1 ^ ab.2)} := by
      sorry

#check irrationalPairWithRationalPower.val -- ℝ × ℝ

