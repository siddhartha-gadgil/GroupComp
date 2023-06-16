import Mathlib
/-!
## Linear Diaphontine Equations

We solve linear diaphontine equations of the form `a * x + b * y = c` where `a`, `b`, `c` are integers if they have a solution with proof. Otherwise, we return a proof that there is no solution.
-/

/--
Solution of the linear diaphontine equation `a * x + b * y = c` where `a`, `b`, `c` are integers or a proof that there is no solution.
-/
inductive DiaphontineSolution (a b c : ℤ) where
    | solution : (x y : ℤ) →  a * x + b * y = c → DiaphontineSolution a b c
    | unsolvable : (∀ x y : ℤ, ¬ (a * x + b * y = c)) → DiaphontineSolution a b c

/-!
This has a solution if and only if the gcd of `a` and `b` divides `c`.
* If the gcd of `a` and `b` divides `c`, by Bezout's Lemma there are integers `x` and `y` such that `a * x + b * y = gcd a b`. Further, as `gcd a b` divides `c`, we have an integer `d` such that `(gcd a b) * d = c`. Then `x * d` and `y * d` are integers such that `a * (x * d) + b * (y * d) = c`.
* The converse follows as `gcd a b` divides `a` and `b`, hence `c = a * x + b * y`.

The main results we need are in the library. Here are most of them:

```lean
#check Int.gcd_dvd_left -- ∀ (i j : ℤ), ↑(Int.gcd i j) ∣ i
#check Int.emod_add_ediv -- ∀ (a b : ℤ), a % b + b * (a / b) = a
#check Int.emod_eq_zero_of_dvd -- ∀ {a b : ℤ}, a ∣ b → b % a = 0
#check Int.dvd_mul_right -- ∀ (a b : ℤ), a ∣ a * b
#check Int.gcd_eq_gcd_ab -- ∀ (x y : ℤ), ↑(Int.gcd x y) = x * Int.gcdA x y + y * Int.gcdB x y
#check dvd_add /-∀ {α : Type u_1} [inst : Add α] [inst_1 : Semigroup α] [inst_2 : LeftDistribClass α] {a b c : α},
  a ∣ b → a ∣ c → a ∣ b + c-/
```
-/

#check Int.gcd_dvd_left -- ∀ (i j : ℤ), ↑(Int.gcd i j) ∣ i
#check Int.emod_add_ediv -- ∀ (a b : ℤ), a % b + b * (a / b) = a
#check Int.emod_eq_zero_of_dvd -- ∀ {a b : ℤ}, a ∣ b → b % a = 0
#check Int.dvd_mul_right -- ∀ (a b : ℤ), a ∣ a * b
#check Int.gcd_eq_gcd_ab -- ∀ (x y : ℤ), ↑(Int.gcd x y) = x * Int.gcdA x y + y * Int.gcdB x y
#check dvd_add /-∀ {α : Type u_1} [inst : Add α] [inst_1 : Semigroup α] [inst_2 : LeftDistribClass α] {a b c : α},
  a ∣ b → a ∣ c → a ∣ b + c-/

/--
Given `a b : ℤ` such that `b ∣ a`, we return an integer `q` such that `a = b * q`.
-/
def dvdQuotient (a b: Int)(h : b ∣ a) : {q : Int // a = b * q} := 
    let q := a / b
    ⟨q, by 
        symm
        apply Int.mul_ediv_cancel_of_emod_eq_zero
        apply Int.emod_eq_zero_of_dvd
        assumption
        ⟩

/-- If `a * x + b * y = c` has a solution, then `gcd a b` divides `c`.
-/
lemma eqn_solvable_iff_divides_gcd (a b c : ℤ) :
    (∃ x : ℤ, ∃ y : ℤ,  a * x + b * y = c) ↔  ↑(Int.gcd a b) ∣ c := by
    apply Iff.intro
    · intro ⟨x, y, h⟩
      rw [← h]
      apply dvd_add
      · trans a
        · apply Int.gcd_dvd_left  
        · apply Int.dvd_mul_right
      · trans b
        · apply Int.gcd_dvd_right  
        · apply Int.dvd_mul_right    
    · intro h
      let d := c / Int.gcd a b
      let h' : Int.gcd a b * d = c := by 
        apply Int.mul_ediv_cancel_of_emod_eq_zero
        apply Int.emod_eq_zero_of_dvd
        assumption
      use d * (Int.gcdA a b), d * (Int.gcdB a b)
      rw [← h', Int.gcd_eq_gcd_ab]
      linarith

/-- Solution or proof there is no solution for `a * x + b * y = c`  -/
def DiaphontineSolution.solve (a b c : ℤ) : DiaphontineSolution a b c := 
    if h : ↑(Int.gcd a b) ∣ c  
    then 
    by
        let ⟨d, h'⟩ := dvdQuotient (c: Int) (Int.gcd a b)  h 
        rw [Int.gcd_eq_gcd_ab a b] at h'
        rw [add_mul, mul_assoc, mul_assoc] at h'
        let x := (Int.gcdA a b * d)
        let y := (Int.gcdB a b * d)
        exact DiaphontineSolution.solution x y h'.symm         
    else
        by  
        apply DiaphontineSolution.unsolvable
        intro x y contra
        apply h
        apply eqn_solvable_iff_divides_gcd a b c |>.1
        use x, y
        assumption   

def span (a b : ℤ) : Set ℤ := {z | ∃ x y : ℤ, a * x + b * y = z}

abbrev inSpan (a b n : ℤ) := n ∈ span a b

instance decInSpan (a b n : ℤ) : Decidable (inSpan a b n) := by
  simp [eqn_solvable_iff_divides_gcd, inSpan, span]
  apply inferInstance

def spanGroup(a b : ℤ) : AddSubgroup ℤ  where
  carrier := {z | ∃ x y : ℤ, a * x + b * y = z}
  zero_mem' := by
    use 0, 0
    simp
  add_mem' := by
    intro z₁ z₂ h₁ h₂
    let ⟨x₁, y₁, eq₁⟩ := h₁
    let ⟨x₂, y₂, eq₂⟩ := h₂
    use x₁ + x₂, y₁ + y₂
    linarith
  neg_mem' := by
    intro z h
    let ⟨x, y, eq⟩ := h
    use -x, -y
    linarith [eq]

abbrev moduloSpan (a b : ℤ) := ℤ ⧸ (spanGroup a b)

theorem eq_zero_in_quot_iff (a b : ℤ)(n : ℤ) :
  (n : moduloSpan a b) = 0 ↔ ∃ x y : ℤ, a * x + b * y = n := by
    simp [moduloSpan, spanGroup, span]

abbrev zeroModSpan (a b n : ℤ) : Prop := 
  (QuotientAddGroup.mk n : moduloSpan a b) = (0 : moduloSpan a b)

#check QuotientGroup.mk

instance wordProblemMod (a b n : ℤ) : Decidable (zeroModSpan a b n) := by
  simp [moduloSpan, spanGroup, eqn_solvable_iff_divides_gcd]
  apply inferInstance

#synth (spanGroup 3 5).Normal -- AddSubgroup.normal_of_comm (spanGroup 3 5)
#synth AddCommGroup ℤ 

#eval decide (zeroModSpan 2 3 5) 

example (a b : ℕ) : Decidable (a ∣ b) := by
  apply inferInstance

set_option pp.all true in 
#check (Real.sqrt 2) ^ (Real.sqrt 2)
#check Real.instPowReal

example (a b c : ℝ)(h : 0 ≤ a) : a ^ (b * c) = (a ^ b) ^ c := by
  rw [Real.rpow_mul]
  assumption

example : 0 ≤ Real.sqrt 2 := by
  apply Real.sqrt_nonneg 

#check Real.rpow_add
#check Real.sqrt_pos


theorem sq2_pow_twice : ((Real.sqrt 2) ^ (Real.sqrt 2)) ^ (Real.sqrt 2) = 2 := by
  have two_nonneg : (2 : ℝ) ≥ 0 := by norm_cast
  have sq2_pos : (Real.sqrt 2) > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have sq2_nonneg : (Real.sqrt 2) ≥ 0 := by
    apply Real.sqrt_nonneg
  rw [← Real.rpow_mul sq2_nonneg, Real.mul_self_sqrt two_nonneg]
  have lm := Real.rpow_add sq2_pos 1 1
  have one_plus_one : (1: ℝ) + (1: ℝ) = 2 := by norm_cast
  rw [one_plus_one] at lm
  rw [lm]
  simp [Real.rpow_one]
  apply  Real.mul_self_sqrt
  exact two_nonneg

#check irrational_sqrt_two
#check irrational_iff_ne_rational

theorem exists_irrationals_pow_rational :
  ∃ a b : ℝ, (Irrational a) ∧ (Irrational b) ∧ ¬ (Irrational (a ^ b)) := by
    let b := Real.sqrt 2
    by_cases c:Irrational (b ^ b)
    · let a := b ^ b
      use a, b
      simp [irrational_sqrt_two, c, sq2_pow_twice]
      simp [irrational_iff_ne_rational]
      use 2, 1
      simp
    · use b, b
      simp [irrational_sqrt_two, c]

noncomputable def irrationalPairWithRationalPower : 
    {ab : ℝ × ℝ  // Irrational ab.1 ∧ Irrational ab.2 ∧ ¬ Irrational (ab.1 ^ ab.2)} := by
      apply Classical.choice
      let ⟨a, b, pf⟩ := exists_irrationals_pow_rational
      use (a, b)
      assumption

