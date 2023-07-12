import Mathlib.GroupTheory.IsFreeGroup

#check IsFreeGroup

-- TODO Integrate this with the definition of a graph
class ProperInvolutiveInv (X : Type _) extends InvolutiveInv X where   
  no_fixed_points : ∀ x : X, x⁻¹ ≠ x

instance (X : Type _) : ProperInvolutiveInv (X ⊕ X) where
  inv := fun | .inl x => .inr x | .inr x => .inl x
  inv_inv := fun | .inl _ | .inr _ => rfl
  no_fixed_points := fun | .inl _ | .inr _ => Sum.noConfusion

-- defined in analogy with `MulHomClass`

@[ext] structure InvHom (X Y : Type _) [Inv X] [Inv Y] where
  toFun : X → Y
  inv_map' : ∀ x : X, toFun x⁻¹ = (toFun x)⁻¹

class InvHomClass (F : Type _) (X Y : outParam (Type _)) [Inv X] [Inv Y] 
  extends FunLike F X fun _ ↦ Y where 
  inv_map : ∀ f : F, ∀ x : X, f x⁻¹ = (f x)⁻¹

instance InvHom.invHomClass [Inv X] [Inv Y] : InvHomClass (InvHom X Y) X Y where
  coe := InvHom.toFun
  coe_injective' _ _ h := by ext; apply congrFun h
  inv_map := InvHom.inv_map'

infix:25 " →⁻¹ " => InvHom

def InvHom.comp [Inv X] [Inv Y] [Inv Z] (f : X →⁻¹ Y) (g : Y →⁻¹ Z) : X →⁻¹ Z where
  toFun := g.toFun ∘ f.toFun
  inv_map' _ := by dsimp; rw [f.inv_map', g.inv_map']

instance MonoidHom.toInvHom [Group G] [Group H] (φ : G →* H) : G →⁻¹ H where
  toFun := φ.toFun
  inv_map' _ := by simp

/-- The definition of a free group on a symmetric generating set. -/
class SymmFreeGroup (G : Type _) [Group G] (X : Type _) [ProperInvolutiveInv X] where
  ι : X →⁻¹ G
  induced {H : Type _} [Group H] (φ : X →⁻¹ H) : G →* H
  induced_is_lift {H : Type _} [Group H] (φ : X →⁻¹ H) : ι.comp (induced φ).toInvHom = φ 
  lift_unique {H : Type _} [Group H] (φ : X →⁻¹ H) : ∀ ψ : G →* H, ι.comp ψ.toInvHom = φ → induced φ = ψ

namespace SymmFreeGroup

variable [Group G] [ProperInvolutiveInv X] [𝓕 : SymmFreeGroup G X] [Group H]

theorem induced_restrict_eq_iff_lift_unique :
    (∀ ψ : G →* H, 𝓕.induced (𝓕.ι.comp ψ.toInvHom) = ψ) ↔
    (∀ φ : X →⁻¹ H, ∀ ψ : G →* H, (𝓕.ι.comp ψ.toInvHom = φ) → 𝓕.induced φ = ψ) := by
  constructor
  · intro h φ ψ hres
    exact hres ▸ (h ψ)
  · intro h ψ
    exact h (𝓕.ι.comp ψ.toInvHom) ψ rfl   

def lift : (X →⁻¹ H) ≃ (G →* H) where
  toFun := SymmFreeGroup.induced
  invFun := fun φ ↦ SymmFreeGroup.ι.comp φ.toInvHom
  left_inv := SymmFreeGroup.induced_is_lift
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse, induced_restrict_eq_iff_lift_unique]
    apply SymmFreeGroup.lift_unique

set_option synthInstance.checkSynthOrder false in -- HACK
instance [SymmFreeGroup G X] : IsFreeGroup G := sorry

instance [IsFreeGroup G] : SymmFreeGroup G (IsFreeGroup.Generators G ⊕ IsFreeGroup.Generators G) where
  ι := 
    { toFun := fun 
        | .inl g => IsFreeGroup.of g 
        | .inr g => (IsFreeGroup.of g)⁻¹
      inv_map' := by intro x; cases x <;> simp }
  induced φ := IsFreeGroup.lift.toFun (φ ∘ .inl) 
  induced_is_lift φ := by
    ext x
    cases x
    · simp [InvHom.comp, InvHom.toFun, MonoidHom.toInvHom]
      rfl
    · rename_i g
      simp [InvHom.comp, InvHom.toFun, MonoidHom.toInvHom]
      have := Eq.symm <| φ.inv_map' (.inl g)
      simp [Inv.inv] at this
      assumption
  lift_unique φ ψ := by
    intro h
    ext g
    simp
    rw [← h]
    rfl

end SymmFreeGroup