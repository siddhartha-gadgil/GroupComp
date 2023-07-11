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
  inv_map' x := by dsimp; rw [f.inv_map', g.inv_map']

instance MonoidHom.toInvHom [Group G] [Group H] (φ : G →* H) : G →⁻¹ H where
  toFun := φ.toFun
  inv_map' x := by simp

/-- The definition of a free group on a symmetric generating set. -/
class SymmFreeGroup (G : Type _) [Group G] (X : Type _) [ProperInvolutiveInv X] where
  ι : X →⁻¹ G
  induced {H : Type _} [Group H] (φ : X →⁻¹ H) : G →* H
  induced_is_lift {H : Type _} [Group H] (φ : X →⁻¹ H) : ι.comp (induced φ).toInvHom = φ 
  lift_unique {H : Type _} [Group H] (φ : X →⁻¹ H) : ∀ ψ : G →* H, ι.comp (induced φ).toInvHom = φ → ψ = induced φ

namespace SymmFreeGroup

variable [Group G] [ProperInvolutiveInv X] [SymmFreeGroup G X] [Group H]

-- theorem induced_restrict_eq_iff_lift_unique : 
--   (∀ ψ : G →* H, SymmFreeGroup.induced (SymmFreeGroup.ι.comp ψ.toInvHom) = φ) ↔
--     (∀ φ : X →⁻¹ H, ∀ ψ : G →* H, (SymmFreeGroup.ι.comp (SymmFreeGroup.induced φ).toInvHom = φ) → (ψ = induced φ)) := sorry
  

def lift [Group G] [ProperInvolutiveInv X] [SymmFreeGroup G X] [Group H] : (X →⁻¹ H) ≃ (G →* H) where
  toFun := SymmFreeGroup.induced
  invFun := fun φ ↦ SymmFreeGroup.ι.comp φ.toInvHom
  left_inv := SymmFreeGroup.induced_is_lift
  right_inv φ := by
    sorry

end SymmFreeGroup