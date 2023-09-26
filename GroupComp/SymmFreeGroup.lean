import Mathlib.GroupTheory.IsFreeGroup
import Mathlib.Data.Bool.Basic

#check IsFreeGroup

-- TODO Integrate this with the definition of a graph
class ProperInvolutiveInv (X : Type _) extends InvolutiveInv X where   
  no_fixed_points : ∀ x : X, x ≠ x⁻¹

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

class OrientableInvolutiveInv (X : Type _) extends InvolutiveInv X where
  pos : X → Bool
  selection : ∀ x : X, xor (pos x) (pos x⁻¹) 

namespace OrientableInvolutiveInv

variable (X : Type _) [OrientableInvolutiveInv X] (x x' : X)

@[simp] lemma no_fixed_points : pos x ≠ pos x⁻¹ := by
  intro h
  have := h ▸ selection x
  simp_all only [Bool.xor_self]

@[simp] lemma not_pos_inv_of_pos (h : pos x) : ¬(pos x⁻¹) := by
  have := h ▸ selection x
  simp_all only [Bool.true_xor, Bool.not_eq_true', not_false_eq_true]

@[simp] lemma pos_of_not_pos_inv (h : ¬(pos x⁻¹)) : pos x := by
  have := selection x
  simp_all only [Bool.not_eq_true, Bool.xor_false_right]

instance (priority := high) : ProperInvolutiveInv X where
  no_fixed_points x := by 
    apply ne_of_apply_ne pos
    simp only [ne_eq, no_fixed_points, not_false_eq_true]

def orientation := {x : X // pos x}

def lift [InvolutiveInv Y] : (orientation X → Y) ≃ (X →⁻¹ Y) where
    toFun f := {
      toFun := fun x ↦
        if h:pos x then
          f ⟨x, h⟩
        else
          (f ⟨x⁻¹, by simp [h]⟩)⁻¹ 
      inv_map' := by
        intro x
        by_cases h : pos x <;>
        simp [h]
    }        
    invFun φ := fun ⟨x, _⟩ ↦ φ x
    left_inv f := by
      ext ⟨x, h⟩
      simp [FunLike.coe, h]
    right_inv φ := by
      ext x
      simp [FunLike.coe, φ.inv_map']

end OrientableInvolutiveInv

namespace Classical

noncomputable scoped instance (priority := low) [ProperInvolutiveInv X] : OrientableInvolutiveInv X := sorry

end Classical

/-- The definition of a free group on a symmetric generating set. -/
class SymmFreeGroup (G : Type _) [Group G] (X : Type _) [ProperInvolutiveInv X] where
  ι : X →⁻¹ G
  induced {H : Type _} [Group H] (φ : X →⁻¹ H) : G →* H
  induced_is_lift {H : Type _} [Group H] (φ : X →⁻¹ H) : ι.comp (induced φ).toInvHom = φ 
  lift_unique {H : Type _} [Group H] (φ : X →⁻¹ H) : ∀ ψ : G →* H, ι.comp ψ.toInvHom = φ → induced φ = ψ

namespace SymmFreeGroup

variable [Group G] [ProperInvolutiveInv X] [Group H]

theorem induced_restrict_eq_iff_lift_unique (ι : X →⁻¹ G) (ind : {H : Type _} → [Group H] → (X →⁻¹ H) → (G →* H)) :
    (∀ ψ : G →* H, ind (ι.comp ψ.toInvHom) = ψ) ↔
    (∀ φ : X →⁻¹ H, ∀ ψ : G →* H, (ι.comp ψ.toInvHom = φ) → ind φ = ψ) := by
  constructor
  · intro h φ ψ hres
    exact hres ▸ (h ψ)
  · intro h ψ
    exact h (ι.comp ψ.toInvHom) ψ rfl   

def lift [SymmFreeGroup G X] : (X →⁻¹ H) ≃ (G →* H) where
  toFun := SymmFreeGroup.induced
  invFun := fun φ ↦ SymmFreeGroup.ι.comp φ.toInvHom
  left_inv := SymmFreeGroup.induced_is_lift
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse, induced_restrict_eq_iff_lift_unique]
    apply SymmFreeGroup.lift_unique

set_option synthInstance.checkSynthOrder false in -- HACK
@[instance] def toFreeGroup {X : Type _} [OrientableInvolutiveInv X] [SymmFreeGroup G X] : IsFreeGroup G :=
  IsFreeGroup.ofLift 
    (OrientableInvolutiveInv.orientation X) 
    ((OrientableInvolutiveInv.lift X).invFun SymmFreeGroup.ι) 
    (Equiv.trans (OrientableInvolutiveInv.lift X) (SymmFreeGroup.lift)) 
    <| by
    intro H _ f ⟨x, h⟩
    simp [lift]
    let φ := (OrientableInvolutiveInv.lift X (Y := H)).toFun f
    show (InvHom.comp ι (MonoidHom.toInvHom (induced φ))) _ = _
    rw [induced_is_lift (G := G) φ]
    simp [OrientableInvolutiveInv.lift, FunLike.coe, EquivLike.coe, h]

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