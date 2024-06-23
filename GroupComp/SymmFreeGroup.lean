import Mathlib
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Zorn
import Mathlib.Data.Set.Functor

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
  extends DFunLike F X fun _ ↦ Y where
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
  simp_all only [Bool.not_eq_true, Bool.xor_false]

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
      simp [DFunLike.coe, h]
    right_inv φ := by
      ext x
      simp [DFunLike.coe, φ.inv_map']

end OrientableInvolutiveInv

namespace Classical

variable {X : Type _} [ProperInvolutiveInv X]

def InvFreeSet (S : Set X) := ∀ x ∈ S, x⁻¹ ∉ S

variable (X) in
abbrev InvFreeSets := {S : Set X // InvFreeSet S}

instance : PartialOrder (InvFreeSets X) where
  le_antisymm S T hST hTS := by ext; aesop

attribute [local instance] Set.monad

def InvFreeSets.chainUnion (c : Set (InvFreeSets X)) (hcChain : IsChain (·.val ⊆ ·.val) c) : InvFreeSets X :=
  ⟨Monad.join (Subtype.val '' c), by
    intro x hxS hx'S
    simp only [Monad.join, joinM, Set.bind_def, Set.mem_image, exists_and_right, exists_eq_right, id_eq,
      Set.iUnion_exists, Set.mem_iUnion, exists_prop] at hxS hx'S
    have ⟨_, ⟨U, hUc, rfl⟩, hxU⟩ := hxS
    have ⟨_, ⟨V, hVc, rfl⟩, hxV⟩ := hx'S
    have hUV := hcChain hUc hVc
    by_cases h:U = V
    · subst h
      exact U.prop x ‹_› ‹_›
    · dsimp at hUV
      have hUV := hUV h
      cases hUV
      · have hxV : x ∈ V.val := by aesop
        exact V.prop x ‹_› ‹_›
      · have hx'U : x⁻¹ ∈ U.val := by aesop
        exact U.prop x ‹_› ‹_›
  ⟩

lemma InvFreeSets.chains_bounded_above (c : Set (InvFreeSets X))
    (hcChain : IsChain LE.le c) : BddAbove c := by
  dsimp [BddAbove, upperBounds]
  let sup := InvFreeSets.chainUnion c hcChain
  use sup
  intro A hAc
  simp only [LE.le, chainUnion, Monad.join, joinM, Set.bind_def, Set.mem_image, exists_and_right,
    exists_eq_right, id_eq, Set.iUnion_exists]
  -- the argument below is very low level
  intro x hxA
  use A
  refine' ⟨_, hxA⟩
  use A
  dsimp
  ext
  simp
  intro
  exact ⟨A.prop, hAc⟩


variable (X) in
noncomputable def ProperInvolutiveInv.maxInvFreeSet :=
  Classical.choose <| zorn_partialOrder <| InvFreeSets.chains_bounded_above (X := X)

theorem ProperInvolutiveInv.maxInvFreeSet_spec : ∀ S : InvFreeSets X,
    (maxInvFreeSet X).val ⊆ S.val → S = (maxInvFreeSet X) :=
  Classical.choose_spec <| zorn_partialOrder <| InvFreeSets.chains_bounded_above (X := X)

noncomputable def ProperInvolutiveInv.orientation : X → Bool :=
  fun x ↦ Decidable.decide (x ∈ (ProperInvolutiveInv.maxInvFreeSet X).val)

lemma ProperInvolutiveInv.maxInvFreeSet_mem_inv {x : X} :
    x ∉ (maxInvFreeSet X).val → x⁻¹ ∈ (maxInvFreeSet X).val := by
  intro h
  let C : InvFreeSets X :=
    ⟨(maxInvFreeSet X).val.insert x⁻¹, by
        simp only [Set.insert]
        intro a h
        simp only [Set.mem_setOf_eq] at h
        cases h
        · subst ‹a = x⁻¹›
          rw [ProperInvolutiveInv.toInvolutiveInv.inv_inv]
          simp [not_or]
          refine' ⟨_, h⟩
          exact ProperInvolutiveInv.no_fixed_points _
        · simp [not_or]
          constructor
          · rintro rfl
            contradiction
          · apply (maxInvFreeSet X).prop a ‹_›
    ⟩
  have : (maxInvFreeSet X).val ⊆ C.val := by
    show (maxInvFreeSet X).val ⊆ (maxInvFreeSet X).val.insert x⁻¹
    intro _; aesop (add norm simp [Set.insert])
  have := maxInvFreeSet_spec C this
  rw [← this]
  simp only [Set.insert, Set.mem_setOf_eq, true_or]

theorem ProperInvolutiveInv.selection (x : X) :
    xor (ProperInvolutiveInv.orientation x) (ProperInvolutiveInv.orientation x⁻¹) := by
  rw [@Bool.xor_iff_ne]
  dsimp [orientation]
  rw [@decide_eq_decide]
  intro hmem
  rw [@iff_eq_eq] at hmem
  by_cases hx:x ∈ (maxInvFreeSet X).val
  · exact (maxInvFreeSet X).prop x hx (hmem ▸ hx)
  · have :=  maxInvFreeSet_mem_inv hx
    rw [← hmem] at this
    contradiction

noncomputable scoped instance (priority := low) [ProperInvolutiveInv X] : OrientableInvolutiveInv X where
  pos := ProperInvolutiveInv.orientation (X := X)
  selection := ProperInvolutiveInv.selection

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
    simp [OrientableInvolutiveInv.lift, DFunLike.coe, EquivLike.coe, h]
    sorry

noncomputable instance [IsFreeGroup G] : SymmFreeGroup G (IsFreeGroup.Generators G ⊕ IsFreeGroup.Generators G) where
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
    dsimp
    rw [← h]
    show (IsFreeGroup.lift (ψ ∘ (IsFreeGroup.of ·))) = ψ
    apply IsFreeGroup.ext_hom
    simp

end SymmFreeGroup
