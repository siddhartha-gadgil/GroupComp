import GroupComp.Graph
import Mathlib.GroupTheory.IsFreeGroup

@[ext] structure GraphLabelledGroup {V E : Type _} (Γ : Graph V E) (G : Type _) [Group G] where
  label : E → G
  label_bar : ∀ e : E, label (Γ.bar e) = (label e)⁻¹


namespace GraphLabelledGroup

attribute [simp] label_bar

variable {V E G : Type _} {Γ : Graph V E} [Group G] {u v w : V} {g h : G} (𝓖 : GraphLabelledGroup Γ G)


def labelEdge (e : Γ.EdgeBetween u v) : G := 𝓖.label e.edge

@[simp] theorem labelEdge_bar (e : Γ.EdgeBetween u v) : 𝓖.labelEdge e.bar = (𝓖.labelEdge e)⁻¹ := by simp [labelEdge]


def pathLabel {u v : V} : Γ.EdgePath u v → G
  | .nil _ => 1
  | .cons e p => (𝓖.labelEdge e) * (pathLabel p)
 

@[simp] theorem pathLabel_nil {v : V} : 𝓖.pathLabel (.nil v) = (1 : G) := rfl

@[simp] theorem pathLabel_cons {u v w : V} (e : Γ.EdgeBetween u v) (p : Γ.EdgePath v w) : 
  𝓖.pathLabel (.cons e p) = (𝓖.labelEdge e) * (𝓖.pathLabel p) := rfl 

@[simp] theorem pathLabel_append {u v w : V} (p : Γ.EdgePath u v) (p' : Γ.EdgePath v w) :
    𝓖.pathLabel (p ++ p') = (𝓖.pathLabel p) * (𝓖.pathLabel p') := by
  induction p <;> aesop (add norm simp [mul_assoc])

@[simp] theorem pathLabel_concat {u v w : V} (p : Γ.EdgePath u v) (e : Γ.EdgeBetween v w) :
    𝓖.pathLabel (p.concat e) = 𝓖.pathLabel p * (𝓖.labelEdge e) := by
  induction p <;> aesop (add norm simp [Graph.EdgePath.concat, mul_assoc])

@[simp] theorem pathLabel_reverse {u v : V} (p : Γ.EdgePath u v) : 𝓖.pathLabel p.reverse = (𝓖.pathLabel p)⁻¹ := by
  induction p <;> aesop (add norm simp [Graph.EdgePath.reverse])

theorem pathLabel_reduction {u v : V} (p p' : Graph.EdgePath Γ u v) : Graph.EdgePath.Reduction p p' → 
    𝓖.pathLabel p = 𝓖.pathLabel p'
  | .step e p p' => by simp

#check Quot.induction_on₂

#check Quot.ind

def Quot.ind₂ {r : α → α → Prop} {β : Quot r → Quot r → Prop} (h : ∀ a a' : α, β (Quot.mk r a) (Quot.mk r a')) :
  ∀ q q' : Quot r, β q q' := sorry

def inducedHom : Γ.π₁ v →* G where
  toFun := Quot.lift 𝓖.pathLabel 𝓖.pathLabel_reduction
  map_one' := rfl
  map_mul' := by
    apply Quot.ind₂
    intro p p'
    simp


end GraphLabelledGroup