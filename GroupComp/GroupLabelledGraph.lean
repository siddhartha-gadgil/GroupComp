import GroupComp.Graph
import Mathlib.GroupTheory.IsFreeGroup

@[ext] structure GroupLabelledGraph {V E : Type _} (Γ : Graph V E) (G : Type _) [Group G] where
  label : E → G
  label_bar : ∀ e : E, label (Γ.bar e) = (label e)⁻¹


namespace GroupLabelledGraph

attribute [simp] label_bar

variable {V E G : Type _} {Γ : Graph V E} [Group G] {u v w : V} {g h : G} (𝓖 : GroupLabelledGraph Γ G)


def labelEdge (e : Γ.EdgeBetween u v) : G := 𝓖.label e.edge

@[simp] theorem labelEdge_bar (e : Γ.EdgeBetween u v) : 𝓖.labelEdge e.bar = (𝓖.labelEdge e)⁻¹ := by simp [labelEdge]


def pathLabel {u v : V} : Γ.EdgePath u v → G := Graph.EdgePath.fold 𝓖.label Mul.mul (1 : G) 

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

def inducedHom : Γ.π₁ v →* G where
  toFun := Quot.lift 𝓖.pathLabel 𝓖.pathLabel_reduction
  map_one' := rfl
  map_mul' := by
    apply Quot.ind; intro p
    apply Quot.ind; intro p'
    show pathLabel _ _ = _
    simp only [pathLabel_append]

end GroupLabelledGraph