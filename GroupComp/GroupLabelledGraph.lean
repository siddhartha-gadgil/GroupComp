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

@[simp] theorem pathLabel_append {u v w : V} : (p : Γ.EdgePath u v) → (p' : Γ.EdgePath v w) → 
    𝓖.pathLabel (p ++ p') = (𝓖.pathLabel p) * (𝓖.pathLabel p')
  | .nil _, _ => by simp?
  | .cons e p, _ => by
    simp only [pathLabel, mul_assoc, mul_right_inj]
    apply pathLabel_append

@[simp] theorem pathLabel_concat {u v w : V} : (p : Γ.EdgePath u v) → (e : Γ.EdgeBetween v w) →
    𝓖.pathLabel (p.concat e) = 𝓖.pathLabel p * (𝓖.labelEdge e)
  | .nil _, _ => by simp [Graph.EdgePath.concat, pathLabel]
  | .cons e p, _ => by
    simp [Graph.EdgePath.concat, pathLabel, mul_assoc]
    apply pathLabel_concat

@[simp] theorem pathLabel_reverse {u v : V} : (p : Γ.EdgePath u v) → 𝓖.pathLabel p.reverse = (𝓖.pathLabel p)⁻¹
  | .nil _ => by simp
  | .cons e p => by
    simp [Graph.EdgePath.reverse, pathLabel]
    apply pathLabel_reverse

def loopMap : Γ.EdgePath v v → G := sorry

def inducedHom : π₁(Γ, v) →* G where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry

end GraphLabelledGroup