import GroupComp.Graph
import Mathlib.GroupTheory.IsFreeGroup

@[ext] structure GroupLabelledGraph {V E : Type _} (Γ : Graph V E) (G : Type _) [Group G] where
  label : {u v : V} → Γ.EdgeBetween u v → G
  label_bar : ∀ {u v : V}, ∀ e : Γ.EdgeBetween u v, label e.bar = (label e)⁻¹


namespace GroupLabelledGraph

attribute [simp] label_bar

variable {V E G : Type _} {Γ : Graph V E} [Group G] {u v w : V} {g h : G} (𝓖 : GroupLabelledGraph Γ G)

def pathLabel {u v : V} : Γ.EdgePath u v → G := Graph.EdgePath.fold 𝓖.label Mul.mul (1 : G) 

@[simp] theorem pathLabel_nil {v : V} : 𝓖.pathLabel (.nil v) = (1 : G) := rfl

@[simp] theorem pathLabel_cons {u v w : V} (e : Γ.EdgeBetween u v) (p : Γ.EdgePath v w) : 
  𝓖.pathLabel (.cons e p) = (𝓖.label e) * (𝓖.pathLabel p) := rfl 

@[simp] theorem pathLabel_append {u v w : V} (p : Γ.EdgePath u v) (p' : Γ.EdgePath v w) :
    𝓖.pathLabel (p ++ p') = (𝓖.pathLabel p) * (𝓖.pathLabel p') := by
  induction p <;> aesop (add norm simp [mul_assoc])

@[simp] theorem pathLabel_concat {u v w : V} (p : Γ.EdgePath u v) (e : Γ.EdgeBetween v w) :
    𝓖.pathLabel (p.concat e) = 𝓖.pathLabel p * (𝓖.label e) := by
  induction p <;> aesop (add norm simp [Graph.EdgePath.concat, mul_assoc])

@[simp] theorem pathLabel_reverse {u v : V} (p : Γ.EdgePath u v) : 𝓖.pathLabel p.reverse = (𝓖.pathLabel p)⁻¹ := by
  induction p <;> aesop (add norm simp [Graph.EdgePath.reverse])

theorem pathLabel_reduction {u v : V} (p p' : Graph.EdgePath Γ u v) : Graph.EdgePath.Reduction p p' → 
    𝓖.pathLabel p = 𝓖.pathLabel p'
  | .step e p p' => by simp

@[simp] theorem pathLabel_singletonPath (e : Γ.EdgeBetween u v) : 
  𝓖.pathLabel (Γ.singletonPath e) = 𝓖.label e := by simp

open CategoryTheory

def pathClassLabel : {u v : V} → (u ⟶ v) → G := 
  Quot.lift 𝓖.pathLabel 𝓖.pathLabel_reduction

@[simp] theorem pathClassLabel_one {u : V} : 𝓖.pathClassLabel (𝟙 u) = (1 : G) := rfl

@[simp] theorem pathClassLabel_append {u v w : V} : ∀ (p : u ⟶ v) (p' : v ⟶ w), 
    𝓖.pathClassLabel (p ≫ p') = 𝓖.pathClassLabel p * 𝓖.pathClassLabel p' := by
  apply Quot.ind; intro p
  apply Quot.ind; intro p'
  show 𝓖.pathLabel (_ ++ _) = _
  simp only [pathLabel_append, pathClassLabel]

@[simp] lemma pathClassLabel_of_pathLabel (p : Γ.EdgePath u v) :
  𝓖.pathClassLabel [[p]] = 𝓖.pathLabel p := rfl
  
abbrev inducedHom : Γ.π₁ v →* G where
  toFun := 𝓖.pathClassLabel
  map_one' := 𝓖.pathClassLabel_one
  map_mul' := 𝓖.pathClassLabel_append

end GroupLabelledGraph