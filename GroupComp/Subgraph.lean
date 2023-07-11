import GroupComp.Graph
import Mathlib.Data.SetLike.Basic

#check SetLike

structure Subgraph {V E : Type _} (G : Graph V E) where
  verts : Set V
  edges : Set E
  edges_bar : ∀ e ∈ edges, G.bar e ∈ edges
  edges_init : ∀ e ∈ edges, G.ι e ∈ verts 
  
namespace Subgraph

variable {V E : Type _} {G : Graph V E} (H : Subgraph G)

attribute [aesop safe apply] edges_bar edges_init

theorem edges_term : ∀ e ∈ H.edges, G.τ e ∈ H.verts := by
  intro e he 
  rw [← G.ι_bar e]
  apply H.edges_init
  apply H.edges_bar
  exact he

theorem bar_edges (e : E) (ebH : G.bar e ∈ H.edges) : e ∈ H.edges := by
  rw [← G.bar_involution e]
  apply edges_bar
  assumption

def coe : Graph H.verts H.edges where
  ι := fun ⟨e, eH⟩ ↦ ⟨G.ι e, H.edges_init _ eH⟩
  bar := fun ⟨e, eH⟩ ↦ ⟨G.bar e, H.edges_bar _ eH⟩
  bar_involution := by intro; simp only [Graph.bar_involution]
  bar_no_fp := by intro ⟨_, _⟩; simp [Graph.bar_no_fp]

def contains {u v : V} : G.EdgePath u v → Prop
  | .nil x => x ∈ H.verts
  | .cons e p => e.edge ∈ H.edges ∧ contains p

@[simp] theorem contains_nil : H.contains (.nil v) ↔ v ∈ H.verts := Iff.rfl 

@[simp] theorem contains_cons : H.contains (.cons e p) ↔ e.edge ∈ H.edges ∧ H.contains p := Iff.rfl

@[aesop safe apply] theorem contains_head (p : G.EdgePath u v) : H.contains p → u ∈ H.verts := by
  induction p with
  | nil => simp
  | cons e _ _ =>
    simp_rw [← e.source]
    aesop

@[aesop safe apply] theorem contains_tail (p : G.EdgePath u v) : H.contains p → v ∈ H.verts := by
  induction p <;> aesop 

@[simp] theorem contains_append {u v w : V} (p : G.EdgePath u v) (p' : G.EdgePath v w) : H.contains (p ++ p') ↔ H.contains p ∧ H.contains p' := by
  induction p <;> aesop    

instance : PartialOrder (Subgraph G) where
  le := sorry
  lt := sorry
  le_refl := sorry
  le_trans := sorry
  lt_iff_le_not_le := sorry
  le_antisymm := sorry

end Subgraph

structure PreconnectedSubgraph (G : Graph V E) extends Subgraph G where
  path : (u v : verts) → {p : G.EdgePath ↑u ↑v // toSubgraph.contains p}

structure PointedSubgraph {V E : Type _} (G : Graph V E) extends Subgraph G where
  basePoint : verts

structure Subtree (G : Graph V E) extends PreconnectedSubgraph G where
  path_unique : ∀ u v : verts, ∀ p : G.EdgePath u v, toSubgraph.contains p →
    [[p]] = [[(path u v).val]]

@[simp] theorem PreconnectedSubgraph.contains_path (H : PreconnectedSubgraph G) (u v : H.verts) : H.contains (H.path u v).val := 
  (H.path u v).property

attribute [aesop safe apply] Subtree.path_unique

open Graph.PathClass in
theorem Subtree.pathBetween_inv (Γ : Subtree G) (u v : Γ.verts) : 
    mul [[(Γ.path u v).val]] [[(Γ.path v u).val]] = .id _ := by
  rw [Graph.PathClass.mul_paths]
  trans ([[Γ.path u u]])
  · apply Γ.path_unique
    simp only [Subgraph.contains_append, PreconnectedSubgraph.contains_path, and_self]
  · symm
    apply Subtree.path_unique
    simp only [Subgraph.contains_nil, Subtype.coe_prop]

structure Graph.hom {V E V' E' : Type _} (G : Graph V E) (G' : Graph V' E') where
  vertexMap : V → V'
  edgeMap : E → E'
  preserve_init : ∀ e : E, vertexMap (G.ι e) = G'.ι (edgeMap e)
  preserve_bar : ∀ e : E, edgeMap (G.bar e) = G'.bar (edgeMap e)

namespace Graph.hom

variable {V E V' E' : Type _} (G : Graph V E) (G' : Graph V' E') (φ : Graph.hom G G')

theorem preserve_term (e : E) : φ.vertexMap (G.τ e) = G'.τ (φ.edgeMap e) := by
  rw [← G.ι_bar, ← G'.ι_bar, preserve_init, preserve_bar]

def edgeBetweenMap {u v : V} (e : G.EdgeBetween u v) : G'.EdgeBetween (φ.vertexMap u) (φ.vertexMap v) where
  edge := φ.edgeMap e.edge
  source := by
    have := φ.preserve_init e.edge
    rw [e.source] at this
    symm
    assumption
  target := by
    have := φ.preserve_term e.edge
    rw [e.target] at this
    symm
    assumption

def pathMap {u v : V} : G.EdgePath u v → G'.EdgePath (φ.vertexMap u) (φ.vertexMap v)
  | .nil _ => .nil _
  | .cons e p => .cons (φ.edgeBetweenMap e) (pathMap p)

def pathMap_append {u v w : V} (p : G.EdgePath u v) (p' : G.EdgePath v w) : 
    φ.pathMap (p ++ p') = φ.pathMap p ++ φ.pathMap p' := by
  induction p with
    | nil _ => rfl
    | cons e p ih => 
      dsimp [pathMap]
      congr
      apply ih

-- instance : @CategoryTheory.Functor V G.FundamentalGroupoid.toCategory V' G'.FundamentalGroupoid.toCategory := sorry
  
end Graph.hom

structure SpanningSubgraph {V E : Type _} (G : Graph V E) extends Subgraph G where
  spanning : verts = (⊤ : Set V)

attribute [simp] SpanningSubgraph.spanning

def SpanningSubgraph.coe {V E : Type _} {G : Graph V E} (H : SpanningSubgraph G) : Graph V H.edges :=
  let H' := H.spanning ▸ H.toSubgraph.coe
  { H' with ι := Subtype.val ∘ H'.ι }

structure SpanningSubtree (G : Graph V E) extends SpanningSubgraph G, Subtree G, PointedSubgraph G

namespace SpanningSubtree

variable {V E : Type _} {G : Graph V E} (Γ : SpanningSubtree G)

def base : V := Γ.basePoint.val

def coe : Graph V Γ.edges := Γ.toSpanningSubgraph.coe

abbrev vertex_coe (v : V) : Γ.verts := ⟨v, by simp⟩

open CategoryTheory

#check Category

def pathClassBetween (u v : V) : u ⟶ v := [[(Γ.toSubtree.path (Γ.vertex_coe u) (Γ.vertex_coe v)).val]]

@[simp] theorem contains_path {u v : V} : Γ.contains (Γ.path (Γ.vertex_coe u) (Γ.vertex_coe v)).val := 
  Γ.toSubtree.toPreconnectedSubgraph.contains_path (Γ.vertex_coe u) (Γ.vertex_coe v)

notation u " ⤳[" Γ "] " v  => pathClassBetween Γ u v 

def surround {u v : V} (p : u ⟶ v) : Γ.base ⟶ Γ.base :=
  (Γ.base ⤳[Γ] u) ≫ p ≫ (v ⤳[Γ] Γ.base)

def surroundEdge (e : E) := Γ.surround [[G.singletonPath e]]

@[simp] theorem tree_path_id {u : V} : (u ⤳[Γ] u) = 𝟙 u :=
  Eq.symm <| Γ.path_unique (Γ.vertex_coe u) (Γ.vertex_coe u) (.nil u) (by simp)

@[simp] theorem tree_path_comp {u v w : V} : (u ⤳[Γ] v) ≫ (v ⤳[Γ] w) = (u ⤳[Γ] w) := by
  apply Γ.path_unique (Γ.vertex_coe u) (Γ.vertex_coe w) 
  simp

@[simp] theorem tree_path_comp_right {u v w x : V} (p : w ⟶ x) :
    (u ⤳[Γ] v) ≫ (v ⤳[Γ] w) ≫ p = (u ⤳[Γ] w) ≫ p := by
  rw [← Category.assoc, tree_path_comp]

attribute [-simp] Graph.PathClass.comp_mul -- TODO ensure that this is removed in the source file

theorem opp_path_eq_inv {u v : V} : (u ⤳[Γ] v) = inv (v ⤳[Γ] u) := by
  rw [← hom_comp_eq_id]
  trans (v ⤳[Γ] v)
  <;> simp

@[simp] theorem surround_append {u v w : V} (p : u ⟶ v) (q : v ⟶ w) : 
    Γ.surround p ≫ Γ.surround q = Γ.surround (p ≫ q) := by
  simp [surround]

@[simp] theorem surround_loop (p : Γ.base ⟶ Γ.base) : Γ.surround p = p := by
  simp [surround]  

def surroundByEdges {u v : V} : G.EdgePath u v → G.π₁ Γ.base := 
  Graph.EdgePath.fold Γ.surroundEdge CategoryStruct.comp (1 : G.π₁ Γ.base) 

-- theorem surround_eq {u v : V} (p : u ⟶ v) : Γ.surround p = Γ.surroundByEdges p := by
--   induction p with
--   | nil _ => _
--   | cons e p ih => _

end SpanningSubtree