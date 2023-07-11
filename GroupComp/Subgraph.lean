import GroupComp.Graph
import Mathlib.Data.SetLike.Basic

#check SetLike

structure Subgraph {V E : Type _} (G : Graph V E) where
  verts : Set V
  edges : Set E
  edges_bar : ∀ e ∈ edges, G.bar e ∈ edges
  edges_init : ∀ e ∈ edges, G.ι e ∈ verts 
  
namespace Subgraph

variable {V E : Type _} (G : Graph V E) (H : Subgraph G)

-- attribute [aesop safe apply] edges_bar edges_init

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

def coe {G : Graph V E} (H : Subgraph G) : Graph H.verts H.edges where
  ι := fun ⟨e, eH⟩ ↦ ⟨G.ι e, H.edges_init _ eH⟩
  bar := fun ⟨e, eH⟩ ↦ ⟨G.bar e, H.edges_bar _ eH⟩
  bar_involution := by intro; simp only [Graph.bar_involution]
  bar_no_fp := by intro ⟨_, _⟩; simp [Graph.bar_no_fp]

end Subgraph

structure PreconnectedSubgraph (G : Graph V E) extends Subgraph G where
  pathBetween : (u v : verts) → (Subgraph.coe _).EdgePath u v

structure Subtree (G : Graph V E) extends PreconnectedSubgraph G where
  path_unique : ∀ u v : verts, ∀ p : (Subgraph.coe _).EdgePath u v, 
    [[p]] = [[pathBetween u v]]

theorem Subtree.pathBetween_inv (Γ : Subtree G) (u v : Γ.verts) : 
    Γ.coe.FundamentalGroupoid.comp [[Γ.pathBetween u v]] [[Γ.pathBetween v u]] = Γ.coe.FundamentalGroupoid.id u := by
  show [[_ ++ _]] = [[_]]
  trans
  · apply Γ.path_unique
  · symm; apply Γ.path_unique

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

instance : @CategoryTheory.Functor V G.FundamentalGroupoid.toCategory V' G'.FundamentalGroupoid.toCategory := sorry
  
end Graph.hom

structure SpanningSubgraph {V E : Type _} (G : Graph V E) extends Subgraph G where
  spanning : verts = (⊤ : Set V)

def SpanningSubgraph.coe {V E : Type _} {G : Graph V E} (H : SpanningSubgraph G) : Graph V H.edges :=
  let H' := H.spanning ▸ H.toSubgraph.coe
  { H' with ι := Subtype.val ∘ H'.ι }

structure SpanningSubtree (G : Graph V E) extends SpanningSubgraph G, Subtree G

namespace SpanningSubtree

variable {V E : Type _} (G : Graph V E) (Γ : SpanningSubtree G)

def coe := Γ.toSpanningSubgraph.coe

end SpanningSubtree

def Graph.spanningTree (G : Graph V E) : SpanningSubtree G := sorry