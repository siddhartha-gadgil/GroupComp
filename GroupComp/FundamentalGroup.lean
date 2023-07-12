import GroupComp.Subgraph
import GroupComp.GroupLabelledGraph

variable {V E : Type _} {X : Graph V E} {Γ : SpanningSubtree X}
variable {G : Type _} [Group G]

open CategoryTheory

def inducedLabelling (φ : X.π₁ Γ.base →* G) : GroupLabelledGraph X G where
  label := φ ∘ Γ.surroundEdge
  label_bar e := by
    dsimp only [Function.comp_apply]
    rw [← map_inv, SpanningSubtree.surroundEdge_bar, Graph.π₁.inv_def]

lemma induced_label_eq_surround_map (e : X.EdgeBetween u v) : 
    (inducedLabelling (G := G) φ).label e = φ (Γ.surroundEdge e) := rfl

lemma label_path_map (φ : X.π₁ Γ.base →* G) {u v : V} (p : X.EdgePath u v) : 
    (inducedLabelling φ).pathLabel p = φ (Γ.surround [[p]]) := by
  induction p with
    | nil _ => rw [GroupLabelledGraph.pathLabel_nil, Graph.PathClass.nil_eq_id, SpanningSubtree.surround_nil, 
        Graph.π₁.one_def, map_one]
    | cons e p ih => simp only [Γ.surround_cons, GroupLabelledGraph.pathLabel_cons, ih, 
        Graph.π₁.mul_def, map_mul, mul_right_cancel_iff, induced_label_eq_surround_map]

theorem hom_induce_induce_eq_self (φ : X.π₁ Γ.base →* G) : 
    (inducedLabelling φ).inducedHom = φ := by
  ext x
  revert x
  apply Graph.PathClass.ind
  intro p
  simp only [GroupLabelledGraph.inducedHom, MonoidHom.coe_mk, OneHom.coe_mk, label_path_map,
    SpanningSubtree.surround_loop]