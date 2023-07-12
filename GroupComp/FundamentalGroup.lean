import GroupComp.Subgraph
import GroupComp.GroupLabelledGraph
import GroupComp.SymmFreeGroup

variable {V E : Type _} {X : Graph V E} {Γ : Graph.SpanningSubtree X}
variable {G : Type _} [Group G]

open CategoryTheory

def inducedLabelling (φ : X.π₁ Γ.base →* G) : GroupLabelledGraph X G where
  label := φ ∘ Γ.surroundEdge
  label_bar e := by
    dsimp only [Function.comp_apply]
    rw [← map_inv, Γ.surroundEdge_bar, Graph.π₁.inv_def]

lemma induced_label_eq_surround_map (e : X.EdgeBetween u v) : 
    (inducedLabelling (G := G) φ).label e = φ (Γ.surroundEdge e) := rfl

lemma label_path_map (φ : X.π₁ Γ.base →* G) {u v : V} (p : X.EdgePath u v) : 
    (inducedLabelling φ).pathLabel p = φ (Γ.surround [[p]]) := by
  induction p with
    | nil _ => rw [GroupLabelledGraph.pathLabel_nil, Graph.PathClass.nil_eq_id, Γ.surround_nil, 
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
    Γ.surround_loop]

namespace Graph

instance : ProperInvolutiveInv E where
  inv := X.bar
  inv_inv := X.bar_involution
  no_fixed_points := X.bar_no_fp

instance (H : Subgraph X) : ProperInvolutiveInv ↑H.edges where
  inv e := ⟨X.bar e.val, H.edges_bar e e.prop⟩
  inv_inv := by
    intro; ext
    apply X.bar_involution
  no_fixed_points := by
    intro ⟨_, _⟩ h
    apply X.bar_no_fp
    simp at h
    assumption

instance (H : Subgraph X) : ProperInvolutiveInv ↑(H.edgesᶜ) where
  inv e := ⟨X.bar e.val, by
    intro h; apply e.prop
    apply H.bar_edges; assumption⟩
  inv_inv := by
    intro; ext
    simp only [bar_involution, Subtype.coe_eta]
  no_fixed_points := by
    intro _
    apply Subtype.ne_of_val_ne
    apply X.bar_no_fp

abbrev SpanningSubtree.ofOutEdge : ↑(Γ.edgesᶜ) →⁻¹ X.π₁ Γ.base where
  toFun e := Γ.surroundEdge (EdgeBetween.ofEdge e.val) 
  inv_map' := by simp [Inv.inv, Graph.PathClass.inv_eq_inv]

abbrev SpanningSubtree.inducedMap 
  [∀ {u v : V} (e : X.EdgeBetween u v), Decidable (e.edge ∈ Γ.edgesᶜ)]
  [Group H] (φ : ↑(Γ.edgesᶜ) →⁻¹ H) : X.π₁ Γ.base →* H := 
  GroupLabelledGraph.inducedHom {
    label := fun e ↦
      if h : e.edge ∈ Γ.edgesᶜ then
        φ ⟨e.edge, h⟩
      else (1 : _) 
    label_bar := by
      intro _ _ ⟨e, _, _⟩
      dsimp
      sorry
  }

instance [∀ {u v : V} (e : X.EdgeBetween u v), Decidable (e.edge ∈ Γ.edgesᶜ)] : -- TODO remove instance 
    SymmFreeGroup (X.π₁ Γ.base) ↑(Γ.edgesᶜ) where
  ι := Γ.ofOutEdge
  induced := Γ.inducedMap 
  induced_is_lift := by
    intro H _ φ
    ext ⟨e, h⟩
    show (Γ.inducedMap φ) (Γ.surroundEdge _) = _
    -- simp [SpanningSubtree.inducedMap]
    sorry
  lift_unique := by
    intro H _ 
    rw [← SymmFreeGroup.induced_restrict_eq_iff_lift_unique (H := H) Γ.ofOutEdge Γ.inducedMap]
    intro ψ
    rw [← hom_induce_induce_eq_self ψ, SpanningSubtree.inducedMap]
    congr
    rw [hom_induce_induce_eq_self ψ]
    ext u v e
    split
    · show ψ.toFun (Γ.surroundEdge _) = ψ.toFun (Γ.surroundEdge _)
      congr 1
      dsimp
      apply Γ.surroundEdge_cast <;> simp
    · rename_i h
      simp only [Set.mem_compl_iff, not_not] at h
      simp
      sorry -- use `surround_tree_edge`
        
    

end Graph