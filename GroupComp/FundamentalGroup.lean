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

@[simp] lemma induced_label_eq_surround_map (e : X.EdgeBetween u v) :
    (inducedLabelling (G := G) φ).label e = φ (Γ.surroundEdge e) := rfl

@[simp] lemma label_path_map (φ : X.π₁ Γ.base →* G) {u v : V} (p : X.EdgePath u v) :
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
  simp only [GroupLabelledGraph.inducedHom, MonoidHom.coe_mk, OneHom.coe_mk,
    GroupLabelledGraph.pathClassLabel_of_pathLabel, label_path_map, Graph.SpanningSubtree.surround_loop]

namespace Graph

instance : ProperInvolutiveInv E where
  inv := X.bar
  inv_inv := X.bar_bar
  no_fixed_points := X.bar_ne_self

instance (H : Subgraph X) : ProperInvolutiveInv ↑H.edges where
  inv e := ⟨X.bar e.val, H.edges_bar e e.prop⟩
  inv_inv := by
    intro; ext
    apply X.bar_bar
  no_fixed_points := by
    intro ⟨_, _⟩ h
    apply X.bar_ne_self
    simp at h
    assumption

instance (H : Subgraph X) : ProperInvolutiveInv ↑(H.edgesᶜ) where
  inv e := ⟨X.bar e.val, by
    intro h; apply e.prop
    apply H.bar_edges; assumption⟩
  inv_inv := by
    intro; ext
    simp only [bar_bar, Subtype.coe_eta]
  no_fixed_points := by
    intro _
    apply Subtype.ne_of_val_ne
    apply X.bar_ne_self

abbrev SpanningSubtree.ofOutEdge : ↑(Γ.edgesᶜ) →⁻¹ X.π₁ Γ.base where
  toFun e := Γ.surroundEdge (EdgeBetween.ofEdge e.val)
  inv_map' := by simp [Inv.inv, Graph.PathClass.inv_eq_inv]

variable {H : Type _} [Group H]
variable  [∀ {u v : V} (e : X.EdgeBetween u v), Decidable (e.edge ∈ Γ.edges)]

abbrev SpanningSubtree.edgeLabelExtension (φ : ↑(Γ.edgesᶜ) →⁻¹ H) : GroupLabelledGraph X H := {
    label := fun e ↦
    if h : e.edge ∈ Γ.edges then
      (1 : _)
    else
      φ ⟨e.edge, h⟩
    label_bar := by
      intro _ _ ⟨e, _, _⟩
      by_cases h : e ∈ Γ.edges
      · have : X.bar e ∈ Γ.edges := Γ.edges_bar e h
        simp only [EdgeBetween.bar_eq_bar, this, dite_true, h, inv_one]
      · have : X.bar e ∉ Γ.edges := h ∘ (Γ.bar_edges e)
        simp only [EdgeBetween.bar_eq_bar, this, dite_false, h]
        erw [← φ.inv_map']; rfl
  }


abbrev SpanningSubtree.inducedMap (φ : ↑(Γ.edgesᶜ) →⁻¹ H) : X.π₁ Γ.base →* H :=
  (Γ.edgeLabelExtension φ).inducedHom

@[simp] theorem pathLabel_on_tree_path {u v : V} (p : X.EdgePath u v) (hpΓ : Γ.contains p) :
    (Γ.edgeLabelExtension φ).pathLabel p = (1 : H) := by
  induction p with
    | nil _ => simp
    | cons _ _ ih => simp_all [ih]

@[simp] theorem pathClassLabel_on_tree_path {u v : V} :
    (Γ.edgeLabelExtension φ).pathClassLabel (u ⤳[Γ] v) = (1 : H) := by
  show (Γ.edgeLabelExtension φ).pathClassLabel ([[_]]) = _
  simp only [GroupLabelledGraph.pathClassLabel_of_pathLabel, SpanningSubtree.contains_path, pathLabel_on_tree_path]

@[instance]
def freeFundamentalGroupSymm [∀ {u v : V} (e : X.EdgeBetween u v), Decidable (e.edge ∈ Γ.edges)] : -- TODO remove instance
    SymmFreeGroup (X.π₁ Γ.base) ↑(Γ.edgesᶜ) where
  ι := Γ.ofOutEdge
  induced := Γ.inducedMap
  induced_is_lift := by
    intro H _ φ
    ext ⟨e, h⟩
    have h' : ¬(e ∈ Γ.edges) := h
    show (Γ.inducedMap φ) (Γ.surroundEdge _) = _
    dsimp [SpanningSubtree.surroundEdge, SpanningSubtree.surround, SpanningSubtree.inducedMap, GroupLabelledGraph.inducedHom]
    simp [h']
    rfl
  lift_unique := by
    intro H _
    rw [← SymmFreeGroup.induced_restrict_eq_iff_lift_unique (H := H) Γ.ofOutEdge Γ.inducedMap]
    intro ψ
    rw [← hom_induce_induce_eq_self ψ, SpanningSubtree.inducedMap]
    congr
    rw [hom_induce_induce_eq_self ψ]
    ext u v e
    dsimp [SpanningSubtree.edgeLabelExtension]
    split
    · rw [SpanningSubtree.surround_tree_edge, ← map_one ψ]
      rfl; assumption
    · show ψ.toFun (Γ.surroundEdge _) = ψ.toFun (Γ.surroundEdge _)
      congr 1
      apply Γ.surroundEdge_cast <;>
      simp [EdgeBetween.init_eq, EdgeBetween.term_eq]

namespace Classical

noncomputable instance : OrientableInvolutiveInv (↑Γ.edgesᶜ) := Classical.instOrientableInvolutiveInv

-- A proof that the fundamental group of a graph is free,
-- which will work once it is shown that any `ProperInvolutiveInv` can be given an orientation
noncomputable def freeFundamentalGroup : IsFreeGroup (X.π₁ Γ.base) :=
  @SymmFreeGroup.toFreeGroup _ _ _ _ freeFundamentalGroupSymm

end Classical


open PathClass

def wedgeCircles.spanningSubTree (S : Type _) : SpanningSubtree (wedgeCircles S) where
  verts := ⊤
  edges := ⊥
  edges_bar := by aesop
  edges_init := by aesop
  spanning := by aesop
  path := fun _ _ ↦ ⟨.nil (), by simp⟩
  path_unique := by
    intro _ _ p
    cases p <;> simp
  basePoint := ⟨(), trivial⟩

instance [DecidableEq S] : ∀ {u v : Unit} (e : (wedgeCircles S).EdgeBetween u v),
  Decidable (e.edge ∈ (wedgeCircles.spanningSubTree S).edges) :=
    fun e ↦ Decidable.isFalse <| by
      show e.edge ∉ ∅
      simp only [Set.mem_empty_iff_false, not_false_eq_true]

instance wedgeCircles.isSymmFreeGroup (S : Type _) [DecidableEq S] :
    SymmFreeGroup ((wedgeCircles S).π₁ ()) ↑(wedgeCircles.spanningSubTree S).edgesᶜ :=
  freeFundamentalGroupSymm (Γ := wedgeCircles.spanningSubTree S)

instance wedgeCircles.isFreeGroup (S : Type _) [DecidableEq S] : IsFreeGroup ((wedgeCircles S).π₁ ()) := sorry

end Graph
