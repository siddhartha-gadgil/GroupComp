import GroupComp.Graph
import Mathlib.Data.SetLike.Basic

namespace Graph

@[ext]
structure Subgraph {V E : Type _} (G : Graph V E) where
  verts : Set V
  edges : Set E
  edges_bar : ∀ e ∈ edges, G.bar e ∈ edges
  edges_init : ∀ e ∈ edges, G.ι e ∈ verts

namespace Subgraph

variable {V E : Type _} {G : Graph V E} (H : Subgraph G)

attribute [aesop safe apply] edges_bar edges_init

theorem edges_terminal : ∀ e ∈ H.edges, G.τ e ∈ H.verts := by
  intro e he
  rw [← G.ι_bar e]
  apply H.edges_init
  apply H.edges_bar
  exact he

theorem bar_edges (e : E) (ebH : G.bar e ∈ H.edges) : e ∈ H.edges := by
  rw [← G.bar_bar e]
  apply edges_bar
  assumption

def coe : Graph H.verts H.edges where
  ι := fun ⟨e, eH⟩ ↦ ⟨G.ι e, H.edges_init _ eH⟩
  bar := fun ⟨e, eH⟩ ↦ ⟨G.bar e, H.edges_bar _ eH⟩
  bar_bar := by intro; simp only [Graph.bar_bar]
  bar_ne_self := by intro ⟨_, _⟩; simp [Graph.bar_ne_self]

def contains {u v : V} : G.EdgePath u v → Prop
  | .nil x => x ∈ H.verts
  | .cons e p => e.edge ∈ H.edges ∧ contains p

@[simp] theorem contains_nil : H.contains (.nil v) ↔ v ∈ H.verts := Iff.rfl

@[simp] theorem contains_cons : H.contains (.cons e p) ↔ e.edge ∈ H.edges ∧ H.contains p := Iff.rfl

@[simp] theorem contains_concat : H.contains (.concat p e) ↔ e.edge ∈ H.edges ∧ H.contains p := by
  induction p with
    | nil =>
      rw [EdgePath.concat]
      simp only [contains_cons, contains_nil, and_congr_right_iff]
      intro he
      have := e.init_eq ▸ H.edges_init e.edge he
      have := e.term_eq ▸ H.edges_terminal e.edge he
      simp_all only
    | cons e p' ih =>
      rw [EdgePath.concat_cons]
      aesop

@[aesop safe apply] theorem contains_head (p : G.EdgePath u v) : H.contains p → u ∈ H.verts := by
  induction p with
  | nil => simp
  | cons e _ _ =>
    simp_rw [← e.init_eq]
    aesop

@[aesop safe apply] theorem contains_tail (p : G.EdgePath u v) : H.contains p → v ∈ H.verts := by
  induction p <;> aesop

@[simp] theorem contains_append {u v w : V} (p : G.EdgePath u v) (p' : G.EdgePath v w) : H.contains (p ++ p') ↔ H.contains p ∧ H.contains p' := by
  induction p <;> aesop

theorem contains_reverse {u v : V} (p : G.EdgePath u v) : H.contains p → H.contains p.reverse := by
  induction p with
    | nil => simp only  [contains_nil, EdgePath.reverse_nil, imp_self]
    | cons e p' ih =>
      rw [EdgePath.reverse_cons]
      simp only [contains_cons, contains_concat, EdgeBetween.bar_eq_bar, and_imp]
      intro he hp'H
      exact ⟨H.edges_bar _ he, ih hp'H⟩

def Subgraph.le {G: Graph V E}(s₁ s₂ : Subgraph G) : Prop :=
  s₁.verts ⊆ s₂.verts ∧ s₁.edges ⊆ s₂.edges

instance {G: Graph V E} : LE (Subgraph G) := ⟨Subgraph.le⟩

theorem contains_le {H H' : Subgraph G} {p : G.EdgePath u v}
    (hpH : H.contains p) (h : H ≤ H') : H'.contains p := by
  let ⟨hv, he⟩ := h
  induction p with
    | nil => apply hv; exact hpH
    | cons e p' ih =>
      simp at hpH ⊢
      refine' ⟨he hpH.left, ih hpH.right⟩

@[simp]
theorem Subgraph.le_defn {G: Graph V E}(s₁ s₂ : Subgraph G) :
    s₁ ≤ s₂ ↔ s₁.verts ⊆ s₂.verts ∧ s₁.edges ⊆ s₂.edges := Iff.rfl

instance : PartialOrder (Subgraph G) where
  lt := fun s₁ s₂ => s₁ ≤ s₂ ∧ ¬ s₂ ≤ s₁
  le_refl := by
    intro s
    simp [Subgraph.le_defn, subset_rfl]
  le_trans := by
    intro s₁ s₂ s₃ h₁ h₂
    simp [Subgraph.le_defn] at *
    apply And.intro
    · apply subset_trans h₁.1 h₂.1
    · apply subset_trans h₁.2 h₂.2
  lt_iff_le_not_le := by simp
  le_antisymm := by
    intro s₁ s₂ h₁ h₂
    simp [Subgraph.le_defn] at *
    let h := subset_antisymm h₁.1 h₂.1
    let h' := subset_antisymm h₁.2 h₂.2
    ext <;> simp [h, h']

def Subgraph.union (H H' : Subgraph G) : Subgraph G where
  verts := H.verts ∪ H'.verts
  edges := H.edges ∪ H'.edges
  edges_bar e := by
    rintro (_ | _)
    · left; apply H.edges_bar; assumption
    · right; apply H'.edges_bar; assumption
  edges_init e := by
    rintro (_ | _)
    · left; apply Subgraph.edges_init; assumption
    · right; apply Subgraph.edges_init; assumption

def Subgraph.inter (H H' : Subgraph G) : Subgraph G where
  verts := H.verts ∩ H'.verts
  edges := H.edges ∩ H'.edges
  edges_bar e := by
    rintro ⟨_, _⟩
    constructor <;>
    ( apply Subgraph.edges_bar
      assumption )
  edges_init e := by
    rintro ⟨_, _⟩
    constructor <;>
    ( apply Subgraph.edges_init
      assumption )

instance : Lattice (Subgraph G) where
  sup := Subgraph.union
  le_sup_left := by aesop (add norm unfold [Subgraph.union])
  le_sup_right := by aesop (add norm unfold [Subgraph.union])
  sup_le := by aesop (add norm unfold [Subgraph.union])
  inf := Subgraph.inter
  inf_le_left := by aesop (add norm unfold [Subgraph.inter])
  inf_le_right := by aesop (add norm unfold [Subgraph.inter])
  le_inf := by aesop (add norm unfold [Subgraph.inter])

end Subgraph

structure PreconnectedSubgraph (G : Graph V E) extends Subgraph G where
  path : (u v : verts) → {p : G.EdgePath ↑u ↑v // toSubgraph.contains p}

structure PointedSubgraph {V E : Type _} (G : Graph V E) extends Subgraph G where
  basePoint : verts

structure Subtree (G : Graph V E) extends PreconnectedSubgraph G where
  path_unique : ∀ u v : verts, ∀ p : G.EdgePath u v, toSubgraph.contains p →
    [[p]] = [[(path u v).val]]

open CategoryTheory in
def Subtree.ofPointed {G : Graph V E} (H : Subgraph G) {u : V}
  (path : (v : H.verts) → {p : G.EdgePath ↑u ↑v // H.contains p})
  (path_unique : (v : H.verts) → (p : G.EdgePath u v) → H.contains p → [[p]] = [[(path v).val]]) :
      Subtree G := { H with
    path := fun (x y : H.verts) ↦
      let ⟨p, hpH⟩ := path x
      let ⟨q, hqH⟩ := path y
      ⟨p.reverse ++ q, by
        rw [H.contains_append]
        exact ⟨H.contains_reverse _ hpH, hqH⟩⟩
    path_unique := by
      intro (a : H.verts) (b : H.verts) p (hpH : H.contains p)
      simp only [Eq.ndrec, id_eq, eq_mpr_eq_cast]
      rw [← mul_path_path, ← PathClass.inv_equiv_reverse]
      rw [← PathClass.mul_id [[p]], ← PathClass.inv_mul [[(path b).val]], ← PathClass.mul_assoc]
      congr
      apply PathClass.inv_eq
      apply path_unique
      apply Subgraph.contains_reverse
      rw [Subgraph.contains_append]
      refine' ⟨hpH, Subgraph.contains_reverse _ _ _⟩
      exact (path b).property
    }

@[simp] theorem PreconnectedSubgraph.contains_path (H : PreconnectedSubgraph G) (u v : H.verts) : H.contains (H.path u v).val :=
  (H.path u v).property

attribute [aesop safe apply] Subtree.path_unique

structure Graph.hom {V E V' E' : Type _} (G : Graph V E) (G' : Graph V' E') where
  toFuncV : V → V'
  toFuncE : E → E'
  preserve_init : ∀ e : E, toFuncV (G.ι e) = G'.ι (toFuncE e)
  preserve_bar : ∀ e : E, toFuncE (G.bar e) = G'.bar (toFuncE e)

namespace Graph.hom

variable {V E V' E' : Type _} (G : Graph V E) (G' : Graph V' E') (φ : Graph.hom G G')

theorem preserve_terminal (e : E) : φ.toFuncV (G.τ e) = G'.τ (φ.toFuncE e) := by
  rw [← G.ι_bar, ← G'.ι_bar, preserve_init, preserve_bar]

def edgeBetweenMap {u v : V} (e : G.EdgeBetween u v) : G'.EdgeBetween (φ.toFuncV u) (φ.toFuncV v) where
  edge := φ.toFuncE e.edge
  init_eq := by
    have := φ.preserve_init e.edge
    rw [e.init_eq] at this
    symm
    assumption
  term_eq := by
    have := φ.preserve_terminal e.edge
    rw [e.term_eq] at this
    symm
    assumption

def pathMap {u v : V} : G.EdgePath u v → G'.EdgePath (φ.toFuncV u) (φ.toFuncV v)
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

section MaximalSubtree

variable {V E : Type _} (G : Graph V E)

instance : LE (Subtree G) where
  le t t' := t.toSubgraph ≤ t'.toSubgraph


def chainUnion (c : Set (Subtree G)) (h : IsChain (· ≤ ·) c) : Subtree G where
  verts := sorry
  edges := sorry
  edges_bar := sorry
  edges_init := sorry
  path := sorry
  path_unique := sorry

def pathToTree (t : Subtree G) [∀ v : V, Decidable (v ∈ t.verts)]
    {u v : V} (hu : u ∈ t.verts) (hv : v ∉ t.verts) (p : G.EdgePath v u) :
    {q : Σ w : V, G.EdgePath v w // q.1 ∈ t.verts ∧ q.2.initVerts.all (· ∉ t.verts)} :=
  match p with
    | .nil _ => by contradiction
    | .cons e p' => by
      rename_i x w
      if h:w ∈ t.verts then
        refine' ⟨⟨w, G.singletonPath e⟩, ⟨h, _⟩⟩
        simp only [EdgePath.initVerts, List.map, EdgeBetween.init_eq,
          decide_not, List.all_cons, hv, decide_False,
          Bool.not_false, List.all_nil, Bool.and_self]
      else
        let ⟨⟨v', q⟩, hqt, hqverts⟩ := pathToTree t hu h p'
        refine' ⟨⟨v', .cons e q⟩, ⟨hqt, _⟩⟩
        simp only [EdgePath.initVerts, decide_not, List.all_eq_true,
          List.mem_map, Bool.not_eq_true', decide_eq_false_iff_not, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, List.map, List.all_cons, Bool.and_eq_true] at hqverts ⊢
        refine' ⟨_, hqverts⟩
        simp only [EdgeBetween.init_eq, hv, not_false_eq_true]

section JointAtPoint

variable (t t' : Subtree G) {u : V} (h : ∀ v : V, v ∈ t.verts ∧ v ∈ t'.verts ↔ v = u)
variable [∀ v : V, Decidable (v ∈ t.verts)] [∀ v : V, Decidable (v ∈ t'.verts)]

def Subtree.joinAtPoint : Subtree G := Subtree.ofPointed (u := u) (t.toSubgraph ⊔ t'.toSubgraph)
  (
    fun ⟨v, (hv : v ∈ t.verts ∨ v ∈ t'.verts)⟩ ↦
      if hvt : v ∈ t.verts then
        let ⟨p, hpt⟩ := t.path ⟨u, ((h u).mpr rfl).left⟩ ⟨v, hvt⟩
        ⟨p, Subgraph.contains_le hpt le_sup_left⟩
      else if hvt' : v ∈ t'.verts then
        let ⟨p, hpt'⟩ := t'.path ⟨u, ((h u).mpr rfl).right⟩ ⟨v, hvt'⟩
        ⟨p, Subgraph.contains_le hpt' le_sup_right⟩
      else by aesop
  )
  sorry

-- def Subtree.jointAtPoint_contains_common_vertex : v ∈ (Subtree.jointAtPoint t t' h).verts := sorry

-- def Subtree.jointAtPoint_contains_left : t ≤ Subtree.joinAtPoint t t' h := sorry

-- def Subtree.jointAtPoint_contains_right : t' ≤ Subtree.joinAtPoint t t' h := sorry

end JointAtPoint

-- Idea: attach the above path to the tree
def extendTree (t : Subtree G) (v : V) (h : v ∉ t.verts) : {t' : Subtree G // t ≤ t' ∧ v ∈ t'.verts} := sorry

end MaximalSubtree

namespace SpanningSubtree

variable {V E : Type _} {G : Graph V E} (Γ : SpanningSubtree G)

def base : V := Γ.basePoint.val

def coe : Graph V Γ.edges := Γ.toSpanningSubgraph.coe

abbrev vertex_coe (v : V) : Γ.verts := ⟨v, by simp⟩

open CategoryTheory

def pathClassBetween (u v : V) : u ⟶ v := [[(Γ.toSubtree.path (Γ.vertex_coe u) (Γ.vertex_coe v)).val]]

@[simp] lemma contains_path {u v : V} : Γ.contains (Γ.path (Γ.vertex_coe u) (Γ.vertex_coe v)).val :=
  Γ.toSubtree.toPreconnectedSubgraph.contains_path (Γ.vertex_coe u) (Γ.vertex_coe v)

notation u " ⤳[" Γ "] " v  => pathClassBetween Γ u v

@[local simp] def surround {u v : V} (p : u ⟶ v) : Γ.base ⟶ Γ.base :=
  (Γ.base ⤳[Γ] u) ≫ p ≫ (v ⤳[Γ] Γ.base)

@[local simp] def surroundEdge {u v : V} (e : G.EdgeBetween u v) := Γ.surround [[G.singletonPath e]]

@[simp] lemma path_class_of_contains_path (p : G.EdgePath u v) (hpΓ : Γ.contains p) :
    [[p]] = u ⤳[Γ] v := by
  apply Γ.path_unique (Γ.vertex_coe u) (Γ.vertex_coe v)
  assumption

@[simp] theorem tree_path_id {u : V} : (u ⤳[Γ] u) = 𝟙 u := by
  symm
  apply path_class_of_contains_path
  simp

@[simp] theorem tree_path_comp {u v w : V} : (u ⤳[Γ] v) ≫ (v ⤳[Γ] w) = (u ⤳[Γ] w) := by
  apply path_class_of_contains_path
  simp

@[simp] theorem tree_path_comp_right {u v w x : V} (p : w ⟶ x) :
    (u ⤳[Γ] v) ≫ (v ⤳[Γ] w) ≫ p = (u ⤳[Γ] w) ≫ p := by
  rw [← Category.assoc, tree_path_comp]

lemma singleton_tree_path {e : G.EdgeBetween u v} (heΓ : e.edge ∈ Γ.edges) : [[G.singletonPath e]] = u ⤳[Γ] v := by
  apply path_class_of_contains_path
  simp; assumption

@[simp] theorem surround_tree_edge {e : G.EdgeBetween u v} (heΓ : e.edge ∈ Γ.edges) :
    Γ.surroundEdge e = 𝟙 Γ.base := by
  simp [surroundEdge, Γ.singleton_tree_path heΓ]

theorem opp_path_eq_inv {u v : V} : (u ⤳[Γ] v) = inv (v ⤳[Γ] u) := by
  rw [← hom_comp_eq_id]
  trans (v ⤳[Γ] v)
  <;> simp

@[local simp] lemma path_to_base_eq {u : V} : (u ⤳[Γ] Γ.base) = inv (Γ.base ⤳[Γ] u) := by
  apply opp_path_eq_inv

@[simp] theorem surround_append {u v w : V} (p : u ⟶ v) (q : v ⟶ w) :
    Γ.surround p ≫ Γ.surround q = Γ.surround (p ≫ q) := by
  simp only [surround, path_to_base_eq, Category.assoc, IsIso.inv_hom_id_assoc]

@[simp] theorem surround_nil (u : V) : Γ.surround (𝟙 u) = 𝟙 Γ.base := by
  simp only [surround, path_to_base_eq, Category.id_comp, IsIso.hom_inv_id]

@[simp] theorem surround_cons :
    Γ.surround [[.cons e p]] = Γ.surroundEdge e ≫ Γ.surround [[p]] := by
  erw [Graph.EdgePath.cons_eq_append_singletonPath, surround_append]; rfl

@[simp] theorem surround_inv {u v : V} (p : u ⟶ v) : Γ.surround (inv p) = inv (Γ.surround p) := by
  rw [← hom_comp_eq_id]; simp only [surround, path_to_base_eq, Category.assoc, IsIso.inv_hom_id_assoc,
    IsIso.hom_inv_id_assoc, IsIso.hom_inv_id]

@[simp] theorem surround_loop (p : Γ.base ⟶ Γ.base) : Γ.surround p = p := by
  simp only [surround, tree_path_id, Category.comp_id, Category.id_comp]

@[simp] theorem surroundEdge_bar (e : G.EdgeBetween u v) : Γ.surroundEdge e.bar = inv (Γ.surroundEdge e) := by
  rw [surroundEdge, surroundEdge, ← surround_inv, Graph.EdgePath.singletonPath_bar,
    Graph.PathClass.reverse_class_eq_inv, Graph.PathClass.inv_eq_inv]

theorem surroundEdge_cast {u v u' v' : V} (huu' : u = u') (hvv' : v = v')
    (e : G.EdgeBetween u v) (e' : G.EdgeBetween u' v')
    (hee' : e.edge = e'.edge) : Γ.surroundEdge e = Γ.surroundEdge e' := by
  cases huu'; cases hvv'
  congr; ext
  exact hee'

@[simp] theorem surroundEdge_bar' (e : E) : Γ.surroundEdge (EdgeBetween.ofEdge (G := G) (G.bar e)) = inv (Γ.surroundEdge (EdgeBetween.ofEdge (G := G) e)) := by
  rw [← surroundEdge_bar]
  apply surroundEdge_cast <;> simp

def surroundEdgewise {u v : V} : G.EdgePath u v → G.π₁ Γ.base :=
  Graph.EdgePath.fold Γ.surroundEdge CategoryStruct.comp (1 : G.π₁ Γ.base)

@[simp] lemma surroundEdgewise_nil {u : V} : Γ.surroundEdgewise (Graph.EdgePath.nil (G := G) u) = 𝟙 Γ.base := rfl

@[simp] lemma surroundEdgewise_cons {u v : V} :
  Γ.surroundEdgewise (Graph.EdgePath.cons e p) = (Γ.surroundEdge e) ≫ (Γ.surroundEdgewise p) := rfl

theorem surround_eq {u v : V} (p : G.EdgePath u v) :
    Γ.surround [[p]] = Γ.surroundEdgewise p := by
  induction p with
  | nil _ => simp only [surround, Subgraph.contains_nil, SpanningSubgraph.spanning, Set.top_eq_univ, Set.mem_univ,
    Graph.PathClass.nil_eq_id, path_to_base_eq, Category.id_comp, IsIso.hom_inv_id, surroundEdgewise_nil]
  | cons _ _ ih => simp only [surroundEdgewise_cons, ← ih, surround_cons]

end SpanningSubtree

end Graph
