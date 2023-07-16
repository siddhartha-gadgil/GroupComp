import GroupComp.Graph.Covering
import GroupComp.Graph.ReducedPaths
import Mathlib
namespace Graph

open EdgePath PathClass

variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]


/-!
## Construction of the Universal covering

We construct the universal cover given a baspoint `x₀` with

* Vertices: reduced edge paths starting at `x₀`
* Edges: reduces edge paths starting at `x₀` followed by an edge.

The non-trivial part is the construction of the `bar` map. The initial vertex should be the terminal vertex of the given edge. This is obtained by reduced concat, using the fact that the result is reduced. The other result is used to show that the `bar` map is an involution.
-/

namespace UniversalCover

variable (G: Graph V E) (x₀ : V)

@[ext]
structure Vert where
  τ : V
  p : EdgePath G x₀ τ
  is_reduced : @reduced V E G x₀ τ p

@[ext]
structure Edge where
  τ₀ : V
  τ₁ : V
  nxt: EdgeBetween G τ₀ τ₁
  p : EdgePath G x₀ τ₀
  is_reduced : reduced p
  
  
  
namespace Edge

def initial (e : Edge G x₀) : Vert G x₀ := 
  ⟨e.τ₀, e.p, e.is_reduced⟩

def terminal (e : Edge G x₀) : Vert G x₀ :=
  ⟨e.τ₁, e.p :+ e.nxt, reducedConcat_reduced e.p e.nxt e.is_reduced⟩

def bar (e : Edge G x₀) : Edge G x₀ :=
  ⟨e.τ₁, e.τ₀, e.nxt.bar, e.p :+ e.nxt,  reducedConcat_reduced e.p e.nxt e.is_reduced⟩


theorem bar_involution (e : Edge G x₀) : 
    bar G x₀ (bar G x₀ e) = e := by
  simp only [bar, EdgeBetween.bar_involution]
  ext
  · rfl
  · rfl
  · rfl  
  · simp only [Eq.ndrec, id_eq, heq_eq_eq]
    apply reducedConcat_cancel_pair
    exact e.is_reduced

def edgeList (e : Edge G x₀) : List E := 
  e.p.toEdgeList

theorem bar_neq_self (e: Edge G x₀) :
  e ≠ bar G x₀ e := by
  intro contra
  have : e.p.toEdgeList.length =  (bar G x₀ e).p.toEdgeList.length 
     := by
      rw [← contra]
  simp [bar, Edge.p] at this
  let h' := concat_parity e.p e.nxt 
  rw [this] at h' 
  symm at h'
  let h'' := not_iff_self  h'
  assumption

def Guniv : Graph (Vert G x₀) (Edge G x₀) where
  ι := initial G x₀
  bar := bar G x₀
  bar_involution := bar_involution G x₀
  bar_no_fp := bar_neq_self G x₀

def proj : Morphism (Guniv G x₀) G where
  vertexMap := Vert.τ
  edgeMap := fun e ↦ e.nxt.edge 
  commutes := by
    intro e
    match e with
    | ⟨τ₀, τ₁, nxt, _, _⟩ => 
      show τ₀ = G.ι nxt.edge
      rw [nxt.source]
  bar_commutes := by
    intro e
    rfl
      
lemma shift_heq (τ₀ τ₁ τ₂ : V)(edge : E)(source : G.ι edge = τ₀)
    (target₁ : G.τ edge = τ₁)(target₂ : G.τ edge = τ₂):
    HEq (⟨edge, source, target₁⟩ : EdgeBetween G τ₀ τ₁)
      (⟨edge, source, target₂⟩ : EdgeBetween G τ₀ τ₂) := by
    induction target₁
    induction target₂
    rfl

instance : CoveringMap (proj G x₀) where
  localSection := 
    fun v₁ e h ↦
      ⟨v₁.τ, G.τ e, ⟨e, Eq.symm h, rfl⟩, v₁.p, v₁.is_reduced⟩
  section_init := by
    intro v₁ e h
    match v₁ with
    | ⟨τ, p, red⟩ =>
      have h' : τ = G.ι e := h
      cases h'
      rfl
  left_inverse := by
    intro v₁ e h
    match v₁ with
    | ⟨τ, p, red⟩ =>
      have h' : τ = G.ι e := h
      cases h'
      rfl 
  right_inverse := by
    intro v₁ e₁ h₁   
    have : (proj G x₀).edgeMap e₁ = e₁.nxt.edge := rfl
    let l := e₁.nxt.target
    rw [← this] at l
    match e₁ with
    | ⟨τ₀, τ₁, nxt, p, red⟩ =>
      cases h₁ 
      show _ = (⟨τ₀, τ₁, nxt, p, red⟩ : Edge G x₀)
      ext
      · rfl
      · rw [← l]
      · show HEq 
          (⟨nxt.edge, nxt.source , rfl⟩  : EdgeBetween G τ₀ (G.τ nxt.edge)) nxt
        apply shift_heq
      · rfl 

end Edge

open Edge

def basepoint : Vert G x₀  := 
  ⟨x₀, EdgePath.nil _, reduced_nil⟩

def rayFrom (G: Graph V E)(x₀ τ : V)(p : EdgePath G τ x₀)
  (hyp : reduced p.reverse)  : 
  EdgePath  (Guniv G x₀) (basepoint G x₀) ⟨τ, p.reverse, hyp⟩   := by
  match p, hyp with
  | nil _,  hyp => apply nil 
  | cons e p', hyp' => 
    rename_i x₀' u
    have red_cons : reduced (cons e p') := by
      rw [← reverse_reverse (cons e p')]
      apply reverse_reduced
      assumption
    have red_p' : reduced p' := by
      apply tail_reduced e p' red_cons
    have red' : reduced p'.reverse := by
      apply reverse_reduced
      assumption
    have init := rayFrom G x₀ u p' red'
    apply init.concat
    let edge : Edge G x₀ := ⟨u, τ, e.bar, p'.reverse, red'⟩ 
    let iv : Vert G x₀ := ⟨u, reverse p', red'⟩
    let τv : Vert G x₀ := ⟨τ, (cons e p').reverse, hyp'⟩
    show EdgeBetween (Guniv G x₀) iv τv
    exact ⟨edge, rfl, (by 
      show edge.terminal = ⟨τ, (cons e p').reverse, hyp'⟩
      simp [terminal, reducedConcat]
      congr
      apply redCons_eq_cons_of_reduced
      assumption)⟩  
    
theorem rayFrom_proj_list (G: Graph V E)(x₀ τ : V)(p : EdgePath G τ x₀)
  (hyp : reduced p.reverse) :
  (rayFrom G x₀ τ p hyp).toEdgeList.map (fun e ↦ e.nxt.edge) = 
    p.toEdgeList.reverse.map (G.bar) := by
    induction p with
  | nil _ => 
    simp [rayFrom, nil_edgeList]    
  | cons e p' ih => 
    rename_i x₀' u u'
    have red_cons : reduced (cons e p') := by
      rw [← reverse_reverse (cons e p')]
      apply reverse_reduced
      assumption
    have red_p' : reduced p' := by
      apply tail_reduced e p' 
      assumption
    have red' : reduced p'.reverse := by
      apply reverse_reduced
      assumption
    simp [rayFrom, cons_edgeList, edgeList_concat, ih red']    
