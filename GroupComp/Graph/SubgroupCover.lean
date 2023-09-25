import GroupComp.Graph.UniversalCover
import Mathlib
namespace Graph

namespace SubgroupCover

open EdgePath PathClass UniversalCover Edge

variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

variable {G: Graph V E} {x₀ : V}

variable (H : Subgroup (π₁ G x₀))

abbrev rel : Vert G x₀ → Vert G x₀ → Prop
| ⟨τ₁, v₁, _⟩, ⟨τ₂, v₂, _⟩ => by
    if c:τ₁=τ₂ then
      cases c
      exact [[ v₁ ++ v₂.reverse ]] ∈ H  
    else
      exact False

def relH {τ : V} (v₁ v₂ : EdgePath G x₀ τ) : Prop := 
  [[v₁ ++ v₂.reverse]] ∈ H


theorem relH_refl {τ : V} (v : EdgePath G x₀ τ) : relH H v v := 
  by 
    simp [relH]
    apply one_mem


theorem relH_symm {τ : V} {v₁ v₂ : EdgePath G x₀ τ} :
  relH H v₁ v₂ → relH H v₂ v₁ := 
  by
    simp [relH]
    intro h
    let h': [[v₁ ++ EdgePath.reverse v₂]].inv ∈ H := inv_mem h
    rw [PathClass.inv_commutes, 
      EdgePath.reverse_append,  reverse_reverse] at h'
    exact h'

theorem relH_trans {τ : V} {v₁ v₂ v₃ : EdgePath G x₀ τ} :
  relH H v₁ v₂ → relH H v₂ v₃ → relH H v₁ v₃ := 
  by
    simp [relH]
    intro h₁ h₂
    let h₃ : [[v₁ ++ EdgePath.reverse v₂]] ++ [[v₂ ++ EdgePath.reverse v₃]] ∈ H := mul_mem h₁ h₂
    rw [append_commutes, EdgePath.append_assoc, 
      ←EdgePath.append_assoc v₂.reverse, ← append_commutes,
      ← append_commutes] at h₃
    simp only [reverse_left_inverse] at h₃ 
    rw [append_commutes] at h₃
    simp only [nil_append, reverse_class_eq_inv] at h₃ 
    rw [← append_commutes, ← reverse_commutes] 
    exact h₃ 

scoped instance vertSetoid  : Setoid (Vert G x₀) where
  r := fun ⟨τ₁, v₁, _⟩ ⟨τ₂, v₂, _⟩ => by
    if c:τ₁=τ₂ then
      cases c
      exact relH H v₁ v₂
    else
      exact False
  iseqv := by
    apply Equivalence.mk
    · intro ⟨τ₁, v₁, _⟩
      simp only [relH_refl, dite_eq_ite]
    · intro ⟨τ₁, v₁, _⟩ ⟨τ₂, v₂, _⟩
      if c:τ₁=τ₂ then
      cases c
      simp only [dite_eq_ite, ite_true]
      apply relH_symm
    else
      simp only [c, dite_false, IsEmpty.forall_iff]
    · intro ⟨τ₁, v₁, _⟩ ⟨τ₂, v₂, _⟩ ⟨τ₃, v₃, _⟩
      if c₁:τ₁=τ₂ then
        cases c₁
        simp
        if c₂:τ₁=τ₃ then
          cases c₂
          simp only [dite_eq_ite, ite_true]
          apply relH_trans
        else
          simp [c₂]
      else
        simp [c₁]

theorem terminal_eq_of_r {v₁ v₂ : Vert G x₀ } :
  vertSetoid H |>.r v₁ v₂ → v₁.τ = v₂.τ := 
  by
    intro h
    simp [Setoid.r] at h
    by_cases c:v₁.τ=v₂.τ <;> simp [c] at h 
    simp [c]

theorem path_eq_iff_r {τ : V}(p₁ p₂ : EdgePath G x₀ τ)
  {red₁ : reduced p₁} {red₂ : reduced p₂} :
  (vertSetoid H |>.r ⟨τ, p₁, red₁⟩ ⟨τ, p₂, red₂⟩) ↔ 
      [[ p₁ ++ p₂.reverse ]] ∈ H := by 
    simp [Setoid.r, relH]

scoped instance edgeSetoid : Setoid (Edge G x₀) where
  r := fun ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩ => by
    if c:τ₀=τ₀' ∧ τ₁ = τ₁' then
      cases c.left
      cases c.right
      exact (relH H p p') ∧ (e = e')
    else
      exact False
  iseqv := by
    apply Equivalence.mk
    · intro ⟨τ₀, τ₁, e, p, _⟩ 
      simp only [relH_refl, dite_eq_ite]
    · intro ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩
      if c:τ₀=τ₀' ∧ τ₁ = τ₁' then
      cases c.left
      cases c.right
      simp only [dite_eq_ite, ite_true]
      intro hyp
      apply And.intro
      · apply relH_symm H hyp.1
      · rw [hyp.2]
    else
      simp only [c, dite_false, IsEmpty.forall_iff]
    · intro ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩ ⟨τ₀'', τ₁'', e'', p'', _⟩ 
      if c₁:τ₀=τ₀' ∧ τ₁ = τ₁' then
        cases c₁.left
        cases c₁.right
        simp
        if c₂:τ₀=τ₀'' ∧ τ₁ = τ₁'' then
          cases c₂.left
          cases c₂.right
          simp 
          intro hyp₁ hyp₂ hyp₃ hyp₄
          apply And.intro
          · apply relH_trans H hyp₁ hyp₃
          · rw [hyp₂, hyp₄]
        else
          simp [c₂]
      else
        simp [c₁]

theorem terminal₁_eq_of_r {e₁ e₂ : Edge G x₀ } :
  edgeSetoid H |>.r e₁ e₂ → e₁.τ₁ = e₂.τ₁ := 
  by
    intro h
    simp [Setoid.r] at h
    by_cases c:(e₁.τ₁=e₂.τ₁) <;> simp [c] at h 
    simp [c]

theorem terminal₀_eq_of_r {e₁ e₂ : Edge G x₀ } :
  edgeSetoid H |>.r e₁ e₂ → e₁.τ₀ = e₂.τ₀ := 
  by
    intro h
    simp [Setoid.r] at h
    by_cases c:(e₁.τ₀=e₂.τ₀) <;> simp [c] at h 
    simp [c]

theorem edge_eq_of_r :{e₁ e₂ : Edge G x₀ } →  
  edgeSetoid H |>.r e₁ e₂ → e₁.nxt.edge = e₂.nxt.edge := 
  by
    intro ⟨τ₀, τ₁, e, p, _⟩ ⟨τ₀', τ₁', e', p', _⟩
    if c:τ₀=τ₀' ∧ τ₁ = τ₁' then
      cases c.left
      cases c.right
      simp [Setoid.r, relH]
      intro _ h
      rw [h]
    else
      simp [Setoid.r, relH, c]
      

def QuotVert  := Quotient (vertSetoid H)
def QuotEdge  := Quotient (edgeSetoid H)

namespace Quot

def ι : Quotient (edgeSetoid H) → Quotient (vertSetoid H) := by
  apply Quotient.lift (⟦ (G.univ x₀).ι ·⟧)
  intro ⟨τ₀, τ₁, e, p, pf⟩ ⟨τ₀', τ₁', e', p', pf'⟩ h
  let lem₀ := terminal₁_eq_of_r H h
  let lem₁ := terminal₀_eq_of_r H h
  simp only at lem₁
  simp only at lem₀
  cases lem₀
  cases lem₁
  simp [init_defn]
  apply Quotient.sound
  simp only [HasEquiv.Equiv]
  rw [path_eq_iff_r]
  simp [HasEquiv.Equiv, Setoid.r, relH] at h
  exact h.1

def bar : Quotient (edgeSetoid H) → Quotient (edgeSetoid H) := by
  apply Quotient.lift (⟦ (G.univ x₀).bar ·⟧)
  intro ⟨τ₀, τ₁, e, p, pf⟩ ⟨τ₀', τ₁', e', p', pf'⟩ h
  let lem₀ := terminal₁_eq_of_r H h
  let lem₁ := terminal₀_eq_of_r H h
  simp only at lem₁
  simp only at lem₀
  cases lem₀
  cases lem₁
  simp [bar_eq_bar]
  have h': edgeSetoid H |>.r ⟨τ₀, τ₁, e, p, pf⟩ ⟨τ₀, τ₁, e', p', pf'⟩ := h
  simp [Setoid.r, relH] at h'
  apply Quotient.sound
  simp [HasEquiv.Equiv, Setoid.r, relH]
  apply And.intro
  · rw [← h'.2]
    rw [← append_commutes]
    simp [reducedConcat, ← cons_homotopic_redCons, cons_natural, PathClass]
    rw [inv_commutes, append_commutes, reverse_cons, reverse_reverse, EdgeBetween.bar_bar,
    concat_append]
    have : [[p ++ cons e (cons (EdgeBetween.bar e) (EdgePath.reverse p'))]] = [[ p ++ p'.reverse ]] := by
      apply Quot.sound
      apply Reduction.step
    rw [this]
    exact h'.1
  · rw [h'.2]

theorem initial_defn (e: Edge G x₀):
  ι H ⟦ e ⟧ = ⟦ (G.univ x₀).ι e ⟧ := rfl

theorem bar_eq_barn (e : Edge G x₀):
  bar H ⟦ e ⟧ = ⟦ (G.univ x₀).bar e ⟧ := rfl

theorem bar_bar :(ebar : Quotient (edgeSetoid H)) → 
  bar H (bar H ebar) = ebar := by
  apply Quotient.ind
  intro e
  simp [bar_eq_barn]

theorem bar_ne_self : (ebar : Quotient (edgeSetoid H)) →
  ebar ≠ bar H ebar := by
  apply Quotient.ind
  intro ⟨τ₀, τ₁, e, p, pf⟩
  simp [bar_eq_barn, Edge.bar_eq_bar]
  intro contra
  rw [@Quotient.eq _ (edgeSetoid H)] at contra
  let lem := terminal₀_eq_of_r H contra
  simp only at lem
  cases lem
  simp [HasEquiv.Equiv, Setoid.r, relH] at contra
  let c := contra.2
  have : e.bar.edge = e.edge := by rw [← c]
  simp at this
  let nfp := G.bar_ne_self e.edge
  simp [this] at nfp

end Quot

def groupCover : 
  Graph (Quotient (vertSetoid H)) (Quotient (edgeSetoid H)) where
  ι := Quot.ι H
  bar := Quot.bar H
  bar_bar := Quot.bar_bar H
  bar_ne_self := Quot.bar_ne_self H

namespace Quot

def vertexMap : Quotient (vertSetoid H) → V := by
  apply Quotient.lift (fun v : Vert G x₀ ↦ v.τ)
  simp [HasEquiv.Equiv]
  intro v₁ v₂
  apply terminal_eq_of_r H
  
theorem vertexMap_defn (v : Vert G x₀):
  vertexMap H ⟦ v ⟧ = v.τ := rfl

def edgeMap : Quotient (edgeSetoid H) → E := by
  apply Quotient.lift (fun e : Edge G x₀ ↦ e.nxt.edge)
  simp [HasEquiv.Equiv]
  intro e₁ e₂
  apply edge_eq_of_r H

theorem edgeMap_defn (e : Edge G x₀):
  edgeMap H ⟦ e ⟧ = e.nxt.edge := rfl

theorem initial (e : Edge G x₀):
  (groupCover H).ι ⟦ e ⟧ = ⟦ (G.univ x₀).ι e⟧ := rfl

theorem bar_eq_barn' (e : Edge G x₀):
  (groupCover H).bar ⟦ e ⟧ = ⟦ (G.univ x₀).bar e ⟧ := rfl

theorem commutes : (ebar : Quotient (edgeSetoid H)) → 
  vertexMap H ((groupCover H).ι ebar) = 
   G.ι (edgeMap H ebar) := by
  apply Quotient.ind
  intro e
  rw [initial]
  rw [vertexMap_defn, edgeMap_defn]
  apply (proj G x₀).commutes

theorem bar_commutes : (ebar : Quotient (edgeSetoid H)) → 
  edgeMap H ((groupCover H).bar ebar) = G.bar (edgeMap H ebar) := by
  apply Quotient.ind
  intro e
  rw [edgeMap_defn, bar_eq_barn']
  apply (proj G x₀).bar_commutes

end Quot

def groupCoverProj : Morphism (groupCover H) G where
  vertexMap := Quot.vertexMap H
  edgeMap := Quot.edgeMap H
  commutes := Quot.commutes H
  bar_commutes := Quot.bar_commutes H

namespace Quot

theorem vertexMap_defn' (v : Vert G x₀):
  (groupCoverProj H).vertexMap ⟦ v ⟧ = v.τ := rfl

theorem edgeMap_defn' (τ₀ : V) (τ₁: V)(nxt: EdgeBetween G τ₀ τ₁) 
  (p: EdgePath G x₀ τ₀)(red: reduced p):
  (groupCoverProj H).edgeMap ⟦ ⟨τ₀, τ₁, nxt, p, red⟩  ⟧ = nxt.edge := rfl

def localSection : (v₁ : Quotient (vertSetoid H)) → (e : E) →
  ((groupCoverProj H).vertexMap v₁) = G.ι e → 
  Quotient (edgeSetoid H) := by
  intro v₁
  apply Quotient.hrecOn v₁ 
    (motive:= fun v₁ ↦ (e : E) → Morphism.vertexMap (groupCoverProj H) v₁ = Graph.ι G e → Quotient (edgeSetoid H)) 
    (fun ⟨τ, p, is_reduced⟩ e h ↦ 
        ⟦ ⟨τ, G.τ e, ⟨e, Eq.symm h, rfl⟩, p, is_reduced⟩ ⟧)
  intro ⟨τ, p, is_reduced⟩ ⟨τ', p', is_reduced'⟩ rel
  have : τ = τ' := terminal_eq_of_r H rel
  cases this
  simp
  simp [HasEquiv.Equiv, Setoid.r, relH] at rel
  funext e h
  apply Quotient.sound
  simp [HasEquiv.Equiv, Setoid.r, relH]
  exact rel

theorem localSection_defn (τ : V) (p : EdgePath G x₀ τ)
  (is_reduced : reduced p) 
  (e: E) (h: τ = G.ι e):
  localSection H ⟦ ⟨τ, p, is_reduced⟩ ⟧ e h = 
    ⟦ ⟨τ, G.τ e, ⟨e, Eq.symm h, rfl⟩, p, is_reduced⟩ ⟧ := rfl

theorem localSection_composition (τ₀ : V) (p : EdgePath G x₀ τ₀)
  (is_reduced : reduced p) 
  (e: Edge G x₀) (h: τ₀ = G.ι e.nxt.edge) :
  localSection H ⟦ ⟨τ₀, p, is_reduced⟩ ⟧ ((groupCoverProj H).edgeMap ⟦ e⟧) h = 
    ⟦ ⟨τ₀, G.τ (e.nxt.edge), 
    ⟨e.nxt.edge, Eq.symm h, rfl⟩, p, is_reduced⟩ ⟧ := rfl

-- set_option maxHeartbeats 200000

#check HEq

theorem localSection_composition' (τ : V) (p : EdgePath G x₀ τ)
  (is_reduced : reduced p)(τ₀ τ₁ : V) (nxt: EdgeBetween G τ₀ τ₁) (p' : EdgePath G x₀ τ₀)
  (is_reduced' : reduced p')
  (h: τ = G.ι nxt.edge) :
  localSection H ⟦ ⟨τ, p, is_reduced⟩ ⟧ 
  ((groupCoverProj H).edgeMap ⟦ (⟨τ₀, τ₁, nxt, p', is_reduced'⟩ : Edge G x₀)⟧) h = 
    ⟦ ⟨τ, τ₁, 
    ⟨nxt.edge, Eq.symm h, nxt.target⟩, p, is_reduced⟩ ⟧ := by
  rw [localSection_composition]
  apply Quotient.sound  
  simp [nxt.target]
  have : (⟨τ, G.τ (nxt.edge), 
    ⟨nxt.edge, Eq.symm h, rfl⟩, p, is_reduced⟩ : Edge G x₀) =
    ⟨τ, τ₁,
    ⟨nxt.edge, Eq.symm h, nxt.target⟩, p, is_reduced⟩ := by
    simp [nxt.target, eq_of_edge_eq]
    congr
    rw [nxt.target]
    have l {τ : V}(pf: G.τ nxt.edge = τ) :
      HEq (rfl: G.τ nxt.edge  = G.τ nxt.edge ) pf   := by
      cases pf
      simp
    apply l nxt.target     
  rw [this]
  apply @Setoid.refl _ (edgeSetoid H)
  


theorem edge_from (e : Edge G x₀)(τ₀ : V): τ₀ = e.τ₀  → 
  ∃ τ₁: V, ∃ nxt: EdgeBetween G τ₀ τ₁, 
  ∃ p': EdgePath G x₀ τ₀, ∃ red: reduced p',
  e = ⟨τ₀, τ₁, nxt, p', red⟩ := by
  intro h
  cases h
  use e.τ₁, e.nxt, e.p, e.is_reduced

theorem edge_to (e : Edge G x₀)(τ₀ : V){τ₁ : V}: τ₀ = e.τ₀  →  e.τ₁ = τ₁  → 
  ∃ nxt: EdgeBetween G τ₀ τ₁, 
  ∃ p': EdgePath G x₀ τ₀, ∃ red: reduced p',
  e = ⟨τ₀, τ₁, nxt, p', red⟩ := by
  intro h₁ h₂
  cases h₁
  cases h₂
  use e.nxt, e.p, e.is_reduced

end Quot 

instance : CoveringMap (groupCoverProj H)  where
  localSection := Quot.localSection H
    
  section_init := by
    apply Quotient.ind
    intro ⟨τ, p, is_reduced⟩ e h
    simp [Quot.localSection_defn]
    rw [Quot.initial, init_defn]

  left_inverse := by
    apply Quotient.ind
    intro ⟨τ, p, is_reduced⟩ e h
    simp [Quot.localSection_defn]
    rw [Quot.edgeMap_defn']
  
  right_inverse := by
    apply Quotient.ind
    intro ⟨τ, p, is_reduced⟩ 
    apply Quotient.ind
    intro ⟨τ₀, τ₁, nxt, p', red⟩   h
    simp [Quot.localSection_composition']
    rw [Quot.initial, init_defn] at h
    let rel:= Quotient.exact h
    let teq :τ = τ₀ := terminal_eq_of_r H rel
    apply Quotient.sound
    cases teq
    simp [HasEquiv.Equiv, Setoid.r, relH] 
    simp [HasEquiv.Equiv, Setoid.r, relH] at rel
    exact rel

end SubgroupCover

end Graph