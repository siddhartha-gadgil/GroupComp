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
    let h': [[v₁ ++ EdgePath.reverse v₂]].reverse ∈ H := inv_mem h
    rw [PathClass.reverse_commutes, 
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
      exact (relH H p p') ∧ (relH H (p :+ e) (p' :+ e')) 
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
      · apply relH_symm H hyp.2
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
          · apply relH_trans H hyp₂ hyp₄
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

def QuotVert  := Quotient (vertSetoid H)
def QuotEdge  := Quotient (edgeSetoid H)

namespace QuotVert

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
  simp [bar_defn]
  have h': edgeSetoid H |>.r ⟨τ₀, τ₁, e, p, pf⟩ ⟨τ₀, τ₁, e', p', pf'⟩ := h
  simp [Setoid.r, relH] at h'
  apply Quotient.sound
  simp [HasEquiv.Equiv, Setoid.r, relH]
  apply And.intro
  · exact h'.2
  · simp [reducedConcat_cancel_pair p e pf, 
      reducedConcat_cancel_pair p' e' pf']
    exact h'.1

theorem initial_defn (e: Edge G x₀):
  ι H ⟦ e ⟧ = ⟦ (G.univ x₀).ι e ⟧ := rfl

theorem bar_defn (e : Edge G x₀):
  bar H ⟦ e ⟧ = ⟦ (G.univ x₀).bar e ⟧ := rfl

theorem bar_involution :(ebar : Quotient (edgeSetoid H)) → 
  bar H (bar H ebar) = ebar := by
  apply Quotient.ind
  intro e
  simp [bar_defn]

theorem bar_no_fp : (ebar : Quotient (edgeSetoid H)) →
  bar H ebar ≠ ebar := by
  apply Quotient.ind
  intro ⟨τ₀, τ₁, e, p, pf⟩
  simp [bar_defn, Edge.bar_defn]
  intro contra
  rw [@Quotient.eq _ (edgeSetoid H)] at contra
  let lem := terminal₀_eq_of_r H contra
  simp only at lem
  cases lem
  simp [HasEquiv.Equiv, Setoid.r, relH] at contra
  sorry

end QuotVert
