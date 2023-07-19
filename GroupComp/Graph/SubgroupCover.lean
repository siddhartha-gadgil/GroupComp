import GroupComp.Graph.UniversalCover
import Mathlib
namespace Graph

namespace SubgroupCover

open EdgePath PathClass UniversalCover

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

scoped instance vertSetoid : Setoid (Vert G x₀) where
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
