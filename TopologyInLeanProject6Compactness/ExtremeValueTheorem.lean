import Mathlib.Tactic
import TopologyInLeanProject6Compactness.HeineBorel
import TopologyInLeanProject6Compactness.Definitions.NewSpaces

open Course
open Constructions

variable (n : ℕ) (K : Set (Rn n)) (f : {x : Rn n | x ∈ K} → ℝ)
/-
K ⊆ ℝ^n
f : K → ℝ
-/

-- K and f(K) must be a type s.t. I can use Compact_image
def K_type := {x : Rn n | x ∈ K}
def f_K_type (n : ℕ) (K : Set (Rn n)) (f : K_type n K → ℝ) := {y : ℝ | ∃ x : K_type n K, f x = y}

instance instTopology_f_K_type
  (n : ℕ) (K : Set (Rn n)) (f : ↑(K_type n K) → ℝ) :
  Topology (f_K_type n K f) :=
  Constructions.pullbackTopology ℝ (inferInstance) (f_K_type n K f) (fun y => (y : ℝ))

instance instSubspace_f_K_type
  (n : ℕ) (K : Set (Rn n)) (f : (K_type n K) → ℝ) :
  Constructions.Subspace ℝ :=
  Constructions.Subspace_pullbackTopology (fun y : f_K_type n K f => (y : ℝ))
    (by
      intro x y h
      cases x; cases y
      simp at h
      simp [h])

#check Constructions.Subspace.incl

theorem ExtremeValueTheorem (K : Set (Rn n)) (hK : Compact K) (f : {x : Rn n | x ∈ K} → ℝ)
  (f_cont : Cont f) :
  ∃ x_min x_max : {x : Rn n | x ∈ K},  ∀ x : {x : Rn n // x ∈ K},
  f x_min ≤ f x ∧ f x ≤ f x_max := by
  let g : K_type n K → f_K_type n K f := fun x => ⟨ f x, ⟨x, rfl⟩ ⟩
  have g_sufj : Function.Surjective g := by
    intro y
    rcases y with ⟨yval, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have g_cont :  Cont g := by
    intro s s_open
    let π : f_K_type n K f → ℝ := sorry--Constructions.Subspace.incl
    have π_cont : Cont π := sorry --Constructions.Cont_incl
    have f_comp : f = π ∘ g := by
      funext x
      rfl
    have comp_cont : Cont (π ∘ g) := by
      rw[f_comp] at f_cont
      exact f_cont
    intro x hx
    rw[Function.comp_def] at f_comp
    rw[f_comp] at f_cont
    rw[Course.Cont] at f_cont
    specialize f_cont s
