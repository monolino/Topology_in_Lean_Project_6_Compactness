import Mathlib.Tactic
import TopologyInLeanProject6Compactness.HeineBorel
import TopologyInLeanProject6Compactness.Definitions.NewSpaces
import TopologyInLeanProject6Compactness.Definitions.Compactness

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
  have g_surj : Function.Surjective g := by
    intro y
    rcases y with ⟨yval, ⟨x, rfl⟩⟩
    exact ⟨x, rfl⟩
  have g_cont :  Cont g := by
    intro s s_open
    let π : f_K_type n K f → ℝ := fun y ↦ (y : ℝ)
    rcases s_open with ⟨V, V_open, rfl⟩
    have h_preim : g ⁻¹' (π ⁻¹' V)  = (fun x ↦ π (g x)) ⁻¹' V := by
      ext x
      rfl
    have h_comp : (fun x ↦ π (g x)) = f := by
      funext x
      rfl
    have h_open : Open ((fun x ↦ π (g x)) ⁻¹' V) := by
      simpa [h_comp] using f_cont V V_open
    simpa [h_preim] using h_open
  have compact_K_type : Compact (K_type n K) := by --prove K_type is compact
    exact hK
  have compact_fK_type : Compact (Set.univ : Set ↑(f_K_type n K f)) := by
    exact AltAttempt.Compact_image_2 g g_surj g_cont compact_K_type
