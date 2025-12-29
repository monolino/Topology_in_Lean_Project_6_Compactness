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

@[simp]
def ContOn {X : Type u} {Y : Type v}
  [Topology X] [Topology Y]
  (f : X → Y) (K : Set X) : Prop :=
  ∀ s, Open s → Open (K ∩ f ⁻¹' s)

lemma Compact.image_on {X Y} [Topology X] [Topology Y]
    {K : Set X} (hK : Compact K)
    {f : X → Y} (hf : ContOn f K) :
    Compact (f '' K) := by
    intro C
    let D : openCover K := {
      Cover := { S : Set X | ∃ V ∈ C.Cover, S = K ∩ f ⁻¹' V }
      Open_cover := by
        intro s hs
        rcases hs with ⟨V, hV_in_C, rfl⟩
        have hV_open : Open V := C.Open_cover V hV_in_C
        exact hf V hV_open
      Is_cover := by
        intro x hxK
        have hx_img : f x ∈ f '' K := ⟨x, hxK, rfl⟩
        rcases C.Is_cover hx_img with ⟨V, hV_in_C, hx_in_V⟩
        refine ⟨K ∩ f ⁻¹' V, ?mem_D, ?mem_set⟩
        · refine ⟨V, hV_in_C, rfl⟩
        · exact ⟨hxK, hx_in_V⟩
    }
    obtain ⟨F, hF_finite, hF_sub⟩ := hK D --K is Compact
    let G : openCover (f '' K) := {
      Cover := { V : Set Y | ∃ S ∈ F.Cover, ∃ V' ∈ C.Cover, S = K ∩ f ⁻¹' V' ∧ V = V' }
      Open_cover := by
        intro V hV
        rcases hV with ⟨S, hS_in_F, V', hV'_in_C, hS_eq, rfl⟩
        exact C.Open_cover V hV'_in_C
      Is_cover := by
        intro y hy
        rcases hy with ⟨x, hxK, rfl⟩
        have hx_in_F : ∃ S ∈ F.Cover, x ∈ S := by
          have := F.Is_cover hxK
          rcases this with ⟨S, hS_in_F, hxS⟩
          exact ⟨S, hS_in_F, hxS⟩
        rcases hx_in_F with ⟨S, hS_in_F, hxS⟩
        have hS_sub : S ∈ D.Cover := hF_sub hS_in_F
        rcases hS_sub with ⟨V', hV'_in_C, hS_eq⟩
        have hxV' : f x ∈ V' := by
          have := hxS
          rw[hS_eq, Set.inter_def, Set.mem_setOf] at hxS
          exact hxS.right
        refine ⟨V', ?mem_G, hxV'⟩
        exact ⟨S, hS_in_F, V', hV'_in_C, hS_eq, rfl⟩
    }
    use G
    constructor
    · sorry --G is finite
    · intro V hV
      rcases hV with ⟨S, hS_in_F, V', hV'_in_C, hS_eq, rfl⟩
      exact hV'_in_C

theorem ExtremeValueTheorem (K : Set (Rn n)) (hK : Compact K) (f : (Rn n) → (Rn 1))
  (f_cont : ContOn f K) :
  ∃ x_min x_max : K,  ∀ x : K,
  f x_min ≤ f x ∧ f x ≤ f x_max :=
  have hfKCompact : Compact (f '' K) := Compact.image_on hK f_cont
  have h_C_B : Closed (f '' K) ∧ Bounded 1 (f '' K) :=
    (HeineBorel (n := 1) (K := f '' K)).mp hfKCompact
  sorry
