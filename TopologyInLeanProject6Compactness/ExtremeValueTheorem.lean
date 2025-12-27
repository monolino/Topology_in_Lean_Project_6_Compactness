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

lemma Compact.image {X Y} [Topology X] [Topology Y]
    {K : Set X} (hK : Compact K)
    {f : X → Y} (hf : Cont f) :
    Compact (f '' K) := by
    intro U
    let V : openCover K :=
      { Cover := { s | ∃ t ∈ U.Cover, s = f ⁻¹' t } --pullback cover
        Open_cover := by
          intro s hs
          rcases hs with ⟨t, htU, rfl⟩
          exact hf t (U.Open_cover t htU)
        Is_cover := by
          intro x hxK
          have : f x ∈ ⋃₀ U.Cover := U.Is_cover ⟨x, hxK, rfl⟩
          rw[Set.sUnion] at this
          rcases this with ⟨t, htU, hxt⟩
          refine Set.mem_sUnion.mpr ?_
          refine ⟨f ⁻¹' t, ?_, ?_⟩
          · exact ⟨t, htU, rfl⟩
          · simpa using hxt
      }
    rcases hK V with ⟨F, hFfin, hFsub⟩ --K is compact
    let F' : openCover (f '' K) :=
      { Cover := { t | ∃ s ∈ F.Cover, t = f '' s },
        Open_cover := by
          intro t ht
          rcases ht with ⟨s, hsF, rfl⟩
          sorry
        Is_cover := by
          intro y hy
          rcases hy with ⟨x, hxK, rfl⟩
          sorry
      }
    refine ⟨F', ?_, ?_⟩
    · sorry
    · sorry

theorem ExtremeValueTheorem (K : Set (Rn n)) (hK : Compact K) (f : (Rn n) → (Rn 1))
  (f_cont : Cont f) :
  ∃ x_min x_max : K,  ∀ x : K,
  f x_min ≤ f x ∧ f x ≤ f x_max := by
  have hfKCompact : Compact (f '' K) := hK.image f_cont
  have h_C_B : Closed (f '' K) ∧ Bounded 1 (f '' K) :=
    (HeineBorel (n := 1) (K := f '' K)).mp hfKCompact
  sorry
