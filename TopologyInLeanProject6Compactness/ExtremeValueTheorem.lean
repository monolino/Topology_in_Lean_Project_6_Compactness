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

lemma ContOn.toContinuousOn
    (hf : ContOn f K) :
    ContinuousOn f K := by
  intro x hx
  refine ContinuousAt_iff_continuousAtWithin.2 ?_
  have h := hf
  unfold ContinuousWithinAt
  intro s hs_open hfx
  have h_pre := h s hs_open
  have hx_in : x ∈ K ∩ f ⁻¹' s := by
    exact ⟨hx, hfx⟩
  have hx_int : x ∈ interior (K ∩ f ⁻¹' s) :=
    IsOpen.mem_interior h_pre hx_in
  simpa [mem_interior_iff_mem_nhds] using hx_int


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
      { Cover := { u | ∃ s ∈ F.Cover, s = f ⁻¹' u ∧ u ∈ U.Cover },
        Open_cover := by
          intro t ht
          rcases ht with  ⟨s, hsF, k⟩
          rcases k with ⟨ hk, htU⟩
          exact U.Open_cover t htU
        Is_cover := by
          intro y hy
          rcases hy with ⟨x, hxK, rfl⟩
          have hxV : x ∈ ⋃₀ V.Cover := V.Is_cover hxK
          rcases Set.mem_sUnion.mp hxV with ⟨s, hsV, hxs⟩
          rcases hsV with ⟨u, huU, rfl⟩
          refine Set.mem_sUnion.mpr ?_
          refine ⟨u, ?_, ?_⟩
          · rw[Set.mem_setOf]
            sorry
          · simpa using hxs
      }


theorem ExtremeValueTheorem (K : Set (Rn n)) (hK : Compact K) (f : (Rn n) → (Rn 1))
  (f_cont : ContOn f K) :
  ∃ x_min x_max : K,  ∀ x : K,
  f x_min ≤ f x ∧ f x ≤ f x_max := by
  have hfKCompact : Compact (f '' K) := sorry
  have h_C_B : Closed (f '' K) ∧ Bounded 1 (f '' K) :=
    (HeineBorel (n := 1) (K := f '' K)).mp hfKCompact
  sorry
