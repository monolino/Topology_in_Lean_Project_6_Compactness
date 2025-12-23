import Mathlib.Tactic
import Mathlib
import TopologyInLeanProject6Compactness.Definitions.Compactness
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces


open Classical in
open Finset
open Course

variable (n : ℕ)

abbrev Rn (n : ℕ) : Type := (Fin n → ℝ)

#check (inferInstance : MetricSpace (Rn n))
#check (inferInstance : TopologicalSpace (Rn n))

def Bounded (K : Set (Rn n)) : Prop := ∃ (r : ℝ) (hr : r > 0) (x₀ : Rn n), ∀ x ∈ K, dist x x₀ < r

theorem HeineBorel {n : ℕ} (K : Set (Rn n)) : Compact K ↔ Closed K ∧ Bounded n K := by
  constructor
  case mp =>
    intro comp
    constructor
    case right =>
      --open Cover of balls with radius 1 around each point in K
      let U : Set (Set (Rn n)) := { s | ∃ x ∈ K, s = Metric.ball (x : Rn n) 1 }
      let U_openCover : openCover K := {
        Cover := U,
        Open_cover := by
          intro s hs
          rcases hs with ⟨ x, hxK, rfl⟩
          apply Open_Basics
          exact Basic_balls
        Is_cover := by
          intro x hx
          apply Set.mem_sUnion.mpr
          use Metric.ball x 1
          constructor
          · use x
          · rw[Metric.ball]
            rw [@Set.mem_setOf_eq]
            have distZero : dist x x = 0 := dist_self x
            rw[distZero]
            linarith
      }
      rw[Compact] at comp
      specialize comp U_openCover
      rcases comp with ⟨F, hFfin, hsub⟩
      rw[subCover] at hsub
      rw[Bounded]
      by_cases hK : K.Nonempty
      · obtain ⟨x, hxK⟩ := hK --get x out of K
        have : K ⊆ ⋃₀ F.Cover := F.Is_cover
        have hxUnion : x ∈ ⋃₀ F.Cover := by
          rw[Set.subset_def] at this
          apply this
          exact hxK
        rcases hxUnion with ⟨t, htF, hxt⟩ --get ball out of cover
        rw[Set.subset_def] at hsub
        have htU : t ∈ U := by
          specialize hsub t
          apply hsub at htF
          exact htF
        unfold U at htU
        rw[Set.mem_setOf] at htU
        rcases htU with ⟨x₀, hx₀K, rfl⟩ --get center of ball t
        let centers : Set (Rn n) := { x₀ | ∃ s ∈ F.Cover, ∃ x₀ ∈ K, s = Metric.ball x₀ 1 } --set of all centers
        have h_centers_finite : centers.Finite := sorry
        let centers_finset : Finset (Rn n) := h_centers_finite.toFinset
        have h_centers_nonempty : centers_finset.Nonempty := sorry
        let r : ℝ := Finset.sup' centers_finset h_centers_nonempty (fun y ↦  dist y x₀ + 1)
        use r
        have hr : r > 0 := by
          rcases h_centers_nonempty with ⟨ y, hy⟩
          have h_fun : (1 : ℝ) ≤ dist y x₀ + 1 := by
            rw [@le_add_iff_nonneg_left]
            exact dist_nonneg
          apply lt_of_lt_of_le
          apply zero_lt_one
          exact Finset.le_sup'_of_le (fun y ↦ dist y x₀ + 1) hy h_fun
        use hr
        use x₀
        intro x hx
        have ⟨t, htF, hxt⟩ := Set.mem_sUnion.mp (this hx) --get ball containing x
        have htU : t ∈ U := by
          specialize hsub t
          apply hsub at htF
          exact htF
        unfold U at htU
        rw[Set.mem_setOf] at htU
        rcases htU with ⟨x₁, hx₁K, rfl⟩ --get center of ball t
        rw[Metric.ball] at hxt
        rw[Set.mem_setOf] at hxt
        have triang : dist x x₀ ≤ dist x x₁ + dist x₁ x₀ := dist_triangle x x₁ x₀
        have h_smaller_r : dist x₁ x₀ + 1 < r := by
          sorry
        linarith
      · --empty K
        let r : ℝ := 1
        have hr : r > 0 := by linarith
        use r
        use hr
        push_neg at hK
        let x₀ : Rn n := fun i ↦ 0 -- 0 ∈ Rn n
        use x₀
        rw[hK]
        intro x hx
        cases hx
    case left =>
      have h_hausdorff : Hausdorff (X := Rn n) := Hausdorff_metricTopology
      rw[Closed]
      intro x hx
      have h_sep : ∀ y ∈ K, ∃ U V, Nbhd U x ∧ Nbhd V y ∧ U ∩ V = ∅ := by
        intro y hy
        have hxy : x ≠ y := by
          intro h
          apply hx
          simpa [h] using hy
        simpa using h_hausdorff x y hxy
      let F : Set (Set (Rn n)) := {V | ∃ y ∈ K, ∃ U, Nbhd U x ∧ Nbhd V y ∧ U ∩ V = ∅} --cover of K
      let F_openCover : openCover K := { --proof F is openCover
        Cover := F,
        Open_cover := by
          intro s hs
          unfold F at hs
          rw[Set.mem_setOf] at hs
          rcases hs with ⟨y, hyK, U, hUx, hVy, h_disj⟩
          rw[Nbhd] at hVy
          exact hVy.left
        Is_cover := by
          intro y hy
          rcases h_sep y hy with ⟨U, V, hUx, hVy, h_disj⟩
          refine Set.mem_sUnion.mpr ?_
          refine ⟨V, ?_, ?_⟩
          · exact ⟨y, hy, U, hUx, hVy, h_disj⟩
          · rw[Nbhd] at hVy
            exact hVy.right
      }
      rw[Compact] at comp
      specialize comp F_openCover
      rcases comp with ⟨ t, ht, ht_sub⟩
      let bx := ⋂₀ {U | ∃ s ∈ t.Cover, ∃ y ∈ K, Nbhd U x ∧ Nbhd s y ∧ U ∩ s = ∅}
      have hbx_nbhd : Nbhd bx x := sorry
      have hbx_Kc   : bx ⊆ Kᶜ := sorry
      rw[Nbhd] at hbx_nbhd
      rcases hbx_nbhd with ⟨b, hb⟩
      --rw[Basis.Basics]
      --rw[metricBasis]
      rw[Open, Topology.Open,  basisTopology] at b
      specialize b x
      apply b at hb
      rcases hb with ⟨B, hB_basic, hxB, hB_subset_bx⟩ -- this is what we want
      use B
      have hBK : B ⊆ Kᶜ := by
        intro z hz
        apply hbx_Kc
        rw[Set.subset_def] at hB_subset_bx
        apply hB_subset_bx at hz
        exact hz
      exact ⟨ hB_basic, hxB, hBK⟩
  case mpr =>
    sorry
