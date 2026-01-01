import Mathlib.Tactic
import Mathlib
import TopologyInLeanProject6Compactness.Definitions.Compactness
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces

open Classical in
open Finset
open scoped Course
open Topology
open Course

variable (n : ℕ)

#check (inferInstance : MetricSpace (Rn n))
#check (inferInstance : TopologicalSpace (Rn n))

universe u
variable {X : Type u} [Topology X]

theorem HeineBorel {n : ℕ} (K : Set (Rn n)) : Compact K ↔ Closed K ∧ Bounded n K := by
  constructor
  case mp =>
    intro comp
    constructor
    case right => --BOUNDED
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
      · --K nonempty
        obtain ⟨x, hxK⟩ := hK --get x out of K
        have : K ⊆ ⋃₀ F.Cover := F.Is_cover
        have hxUnion : x ∈ ⋃₀ F.Cover := by
          rw[Set.subset_def] at this
          apply this
          exact hxK
        let centers : Set (Rn n) :=
          { x₀ | ∃ s ∈ F.Cover, s = Metric.ball x₀ 1 } --set of all centers
        have h_centers_finite : centers.Finite := by --centers is again finite
          have h_center_of : ∀ s : F.Cover, ∃ x₀, (s : Set (Rn n)) = Metric.ball x₀ 1 := by
            intro s
            rw[Set.subset_def] at hsub
            have hsU : (s : Set (Rn n)) ∈ U := hsub s s.property
            rcases hsU with ⟨x₀, hx₀K⟩
            use x₀
            exact hx₀K.right
          choose f hf using h_center_of --function that maps ball s ∈ F.Cover to its center x₀
          have h_centers_subset : centers ⊆ Set.range f := by
            -- centers is the image of the function
            intro x₀ hx₀
            rcases hx₀ with ⟨s, hsF, rfl⟩
            rw [@Set.mem_range]
            let y : F.Cover := ⟨ Metric.ball x₀ 1, hsF⟩
            use y
            specialize hf y
            have h_equal : Metric.ball (f y) 1 = Metric.ball x₀ 1 := by
              exact id (Eq.symm hf)
            have : (1 : ℝ ) > 0 := by
              exact Real.zero_lt_one
            have hx : x₀ ∈ Metric.ball (f y) 1 := by
              rw [h_equal]
              exact Metric.mem_ball_self this
            have hy : (f y) ∈ Metric.ball x₀ 1 := by
              rw [← h_equal]
              exact Metric.mem_ball_self this
            have zero_b_one : (0 : ℝ ) < 1 := zero_lt_one
            exact eq_of_mem_ball_of_mem_ball n hy hx h_equal zero_b_one
          haveI : Fintype F.Cover := hFfin.fintype --convert to fintype
          have h_finite_range : (Set.range f).Finite := Set.finite_range f
          rw[Set.subset_def] at h_centers_subset
          exact Set.Finite.subset h_finite_range h_centers_subset
        let centers_finset : Finset (Rn n) := h_centers_finite.toFinset
        have h_centers_nonempty : centers_finset.Nonempty := by --centers.finset is nonempty
          rcases hxUnion with ⟨s, hsF, hx_in_s⟩
          have hsU : s ∈ U_openCover.Cover := hsub hsF
          have : ∃ x₀ ∈ K, s = Metric.ball x₀ 1 := hsU
          rcases this with ⟨x₀, hx₀K, rfl⟩
          have hx₀_centers : x₀ ∈ centers := by
            refine ⟨Metric.ball x₀ 1, ?_, rfl⟩
            exact hsF
          have h_centers_nonempty_set : centers.Nonempty := ⟨x₀, hx₀_centers⟩ --centers is nonempty
          rcases h_centers_nonempty_set with ⟨c, hc⟩
          have hc_finset : c ∈ centers_finset := by
            simpa [centers_finset] using (h_centers_finite.mem_toFinset.mpr hc)
          exact ⟨c, hc_finset⟩
        let r : ℝ := Finset.sup' centers_finset h_centers_nonempty (fun y ↦  dist y x + 1)
        use r
        have hr : r > 0 := by
          rcases h_centers_nonempty with ⟨ y, hy⟩
          have h_fun : (1 : ℝ) ≤ dist y x + 1 := by
            rw [@le_add_iff_nonneg_left]
            exact dist_nonneg
          apply lt_of_lt_of_le
          · apply zero_lt_one
          exact Finset.le_sup'_of_le (fun y ↦ dist y x + 1) hy h_fun
        use hr
        use x
        intro x₀ hx₀
        have ⟨t, htF, hx₀t⟩ := Set.mem_sUnion.mp (this hx₀) --get ball containing x
        have htU : t ∈ U := by
          rw[Set.subset_def] at hsub
          specialize hsub t
          apply hsub at htF
          exact htF
        unfold U at htU
        rw[Set.mem_setOf] at htU
        rcases htU with ⟨x₁, hx₁K, rfl⟩ --get center of ball t
        rw[Metric.ball] at hx₀t
        rw[Set.mem_setOf] at hx₀t
        have triang : dist x₀ x ≤ dist x₀ x₁ + dist x₁ x := dist_triangle x₀ x₁ x
        have h_smaller_r : 1 + dist x₁ x ≤ r := by
          rw[add_comm]
          unfold r
          have hx₁_centers : x₁ ∈ centers := by
            refine ⟨Metric.ball x₁ 1, htF, rfl⟩
          have hx₁_fin : x₁ ∈ centers_finset := h_centers_finite.mem_toFinset.mpr hx₁_centers
          rw [@Finset.le_sup'_iff]
          use x₁
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
    case left => --CLOSED
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
      have hbx_nbhd : Nbhd bx x := by
        rw[Nbhd]
        constructor
        · sorry
        · unfold bx
          rw [@Set.mem_sInter]
          intro k hk
          rw[Set.mem_setOf] at hk
          obtain ⟨ s, hs,l,hl,h_nbhdkx, h_nbhdsl,hks_empty⟩ := hk
          rcases h_nbhdkx with ⟨hk_open, hxk⟩
          exact hxk
      have hbx_Kc   : bx ⊆ Kᶜ := by
        rw[Set.subset_def]
        intro z hzbx hzK
        have hzUnion : z ∈ ⋃₀ t.Cover := t.Is_cover hzK
        rcases hzUnion with ⟨s, hs_t, hz_in_s⟩
        have hsF : s ∈ F := ht_sub hs_t
        have hsF_def : ∃ y ∈ K, ∃ U, Nbhd U x ∧ Nbhd s y ∧ U ∩ s = ∅ := by
          simpa [F] using hsF
        rcases hsF_def with ⟨y, hyK, U, hUx, hsy, hU_s_empty⟩
        have hU_mem : U ∈ {U | ∃ s ∈ t.Cover, ∃ y ∈ K, Nbhd U x ∧ Nbhd s y ∧ U ∩ s = ∅} := by
          exact ⟨s, hs_t, y, hyK, hUx, hsy, hU_s_empty⟩
        have hz_all : ∀ V ∈ {U | ∃ s ∈ t.Cover, ∃ y ∈ K,
            Nbhd V x ∧ Nbhd s y ∧ V ∩ s = ∅}, z ∈ V := by
          simpa [bx] using hzbx
        have hzU : z ∈ U := hz_all U hU_mem
        have hz_in_inter : z ∈ U ∩ s := ⟨hzU, hz_in_s⟩
        have : z ∈ (∅ : Set (Rn n)) := by
          simpa [hU_s_empty] using hz_in_inter
        exact this.elim
      rw[Nbhd] at hbx_nbhd
      rcases hbx_nbhd with ⟨b, hb⟩
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
    intro h
    rcases h with ⟨hClosed, hBounded⟩
    rcases exists_box_of_bounded (n := n) (K := K) hBounded with
      ⟨a, b, hKsubset⟩
    have hBoxCompact' : Compact (box a b) :=
      hBoxCompact (n := n) a b
    have hKcompact : Compact K :=
      Closed.compact_of_subset
        (X := Rn n)
        hClosed
        hKsubset
        hBoxCompact'
    exact hKcompact
