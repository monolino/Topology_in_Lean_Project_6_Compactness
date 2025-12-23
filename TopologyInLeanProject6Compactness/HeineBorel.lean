import TopologyInLeanProject6Compactness.Definitions.Compactness
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces

open Classical in
open Finset

def Rn (n : ℕ) : Type := (Fin n → ℝ)

--Euclidean distance
@[simp]
noncomputable def Eucldist (n : ℕ) (x y : Rn n) : ℝ := Real.sqrt (∑ i , (x i- y i)^2)

noncomputable instance Rn_metric_space (n : ℕ) : MetricSpace (Rn n) := {
  dist := Eucldist n
  dist_self := by
    intro x
    simp
  dist_comm := by
    intro x y
    simp
    congr
    ext i
    ring
  dist_triangle := by
    intro x y z
    simp
    sorry
  eq_of_dist_eq_zero := by
    intro x y hxy
    simp at hxy
    sorry
}

noncomputable def Rn_topology (n : ℕ) : Topology (Rn n) :=
{ Open := fun U ↦ ∀ x ∈ U, ∃ ε > 0, ∀ y, Eucldist n x y < ε → y ∈ U,
  Open_univ := by
    intro x hx
    use 1
    constructor
    · linarith
    intro y hy
    trivial
  Open_inter := by
    intros U V hU hV x hx
    rcases hx with ⟨hxU, hxV⟩
    rcases hU x hxU with ⟨ Uε ,hUε, hUε_prop⟩
    rcases hV x hxV with ⟨ Vε, hVε , hVε_prop⟩
    let total_ε := min Uε Vε
    use total_ε
    constructor
    · exact lt_min hUε hVε
    intro y hy
    have hU' : Eucldist n x y < Uε :=
      lt_of_lt_of_le hy (min_le_left _ _)
    have hV' : Eucldist n x y < Vε :=
      lt_of_lt_of_le hy (min_le_right _ _)
    exact ⟨hUε_prop y hU', hVε_prop y hV'⟩
  Open_sUnion := by
    intros S hS x hx
    rcases hx with ⟨U, hUinS, hxU⟩
    rcases hS U hUinS x hxU with ⟨ε, hε_pos, hUprop⟩
    use ε
    constructor
    · exact hε_pos
    intro y hy
    exact ⟨U, hUinS, hUprop y hy⟩
}

def Bounded (K : Set (Rn n)) : Prop := ∃ (r : ℝ) (hr : r > 0) (x₀ : Rn n), ∀ x ∈ K, dist x x₀ < r

theorem HeineBorel {n : ℕ} (K : Set (Rn n)) : Compact K ↔ Closed K ∧ Bounded K := by
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
          have h_fun : 1 ≤ dist y x₀ + 1 := by
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
      have h_hausdorff : @Hausdorff (X?) (Rn_topology n) (Rn n) :=  sorry

  case mpr =>
    intro h
    rcases h with ⟨hClosed, hBounded⟩ -- split hypothesis into two parts, prove them seperately
    rcases hBounded with ⟨r, hr, x₀, hx⟩
    let a : Rn n := fun i => x₀ i - r
    let b : Rn n := fun i => x₀ i + r
    have hKsubset : K ⊆ box a b := by
      intro x hxK i
  -- use hx x hxK and translate dist bound to coordinate bounds


    -- FROM AI: weiss nöd gnau wie wiiter, basically die beide hypothesis prove
    -- Step 1: use boundedness to find a bounding box
    rcases exists_box_of_bounded (K := K) hBounded with ⟨a, b, hKsubset⟩

    -- Step 2: the box itself is compact (Tychonoff on intervals)
    have hBoxCompact : Compact (box a b) :=
      compact_box a b

    -- Step 3: K is a closed subset of a compact set ⇒ K is compact
    have hKcompact : Compact K :=
      Compact_closed_subset_of_subset hBoxCompact hClosed hKsubset

    exact hKcompact
