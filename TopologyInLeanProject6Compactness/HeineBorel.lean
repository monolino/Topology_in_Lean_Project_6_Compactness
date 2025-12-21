import TopologyInLeanProject6Compactness.Definitions.Compactness
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces

open Classical in

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
      have U_openCover : openCover K := {
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
      use 1
      have hr : (1 : ℝ) > 0 := by
        linarith
      use hr
      rw [Set.finite_def] at hFfin
      --let s0 : Set (Rn n) := Nonempty.some (hFfin) --take element out of nonempty
      sorry





    case left =>
      sorry
  case mpr =>
    sorry
