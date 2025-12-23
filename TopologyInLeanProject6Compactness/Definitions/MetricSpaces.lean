import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.Bases

namespace Course
universe u v
variable {X : Type u} [MetricSpace X]

/-
# Metric Spaces

Defined at https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Defs.html#MetricSpace

class `MetricSpace`
- `dist : α → α → ℝ`
- `dist_self (x : α) : dist x x = 0`
- `dist_comm (x y : α) : dist x y = dist y x`
- `dist_triangle (x y z : α) : dist x z ≤ dist x y + dist y z`

## Open balls

Defined at https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/MetricSpace/Pseudo/Defs.html#Metric.ball

See there for useful theorems.

Also helpful:
- linarith
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/Defs/LinearOrder.html
-/

open Metric

theorem ball_in_ball {x : X} {ε : ℝ} : ∀ y ∈ ball x ε, ∃ δ, (0 < δ ∧ ball y δ ⊆ ball x ε) := by
  simp only [ball, Set.setOf_subset_setOf]
  intro y hy
  simp at hy
  use ε - (dist y x)
  constructor
  case left =>
    linarith
  case right =>
    intro z hz
    have hzyx : dist z y + dist y x < ε := by
      linarith
    have triangle : dist z x ≤ dist z y + dist y x := by
      apply dist_triangle
    linarith

instance metricBasis : Basis X where
  Basics := {B | ∃ x ε, B = ball x ε}
  Basis_cover := by
    rw [Set.sUnion_eq_univ_iff]
    intro a
    use Metric.ball a 1
    simp only [Set.mem_setOf_eq, exists_apply_eq_apply2', mem_ball, dist_self, zero_lt_one,
      and_self]
  Basis_inter := by
    intro b1 hb1 b2 hb2 x hx
    rw [Set.mem_setOf_eq] at hb1
    rw [Set.mem_setOf_eq] at hb2
    obtain ⟨xb1, εb1, hxb1⟩ := hb1
    have w1 : x ∈ ball xb1 εb1 := by
      rw [← hxb1]
      exact hx.left
    obtain ⟨δ1, hδ1⟩ := ball_in_ball x w1
    obtain ⟨xb2, εb2, hxb2⟩ := hb2
    have w2 : x ∈ ball xb2 εb2 := by
      rw [← hxb2]
      exact hx.right
    obtain ⟨δ2, hδ2⟩ := ball_in_ball x w2
    set δ := min δ1 δ2
    use ball x δ
    simp only [Set.mem_setOf_eq, exists_apply_eq_apply2', mem_ball, dist_self, Set.subset_inter_iff,
      true_and]
    constructor
    case left => exact lt_min hδ1.left hδ2.left
    case right =>
      constructor
      case left =>
        have w : ball x δ ⊆ ball x δ1 := by
          apply ball_subset_ball
          exact min_le_left δ1 δ2
        intro z hz
        rw [hxb1]
        apply hδ1.right
        apply w
        exact hz
      case right =>
        have w : ball x δ ⊆ ball x δ2 := by
          apply ball_subset_ball
          exact min_le_right δ1 δ2
        intro z hz
        rw [hxb2]
        apply hδ2.right
        apply w
        exact hz


def metricTopology := @basisTopology X metricBasis

@[simp]
theorem Basic_balls {x : X} {ε : ℝ} : ball x ε ∈ Basis.Basics := by
  use x
  use ε

def Hausdorff [Topology X] : Prop :=
  ∀ x y : X, ¬(x = y) → ∃ U V : Set X, (Nbhd U x) ∧ (Nbhd V y) ∧ U ∩ V = ∅

theorem Hausdorff_metricTopology : @Hausdorff X metricTopology := by
  intro x y neqxy
  set ε := (dist x y / 2)
  use ball x ε
  use ball y ε
  simp only [Nbhd, Open_basisTopology, mem_ball, dist_self]
  constructor
  case left =>
    constructor
    case left =>
      intro z hz
      use ball x ε
      simp only [Basic_balls, mem_ball, subset_refl, and_true, true_and]
      exact hz
    case right =>
      have w : dist x y > 0 := dist_pos.mpr neqxy
      exact half_pos w
  case right =>
    constructor
    case left =>
      constructor
      case left =>
        intro z hz
        use ball y ε
        simp only [Basic_balls, mem_ball, subset_refl, and_true, true_and]
        exact hz
      case right =>
        have w : dist x y > 0 := dist_pos.mpr neqxy
        exact half_pos w
    case right =>
      by_contra c
      rw [Set.eq_empty_iff_forall_notMem] at c
      push_neg at c
      obtain ⟨z, hzx, hzy⟩ := c
      simp only [mem_ball] at hzx
      simp only [mem_ball] at hzy
      have w1 : dist x y ≤ dist z x + dist z y := by
        nth_rw 2 [dist_comm]
        apply dist_triangle
      have w2 : dist z x + dist z y < dist x y:= by
        have w3 : dist x y = ε + ε := by
          ring
        rw [w3]
        apply add_lt_add hzx hzy
      linarith

end Course
