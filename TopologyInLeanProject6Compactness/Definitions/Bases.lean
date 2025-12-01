import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.ContinuousFunctions

universe u v
open Set

class Basis (X : Type u) : Type u where
  Basics : Set (Set X)
  Basis_cover : ⋃₀Basics = univ
  Basis_inter : ∀ b1 ∈ Basics, ∀ b2 ∈ Basics, ∀ x ∈ b1 ∩ b2, ∃ b3 ∈ Basics, x ∈ b3 ∧ b3 ⊆ b1 ∩ b2

variable {X : Type u} {Y : Type v}

section
variable [B : Basis X]

@[simp]
theorem Basis_cover : ⋃₀B.Basics = univ := B.Basis_cover

theorem Basis_cover_x (x : X) : ∃ bx ∈ B.Basics, x ∈ bx := by
  rw [← mem_sUnion, Basis_cover]
  trivial

instance basisTopology : Topology X where
  Open := fun U ↦ ∀ x ∈ U, ∃ bx ∈ B.Basics, x ∈ bx ∧ bx ⊆ U
  Open_univ := by
    intro x hx
    simp only [subset_univ, and_true]
    apply Basis_cover_x
  Open_inter := by
    intro U V open_U open_V x hx
    specialize open_U x hx.left
    obtain ⟨bUx, hbUx1, hbUx2, hbUx3⟩ := open_U
    specialize open_V x hx.right
    obtain ⟨bVx, hbVx1, hbVx2, hbVx3⟩ := open_V
    have w : ∃ bUVx ∈ B.Basics, x ∈ bUVx ∧ bUVx ⊆ bUx ∩ bVx := by
      apply B.Basis_inter
      · exact hbUx1
      · exact hbVx1
      · exact ⟨hbUx2, hbVx2⟩
    obtain ⟨bUVx, hbUVx1, hbUVx2, hbUVx3⟩ := w
    have z : bUVx ⊆ U ∩ V := by
      intro y hy
      apply hbUVx3 at hy
      exact ⟨hbUx3 hy.left, hbVx3 hy.right⟩
    use bUVx
  Open_sUnion := by
    intro S hS x hx
    rw [mem_sUnion] at hx
    obtain ⟨Ux, hUx1, hUx2⟩ := hx
    specialize hS Ux hUx1 x hUx2
    obtain ⟨bx, hbx1, hbx2, hbx3⟩ := hS
    have w : bx ⊆ ⋃₀S := by
      intro y hy
      specialize hbx3 hy
      rw [mem_sUnion]
      use Ux
    use bx

@[simp]
theorem Open_basisTopology {U : Set X} : Open U ↔ ∀ x ∈ U, ∃ bx ∈ B.Basics, x ∈ bx ∧ bx ⊆ U := by
  trivial

@[simp]
theorem Open_Basics : ∀ b ∈ B.Basics, Open b := by
  intro b basic_b x hx
  use b

def IsBasis [Topology X] : Prop :=
  (∀ b ∈ B.Basics, Open b) ∧
  (∀ U, Open U → ∃ C ⊆ B.Basics, U = ⋃₀ C)

theorem IsBasis_basisTopology : @IsBasis X B basisTopology := by
  constructor
  case left => apply Open_Basics
  case right =>
    intro U open_U
    have w : ∀ x ∈ U, ∃ Bx ∈ B.Basics, x ∈ Bx ∧ Bx ⊆ U := open_U
    set C := {Bx ∈ B.Basics | Bx ⊆ U}
    use C
    constructor
    case left =>
      intro y hy
      exact hy.1
    case right =>
      ext y; constructor
      case mp =>
        intro hy
        rw [mem_sUnion]
        specialize w y hy
        obtain ⟨Bx,hBx1, hBx2, hBx3⟩ := w
        have z : Bx ∈ C := by
          rw [mem_setOf]
          constructor
          case left => exact hBx1
          case right => exact hBx3
        use Bx
      case mpr =>
        intro hy
        rw [mem_sUnion] at hy
        obtain ⟨By, hBy1, hBy2⟩ := hy
        apply hBy1.right
        exact hBy2

end

variable [Topology X] [BY : Basis Y]

theorem Cont_Basics (f : X → Y) : Cont f ↔ ∀ b ∈ BY.Basics, Open (f ⁻¹' b) := by
  constructor
  case mp =>
    intro cont_f b basic_b
    apply cont_f
    exact Open_Basics b basic_b
  case mpr =>
    intro h U open_U
    have w : ∃ C ⊆ BY.Basics, U = ⋃₀ C :=
      IsBasis_basisTopology.right U open_U
    obtain ⟨C, hC1, hC2⟩ := w
    rw [hC2]
    rw [Set.preimage_sUnion, ← Set.sUnion_image]
    apply Open_sUnion
    simp only [Set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro V hV
    apply hC1 at hV
    exact h V hV
