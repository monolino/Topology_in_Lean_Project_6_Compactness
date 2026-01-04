import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.Compactness
import TopologyInLeanProject6Compactness.Definitions.ContinuousFunctions


namespace Course

open Set
open scoped Course
open Course

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [Topology X] [Topology Y] [Topology Z]



@[simp]
def ContOn {X : Type u} {Y : Type v}
  [Topology X] [Topology Y]
  (f : X → Y) (K : Set X) : Prop :=
  ∀ s, Open s → Open (K ∩ f ⁻¹' s)

lemma Cont.contOn {f : X → Y} (hf : Cont f) (K : Set X) :
  ContOn f K := sorry

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

end Course
