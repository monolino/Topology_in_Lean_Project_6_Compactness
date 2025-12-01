import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.ContinuousFunctions
import TopologyInLeanProject6Compactness.Definitions.Filters

universe u

structure openCover {X : Type u} [Topology X] (K : Set X) where
  Cover : Set (Set X)
  Open_cover : ∀ s ∈ Cover, Open s
  Is_cover : K ⊆ ⋃₀ Cover

def subCover {X : Type u} [Topology X] {K : Set X} (C : openCover K) (D : openCover K) : Prop :=
  C.Cover ⊆ D.Cover

def Compact {X : Type u} [Topology X] (K : Set X) : Prop
  := ∀ (C : openCover K), ∃ (F : openCover K), F.Cover.Finite ∧ subCover F C

variable {X Y : Type u} [Topology X] [Topology Y]

theorem Compact_image (f : X → Y) (cont_f : Cont f) (surj_f : Function.Surjective f) (K : Set X) :
  Compact K → Compact (f '' K) := by
  intro compact_X C
  let D : openCover K := by
    constructor
    case Cover => exact (Set.preimage f) '' C.Cover
    case Open_cover =>
      intro s hs
      rw [Set.mem_image] at hs
      obtain ⟨c,hc1,hc2⟩ := hs
      rw [← hc2]
      apply cont_f
      exact C.Open_cover c hc1
    case Is_cover =>
      intro x h
      rw [Set.mem_sUnion]
      have w : ∃ s ∈ C.Cover, x ∈ f ⁻¹' s := by
        simp only [Set.mem_preimage]
        rw [← @Set.mem_sUnion]
        apply C.Is_cover
        use x
      obtain ⟨s,hs1,hs2⟩ := w
      have hs3 : f ⁻¹' s ∈ Set.preimage f '' C.Cover := by
        rw [Set.mem_image]
        use s
      use f ⁻¹' s
  obtain ⟨F,fin_N,sub_D⟩  := compact_X D
  let G : openCover (f '' K) := by
    constructor
    case Cover => exact (Set.image f) '' F.Cover
    case Open_cover =>
      intro s hs
      obtain ⟨d,hd1,hd2⟩ := hs
      apply sub_D at hd1
      obtain ⟨c,hc1,hc2⟩ := hd1
      rw [← hc2] at hd2
      rw [Set.image_preimage_eq c surj_f] at hd2
      rw [← hd2]
      exact C.Open_cover c hc1
    case Is_cover =>
      rw [← Set.image_sUnion]
      exact Set.image_mono F.Is_cover
  use G
  constructor
  case left => apply Set.Finite.image (Set.image f) (fin_N)
  case right =>
    intro d hd
    change d ∈ (Set.image f) '' F.Cover at hd
    apply Set.image_mono sub_D at hd
    change d ∈ Set.image f '' ((Set.preimage f) '' C.Cover) at hd
    simp only [Set.mem_image, exists_exists_and_eq_and] at hd
    obtain ⟨c,hc1,hc2⟩ := hd
    rw [Set.image_preimage_eq c surj_f] at hc2
    rw [← hc2]
    exact hc1

theorem Compact_Closed_of_Compact {W : Type u} [Topology W]
  (compact_X : Compact (Set.univ : Set X)) (K : Set X) (closed_K : Closed K) : Compact K := by
  intro C
  let D : openCover (Set.univ : Set X) := by
    constructor
    case Cover => exact C.Cover ∪ {Kᶜ}
    case Open_cover =>
      intro s hs
      obtain h1 | h2 := hs
      case inl => exact C.Open_cover s h1
      case inr =>
        rw [Set.mem_singleton_iff] at h2
        rw [h2]
        exact closed_K
    case Is_cover =>
      rw [@Set.sUnion_union]
      intro x hx
      by_cases h : x ∈ K
      case pos => left; exact C.Is_cover h
      case neg => right; rw [@Set.sUnion_singleton]; trivial
  obtain ⟨G,fin_G,sub_D⟩ := compact_X D
  let F : openCover K := by
    constructor
    case Cover => exact G.Cover \ {Kᶜ}
    case Open_cover => intro s hs; exact G.Open_cover s hs.1
    case Is_cover =>
      intro k hk
      have w : ∃ c ∈ G.Cover, k ∈ c := by
        rw [← Set.mem_sUnion]
        apply G.Is_cover
        trivial
      obtain ⟨c,hc1,hc2⟩ := w
      have w2 : c ≠ Kᶜ := by
        intro h
        rw [h] at hc2
        contradiction
      have w3 : c ∈ G.Cover \ {Kᶜ} := by
        constructor
        case left => exact hc1
        case right =>
          intro h
          rw [Set.mem_singleton_iff] at h
          contradiction
      rw [Set.mem_sUnion]
      use c
  use F
  constructor
  case left =>
    have w : F.Cover ⊆ G.Cover := Set.diff_subset
    exact Set.Finite.subset fin_G w
  case right =>
    intro c hc
    change c ∈ G.Cover \ {Kᶜ} at hc
    have hc1 : c ∈ G.Cover := hc.1
    have hc2 : c ≠ Kᶜ := hc.2
    apply sub_D at hc1
    obtain h1 | h2 := hc1
    case inl => trivial
    case inr => contradiction

def finite_inter (C : Set (Set X)) : Prop := ∀ S, S ⊆ C ∧ S.Finite → (⋂₀ S).Nonempty

def Closed_collection (C : Set (Set X)) : Prop := ∀ c ∈ C, Closed c

theorem Compact_iff_Closed_finite_inter :
  Compact (Set.univ : Set X) ↔
  ∀ C : Set (Set X), Closed_collection C ∧ finite_inter C → (⋂₀ C).Nonempty := by
  constructor
  case mp =>
    contrapose!
    intro h
    obtain ⟨C, ⟨closed_C, fip_C⟩, empty_inter_C⟩ := h
    rw [Compact]; push_neg
    let U : openCover (Set.univ : Set X) := by
      constructor
      case Cover => exact (fun c ↦ cᶜ) '' C
      case Open_cover => sorry
      case Is_cover => sorry
    use U
    intro F fin_F
    let D := (fun c ↦ cᶜ) '' F.Cover
    have w1 : ¬ (⋂₀ D).Nonempty := by
      have z : Set.univ = ⋃₀ F.Cover := by
        rw [Set.Subset.antisymm_iff]
        constructor
        case left => exact F.Is_cover
        case right => intro x hx; trivial
      unfold D
      rw [← @Set.compl_sUnion, ← z]
      simp only [Set.compl_univ, Set.not_nonempty_empty, not_false_eq_true]
    have w2 : (⋂₀ D).Nonempty := by
      have z1 : D ⊆ C := by sorry
      have z2 : D.Finite := by sorry
      apply fip_C D ⟨z1,z2⟩
    contradiction
  case mpr =>
    contrapose!
    intro h
    rw [Compact] at h; push_neg at h
    obtain ⟨C, hC⟩ := h
    sorry

open MyFilter

def filterCompact (X : Type u) [Topology X] := ∀ (F : MyFilter.Filter X), primeFilter F → ∃ x, F lim x

theorem filterCompact_iff_Compact (X : Type u) [Topology X] :
  filterCompact X ↔ Compact (Set.univ : Set X) := by sorry

/- Tychonov's theorem -/


/- This section shows a alternate attempt to define the concepts using indexed collections of sets.
This approach does not seem to allow easy extension of covers. -/
namespace AltAttempt

structure openCover (I : Type u) (X : Type u) [Topology X] where
  Cover : I → Set X
  Open_cover : ∀ i, Open (Cover i)
  Is_cover : (⋃ i, Cover i) = Set.univ

def subCover {I J : Type u} {X : Type u} [Topology X] (s : I → J) (C : openCover J X) : Prop :=
  Function.Injective s ∧
  (⋃ i : I, C.Cover (s i)) = Set.univ

def Compact (X : Type u) [Topology X] : Prop
  := ∀ (I : Type u) (C : openCover I X), ∃ (N : Type u) (s : N → I), Finite N ∧ subCover s C

variable {X Y : Type u} [Topology X] [Topology Y]

def pullbackCover {I : Type u} (f : X → Y) (cont_f : Cont f) (C : openCover I Y)
  : openCover I X where
  Cover := fun i ↦ f ⁻¹' (C.Cover i)
  Open_cover := by
    intro i
    apply cont_f
    exact C.Open_cover i
  Is_cover := by
    rw [← Set.preimage_iUnion, C.Is_cover, Set.preimage_univ]

theorem Compact_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f) :
  Compact X → Compact Y := by
  intro compact_X
  intro I C
  let D := pullbackCover f cont_f C
  rw [Compact] at compact_X
  obtain ⟨N,s,fin_N,sub_s_D⟩  := compact_X I D
  use N ; use s
  constructor
  case left => exact fin_N
  case right =>
    constructor
    case left => exact sub_s_D.1
    case right =>
      rw [Set.iUnion_eq_univ_iff]
      intro y
      obtain ⟨x, hx⟩ := surj_f y
      rw [← @Set.mem_iUnion, ← hx, ← Set.mem_preimage, Set.preimage_iUnion]
      have w : x ∈ ⋃ i, D.Cover (s i) := by
        rw [sub_s_D.2]
        trivial
      apply w

theorem Compact_Closed_of_Compact {W : Type u} [Topology W]
  (f : W → X) (cont_f : Cont f) (open_f : OpenMap f)
  (compact_X : Compact X) (closed_image : Closed (f '' Set.univ)) : Compact W := by
  intro I C
  let sets : I ⊕ Unit → Set X
    | Sum.inl i => f '' C.Cover i
    | Sum.inr () => (f '' Set.univ)ᶜ
  let D : openCover (I ⊕ Unit) X := by
    constructor
    case Cover => exact sets
    case Open_cover =>
      intro i
      obtain j | u := i
      case inl =>
        change Open ( f '' C.Cover j)
        apply open_f
        apply C.Open_cover
      case inr =>
        change Open ( (f '' Set.univ)ᶜ )
        apply closed_image
    case Is_cover =>
      have u : ⋃ j : I ⊕ Unit, sets j = (⋃ i : I, f '' C.Cover i) ∪ (f '' Set.univ)ᶜ := by
        ext x; constructor
        case mp =>
          intro hx
          rw [Set.mem_iUnion] at hx
          obtain ⟨i,hi⟩ := hx
          obtain j | u := i
          case inl =>
            change x ∈ f '' C.Cover j at hi
            left
            rw [Set.mem_iUnion]
            use j
          case inr =>
            change x ∈ (f '' Set.univ)ᶜ at hi
            right
            exact hi
        case mpr =>
          intro hx
          obtain hx1 | hx2 := hx
          case inl => sorry
          case inr => sorry
      rw [u, ← Set.image_iUnion, C.Is_cover, Set.image_univ, Set.union_compl_self]
  obtain ⟨N,s,fin_N,sub_D⟩ := compact_X (I ⊕ Unit) D
  let s' := Set.restrictPreimage (Sum.inl '' (Set.univ : Set I)) s
  -- It is not obvious to me how to restrict s to a map N' -> I.
  sorry

end AltAttempt
