import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.ContinuousFunctions
import TopologyInLeanProject6Compactness.Definitions.Filters
import TopologyInLeanProject6Compactness.Definitions.NewSpaces

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

theorem Compact_Closed_of_Compact
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
      case Cover => exact compl '' C
      case Open_cover =>
        intro s hs
        rw [Set.mem_image] at hs
        obtain ⟨c,hc⟩ := hs
        rw [←hc.2]
        exact closed_C c hc.1
      case Is_cover =>
        rw [← @Set.compl_sInter, empty_inter_C, Set.compl_empty]
    use U
    intro F fin_F F_sub_U
    let D := compl '' F.Cover
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
      have z1 : D ⊆ C := by
        unfold D
        rw [Set.image_subset_iff, ← @Set.compl_image]
        exact F_sub_U
      have z2 : D.Finite := by
        unfold D
        exact Set.Finite.image compl fin_F
      apply fip_C D ⟨z1,z2⟩
    contradiction
  case mpr =>
    contrapose!
    intro h
    rw [Compact] at h; push_neg at h
    obtain ⟨C, hC⟩ := h
    let D := compl '' C.Cover
    have w1 : Closed_collection D := by
      intro d hd
      change d ∈ compl '' C.Cover at hd
      simp only [Set.mem_image] at hd
      obtain ⟨c,hc1,hc2⟩ := hd
      rw [← hc2]
      simp only [Closed, compl_compl]
      exact C.Open_cover c hc1
    have w2 : finite_inter D := by
      intro S ⟨S_sub_D,fin_S⟩
      by_contra! c
      let F : openCover (Set.univ : Set X) := by
        constructor
        case Cover => exact compl '' S
        case Open_cover =>
          intro s hs
          rw [Set.mem_compl_image] at hs
          apply S_sub_D at hs
          unfold D at hs
          simp only [Set.mem_image, compl_inj_iff, exists_eq_right] at hs
          exact C.Open_cover s hs
        case Is_cover =>
          rw [← @Set.compl_sInter, c, Set.compl_empty]
      have fin_F : F.Cover.Finite := by
        change (compl '' S).Finite
        exact Set.Finite.image compl fin_S
      have subcover : subCover F C := by
        rw [subCover]
        change compl '' S ⊆ C.Cover
        rw [@Set.image_subset_iff, ← @Set.compl_image]
        exact S_sub_D
      specialize hC F fin_F
      contradiction
    have w3 : ⋂₀ D = ∅ := by
      unfold D
      have cover : ⋃₀ C.Cover = Set.univ := by
        rw [← Set.univ_subset_iff]
        exact C.Is_cover
      rw [← Set.compl_sUnion, cover, Set.compl_empty_iff]
    use D

open MyFilter

theorem prime_extension (C : Set (Set X)) (fin_inter : finite_inter C) :
∃ F : MyFilter.Filter X, primeFilter F ∧ C ⊆ F.Sets := by
  sorry

def filterCompact (X : Type u) [Topology X] :=
  ∀ (F : MyFilter.Filter X), primeFilter F → ∃ x, F lim x

theorem filterCompact_iff_Compact (X : Type u) [Topology X] :
  filterCompact X ↔ Compact (Set.univ : Set X) := by
  constructor
  case mp =>
    rw [Compact_iff_Closed_finite_inter]
    contrapose!
    intro h
    obtain ⟨C,⟨closed_C,fin_inter_C⟩,inter_empty⟩ := h
    obtain ⟨F,prime_F, C_sub_F⟩ := prime_extension C fin_inter_C
    intro filter_compact
    specialize filter_compact F prime_F
    obtain ⟨x,F_lim_x⟩ := filter_compact
    have w2 : ∀ x, ∃ s ∈ C, x ∉ s := by
      intro y
      by_contra! c
      rw [← Set.mem_sInter] at c
      rw [inter_empty] at c
      contradiction
    obtain ⟨s,s_in_C, x_nin_s⟩ := w2 x
    have sc_nbhd : Nbhd sᶜ x := by
      constructor
      case left =>
        rw [← Closed]
        apply closed_C
        exact s_in_C
      case right =>
        exact x_nin_s
    apply F_lim_x at sc_nbhd
    apply C_sub_F at s_in_C
    have np : ∅ ∈ F.Sets := by
      rw [← Set.inter_compl_self s]
      exact inter_mem s_in_C sc_nbhd
    have p : ∅ ∉ F.Sets := by
      exact prime_F.1
    contradiction
  case mpr =>
    intro compact
    rw [filterCompact]
    by_contra! c
    obtain ⟨F,prime_F,no_lim_F⟩ := c
    have w : ∀ x, ∃ U, Nbhd U x ∧ U ∉ F.Sets := by
      intro x
      specialize no_lim_F x
      rw [filter_convergence] at no_lim_F
      by_contra! c
      contradiction
    choose U hU using w
    let C : openCover (Set.univ : Set X) := by
      constructor
      case Cover => exact ⋃ x, {U x}
      case Open_cover =>
        intro s hs
        simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at hs
        obtain ⟨y,hy⟩ := hs
        rw [← hy]
        exact (hU y).1.1
      case Is_cover =>
        intro y hy
        simp only [Set.iUnion_singleton_eq_range, Set.sUnion_range, Set.mem_iUnion]
        use y
        exact (hU y).1.2
    obtain ⟨G,fin_G, G_sub_C⟩ := compact C
    have w1 : ⋃₀ G.Cover = Set.univ := by
      rw [← Set.univ_subset_iff]
      exact G.Is_cover
    have w2 : ⋃₀ G.Cover ∈ F := by
      rw [w1]; exact univ_mem
    apply prime_finite_sUnion prime_F fin_G at w2
    obtain ⟨c,hc1,hc2⟩ := w2
    apply G_sub_C at hc1
    change c ∈ ⋃ x, {U x} at hc1
    simp at hc1
    obtain ⟨y,hy⟩ := hc1
    rw [← hy] at hc2
    specialize hU y
    apply hU.2
    exact hc2

open Constructions

/- Tychonov's theorem -/
theorem filterCompact_iProduct {I : Type u} (Xs : I → Type u) (TXs : (i : I) → Topology (Xs i)) :
  (∀ i, @filterCompact (Xs i) (TXs i)) →
  @filterCompact (Π i, Xs i) (iProductTopology Xs TXs) := by
    intro h F prime_F
    let pi := fun (i : I) (x : Π i, Xs i) ↦ x i
    have w1 : ∀ (i : I), ∃ x : Xs i, mapFilter (pi i) F lim x := by
      intro i
      apply h i
      exact mapFilter_prime (pi i) F prime_F
    choose l hl using w1
    use l
    intro U nbhd_U
    have z : ∃ (V : Set (Set (Π i, Xs i))),
      ⋂₀ V ⊆ U ∧
      V.Finite ∧
      ∀ v ∈ V, ∃ (i : I) (W : Set (Xs i)), v = (pi i) ⁻¹' W ∧ Open W ∧ (l i) ∈ W
      := by
        obtain ⟨B,hB1,hB2,hB3⟩ := nbhd_U.1 l nbhd_U.2
        obtain ⟨V,hV1,hV2,hV3⟩ := hB1
        rw [hV1] at hB3
        use V
        refine ⟨hB3,hV2,?_⟩
        intro v hV
        obtain ⟨i,W,hiW⟩ := hV3 v hV
        use i; use W
        refine ⟨hiW.1, hiW.2, ?_⟩
        change l ∈ (pi i) ⁻¹' W
        rw [← hiW.1]
        have z : B ⊆ v := by
          rw [hV1]
          intro y hy
          rw [Set.mem_sInter] at hy
          exact hy v hV
        apply z
        exact hB2
    obtain ⟨V,hV1,hV2,hV3⟩ := z
    refine upward_closed ?_ hV1
    apply inter_mem_finite_sInter V hV2
    intro v hv
    specialize hV3 v hv
    obtain ⟨i,W,hiW1,hiW2,hiW3⟩ := hV3
    simp only [mapFilter, filter_convergence] at hl
    rw [hiW1]
    apply hl
    rw [neighborhoods]
    exact ⟨hiW2,hiW3⟩

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
