import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.ContinuousFunctions
import TopologyInLeanProject6Compactness.Definitions.Filters
import TopologyInLeanProject6Compactness.Definitions.NewSpaces
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces
namespace Course

open scoped Course

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

theorem Compact_image_2 (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f) :
  Compact X → Compact Y := by
  intro compact_X I C
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

def box {n : ℕ} (a b : Rn n) : Set (Rn n) := { x | ∀ i, a i ≤ x i ∧ x i ≤ b i }

lemma Compact_def {X : Type u} [Topology X] (K : Set X) : Compact K ↔
    ∀ (C : openCover K), ∃ (F : openCover K), F.Cover.Finite ∧ subCover F C := by
  rfl

lemma exists_box_of_bounded {n : ℕ} {K : Set (Rn n)} :
  Bounded n K →  ∃ a b : Rn n, K ⊆ box a b := by
  intro hB
  rcases hB with ⟨r, hr, x₀, hdist⟩
  let a : Rn n := fun i => x₀ i - r
  let b : Rn n := fun i => x₀ i + r
  refine ⟨a, b, ?_⟩
  intro x hx i
  have hxball : dist x x₀ < r := hdist x hx
  have hcoord : |x i - x₀ i| ≤ dist x x₀ := by
    simpa [dist_eq_norm] using norm_le_pi_norm (i := i) (x - x₀)
  have hlt : |x i - x₀ i| < r :=
    lt_of_le_of_lt hcoord hxball
  constructor
  case right =>
    have hx_lt : x i - x₀ i < r := by
      exact (abs_lt.mp hlt).2
    have : x i < x₀ i + r := by linarith
    exact le_of_lt this
  case left =>
    have hx_gt : -r < x i - x₀ i := by
      exact (abs_lt.mp hlt).1
    have : x₀ i - r < x i := by linarith
    exact le_of_lt this

/-- If `L` is compact in the `openCover` sense, and `K` is a closed subset of `L`,
then `K` is compact. -/
lemma Closed.compact_of_subset {K L : Set X}
    (hK_closed : Closed K) (hKL : K ⊆ L) (hL_compact : Compact L) : Compact K := by
  intro C
  classical
  let D : openCover L :=
  { Cover      := C.Cover ∪ {Kᶜ}
    Open_cover := by
      intro s hs
      rcases hs with hs | hs
      case inl =>
        exact C.Open_cover s hs
      case inr =>
        have : s = Kᶜ := by
          simpa [Set.mem_singleton_iff] using hs
        subst this
        simpa [Closed] using hK_closed
    Is_cover   := by
      intro x hxL
      by_cases hxK : x ∈ K
      case pos =>
        have hxUnionC : x ∈ ⋃₀ C.Cover := C.Is_cover hxK
        apply Set.mem_sUnion.mpr
        rcases Set.mem_sUnion.mp hxUnionC with ⟨s, hsC, hxs⟩
        refine ⟨s, ?_, hxs⟩
        exact Or.inl hsC
      case neg =>
        apply Set.mem_sUnion.mpr
        refine ⟨Kᶜ, ?_, ?_⟩
        case refine_1 =>
          exact Or.inr (by simp)
        case refine_2 =>
          simpa [Set.mem_compl] using hxK
  }
  obtain ⟨F, hF_fin, hF_sub⟩ := hL_compact D
  let G : openCover K :=
  { Cover      := F.Cover \ {Kᶜ}
    Open_cover := by
      intro s hs
      exact F.Open_cover s hs.1
    Is_cover   := by
      intro x hxK
      have hxL : x ∈ L := hKL hxK
      have coverF : L ⊆ ⋃₀ F.Cover := F.Is_cover
      have hxUnionF : x ∈ ⋃₀ F.Cover := coverF hxL
      rcases Set.mem_sUnion.mp hxUnionF with ⟨s, hsF, hxs⟩
      have hsD : s ∈ D.Cover := hF_sub hsF
      have hsNotKc : s ≠ Kᶜ := by
        intro h
        subst h
        have : x ∈ Kᶜ := hxs
        exact this (by exact hxK)
      have hsG : s ∈ F.Cover \ {Kᶜ} := by
        refine ⟨hsF, ?_⟩
        intro hsKc
        have : s = Kᶜ := by
          simpa [Set.mem_singleton_iff] using hsKc
        exact hsNotKc this
      apply Set.mem_sUnion.mpr
      exact ⟨s, hsG, hxs⟩
  }
  refine ⟨G, ?_, ?_⟩
  case refine_1 =>
    have hSub : G.Cover ⊆ F.Cover := by
      intro s hs
      exact hs.1
    exact Set.Finite.subset hF_fin hSub
  case refine_2 =>
    intro s hsG
    have hsF : s ∈ F.Cover := hsG.1
    have hsD : s ∈ D.Cover := hF_sub hsF
    change s ∈ C.Cover ∪ {Kᶜ} at hsD
    rcases hsD with hsC | hsKc
    case inl =>
      exact hsC
    case inr =>
      have : s = Kᶜ := by
        simpa [Set.mem_singleton_iff] using hsKc
      have : s ≠ Kᶜ := hsG.2
      exact (this ‹s = Kᶜ›).elim

lemma IsCompact.toCompact {X : Type u} [TopologicalSpace X] [Topology X]
  {K : Set X} (hK : IsCompact K) : Compact K := by
  sorry
  /- classical
  intro C
  have h' :
      ∀ (U : Set (Set X)),
        (∀ s ∈ U, IsOpen s) →
        K ⊆ ⋃₀ U →
        ∃ V ⊆ U, V.Finite ∧ K ⊆ ⋃₀ V :=
    (isCompact_iff_finite_subcover).mp hK
  have hC' :
      ∃ V ⊆ C.Cover, V.Finite ∧ K ⊆ ⋃₀ V :=
    h' C.Cover
      (by
        intro s hs
        simpa [Open] using C.Open_cover s hs)
      C.Is_cover
  rcases hC' with ⟨V, hVsub, hVfin, hVK⟩
  let F : openCover K :=
  { Cover      := V
    Open_cover := by
      intro s hs
      have hsC : s ∈ C.Cover := hVsub hs
      simpa [Open] using C.Open_cover s hsC
    Is_cover   := hVK }
  refine ⟨F, hVfin, ?_⟩
  intro s hs
  exact hVsub hs -/

lemma hBoxCompact {n : ℕ} (a b : Rn n) : Compact (box a b) := by
  classical
  have h_eq :
      box a b =
        Set.univ.pi (fun i : Fin n => Set.Icc (a i) (b i)) := by
    ext x; constructor
    case h.mp =>
      intro hx i hi
      specialize hx i
      exact hx
    case h.mpr =>
      intro hx i
      have hx' : x i ∈ Set.Icc (a i) (b i) := hx i (by trivial)
      exact hx'
  have h_isCompact_pi :
      IsCompact (Set.univ.pi (fun i : Fin n => Set.Icc (a i) (b i))) := by
    have h_coord : ∀ i : Fin n, IsCompact (Set.Icc (a i) (b i)) := fun i =>
      isCompact_Icc
    simpa using isCompact_univ_pi h_coord
  have h_isCompact : IsCompact (box a b) := by
    simpa [h_eq] using h_isCompact_pi
  exact (IsCompact.toCompact h_isCompact)

  lemma closed_bddBelow_has_min {K : Set ℝ}
  (h_closed : Closed K)
  (h_nonempty : K.Nonempty)
  (h_bdd : BoundedBelow K) :
  ∃ m ∈ K, ∀ y ∈ K, m ≤ y := by
  let m := sInf K
  have h_le : ∀ y ∈ K, m ≤ y := by
    intro y hy
    have hm_le : sInf K ≤ y := csInf_le h_bdd hy
    simpa [m] using hm_le
  have h_approx : ∀ ε > 0, ∃ y ∈ K, |y - m| < ε := by
    intro ε hε
    have h_lt : sInf K < m + ε := by
      simpa [m] using lt_add_of_pos_right (sInf K) hε
    obtain ⟨y, hyK, hylt⟩ :=
      exists_lt_of_csInf_lt h_nonempty h_lt
    have hm_le_y : m ≤ y := h_le y hyK
    have hdist : |y - m| < ε := by
      have : y - m < ε := by
        have := sub_lt_iff_lt_add'.mpr hylt
        simpa using this
      simpa [abs_of_nonneg (sub_nonneg.mpr hm_le_y)] using this
    exact ⟨y, hyK, hdist⟩
  have hm_mem : m ∈ K := by
    rw[Closed] at h_closed
    by_contra hm
    have hm_in : m ∈ Kᶜ := hm
    rcases h_closed m hm_in with ⟨ε, hεpos, hball⟩
    rcases hεpos with ⟨x₀, r, hrpos, rfl⟩
    have hm_ball : |m - x₀| < r := hball.left
    have hpos : r - |m - x₀| > 0 := sub_pos.mpr hm_ball
    rcases h_approx (r - |m - x₀|) hpos with ⟨y, hyK, hy_dist⟩
    have hy_ball : y ∈ Metric.ball x₀ r := by
      have htri : |y - x₀| ≤ |y - m| + |m - x₀| := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using abs_sub_le (y) (m) (x₀)
      rw[Metric.ball, Set.mem_setOf]
      have hsum_lt : |y - m| + |m - x₀| < r := by
        have h1 : |y - m| + |m - x₀| < (r - |m - x₀|) + |m - x₀| := by
          exact (add_lt_add_iff_right |m - x₀|).mpr hy_dist
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
      exact lt_of_le_of_lt htri hsum_lt
    have hyKc : y ∈ Kᶜ := hball.right hy_ball
    exact hyKc hyK
  exact ⟨m, hm_mem, h_le⟩

lemma closed_bddAbove_has_max {K : Set ℝ}
  (h_closed : Closed K)
  (h_nonempty : K.Nonempty)
  (h_bdd : BoundedAbove K) :
  ∃ M ∈ K, ∀ y ∈ K, y ≤ M := by
  let M := sSup K
  have h_le : ∀ y ∈ K, y ≤ M := by
    intro y hy
    have := le_csSup h_bdd hy
    simpa [M] using this
  have h_approx : ∀ ε > 0, ∃ y ∈ K, |y - M| < ε := by
    intro ε hε
    have h_lt : M - ε < sSup K := sub_lt_self M hε
    obtain ⟨y, hyK, hylt⟩ := exists_lt_of_lt_csSup h_nonempty h_lt
    refine ⟨y, hyK, ?_⟩
    have hMy_lt : M - y < ε := by
      exact sub_lt_comm.mp hylt
    have hy_le_M : y ≤ M := h_le y hyK
    have hy_nonpos : y - M ≤ 0 := sub_nonpos.mpr hy_le_M
    have : |y - M| = M - y := by
      simp [abs_of_nonpos hy_nonpos]
    simpa [this] using hMy_lt
  have hM_mem : M ∈ K := by
    rw [Closed] at h_closed
    by_contra hM
    have hM_in : M ∈ Kᶜ := hM
    rcases h_closed M hM_in with ⟨U, hUopen, hMU, hUsubset⟩
    rcases hUopen with ⟨x₀, r, hrpos, rfl⟩
    have hM_ball : |M - x₀| < r := hMU
    have hpos : r - |M - x₀| > 0 := sub_pos.mpr hM_ball
    rcases h_approx (r - |M - x₀|) hpos with ⟨y, hyK, hy_dist⟩
    have hy_ball : y ∈ Metric.ball x₀ r := by
      have htri : |y - x₀| ≤ |y - M| + |M - x₀| := by
        simpa [sub_eq_add_neg] using abs_sub_le y M x₀
      have hsum_lt : |y - M| + |M - x₀| < r := by
        have h1 : |y - M| + |M - x₀| < (r - |M - x₀|) + |M - x₀| := by
          exact (add_lt_add_iff_right |M - x₀|).mpr hy_dist
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1
      exact lt_of_le_of_lt htri hsum_lt
    have hyKc : y ∈ Kᶜ := hUsubset hy_ball
    exact hyKc hyK
  exact ⟨M, hM_mem, h_le⟩

lemma compact_isClosed {S : Set ℝ} :
  Compact S → Closed S := sorry

end Course
