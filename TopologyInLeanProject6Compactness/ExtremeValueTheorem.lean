import Mathlib.Tactic
import TopologyInLeanProject6Compactness.HeineBorel
import TopologyInLeanProject6Compactness.Definitions.NewSpaces
import TopologyInLeanProject6Compactness.Definitions.Compactness

open Course
open Constructions

variable (n : ℕ)

@[simp]
def ContOn {X : Type u} {Y : Type v}
  [Topology X] [Topology Y]
  (f : X → Y) (K : Set X) : Prop :=
  ∀ s, Open s → Open (K ∩ f ⁻¹' s)

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

private def coord0 (x : Rn 1) : ℝ := x 0


lemma closed_bounded_has_minmax_Rn1
    (K : Set (Rn 1)) (hK_ne : K.Nonempty)
    (hK_closed : Closed K) (hK_bdd : Bounded 1 K) :
    ∃ y_min y_max, y_min ∈ K ∧ y_max ∈ K ∧
      ∀ y ∈ K, y_min ≤ y ∧ y ≤ y_max := by
  classical
  have hK_compact : Compact K :=
    (HeineBorel (n := 1) (K := K)).mpr ⟨hK_closed, hK_bdd⟩
  let g : Rn 1 → ℝ := fun x => x 0
  have hg_cont : Continuous g := by
    simpa using (continuous_apply 0 : Continuous fun x : Rn 1 => x 0)
  obtain ⟨y_min, hy_minK, hmin⟩ :=
    hK_compact.exists_isMinOn g K hK_ne
  obtain ⟨y_max, hy_maxK, hmax⟩ :=
    hK_compact.exists_isMaxOn g K hK_ne
  refine ⟨y_min, y_max, hy_minK, hy_maxK, ?_⟩
  intro y hyK
  have h1 : g y_min ≤ g y := hmin hyK
  have h2 : g y ≤ g y_max := hmax hyK
  simpa [g] using And.intro h1 h2




  theorem ExtremeValueTheorem (n : ℕ)
  (K : Set (Rn n)) (hK : Compact K) (hK_ne : K.Nonempty)
  (f : (Rn n) → (Rn 1)) (f_cont : ContOn f K) :
  ∃ x_min x_max : K,  ∀ x : K,
    f x_min ≤ f x ∧ f x ≤ f x_max := by
  classical
  have hfKCompact : Compact (f '' K) :=
    Compact.image_on (K := K) hK f_cont
  have h_C_B : Closed (f '' K) ∧ Bounded 1 (f '' K) :=
    (HeineBorel (n := 1) (K := f '' K)).mp hfKCompact
  have h_closed : Closed (f '' K) := h_C_B.1
  have h_bdd    : Bounded 1 (f '' K) := h_C_B.2
  have h_img_ne : (f '' K).Nonempty := by
    rcases hK_ne with ⟨x0, hx0K⟩
    exact ⟨f x0, ⟨x0, hx0K, rfl⟩⟩
  obtain ⟨y_min, hy_min_in, y_max, hy_max_in, h_extreme⟩ :=
    closed_bounded_has_minmax_Rn1 (K := f '' K) h_img_ne h_closed h_bdd
  rcases hy_min_in with ⟨x_min, hx_minK, rfl⟩
  rcases hy_max_in with ⟨x_max, hx_maxK, rfl⟩
  refine ⟨⟨x_min, hx_minK⟩, ⟨x_max, hx_maxK⟩, ?_⟩
  intro x
  have hx_img : f x ∈ f '' K := ⟨x, x.property, rfl⟩
  specialize h_extreme (f x) hx_img
  exact h_extreme


def f_sub {n : ℕ} (K : Set (Rn n)) (f : Rn n → Rn 1) :
    K → { y : Rn 1 // y ∈ f '' K } :=
  fun x => ⟨f x, ⟨x, x.property, rfl⟩⟩

/-
I also tried to solve everything within the EVT, but I could not resolve the errors,
similarly to the seperate version.

variable (n : ℕ)

theorem ExtremeValueTheorem
  (K : Set (Rn n)) (hK : Compact K) (hK_ne : K.Nonempty)
  (f : (Rn n) → (Rn 1)) (f_cont : ContOn f K) :
  ∃ x_min x_max : K, ∀ x : K,
    f x_min ≤ f x ∧ f x ≤ f x_max := by
  classical
  have hfKCompact : Compact (f '' K) :=
    Compact.image_on (K := K) hK f_cont
  have h_C_B : Closed (f '' K) ∧ Bounded 1 (f '' K) :=
    (HeineBorel (n := 1) (K := f '' K)).mp hfKCompact
  have h_closed : Closed (f '' K) := h_C_B.1
  have h_bdd    : Bounded 1 (f '' K) := h_C_B.2
  have h_closed_iso : IsClosed (f '' K) := by
    sorry
  have h_bdd_iso : Bornology.IsBounded (f '' K) := by
    sorry
  have h_compact_iso : Compact (f '' K) :=
    sorry --(isCompact_iff_isClosed_bounded).2 ⟨h_closed_iso, h_bdd_iso⟩
  have h_img_ne : (f '' K).Nonempty := by
    rcases hK_ne with ⟨x0, hx0K⟩
    exact ⟨f x0, ⟨x0, hx0K, rfl⟩⟩
  let g : f '' K → ℝ := fun y => (y : Rn 1) 0
  have hg_cont : Continuous g := by
    have h_coord : Continuous fun x : Rn 1 => x 0 := by
      simpa using (continuous_apply 0 : Continuous fun x : Rn 1 => x 0)
    exact h_coord.comp continuous_subtype_val
  have hg_cont_on : ContinuousOn g (f '' K) := hg_cont.continuousOn
  obtain ⟨y_min, hy_min_in, hmin⟩ :=
    h_compact_iso.exists_isMinOn hg_cont_on h_img_ne
  obtain ⟨y_max, hy_max_in, hmax⟩ :=
    h_compact_iso.exists_isMaxOn hg_cont_on h_img_ne
  rcases hy_min_in with ⟨x_min, hx_minK, rfl⟩
  rcases hy_max_in with ⟨x_max, hx_maxK, rfl⟩
  refine ⟨⟨x_min, hx_minK⟩, ⟨x_max, hx_maxK⟩, ?_⟩
  intro x
  have hx_img : f x ∈ f '' K := ⟨x, x.property, rfl⟩
  have h1 : g ⟨f x_min, ?proof⟩ ≤ g ⟨f x, hx_img⟩ := by
    have h1' : g ⟨f x_min, hy_min_in⟩ ≤ g ⟨f x, hx_img⟩ :=
      hmin hx_img
    simpa using h1'
  have h2 : g ⟨f x, hx_img⟩ ≤ g ⟨f x_max, ?proof⟩ := by
    have h2' : g ⟨f x, hx_img⟩ ≤ g ⟨f x_max, hy_max_in⟩ :=
      hmax hx_img
    simpa using h2'
  sorry
-/
