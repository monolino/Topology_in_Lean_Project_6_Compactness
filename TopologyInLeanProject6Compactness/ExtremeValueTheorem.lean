import Mathlib.Tactic
import TopologyInLeanProject6Compactness.HeineBorel
import TopologyInLeanProject6Compactness.Definitions.NewSpaces
import TopologyInLeanProject6Compactness.Definitions.Compactness
import TopologyInLeanProject6Compactness.Definitions.CompactContinuous
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces

open scoped Course
open Course

variable (n : ℕ)

def BoundedBelow (T : Set ℝ) : Prop :=
  ∃ m : ℝ, ∀ y ∈ T, m ≤ y

def BoundedAbove (T : Set ℝ) : Prop :=
  ∃ M : ℝ, ∀ y ∈ T, y ≤ M

lemma dist_eq_abs_coord (x x0 : Rn 1) :
  dist x x0 = |coord x - coord x0| := by
  simp [dist_eq_norm, coord, sub_eq_add_neg]
  sorry

lemma closed_bddBelow_has_min {K : Set ℝ}
  (h_closed : Closed K)
  (h_nonempty : K.Nonempty)
  (h_bdd : BoundedBelow K) :
  ∃ m ∈ K, ∀ y ∈ K, m ≤ y := by
  let m := sInf K
  have h_le : ∀ y ∈ K, m ≤ y := by
    sorry
  have hm_mem : m ∈ K := by
    sorry
  exact ⟨m, hm_mem, h_le⟩

lemma closed_bddAbove_has_max {K : Set ℝ}
  (h_closed : Closed K)
  (h_nonempty : K.Nonempty)
  (h_bdd : BoundedAbove K) :
  ∃ M ∈ K, ∀ y ∈ K, y ≤ M := by
  rcases h_bdd with ⟨M0, hM0⟩
  let M := sSup K
  sorry

instance : LE (Rn 1) :=
  ⟨fun u v => coord u ≤ coord v⟩

lemma le_iff_coord_le (u v : Rn 1) :
  u ≤ v ↔ coord u ≤ coord v :=
Iff.rfl


theorem ExtremeValueTheorem (K : Set (Rn n)) (hK : Compact K) (hKnonempty : K.Nonempty) (f : (Rn n) → (Rn 1))
  (f_cont : ContOn f K) :
  ∃ x_min x_max : K,  ∀ x : K,
  f x_min ≤ f x ∧ f x ≤ f x_max := by
  have hfKCompact : Compact (f '' K) := Compact.image_on hK f_cont
  have h_C_B : Closed (f '' K) ∧ Bounded 1 (f '' K) :=
    (HeineBorel (n := 1) (K := f '' K)).mp hfKCompact
  have h_closed : Closed (f '' K) := h_C_B.left
  have h_bdd : Bounded 1 (f '' K) := by
    exact h_C_B.right
  have h_img_nonempty : (f '' K).Nonempty := hKnonempty.image f
  have hfK_bbd_below : BoundedBelow (coord '' (f '' K)) := by
    rw[BoundedBelow]
    rw[Bounded] at h_bdd
    rcases h_bdd with ⟨M, Mpos, x0, hM⟩
    have h_abs : ∀ x ∈ f '' K, |coord x - coord x0| < M := by
      intro x hx
      simpa [dist_eq_abs_coord] using hM x hx
    refine ⟨coord x0 - M, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx_fK, rfl⟩
    have h := h_abs x hx_fK
    have h_pair : coord x0 - M < coord x ∧ coord x < coord x0 + M := by
      have h' := abs_lt.mp (by simpa [sub_eq_add_neg] using h)
      constructor
      · have h1 : -M < coord x - coord x0 := h'.left
        linarith
      · have h2 : coord x - coord x0 < M := h'.right
        linarith
    exact le_of_lt h_pair.left

  have hfK_bbd_above : BoundedAbove (coord '' (f '' K)) := by
    rw[BoundedAbove]
    rcases h_bdd with ⟨M, Mpos, x0, hM⟩
    have h_abs : ∀ x ∈ f '' K, |coord x - coord x0| < M := by
      intro x hx
      simpa [dist_eq_abs_coord] using hM x hx
    refine ⟨coord x0 + M, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx_fK, rfl⟩
    have h := h_abs x hx_fK
    have h_pair : coord x0 - M < coord x ∧ coord x < coord x0 + M := by
      have h' := abs_lt.mp (by simpa [sub_eq_add_neg] using h)
      constructor
      · have h1 : -M < coord x - coord x0 := h'.left
        linarith
      · have h2 : coord x - coord x0 < M := h'.right
        linarith
    exact le_of_lt h_pair.right
  let T : Set ℝ := coord '' (f '' K)
  have hT_nonempty : T.Nonempty := by
    rcases hKnonempty with ⟨x₀, hx₀K⟩
    refine ⟨coord (f x₀), ?_⟩
    refine ⟨f x₀, ?_, rfl⟩
    exact ⟨x₀, hx₀K, rfl⟩
  have hT_closed : Closed T := sorry
  have hT_below : BoundedBelow T := hfK_bbd_below
  have hT_above : BoundedAbove T := hfK_bbd_above
  obtain ⟨m, hmT, hm_le⟩ := closed_bddBelow_has_min hT_closed hT_nonempty hT_below --Minimum
  obtain ⟨M, hMT, h_leM⟩ := closed_bddAbove_has_max hT_closed hT_nonempty hT_above --Maximum
  rcases hmT with ⟨y_min, hy_min_fK, rfl⟩ --pullback to points of K
  rcases hy_min_fK with ⟨x_min, hx_minK, rfl⟩
  have h_min_on_K : ∀ x ∈ K, coord (f x_min) ≤ coord (f x) := by
    intro x hxK
    have hxT : coord (f x) ∈ T := by
      refine ⟨f x, ?_, rfl⟩
      exact ⟨x, hxK, rfl⟩
    exact hm_le _ hxT
  rcases hMT with ⟨y_max, hy_max_fK, rfl⟩
  rcases hy_max_fK with ⟨x_max, hx_maxK, rfl⟩
  have h_max_on_K : ∀ x ∈ K, coord (f x) ≤ coord (f x_max) := by
    intro x hxK
    have hxT : coord (f x) ∈ T := by
      refine ⟨f x, ?_, rfl⟩
      exact ⟨x, hxK, rfl⟩
    exact h_leM _ hxT
  refine ⟨⟨x_min, hx_minK⟩, ⟨x_max, hx_maxK⟩, ?_⟩
  intro x
  rcases x with ⟨x, hxKx⟩
  refine And.intro ?_ ?_
  · -- lower bound
    have hcoord : coord (f x_min) ≤ coord (f x) := h_min_on_K x hxKx
    simpa [le_iff_coord_le] using hcoord
  · -- upper bound
    change coord (f x) ≤ coord (f x_max)
    exact h_max_on_K x hxKx
