import Mathlib.Tactic
import TopologyInLeanProject6Compactness.HeineBorel
import TopologyInLeanProject6Compactness.Definitions.NewSpaces
import TopologyInLeanProject6Compactness.Definitions.Compactness
import TopologyInLeanProject6Compactness.Definitions.CompactContinuous

open scoped Course
open Course

variable (n : ℕ)

theorem ExtremeValueTheorem (K : Set (Rn n)) (hK : Compact K) (f : (Rn n) → (Rn 1))
  (f_cont : ContOn f K) :
  ∃ x_min x_max : K,  ∀ x : K,
  f x_min ≤ f x ∧ f x ≤ f x_max := by
  have hfKCompact : Compact (f '' K) := Compact.image_on hK f_cont
  have h_C_B : Closed (f '' K) ∧ Bounded 1 (f '' K) :=
    (HeineBorel (n := 1) (K := f '' K)).mp hfKCompact
  sorry
