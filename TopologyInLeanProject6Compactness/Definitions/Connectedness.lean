import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.ContinuousFunctions
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces
import TopologyInLeanProject6Compactness.Definitions.Bases
import TopologyInLeanProject6Compactness.Definitions.NewSpaces

open scoped Course
namespace Course

variable {X Y : Type*} [Topology X] [Topology Y]

instance : Topology Prop := discreteTopology Prop

def Connected (X : Type*) [Topology X] : Prop := ∀ f : X → Prop, Cont f → ∃ b, Constant f b

theorem Connected_iff_nonSep : Connected X ↔ ∀ U V : Set X, Open U ∧ U.Nonempty ∧ Open V ∧ V.Nonempty ∧ Disjoint U V → U ∪ V ≠ Set.univ := by
  constructor
  case mp =>
    contrapose!
    intro h
    obtain ⟨U,V,⟨open_U,open_V,disj_UV⟩,cover_UV⟩ := h
    rw [Connected]
    push_neg
    let f x : Prop := x ∈ U
    have cont_f : Cont f := by
      sorry -- Points are basis. Preimages of True and False are U and V respectively
    have w : ∀ b, ¬ Constant f b := by sorry
    use f
  case mpr =>
    sorry

theorem Disconnected_Prop : ¬(Connected Prop) := by
  rw [Connected]
  push_neg
  have cont_id : Cont (id : Prop → Prop) := Cont_id
  have non_const : ∀ b : Prop, ¬(Constant id b) := by
    intro b
    rw [Constant]
    push_neg
    have w : b = True ∨ b = False := by
        exact Classical.propComplete b
    obtain c1|c2 := w
    case inl =>
      use False
      rw [c1]
      simp only [id_eq, ne_eq, eq_iff_iff, iff_true, not_false_eq_true]
    case inr =>
      use True
      rw [c2]
      simp only [id_eq, ne_eq, eq_iff_iff, iff_false, not_true_eq_false, not_false_eq_true]
  use id

theorem Connected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : Connected X → Connected Y := by
    intro connected_X k cont_k
    specialize connected_X (k ∘ f) (Cont_comp f k cont_f cont_k)
    obtain ⟨b, constant_kf⟩ := connected_X
    use b
    intro y
    specialize surj_f y
    obtain ⟨a,ha⟩ := surj_f
    rw [← ha]
    exact constant_kf a

def I := {x : ℝ // 0 ≤ x ∧ x ≤ 1}

def zero : I := by
  constructor
  case val => exact 0
  case property =>
    constructor
    case left => exact Preorder.le_refl 0
    case right => exact zero_le_one' ℝ

def one : I := ⟨1, ⟨zero_le_one' ℝ, Preorder.le_refl 1⟩⟩

instance : MetricSpace I where
  dist := fun x y ↦ Real.metricSpace.dist x.val y.val
  dist_self := by
    intro x; exact Real.metricSpace.dist_self x.val
  dist_comm := fun x y ↦ Real.metricSpace.dist_comm x.val y.val
  dist_triangle x y z := Real.metricSpace.dist_triangle x.val y.val z.val
  eq_of_dist_eq_zero := by
    intro x y h
    apply Real.metricSpace.eq_of_dist_eq_zero at h
    rw [SetCoe.ext_iff] at h
    exact h

instance : Topology I := @basisTopology I metricBasis

structure Path (x : X) (y : X) where
  p : I → X
  Cont_p : Cont p
  source : p zero = x
  target : p one = y

def Paths (X : Type*) [Topology X] := Σ x y : X, Path x y

def mapPath {x : X} {y : X} (f : X → Y) (cont_f : Cont f) (path : Path x y) : Path (f x) (f y) where
  p := f ∘ path.p
  Cont_p := Cont_comp path.p f path.Cont_p cont_f
  source := by rw [Function.comp_apply, path.source]
  target := by rw [Function.comp_apply, path.target]

def PathConnected (X : Type*) [TX : Topology X] : Prop := ∀ x y : X, Nonempty (Path x y)

theorem PathConnected_image (f : X → Y) (surj_f : Function.Surjective f) (cont_f : Cont f)
  : PathConnected X → PathConnected Y := by
    intro pathconnected_X u v
    obtain ⟨x, hx⟩ := surj_f u
    obtain ⟨y, hy⟩ := surj_f v
    have pathX : Path x y := Classical.choice (pathconnected_X x y)
    have pathY : Path (f x) (f y) := mapPath f cont_f pathX
    rw [hx,hy] at pathY
    constructor
    exact pathY

theorem Connected_I : Connected I := by sorry

theorem Connected_PathConnected : PathConnected X → Connected X := by
  rw [Connected, PathConnected]
  contrapose!
  intro h
  obtain ⟨f,cont_f,constant_f⟩ := h
  have w : ∃ x y : X, f x ≠ f y := by sorry
  obtain ⟨x,y,hxy⟩ := w
  use x; use y
  intro is_path
  have p : Path x y := Classical.choice is_path
  obtain ⟨fp,cont_fp,source_fp,target_fp⟩ := mapPath f cont_f p
  have connected_I := Connected_I
  specialize connected_I fp cont_fp
  obtain ⟨b, constant_fp⟩ := connected_I
  rw [Constant] at constant_fp
  have c : f x = f y := by
    rw [← source_fp, ← target_fp, constant_fp one, constant_fp zero]
  contradiction

-- Products of (path)-connected spaces are (path)-connected.

end Course
