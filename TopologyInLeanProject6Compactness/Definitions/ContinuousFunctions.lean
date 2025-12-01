import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces

open Set

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/- # Continuous functions -/
section
variable [Topology X] [Topology Y] [Topology Z]

/- A function `f : X → Y` is continuous, iff preimages of open sets are open. -/
@[simp]
def Cont (f : X → Y) : Prop := ∀ s, Open s → Open (f ⁻¹' s)

/- Constant maps are continuous. -/
@[simp]
def Constant (f : X → Y) (y : Y) : Prop := (∀ x : X, f x = y)

@[simp]
theorem Cont_Constant (f : X → Y) (y : Y) : Constant f y → Cont f := by
  intro const_f
  intro U open_U
  by_cases c : y ∈ U
  case pos =>
    have w : f ⁻¹' U = univ := by
      rw [eq_univ_iff_forall]
      intro x
      specialize const_f x
      rw [← const_f] at c
      apply c
    rw [w]
    exact Open_univ
  case neg =>
    have w : f ⁻¹' U = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro x
      specialize const_f x
      rw [← const_f] at c
      apply c
    rw [w]
    exact Open_empty

/- Identity maps are continuous. -/
@[simp]
theorem Cont_id : Cont (id : X → X) := by
  intro U open_U
  rw [preimage_id]
  exact open_U

/- Compositions of continuous functions are continuous. -/
@[simp]
theorem Cont_comp (f : X → Y) (g : Y → Z) (cf : Cont f) (cg : Cont g) : Cont (g ∘ f) := by
  intro U
  intro open_U
  specialize cg U open_U
  specialize cf (g ⁻¹' U) cg
  exact cf

end

/- ## Special types of continuous functions -/
section
variable (f : X → Y) (g : Y → X)

@[simp]
def InverseFun (f : X → Y) (g : Y → X) : Prop := (f ∘ g = id ∧ g ∘ f = id)

lemma l1 (inv_fg : InverseFun f g) (x : X) : g (f x) = x := by
  obtain ⟨h1,h2⟩ := inv_fg
  rw [funext_iff] at h2
  apply h2

lemma l2 (inv_fg : InverseFun f g) (y : Y) : f (g y) = y := by
  obtain ⟨h1,h2⟩ := inv_fg
  rw [funext_iff] at h1
  apply h1

lemma image_eq_preimage_InverseFun (inv_fg : InverseFun f g) (U : Set X) : f '' U = g ⁻¹' U := by
  ext y; constructor
  case mp =>
    intro hy
    obtain ⟨x, hx1, hx2⟩ := hy
    rw [Set.mem_preimage, ← hx2, l1 f g inv_fg x]
    exact hx1
  case mpr =>
    intro hy
    use g y
    constructor
    case left => exact hy
    case right => exact l2 f g inv_fg y

variable [Topology X] [Topology Y]

@[simp]
def HomeoMap (f : X → Y) : Prop := Cont f ∧ (∃ g : Y → X, Cont g ∧ InverseFun f g)

@[simp]
def OpenMap (f : X → Y) : Prop := ∀ U : Set X, Open U → Open (f '' U)

@[simp]
def ClosedMap (f : X → Y) : Prop := ∀ U : Set X, Closed U → Closed (f '' U)

theorem HomeoMap_OpenMap : HomeoMap f → OpenMap f := by
  intro homeo_f U open_U
  obtain ⟨cont_f, ⟨g2, cont_g2, inv_fg2⟩⟩ := homeo_f
  rw [image_eq_preimage_InverseFun f g2 inv_fg2 U]
  apply cont_g2
  exact open_U

theorem inv_Cont_OpenMap_HomeoMap
  (inv_fg : InverseFun f g) (cont_f : Cont f) :
  OpenMap f → HomeoMap f := by
    intro open_f
    constructor
    case left => exact cont_f
    case right =>
      use g
      constructor
      case left =>
        intro U open_U
        rw [← image_eq_preimage_InverseFun f g inv_fg U]
        apply open_f
        exact open_U
      case right => exact inv_fg

theorem bij_OpenMap_iff_ClosedMap (bij_f : Function.Bijective f) : OpenMap f ↔ ClosedMap f := by
  constructor
  case mp =>
    intro open_f C closed_C
    have open_Cc : Open Cᶜ := by
      apply closed_C
    apply open_f at open_Cc
    rw [Closed]
    rw [← Set.image_compl_eq bij_f]
    exact open_Cc
  case mpr =>
    intro closed_f U open_U
    have closed_Uc : Closed Uᶜ := by
      simp only [Closed, compl_compl]
      exact open_U
    apply closed_f at closed_Uc
    rw [Set.image_compl_eq bij_f] at closed_Uc
    simp only [Closed, compl_compl] at closed_Uc
    exact closed_Uc

end
