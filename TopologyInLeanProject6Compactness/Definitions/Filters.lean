import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.MetricSpaces

namespace Course
open scoped Course

namespace MyFilter

structure Filter (X : Type*) where
  Sets : Set (Set X)
  univ_Sets : Set.univ ∈ Sets
  upward_Sets {A B} : A ∈ Sets → A ⊆ B → B ∈ Sets
  inter_Sets {A B} : A ∈ Sets → B ∈ Sets → A ∩ B ∈ Sets

variable {X Y : Type*} {F G : Filter X} {A B : Set X}

instance instMembership : Membership (Set X) (Filter X) where
  mem := fun F U ↦ U ∈ F.Sets

theorem filter_eq : ∀ {F G : Filter X}, F.Sets = G.Sets → F = G := by
  intro F G h
  cases F
  cases G
  simp only [Filter.mk.injEq]
  exact h

@[ext]
theorem ext (h : ∀ A, A ∈ F ↔ A ∈ G) : F = G := by
  apply filter_eq
  ext A
  apply h

@[simp]
theorem mem_sets : A ∈ F.Sets ↔ A ∈ F := Iff.rfl

@[simp]
theorem univ_mem : Set.univ ∈ F := F.univ_Sets

theorem upward_closed (hA : A ∈ F) (hAB : A ⊆ B) : B ∈ F :=
  F.upward_Sets hA hAB

theorem inter_mem (hA : A ∈ F) (hB : B ∈ F) : A ∩ B ∈ F :=
  F.inter_Sets hA hB

theorem inter_mem_finite_sInter (C : Set (Set X)) (fin : C.Finite) :
  (∀ c ∈ C, c ∈ F) → ⋂₀ C ∈ F := by
    refine Set.Finite.induction_on C fin ?base ?step
    case base =>
      simp only [Set.mem_empty_iff_false, IsEmpty.forall_iff,
      implies_true, Set.sInter_empty, univ_mem]
    case step =>
      intro s S s_nin_S fin_S hS
      simp only [Set.mem_insert_iff, forall_eq_or_imp, Set.sInter_insert, and_imp]
      intro s_in_F h
      exact inter_mem s_in_F (hS h)

def principalFilter (S : Set X) : Filter X where
  Sets := { T | S ⊆ T }
  univ_Sets := Set.subset_univ S
  upward_Sets := Set.Subset.trans
  inter_Sets := Set.subset_inter

def properFilter (F : Filter X) : Prop := ∅ ∉ F

def maxFilter (F : Filter X) : Prop := properFilter F ∧ ∀ G : Filter X, properFilter G ∧ F.Sets ⊆ G.Sets → F = G

def ultraFilter (F : Filter X) : Prop := properFilter F ∧ ∀ A, A ∈ F ∨ Aᶜ ∈ F

theorem ultra_iff_max {F : Filter X} : ultraFilter F ↔ maxFilter F := by sorry

def primeFilter (F : Filter X) : Prop := properFilter F ∧ ∀ R S, R ∪ S ∈ F → R ∈ F ∨ S ∈ F

theorem prime_finite_sUnion {F : Filter X} {C : Set (Set X)} (p : primeFilter F) (fin : C.Finite) :
  ⋃₀ C ∈ F → ∃ c ∈ C, c ∈ F := by
    refine Set.Finite.induction_on C fin ?base ?step
    case base =>
      simp only [Set.sUnion_empty, Set.mem_empty_iff_false,
      false_and, exists_const, imp_false]
      exact p.1
    case step =>
      intro s S s_nin_S fin_S hS h
      simp only [Set.sUnion_insert] at h
      simp only [Set.mem_insert_iff, exists_eq_or_imp]
      rw [primeFilter] at p
      apply p.2 s (⋃₀ S) at h
      obtain c1 | c2 := h
      case inl => left; exact c1
      case inr => right; exact hS c2

theorem ultra_iff_prime {F : Filter X} : ultraFilter F ↔ primeFilter F := by sorry

def mapFilter (f : X → Y) (F : Filter X) : Filter Y where
  Sets := Set.preimage (Set.preimage f) F.Sets
  univ_Sets := univ_mem
  upward_Sets := by
    intro A B hA hAB
    have w : f ⁻¹' A ⊆ f ⁻¹' B := by
      intro x hx
      apply hAB at hx
      exact hx
    exact upward_closed hA w
  inter_Sets := inter_mem

@[simp]
theorem mem_mapFilter (f : X → Y) (F : Filter X) (s : Set Y) :
  s ∈ mapFilter f F ↔ (f ⁻¹' s) ∈ F := by
  trivial

theorem mapFilter_prime (f : X → Y) (F : Filter X) : primeFilter F → primeFilter (mapFilter f F) := by
  intro prime_F
  rw [primeFilter]
  constructor
  case left =>
    rw [properFilter]
    simp only [mem_mapFilter, Set.preimage_empty]
    exact prime_F.1
  case right =>
    intro R S
    simp only [mem_mapFilter, Set.preimage_union]
    intro h
    apply prime_F.2
    exact h

def neighborhoods [Topology X] (x : X) : Set (Set X) := {U | Nbhd U x}

def filter_convergence [Topology X] (F : Filter X) (x : X) : Prop :=
  neighborhoods x ⊆ F.Sets

notation:50 F:50 " lim " x:50 => filter_convergence F x

def tail (s : ℕ → X) n := {x | ∃ m, m ≥ n ∧ s m = x}

lemma max_tail {s : ℕ → X} {nA nB : ℕ}
(hn : tail s nA ⊆ A) (hm : tail s nB ⊆ B)
: tail s (max nA nB) ⊆ A ∩ B := by
  intro x hx
  obtain ⟨m, hm1, hm2⟩ := hx
  have w1 : m ≥ nA := by
    exact le_of_max_le_left hm1
  have w2 : m ≥ nB := by
    exact le_of_max_le_right hm1
  have xA : x ∈ A := by
    apply hn
    use m
  have xB : x ∈ B := by
    apply hm
    use m
  exact ⟨xA,xB⟩

def eventuality (s : ℕ → X) : Filter X where
  Sets := {A | ∃ n, tail s n ⊆ A}
  univ_Sets := by use 0; apply Set.subset_univ
  upward_Sets := by
    intro A B hA A_sub_B
    obtain ⟨nA,hnA⟩ := hA
    use nA
    exact Set.Subset.trans hnA A_sub_B
  inter_Sets := by
    intro A B hA hB
    obtain ⟨nA,hnA⟩ := hA
    obtain ⟨nB,hnB⟩ := hB
    use (max nA nB)
    apply max_tail hnA hnB

def unique_limits [Topology X] : Prop := ∀ x y, (F lim x) ∧ (F lim y) → x = y

def UVFilter [Topology X] (x y : X) : Filter X where
  Sets := {B | ∃ U V, Nbhd U x ∧ Nbhd V y ∧ U ∩ V ⊆ B}
  univ_Sets := by
    rw [@Set.mem_setOf_eq]
    use Set.univ; use Set.univ
    simp only [Nbhd, Open_univ, Set.mem_univ, and_self, Set.inter_self, subset_refl]
  upward_Sets := by
    intro A B hA A_sub_B
    obtain ⟨U,V,hU,hV,hUV⟩ := hA
    have w : U ∩ V ⊆ B := by
      intro z hz
      exact A_sub_B (hUV hz)
    use U; use V
  inter_Sets := by
    intro A B hA hB
    obtain ⟨U_A,V_A,hU_A,hV_A,hUV_A⟩ := hA
    obtain ⟨U_B,V_B,hU_B,hV_B,hUV_B⟩ := hB
    let U := U_A ∩ U_B
    let V := V_A ∩ V_B
    have w1 : Nbhd U x := by
      have open_U : Open U := by
        exact Open_inter hU_A.1 hU_B.1
      have x_mem_U : x ∈ U := by
        exact ⟨hU_A.2, hU_B.2⟩
      exact ⟨open_U, x_mem_U⟩
    have w2 : Nbhd V y := by
      have open_V : Open V := by
        exact Open_inter hV_A.1 hV_B.1
      have y_mem_V : y ∈ V := by
        exact ⟨hV_A.2, hV_B.2⟩
      exact ⟨open_V, y_mem_V⟩
    have w3 : U ∩ V ⊆ A ∩ B := by
      have r : (U_A ∩ U_B) ∩ (V_A ∩ V_B) = (U_A ∩ V_A) ∩ (U_B ∩ V_B) := by
        rw [@Set.inter_inter_inter_comm]
      rw [r]
      exact Set.inter_subset_inter hUV_A hUV_B
    use U; use V

theorem Hausdorff_unique_limits [TX : Topology X]
  : @Hausdorff X TX ↔ ∀ G : Filter X, properFilter G → @unique_limits X G TX := by
    constructor
    case mp =>
      intro hausdorff G proper_G x y ⟨hGx, hGy⟩
      by_contra c
      obtain ⟨U, ⟨V, hU, hV, disj_UV⟩⟩ := hausdorff x y c
      have w1 : U ∈ G := by
        apply hGx
        trivial
      have w2 : V ∈ G := by
        apply hGy
        trivial
      have w3 : U ∩ V ∈ G := by
        exact inter_mem w1 w2
      rw [disj_UV] at w3
      contradiction
    case mpr =>
      contrapose!
      intro h
      rw [Hausdorff] at h
      push_neg at h
      obtain ⟨x,y,⟨x_neq_y,hxy⟩⟩ := h
      let C := {B | ∃ U V, Nbhd U x ∧ Nbhd V y ∧ U ∩ V ⊆ B}
      let F := UVFilter x y
      have proper_F : properFilter F := by
        intro c
        obtain ⟨U,V,hU,hV,hUV⟩ := c
        specialize hxy U V hU hV
        rw [Set.subset_empty_iff] at hUV
        rw [Set.nonempty_iff_ne_empty] at hxy
        contradiction
      have non_unique_lims : ¬(@unique_limits X F TX) := by
        rw [unique_limits]
        push_neg
        have F_to_x : F lim x := by
          intro N hN
          use N; use Set.univ
          simp only [Nbhd, Open_univ, Set.mem_univ, and_self, Set.inter_univ, subset_refl, and_true]
          exact ⟨hN.1,hN.2⟩
        have F_to_y : F lim y := by
          intro N hN
          use Set.univ; use N
          simp only [Nbhd, Open_univ, Set.mem_univ, and_self,
          Set.univ_inter, subset_refl, and_true, true_and]
          exact ⟨hN.1,hN.2⟩
        use x
        use y
      use F

def NbhdFilter [Topology X] (x : X) : Filter X where
  Sets := {B | ∃ U, Nbhd U x ∧ U ⊆ B}
  univ_Sets := by
    use Set.univ
    simp only [Nbhd, Open_univ, Set.mem_univ, and_self, subset_refl]
  upward_Sets := by
    intro A B hA A_sub_B
    obtain ⟨U,hU1,hU2⟩ := hA
    have w : U ⊆ B := by
      exact Set.Subset.trans hU2 A_sub_B
    use U
  inter_Sets := by
    intro A B hA hB
    obtain ⟨UA,hUA1,hUA2⟩ := hA
    obtain ⟨UB,hUB1,hUB2⟩ := hB
    let U := UA ∩ UB
    have w1 : Nbhd U x := by
      have open_U : Open U := by
        exact Open_inter hUA1.1 hUB1.1
      have x_in_U : x ∈ U := by
        exact ⟨hUA1.2, hUB1.2⟩
      exact ⟨open_U, x_in_U⟩
    have w2 : U ⊆ A ∩ B := by
      exact Set.inter_subset_inter hUA2 hUB2
    use U

theorem Cont_convergence [Topology X] [Topology Y] (f : X → Y)
  : Cont f ↔ ∀ (G : Filter X) (x : X), G lim x → (mapFilter f G) lim (f x) := by
    constructor
    case mp =>
      intro cont_f G x G_lim_x U hU
      apply G_lim_x
      have open_fU : Open (f ⁻¹' U) := by
        apply cont_f
        exact hU.1
      have x_in_fU : x ∈ (f ⁻¹' U) := by
        exact hU.2
      exact ⟨open_fU, x_in_fU⟩
    case mpr =>
      intro h U open_U
      have g : ∀ x ∈ f ⁻¹' U, ∃ V, Nbhd V x ∧ V ⊆ f ⁻¹' U := by
        intro x hx
        let F := NbhdFilter x
        have F_lim_x : F lim x := by
          intro U hU
          have w1 : Nbhd U x := by
            exact hU
          use U
        specialize h F x F_lim_x
        have w : f ⁻¹' U ∈ F := by
          apply h
          exact ⟨open_U, hx⟩
        obtain ⟨V,hV1,hV2⟩ := w
        use V
      choose V g using g
      have union_fU : f ⁻¹' U = ⋃₀ {B | ∃ (x : X) (w : x ∈ f ⁻¹' U), B = V x w} := by
        ext x
        constructor
        case mp =>
          intro wx
          use V x wx
          constructor
          case left => use x; use wx
          case right => specialize g x wx; exact g.1.2
        case mpr =>
          intro hx
          obtain ⟨B,hB1,hB2⟩ := hx
          obtain ⟨y,wy,hy⟩ := hB1
          specialize g y wy
          apply g.2
          rw [← hy]
          exact hB2
      rw [union_fU]
      apply Open_sUnion
      intro W hW
      obtain ⟨x,wx,hx⟩ := hW
      specialize g x wx
      rw [hx]
      exact g.1.1

end MyFilter
end Course
