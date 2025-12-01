import Mathlib.Tactic
import TopologyInLeanProject6Compactness.Definitions.TopologicalSpaces
import TopologyInLeanProject6Compactness.Definitions.Bases


/-
Let Top(X,Y) := {f : X → Y | f continuous} denote the set of continuous maps from X to Y.

We can characterize a topological space X by either by specifying either
- Top(X,T) for all spaces T
- Top(T,X) for all spaces T.

This is a consequence of the Yoneda lemma.
You can also see it directly since id ∈ Top((X,TX),(X,TX')) is equivalent to TX' ⊆ TX.
In other words, the topology on X is completely determined (up to unique homeomorphism) by the continuous maps going into X (resp. out of X).
-/

namespace Constructions

universe u

/- # Subspaces -/
class Subspace (X : Type u) [TX : Topology X] where
  S : Type u
  TS : Topology S
  incl : S → X
  Injective_incl : Function.Injective incl
  /- Top(T,S) ≅ {f : T → S | incl ∘ f : T → X continuous }. -/
  char_Subspace {T : Type u} (TT: Topology T) (f : T → S) : Cont f ↔ Cont (incl ∘ f)

variable {X : Type u} [TX : Topology X]

theorem Cont_incl [sub : Subspace X] : @Cont sub.S X sub.TS TX (sub.incl) := by
  have h : sub.incl ∘ id = sub.incl := by
    exact rfl
  rw [← h]
  rw [← sub.char_Subspace]
  intro U open_U
  exact open_U

@[simp]
def Coarser (T T' : Topology X) : Prop :=
  @Cont X X T' T id

@[simp]
def Finer (T T' : Topology X) : Prop := @Coarser X T' T

infix:50 " ≤ " => Coarser -- T ≤ T' means T is coarser than T'
infix:50 " ≥ " => Finer

/- The subspace topology is the smallest (coarsest) topology on S that makes `incl` continuous. -/
theorem initial_Subspace [sub : Subspace X] [TS' : Topology sub.S] :
  @Cont sub.S X TS' TX sub.incl → sub.TS ≤ TS' := by
  intro h
  rw [Coarser]
  rw [sub.char_Subspace, Function.comp_id]
  exact h

instance pullbackTopology (X : Type u) (TX : Topology X) (S : Type u) (f : S → X) : Topology S where
  Open := fun (U : Set S) ↦ ∃ (V : Set X), Open V ∧ U = f ⁻¹' V
  Open_univ := by
    use Set.univ; simp
  Open_inter := by
    intro U1 U2 hU1 hU2
    obtain ⟨V1, hV1_open, hV1_pre⟩ := hU1
    obtain ⟨V2, hV2_open, hV2_pre⟩ := hU2
    use V1 ∩ V2
    constructor
    case left => exact Open_inter hV1_open hV2_open
    case right =>
      rw [Set.preimage_inter, hV1_pre, hV2_pre]
  Open_sUnion := by
    intro C hC
    use ⋃₀ {V | Open V ∧ ∃ U ∈ C, U = f ⁻¹' V}
    constructor
    case left =>
      apply Open_sUnion
      intro V hV
      rw [Set.mem_setOf] at hV
      exact hV.left
    case right =>
      ext s
      constructor
      case mp =>
        intro hs
        obtain ⟨A, hA1, hA2⟩:= hs
        simp only [exists_eq_right, Set.preimage_sUnion, Set.mem_setOf_eq, Set.mem_iUnion,
          Set.mem_preimage, exists_prop]
        specialize hC A hA1
        obtain ⟨V, hV1, hV2⟩:= hC
        use V
        rw [← hV2]
        rw [hV2] at hA2
        exact ⟨⟨hV1, hA1⟩, hA2⟩
      case mpr =>
        simp only [exists_eq_right, Set.preimage_sUnion, Set.mem_setOf_eq, Set.mem_iUnion,
          Set.mem_preimage, exists_prop, Set.mem_sUnion, forall_exists_index, and_imp]
        intro V open_V hV1 hV2
        use f ⁻¹' V
        exact ⟨hV1, hV2⟩

instance Subspace_pullbackTopology {S : Type u} (incl : S → X) (inj : Function.Injective incl)
  : Subspace X where
    S := S
    TS := pullbackTopology X TX S incl
    incl := incl
    Injective_incl := inj
    char_Subspace := by
      intro T TT f
      constructor
      case mp =>
        intro cont_f V open_V
        rw [Set.preimage_comp]
        apply cont_f
        use V
      case mpr =>
        intro cont_if U open_U
        obtain ⟨V, hV1, hV2⟩ := open_U
        rw [hV2]
        rw [← Set.preimage_comp]
        apply cont_if
        exact hV1

/- # Quotient Spaces -/

class Quotient (X : Type u) [TX : Topology X] where
  Q : Type u
  TQ : Topology Q
  qmap : X → Q
  Surjective_qmap : Function.Surjective qmap
  /- Top(Q,T) ≅ {f : Q → T | f ∘ qmap : X → T continuous }. -/
  char_Quotient {T : Type u} (TT: Topology T) (f : Q → T) : Cont f ↔ Cont (f ∘ qmap)

theorem Cont_qmap [quot : Quotient X] : @Cont X quot.Q TX quot.TQ quot.qmap := by
    have h : id ∘ quot.qmap = quot.qmap := by
      exact rfl
    rw [← h]
    rw [← quot.char_Quotient]
    intro U open_U
    exact open_U

/- The quotient topology is the largest (finest) topology on Q that makes `qmap` continuous. -/
theorem final_Quotient [quot : Quotient X] [TQ' : Topology quot.Q] :
  @Cont X quot.Q TX TQ' quot.qmap → TQ' ≤ quot.TQ := by
    intro h
    rw [Coarser]
    rw [quot.char_Quotient, Function.id_comp]
    exact h

instance pushforwardTopology
  (X : Type u) (TX : Topology X) (Q : Type u) (qmap : X → Q)
  : Topology Q where
    Open := fun (U : Set Q) ↦ Open (qmap ⁻¹' U)
    Open_univ := by
      simp only [Set.preimage_univ, Open_univ]
    Open_inter := by
      intro U V hU hV
      rw [Set.preimage_inter]
      exact Open_inter hU hV
    Open_sUnion := by
      intro C hC
      rw [Set.preimage_sUnion]
      exact Open_preimageUnion hC

instance Quotient_pushforwardTopology
  {Q : Type u} (qmap : X → Q) (surj : Function.Surjective qmap)
  : Quotient X where
    Q := Q
    TQ := pushforwardTopology X TX Q qmap
    qmap := qmap
    Surjective_qmap := surj
    char_Quotient := by
      intro T TT f
      constructor
      case mp =>
        intro cont_f U open_U
        apply cont_f
        exact open_U
      case mpr =>
        intro cont_fq U open_U
        exact cont_fq U open_U

/- # Product Spaces -/

class ProductSpace (X : Type u) [Topology X] (Y : Type u) [Topology Y] where
  TP : Topology (X × Y)
  /- Top(T,P) ≅ Top(T,X) × Top(T,Y) -/
  char_Product {T : Type u} (TT : Topology T) (f : T → X × Y) :
    Cont f ↔ Cont (Prod.fst ∘ f) ∧ Cont (Prod.snd ∘ f)

class iProductSpace (I : Type u) (Xs : I → Type u) (TXs : (i : I) → Topology (Xs i)) where
  TP : Topology (Π i, Xs i) -- (\P) dependent product
  /- Top(T, Π X i) ≅ Π Top(T,X i) -/
  char_Product {T : Type u} (TT : Topology T) (f : T → (Π i, Xs i))
    : Cont f ↔ ∀ i, Cont (fun t ↦ f t i)

-- Projections are continuous
theorem Cont_fst
  (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y] [prod : ProductSpace X Y]
  : (@Cont (X × Y) X prod.TP TX Prod.fst) := by sorry

theorem Cont_snd
  (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y] [prod : ProductSpace X Y]
  : (@Cont (X × Y) Y prod.TP TY Prod.snd) := by sorry

theorem Cont_iproj
  {I : Type u} {Xs : I → Type u} {TXs : (i : I) → Topology (Xs i)} [prod : iProductSpace I Xs TXs]
  : ∀ i : I, @Cont (Π i, Xs i) (Xs i) prod.TP (TXs i) (fun x ↦ x i) := by sorry

-- Product topology is coarsest topology making projections continuous.

-- Projections are open maps

instance productBasis
  (X : Type u) [Topology X] (Y : Type u) [Topology Y]
  : Basis (X × Y) where
    /- Basis of the form U × V for U open in X, V open in Y.
    Note the use of `Set.prod`.
    -/
    Basics :=
      {B : Set (X × Y) | ∃ (BX : Set X) (BY : Set Y), Open BX ∧ Open BY ∧ B = Set.prod BX BY}
    Basis_cover := by sorry
    Basis_inter := by sorry

instance productTopology (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y]
  : Topology (X × Y) := @basisTopology (X × Y) (productBasis X Y)

instance Product_productTopology (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y] : ProductSpace X Y where
  TP := productTopology X Y
  char_Product := by
    sorry


/- # Coproduct Spaces -/

class CoproductSpace (X : Type u) [Topology X] (Y : Type u) [Topology Y] where
  TC : Topology (X ⊕ Y)
  /- Top(X ⊕ Y,T) ≅ Top(X,T) × Top(Y,T) -/
  char_Coproduct {T : Type max u} (TT : Topology T) (f : (X ⊕ Y) → T) :
    Cont f ↔ Cont (f ∘ Sum.inl) ∧ Cont (f ∘ Sum.inr)

class iCoproductSpace (I : Type u) (Xs : I → Type u) (TXs : (i : I) → Topology (Xs i)) where
  TC : Topology (Σ i , Xs i)  -- (\S) dependent sum
  /- Top(Σ X i,T) ≅ Π Top(X i, T) -/
  char_Product {T : Type max u} (TT : Topology T) (f : (Σ i , Xs i) → T) :
    Cont f ↔ ∀ i, Cont (fun x ↦ f ⟨i, x⟩)

-- Injections are continuous

-- Coproduct topology is finest topology making projections continuous.

-- Injections are open and closed maps

instance coproductTopology (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y] : Topology (X ⊕ Y) where
  Open := {B | Open (Sum.inl ⁻¹' B) ∧ Open (Sum.inr ⁻¹' B)}
  Open_univ := by
    have l : Open (Sum.inl ⁻¹' (Set.univ : Set (X ⊕ Y))) := by
      rw [Set.preimage_univ]
      exact Open_univ
    have r : Open (Sum.inr ⁻¹' (Set.univ : Set (X ⊕ Y))) := by
      rw [Set.preimage_univ]
      exact Open_univ
    exact ⟨l,r⟩
  Open_inter := by sorry
  Open_sUnion := by sorry

instance Coproduct_coproductTopology (X : Type u) [TX : Topology X] (Y : Type u) [TY : Topology Y] : CoproductSpace X Y where
  TC := coproductTopology X Y
  char_Coproduct := by sorry

end Constructions
