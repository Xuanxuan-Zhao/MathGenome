import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AdelicGroups

noncomputable section

open AlgebraicGeometry CategoryTheory Topology
open scoped BigOperators RatFunc RestrictedProduct

universe u

namespace LinearAlgebraicGroups.Specs.RationalFunctionSLAdelicReduction

open Arithmetic Arithmetic.AdelicGroups
open GeneralLinearStructure (MatrixPoints SpecialMatrixPoints)
open IntegralModels (MatrixRealization RationalPoints)
open Unipotent (Index closedSubgroupAlgebraicGroup)

/-- A realization of the scheme of determinant-one matrices inside the scheme of
invertible matrices, compatible with their natural point comparisons. -/
structure SpecialLinearRealization (k : Type u) [Field k] (m : ℕ) where
  group : AffineAlgebraicGroup k
  ambient : AffineAlgebraicGroup k
  specialPoints : SpecialMatrixPoints group m
  generalPoints : MatrixPoints ambient m
  inclusion : group.val ⟶ ambient.val
  closed : IsClosedImmersion inclusion.hom.hom.left
  matrix_eq : ∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj group.val).obj R),
    generalPoints.hom.app R (((groupPointsFunctor k).map inclusion).app R x) =
      Matrix.SpecialLinearGroup.toGL (n := Index.{u} m) (R := R) (specialPoints.hom.app R x)

/-- The standard inclusion of determinant-one matrices is a closed matrix realization. -/
def StandardMatrixRealization : Prop :=
  ∀ (k : Type u) [Field k] (m : ℕ), Nonempty (SpecialLinearRealization k m)

namespace SpecialLinearRealization

variable {k : Type u} [Field k] {m : ℕ}

/-- The realization used by the common adelic construction. -/
def realization (P : SpecialLinearRealization k m) : MatrixRealization P.group where
  size := m
  ambient := P.ambient
  matrix := P.generalPoints
  embedding := P.inclusion
  closed := P.closed

/-- A closed subgroup has the realization induced by its inclusion in the
determinant-one scheme. -/
def subgroupRealization (P : SpecialLinearRealization k m) (H : ClosedSubgroup P.group.val) :
    MatrixRealization (closedSubgroupAlgebraicGroup H) where
  size := m
  ambient := P.ambient
  matrix := P.generalPoints
  embedding := H.inclusion ≫ P.inclusion
  closed := by
    let := H.isClosedImmersion
    let := P.closed
    change IsClosedImmersion (H.inclusion.hom.hom.left ≫ P.inclusion.hom.hom.left)
    exact IsClosedImmersion.comp _ _

/-- The rational scheme point corresponding to a determinant-one matrix. -/
def rationalPoint (P : SpecialLinearRealization k m) (a : Matrix.SpecialLinearGroup (Index.{u} m) k) :
    RationalPoints P.group :=
  P.specialPoints.inv.app (CommAlgCat.of k k) a

/-- The local homomorphism induced by the subgroup inclusion. -/
def subgroupLocalPoint (P : SpecialLinearRealization k m) (H : ClosedSubgroup P.group.val)
    (D : GlobalFieldData.{u, u} k) (w : D.Place) :
    LocalPoints D (P.subgroupRealization H) w →* LocalPoints D P.realization w :=
  (((groupPointsFunctor k).map H.inclusion).app (CommAlgCat.of k (D.Completion w))).hom

end SpecialLinearRealization

/-- The separating parameter X on the rational function field. -/
def rationalParameter (F : Type u) [Field F] : SeparatingParameter F F⟮X⟯ where
  element := RatFunc.X
  transcendental := RatFunc.transcendental_X
  finite := by
    rw [RatFunc.adjoin_X]
    exact Module.Finite.of_surjective (Algebra.linearMap _ _)
      (fun x => ⟨⟨x, IntermediateField.mem_top⟩, rfl⟩)
  separable := by
    rw [RatFunc.adjoin_X]
    exact ⟨fun x => isSeparable_algebraMap
      (K := F⟮X⟯) (⟨x, IntermediateField.mem_top⟩ : (⊤ : IntermediateField F F⟮X⟯))⟩

abbrev baseFieldData (F : Type u) [Field F] [Finite F] : GlobalFieldData.{u, u} F⟮X⟯ :=
  GlobalFieldData.function F (rationalParameter F)

open Classical in
/-- The actual place associated to the valuation at infinity on F(X). -/
def pole (F : Type u) [Field F] : FunctionPlace F⟮X⟯ :=
  ⟨(RatFunc.inftyValuation F).valuationSubring, by
    intro h
    have hX : (RatFunc.X : F⟮X⟯) ∈ (RatFunc.inftyValuation F).valuationSubring := by
      rw [h]
      trivial
    change RatFunc.inftyValuation F RatFunc.X ≤ 1 at hX
    simp [← WithZero.exp_zero] at hX⟩

/-- The place just defined is precisely the unique place where X is nonintegral. -/
def UniquePole : Prop :=
  ∀ (F : Type u) [Field F] [Finite F] (w : FunctionPlace F⟮X⟯),
    w = pole F ↔ (RatFunc.X : F⟮X⟯) ∉ w.val

/-- A function-field place as an index of the full adelic group. -/
def adelicPlace {F : Type u} [Field F] [Finite F] (w : FunctionPlace F⟮X⟯) :
    Outside (baseFieldData F) ∅ :=
  ⟨.inl w, Finset.notMem_empty _⟩

private abbrev fullAdelicTopology {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    (D : GlobalFieldData.{u, u} k) (i : MatrixRealization G) :
    TopologicalSpace (Adeles D i ∅) :=
  inferInstance

section FunctionField

variable {F : Type u} [Field F] [Finite F] {m : ℕ}

/-- The determinant-one matrix at one of the intrinsic places. -/
def localMatrix (P : SpecialLinearRealization F⟮X⟯ m)
    (g : Adeles (baseFieldData F) P.realization ∅) (w : FunctionPlace F⟮X⟯) :
    Matrix.SpecialLinearGroup (Index.{u} m) w.Completion :=
  letI : Algebra F⟮X⟯ w.Completion := completionAlgebra (baseFieldData F) (.inl w)
  P.specialPoints.hom.app (CommAlgCat.of F⟮X⟯ w.Completion) (g (adelicPlace w))

/-- Away from the pole the matrices are integral. At the pole the matrix is
an integral determinant-one matrix times the given powers of X. -/
def HasNormalForm (P : SpecialLinearRealization F⟮X⟯ m)
    (g : Adeles (baseFieldData F) P.realization ∅) (a : Index.{u} m → ℤ) : Prop :=
  (∀ w : FunctionPlace F⟮X⟯, w ≠ pole F →
    localMatrix P g w ∈ (Matrix.SpecialLinearGroup.map w.integers.subtype).range) ∧
  ∃ b : Matrix.SpecialLinearGroup (Index.{u} m) (pole F).integers,
    (localMatrix P g (pole F)).val =
      (Matrix.SpecialLinearGroup.map (pole F).integers.subtype b).val *
        Matrix.diagonal (fun i => ((pole F).embedding RatFunc.X) ^ a i)

/-- Right multiplication by a rational special linear matrix gives an integral
basis at each finite prime and an ordered basis of total exponent zero at the pole. -/
def OrderedReduction : Prop :=
  ∀ {F : Type u} [Field F] [Finite F] {m : ℕ} (P : SpecialLinearRealization F⟮X⟯ m)
    (g : Adeles (baseFieldData F) P.realization ∅),
    ∃ (γ : Matrix.SpecialLinearGroup (Index.{u} m) F⟮X⟯)
      (δ : Adeles (baseFieldData F) P.realization ∅) (a : Index.{u} m → ℤ),
      (∀ w : Outside (baseFieldData F) ∅,
        δ w = localPoint (baseFieldData F) P.realization w.1 (P.rationalPoint γ)) ∧
      Monotone a ∧ (∑ i, a i) = 0 ∧ HasNormalForm P (g * δ) a

/-- A single compact subset of the full adelic group contains all matrices in
normal form with exponents in any prescribed finite subset of the sum-zero lattice. -/
def CompactNormalForms : Prop :=
  ∀ {F : Type u} [Field F] [Finite F] {m : ℕ} (P : SpecialLinearRealization F⟮X⟯ m)
    (E : Set (Index.{u} m → ℤ)), E.Finite → (∀ a ∈ E, (∑ i, a i) = 0) →
    letI := fullAdelicTopology (baseFieldData F) P.realization
    ∃ C : Set (Adeles (baseFieldData F) P.realization ∅), IsCompact C ∧
      ∀ g a, a ∈ E → HasNormalForm P g a → g ∈ C

/-- The inclusion of a closed subgroup, with the induced matrix realization,
embeds its full adelic group as a closed subgroup and commutes with the rational diagonal. -/
def AdelicClosedSubgroupEmbedding : Prop :=
  ∀ {F : Type u} [Field F] [Finite F] {m : ℕ} (P : SpecialLinearRealization F⟮X⟯ m)
    (H : ClosedSubgroup P.group.val),
    let D := baseFieldData F
    let i := P.subgroupRealization H
    let j := P.realization
    letI := fullAdelicTopology D i
    letI := fullAdelicTopology D j
    ∃ e : Adeles D i ∅ →* Adeles D j ∅,
      IsClosedEmbedding e ∧
      (∀ (x : Adeles D i ∅) (w : Outside D ∅),
        e x w = P.subgroupLocalPoint H D w.1 (x w)) ∧
      ∀ (d : Specs.AdelicGroups.diagonalType.{u, u}),
        Specs.AdelicGroups.diagonalCoordinates d →
        e.comp (d D i ∅) = (d D j ∅).comp
          (((groupPointsFunctor F⟮X⟯).map H.inclusion).app (CommAlgCat.of F⟮X⟯ F⟮X⟯)).hom

end FunctionField

end LinearAlgebraicGroups.Specs.RationalFunctionSLAdelicReduction
