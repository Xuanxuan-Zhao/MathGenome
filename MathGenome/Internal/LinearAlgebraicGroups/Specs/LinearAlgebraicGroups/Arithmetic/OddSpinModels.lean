import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinCharTwoStabilizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinAwayFromTwo
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OddSpinInnerDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.SymplecticMatrixStructure
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.RankOneFlag
import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.Algebra.Module.BigOperators
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

open AlgebraicGeometry CategoryTheory Matrix
open scoped Matrix

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels

/-- The relative coordinate ring obtained by adjoining the specified square roots.
The mapping property is imposed for every commutative target ring. -/
def PresentsSquareRoots {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type v} (c : ι → A) (z : ι → B) : Prop :=
  (∀ i, z i ^ 2 = algebraMap A B (c i)) ∧
  ∀ (S : Type u) [CommRing S] (f : A →+* S) (l : ι → S),
    (∀ i, l i ^ 2 = f (c i)) →
    ∃! g : B →+* S, g.comp (algebraMap A B) = f ∧ ∀ i, g (z i) = l i

/-- In characteristic two the finite free square-root projection is faithfully
flat and radicial. The coefficients may be taken in the symplectic coordinate ring. -/
def SquareRootProjection : Prop :=
  ∀ (A : Type u) [CommRing A] [Nontrivial A] (ι : Type v) [Finite ι]
    (c : ι → A), (2 : A) = 0 →
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (z : ι → B),
      PresentsSquareRoots c z ∧ Module.Free A B ∧ Module.Finite A B ∧
      Module.FaithfullyFlat A B ∧
      let p := Spec.map (CommRingCat.ofHom (algebraMap A B))
      IsFinite p ∧ Flat p ∧ Surjective p ∧ UniversallyInjective p

open SymplecticMatrixStructure (Indices PointGroup Coordinates alternatingForm
  universalSymplecticMatrix)

noncomputable section

/-- The quadratic norm on the sum of the hyperbolic planes. -/
def hyperbolicForm (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R] :
    QuadraticForm R (Indices ι → R) :=
  LinearMap.BilinMap.toQuadraticMap
    (Matrix.toLinearMap₂' R (Matrix.fromBlocks 0 1 0 0 : Matrix (Indices ι) (Indices ι) R))

/-- The split odd quadratic form, with the last coordinate of norm one. -/
def oddForm (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R] :
    QuadraticForm R ((Indices ι → R) × R) :=
  (hyperbolicForm ι R).prod (QuadraticMap.sq (R := R) (A := R))

abbrev standardVector {ι : Type u} [DecidableEq ι] (R : Type u) [CommRing R]
    (i : Indices ι) : Indices ι → R := Pi.single i 1

/-- The hyperbolic norm polarizes to the specified symplectic form in characteristic two. -/
def HyperbolicPolar : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R],
    (2 : R) = 0 →
    (hyperbolicForm ι R).polarBilin = alternatingForm ι R

/-- The data of a pair come from the specified symplectic point group. -/
def IsOddPair {ι R : Type u} [Fintype ι] [DecidableEq ι] [CommRing R]
    (A : PointGroup ι R) (l : (Indices ι → R) →ₗ[R] R) : Prop :=
  ∀ x, hyperbolicForm ι R (A.val *ᵥ x) + l x ^ 2 = hyperbolicForm ι R x

def PairEquations : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R], (2 : R) = 0 →
    ∀ (A : PointGroup ι R) (l : (Indices ι → R) →ₗ[R] R),
      IsOddPair A l ↔
      ∀ i, l (standardVector R i) ^ 2 = -hyperbolicForm ι R (A.val *ᵥ standardVector R i)

/-- Square-root coefficients over the canonical coordinate ring of the symplectic group. -/
def universalCoefficient (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι]
    (i : Indices ι) : Coordinates k ι :=
  -hyperbolicForm ι (Coordinates k ι)
    (universalSymplecticMatrix k ι *ᵥ standardVector (Coordinates k ι) i)

/-- The relative affine scheme of pairs over the specified symplectic scheme.
The universal property is over a symplectic point on every test algebra. -/
def PairCoordinatePresentation : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι], (2 : k) = 0 →
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra (Coordinates k ι) B) (z : Indices ι → B),
      PresentsSquareRoots (universalCoefficient k ι) z ∧
      Module.Free (Coordinates k ι) B ∧ Module.Finite (Coordinates k ι) B ∧
      Module.FaithfullyFlat (Coordinates k ι) B ∧
      (let p := Spec.map (CommRingCat.ofHom (algebraMap (Coordinates k ι) B))
       IsFinite p ∧ Flat p ∧ Surjective p ∧ UniversallyInjective p ∧
       GeometricallyConnected
         (p ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Coordinates k ι))))) ∧
      ringKrullDim B = (Fintype.card ι * (2 * Fintype.card ι + 1) : ℕ) ∧
      ∀ (R : Type u) [CommRing R] [Algebra k R],
        ∃ e : (Coordinates k ι →ₐ[k] R) ≃ PointGroup ι R,
          (∀ f i j, (e f).val i j = f (universalSymplecticMatrix k ι i j)) ∧
          ∀ (f : Coordinates k ι →ₐ[k] R) (l : (Indices ι → R) →ₗ[R] R),
            IsOddPair (e f) l ↔
              ∃! g : B →+* R, g.comp (algebraMap (Coordinates k ι) B) = f.toRingHom ∧
                ∀ i, g (z i) = l (standardVector R i)


/-- A linear equivalence fixing the last basis vector is an isometry
exactly when it acts as a symplectic pair on the direct sum. -/
def FixesNormComparison : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R], (2 : R) = 0 →
    ∀ (g : ((Indices ι → R) × R) ≃ₗ[R] ((Indices ι → R) × R)), g (0, 1) = (0, 1) →
      ((∀ x, oddForm ι R (g x) = oddForm ι R x) ↔
        ∃ (A : PointGroup ι R) (l : (Indices ι → R) →ₗ[R] R), IsOddPair A l ∧
          ∀ x t, g (x, t) = (A.val *ᵥ x, l x + t))

/-- Each pair acts by the indicated linear isometry fixing the distinguished vector. -/
def PairAction : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R], (2 : R) = 0 →
    ∀ (A : PointGroup ι R) (l : (Indices ι → R) →ₗ[R] R), IsOddPair A l →
      ∃! g : ((Indices ι → R) × R) ≃ₗ[R] ((Indices ι → R) × R),
        (∀ x t, g (x, t) = (A.val *ᵥ x, l x + t)) ∧
        g (0, 1) = (0, 1) ∧ ∀ x, oddForm ι R (g x) = oddForm ι R x

/-- The marked last coordinate generates the full polar radical in characteristic two. -/
def SplitRadical : Prop :=
  ∀ (ι R : Type u) [Fintype ι] [DecidableEq ι] [CommRing R], (2 : R) = 0 →
    LinearMap.ker (oddForm ι R).polarBilin = R ∙ ((0, 1) : (Indices ι → R) × R) ∧
    oddForm ι R (0, 1) = 1

/-- The matrices reducing to the identity on the dual numbers. -/
abbrev tangentMatrix {k ι : Type u} [Field k] [DecidableEq ι]
    (X : Matrix (Indices ι) (Indices ι) k) :
    Matrix (Indices ι) (Indices ι) (DualNumber k) :=
  fun i j => ⟨(1 : Matrix (Indices ι) (Indices ι) k) i j, X i j⟩

/-- The pair equations impose a zero diagonal on JX and leave the covector
free to have any dual-number term with constant coefficient zero. -/
def PairTangent : Prop :=
  ∀ (k ι : Type u) [Field k] [Fintype ι] [DecidableEq ι], (2 : k) = 0 →
    ∀ (X : Matrix (Indices ι) (Indices ι) k)
      (l : (Indices ι → DualNumber k) →ₗ[DualNumber k] DualNumber k),
      (∀ i, (l (standardVector (DualNumber k) i)).fst = 0) →
      ((∃ A : PointGroup ι (DualNumber k), A.val = tangentMatrix X ∧ IsOddPair A l) ↔
        (Matrix.J ι k * X).IsSymm ∧ ∀ i, (Matrix.J ι k * X) i i = 0)

section Lattice

variable (ι : Type u) [Fintype ι] [DecidableEq ι]

abbrev coordinateVector (i : ι) : ι → ℤ := Pi.single i 1

def coroots : Set (ι → ℤ) :=
  {v | (∃ i, v = (2 : ℤ) • coordinateVector ι i ∨ v = -((2 : ℤ) • coordinateVector ι i)) ∨
    ∃ i j, i ≠ j ∧ (v = coordinateVector ι i - coordinateVector ι j ∨ v = coordinateVector ι i + coordinateVector ι j ∨ v = -(coordinateVector ι i + coordinateVector ι j))}

def evenSum : Submodule ℤ (ι → ℤ) where
  carrier := {v | Even (∑ i, v i)}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    change Even (∑ i, (x i + y i))
    rw [Finset.sum_add_distrib]
    exact hx.add hy
  smul_mem' a x hx := by
    change Even (∑ i, a * x i)
    rw [← Finset.mul_sum]
    exact hx.mul_left a

/-- In adjoint torus coordinates, the scalar lift equation cuts out exactly
the integer span of the type-B coroots. -/
def CorootLattice : Prop :=
  ∀ (ι : Type u) [Fintype ι] [DecidableEq ι] [Nonempty ι],
    Submodule.span ℤ (coroots ι) = evenSum ι ∧
    ∀ v : ι → ℤ, (∃ a : ℤ, 2 * a + ∑ i, v i = 0) ↔ v ∈ evenSum ι

end Lattice

end

end LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels

namespace LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels

open SymplecticMatrixStructure (Indices PointGroup Coordinates)
open Arithmetic.OddSpinCharTwoStabilizer (OddIndex OddModule MarkedIsometries oddMatrixAction)
open Albert.SpinSpecification (GroupScheme SchemePoints)
open Opposite
open scoped CategoryTheory.MonObj

noncomputable section

/-- Use these indices for the symplectic group over a field in universe `u`. -/
abbrev PlaneIndex (n : ℕ) := ULift.{u} (Fin n)

/-- Index the hyperbolic coordinates of the marked model in symplectic order. -/
def hyperbolicIndices (n : ℕ) : Indices (PlaneIndex.{u} n) ≃ Indices (Fin n) :=
  Equiv.sumCongr Equiv.ulift Equiv.ulift

/-- Separate the marked coordinate from the hyperbolic coordinates. -/
def splitCoordinates (R : Type u) [CommRing R] (n : ℕ) :
    OddModule R n ≃ₗ[R] ((Indices (PlaneIndex.{u} n) → R) × R) where
  toFun x := (fun j => x (↑(toLex (hyperbolicIndices n j)) : OddIndex n), x ⊤)
  invFun x := WithTop.recTopCoe x.2 (fun j => x.1 ((hyperbolicIndices n).symm (ofLex j)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    cases i using WithTop.recTopCoe
    · rfl
    · simp
  right_inv x := by
    apply Prod.ext
    · funext j
      simp
    · rfl

/-- The represented pair projection, evaluated on every test algebra. -/
def RepresentsPairProjection {k : Type u} [Field k] {n : ℕ}
    {O P : GroupScheme k} (p : O ⟶ P)
    (o : ∀ S : CommAlgCat k, SchemePoints O S ≃* MarkedIsometries S n)
    (s : ∀ S : CommAlgCat k, SchemePoints P S ≃* PointGroup (PlaneIndex.{u} n) S) : Prop :=
  (∀ {R S : CommAlgCat k} (f : R ⟶ S) (a : SchemePoints O R),
    (o S ((algSpec (CommRingCat.of k)).map f.op ≫ a)).val =
      Matrix.GeneralLinearGroup.map f.hom.toRingHom (o R a).val) ∧
  (∀ {R S : CommAlgCat k} (f : R ⟶ S) (a : SchemePoints P R),
    s S ((algSpec (CommRingCat.of k)).map f.op ≫ a) =
      SymplecticMatrixStructure.mapSymplecticPoint f.hom.toRingHom (s R a)) ∧
  (∀ (R : CommAlgCat k) (a : SchemePoints O R),
    ∃! l : (Indices (PlaneIndex.{u} n) → R) →ₗ[R] R,
      IsOddPair (s R (a ≫ p.hom.hom)) l ∧
      ∀ x t, splitCoordinates R n
        (oddMatrixAction (o R a).val ((splitCoordinates R n).symm (x, t))) =
        ((s R (a ≫ p.hom.hom)).val *ᵥ x, l x + t)) ∧
  (∀ (R : CommAlgCat k) (A : PointGroup (PlaneIndex.{u} n) R)
    (l : (Indices (PlaneIndex.{u} n) → R) →ₗ[R] R),
    IsOddPair A l → ∃! a : SchemePoints O R,
      s R (a ≫ p.hom.hom) = A ∧
      ∀ x t, splitCoordinates R n
        (oddMatrixAction (o R a).val ((splitCoordinates R n).symm (x, t))) =
        (A.val *ᵥ x, l x + t))

/-- The marked odd isometry group represents the pairs, with the square-root
extension as its coordinate algebra over the specified symplectic group. -/
def RepresentedPairGroup : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 →
    ∃ (O P : AffineAlgebraicGroup k) (p : O.val ⟶ P.val)
      (o : ∀ R : CommAlgCat k, SchemePoints O.val R ≃* MarkedIsometries R n)
      (s : ∀ R : CommAlgCat k, SchemePoints P.val R ≃* PointGroup (PlaneIndex.{u} n) R),
      RepresentsPairProjection p o s ∧
      ∃ hP : P.val.X = SymplecticMatrixStructure.symplecticScheme k (PlaneIndex.{u} n),
      IsFinite p.hom.hom.left ∧ Flat p.hom.hom.left ∧
      Surjective p.hom.hom.left ∧ UniversallyInjective p.hom.hom.left ∧
      Smooth O.val.X.hom ∧ GeometricallyConnected O.val.X.hom ∧
      (0 < n → GeometricRadicals.IsReductive O) ∧
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra k B)
        (_ : Algebra (Coordinates k (PlaneIndex.{u} n)) B)
        (z : Indices (PlaneIndex.{u} n) → B),
        IsScalarTower k (Coordinates k (PlaneIndex.{u} n)) B ∧
        ∃ hO : O.val.X = (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k B)),
        p.hom.hom.left = eqToHom (congrArg Over.left hO) ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (Coordinates k (PlaneIndex.{u} n)) B)) ≫
            eqToHom (congrArg Over.left hP).symm ∧
        PresentsSquareRoots (universalCoefficient k (PlaneIndex.{u} n)) z ∧
        Module.Free (Coordinates k (PlaneIndex.{u} n)) B ∧
        Module.Finite (Coordinates k (PlaneIndex.{u} n)) B ∧
        Module.FaithfullyFlat (Coordinates k (PlaneIndex.{u} n)) B ∧
        ringKrullDim B = (n * (2 * n + 1) : ℕ)

/-- The lifted hyperbolic diagonal is the split rank-`n` torus in the pair
group and stays maximal over the algebraic closure. -/
def PairDiagonalTorus : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 →
    ∃ (O P : AffineAlgebraicGroup k) (p : O.val ⟶ P.val)
      (o : ∀ R : CommAlgCat k, SchemePoints O.val R ≃* MarkedIsometries R n)
      (s : ∀ R : CommAlgCat k, SchemePoints P.val R ≃* PointGroup (PlaneIndex.{u} n) R),
      RepresentsPairProjection p o s ∧
      P.val.X = SymplecticMatrixStructure.symplecticScheme k (PlaneIndex.{u} n) ∧
      ∃ (T : ClosedSubgroup O.val) (U : ClosedSubgroup P.val) (j : T.group ≅ U.group)
        (d : (groupPointsFunctor k).obj T.group ≅
          StandardGroups.multiplicativePowerPoints k (PlaneIndex.{u} n)),
        T.inclusion ≫ p = j.hom ≫ U.inclusion ∧
        Nonempty (T.group ≅ (StandardGroups.multiplicativePowerGroup k (PlaneIndex.{u} n)).val) ∧
        RankOneFlag.IsGeometricallyMaximal T ∧
        ∀ (R : TestAlgebra k) (a : SchemePoints T.group R) x t,
          splitCoordinates R n (oddMatrixAction (o R (a ≫ T.inclusion.hom.hom)).val
            ((splitCoordinates R n).symm (x, t))) =
              (SymplecticMatrixStructure.hyperbolicDiagonal (d.hom.app R a) *ᵥ x, t)

open Arithmetic.OddSpinCharTwoStabilizer
  (ambientForm inclusion radicalVector diagonalOddVector HasScalarRestrictionKernel HasDiagonalRestrictionFibre
    HasDiagonalExponents laurentMultiplicativeGroup IsReductiveGroupScheme)
open Albert.SpinSpecification
  (ScalarClifford IsSpinPointRepresentation IsVectorAction vectors)
open scoped TensorProduct

/-- The even spin stabilizer and its intrinsic odd spin representation for
the very same marked isometry group that represents the symplectic pairs. -/
def PairStabilizerCover : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 → 0 < n →
    let q := Arithmetic.OddSpinCharTwoStabilizer.oddForm k n
    let Q := ambientForm k n
    let J := inclusion k n
    let r := J (radicalVector k n)
    ∃ (G H : GroupScheme k) (O P : AffineAlgebraicGroup k)
      (i : H ⟶ G) (f : H ⟶ O.val) (p : O.val ⟶ P.val)
      (e : ∀ R : TestAlgebra k, SchemePoints G R →* (ScalarClifford Q R)ˣ)
      (h : ∀ R : TestAlgebra k, SchemePoints H R →* (ScalarClifford q R)ˣ)
      (o : ∀ R : TestAlgebra k, SchemePoints O.val R ≃* MarkedIsometries R n)
      (s : ∀ R : TestAlgebra k, SchemePoints P.val R ≃* PointGroup (PlaneIndex.{u} n) R),
      RepresentsPairProjection p o s ∧
      P.val.X = SymplecticMatrixStructure.symplecticScheme k (PlaneIndex.{u} n) ∧
      GeometricRadicals.IsReductive O ∧
      (∀ (S : SchemeOver k) (a : S ⟶ O.val.X), Centralizes (𝟙 O.val) a → a = 1) ∧
      IsSpinPointRepresentation Q G e ∧ IsSpinPointRepresentation q H h ∧
      IsClosedImmersion i.hom.hom.left ∧ IsReductiveGroupScheme H ∧
      IsFinite f.hom.hom.left ∧ Flat f.hom.hom.left ∧ Surjective f.hom.hom.left ∧
      UniversallyInjective f.hom.hom.left ∧
      HasScalarRestrictionKernel (n := n) i f e ∧ HasDiagonalRestrictionFibre i f e o ∧
      (∀ m : Fin n → ℤ, ∃ χ : laurentMultiplicativeGroup k ⟶ O.val, HasDiagonalExponents o χ m) ∧
      (∀ (χ : laurentMultiplicativeGroup k ⟶ O.val) (m : Fin n → ℤ),
        HasDiagonalExponents o χ m →
        ((∃ c : laurentMultiplicativeGroup k ⟶ H, c ≫ f = χ) ↔ m ∈ evenSum (Fin n))) ∧
      ∀ R : TestAlgebra k,
        (∀ a : SchemePoints G R, Commute (vectors Q R (1 ⊗ₜ[k] r)) (e R a).val ↔
          ∃! b : SchemePoints H R, b ≫ i.hom.hom = a) ∧
        ∀ b : SchemePoints H R,
          let j : ScalarClifford q R →ₐ[R] ScalarClifford Q R :=
            Algebra.TensorProduct.map (AlgHom.id R R) (CliffordAlgebra.map J)
          Units.map j.toMonoidHom (h R b) = e R (b ≫ i.hom.hom) ∧
          let c := ((Pi.basisFun k (OddIndex n)).baseChange R).equivFun
          IsVectorAction q R (h R b) (c.trans ((oddMatrixAction (o R (b ≫ f.hom.hom)).val).trans c.symm))

open CharacterDescent (Character Cocharacter)
open CharacterPairing (characterValue)
open AbstractPairing (Datum)
open GeometricRadicals (IsSemisimple IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open Arithmetic.OddSpinAwayFromTwo (IsTypeBDatum)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

/-- In characteristic two the very same marked isometry group of pairs
has the split adjoint type-B root datum on its hyperbolic diagonal torus. -/
def PairRootDatum : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 → 0 < n →
    ∃ (O P : AffineAlgebraicGroup k) (p : O.val ⟶ P.val)
      (o : ∀ R : TestAlgebra k, SchemePoints O.val R ≃* MarkedIsometries R n)
      (s : ∀ R : TestAlgebra k, SchemePoints P.val R ≃* PointGroup (PlaneIndex.{u} n) R),
      RepresentsPairProjection p o s ∧
      P.val.X = SymplecticMatrixStructure.symplecticScheme k (PlaneIndex.{u} n) ∧
      IsSemisimple O ∧
      (∀ (S : SchemeOver k) (a : S ⟶ O.val.X), Centralizes (𝟙 O.val) a → a = 1) ∧
      ∃ (T : ClosedSubgroup O.val), IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
      ∃ (t : ∀ R : TestAlgebra k, SchemePoints T.group R ≃* (Fin n → Rˣ)),
        (∀ {R S : TestAlgebra k} (f : R ⟶ S) (a : SchemePoints T.group R) i,
          t S (mapPoints f a) i = Units.map f.hom.toMonoidHom (t R a i)) ∧
        (∀ R (a : SchemePoints T.group R) x,
          oddMatrixAction (o R (a ≫ T.inclusion.hom.hom)).val x = diagonalOddVector (t R a) x) ∧
        ∃ (comm : IsCommMonObj T.group.X),
          letI := comm
          ∃ (D : Datum T) (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
            (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ)),
            IsTypeBDatum n T D X Y ∧
            (∀ R (a : SchemePoints T.group R) (χ : Character T.group),
              characterValue χ R a = ((∏ i, (t R a i) ^ (X (Additive.ofMul χ) i) : Rˣ) : R)) ∧
            (∀ (R : TestAlgebra k) (z : Rˣ) (c : Cocharacter T.group) i,
              t R (cocharacterPoint c R z) i = z ^ (Y (Additive.ofMul c) i))

open Arithmetic.OddSpinAwayFromTwo (liftTorus)
open SimplyConnectedLattice (GeometricallySimplyConnected corootLatticeOf)
open CentralIsogenies (IsCentralIsogeny IsTorusRestriction)
open Arithmetic.OddSpinCharTwoStabilizer (oddBasis)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification (spinUnits coefficientMap conjugate)
open _root_.LinearAlgebraicGroups.Albert.CliffordSpecification (coefficientForm)

/-- A quadratic action and its extension on the entire Clifford algebra,
compatible with changes of test algebra and with every spin implementer. -/
structure QuadraticCliffordAction {k V I : Type u} [Field k] [AddCommGroup V] [Module k V]
    [LinearOrder I] (q : QuadraticForm k V) (b : Module.Basis I k V) (O : GroupScheme k) where
  linear : ∀ R : TestAlgebra k, SchemePoints O R →* ((R ⊗[k] V) ≃ₗ[R] (R ⊗[k] V))
  preserves : ∀ (R : TestAlgebra k) (p : SchemePoints O R) x,
    coefficientForm R q b (linear R p x) = coefficientForm R q b x
  natural : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (p : SchemePoints O R) x,
    let fV := TensorProduct.map f.hom.toLinearMap (LinearMap.id : V →ₗ[k] V)
    fV (linear R p x) = linear S (mapPoints f p) (fV x)
  clifford : ∀ (R : TestAlgebra k), SchemePoints O R → (ScalarClifford q R ≃ₐ[R] ScalarClifford q R)
  generators : ∀ (R : TestAlgebra k) (p : SchemePoints O R) x,
    clifford R p (vectors q R x) = vectors q R (linear R p x)
  clifford_natural : ∀ {R S : TestAlgebra k} (f : R ⟶ S) (p : SchemePoints O R) x,
    coefficientMap q R f.hom (clifford R p x) =
      clifford S (mapPoints f p) (coefficientMap q R f.hom x)
  preservesSpin : ∀ (R : TestAlgebra k) (p : SchemePoints O R) (a : (ScalarClifford q R)ˣ),
    a ∈ spinUnits q R → Units.map (clifford R p).toMonoidHom a ∈ spinUnits q R
  conjugates : ∀ (R : TestAlgebra k) (p : SchemePoints O R) (a : (ScalarClifford q R)ˣ),
    IsVectorAction q R a (linear R p) → ∀ x, clifford R p x = conjugate q R a x

/-- The characteristic-two intrinsic odd spin model is the split simply
connected cover of the marked adjoint group of pairs. -/
def PairSplitSpin : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), (2 : k) = 0 → 0 < n →
    let q := Arithmetic.OddSpinCharTwoStabilizer.oddForm k n
    ∃ (H O P : AffineAlgebraicGroup k) (f : H.val ⟶ O.val) (p : O.val ⟶ P.val)
      (h : ∀ R : TestAlgebra k, SchemePoints H.val R →* (ScalarClifford q R)ˣ)
      (o : ∀ R : TestAlgebra k, SchemePoints O.val R ≃* MarkedIsometries R n)
      (s : ∀ R : TestAlgebra k, SchemePoints P.val R ≃* PointGroup (PlaneIndex.{u} n) R),
      RepresentsPairProjection p o s ∧
      P.val.X = SymplecticMatrixStructure.symplecticScheme k (PlaneIndex.{u} n) ∧
      IsSpinPointRepresentation q H.val h ∧ IsSemisimple H ∧ GeometricallySimplyConnected H ∧
      IsSemisimple O ∧ IsCentralIsogeny f ∧ UniversallyInjective f.hom.hom.left ∧
      (∃ A : QuadraticCliffordAction q (oddBasis k n) O.val,
        ∀ (R : TestAlgebra k) (a : SchemePoints O.val R),
          let c := ((Pi.basisFun k (OddIndex n)).baseChange R).equivFun
          A.linear R a = c.trans ((oddMatrixAction (o R a).val).trans c.symm)) ∧
      (∀ (R : TestAlgebra k) (a : SchemePoints H.val R),
        let c := ((Pi.basisFun k (OddIndex n)).baseChange R).equivFun
        IsVectorAction q R (h R a) (c.trans ((oddMatrixAction (o R (a ≫ f.hom.hom)).val).trans c.symm))) ∧
      (∃ (M : GroupScheme k) (Z : ClosedSubgroup H.val),
        M.X = Albert.SpinSpecification.muTwoUnderlying k ∧ Nonempty (M ≅ Z.group) ∧
        IsSchemeKernel f Z ∧ RepresentsSubgroup Z (fun _ z => Centralizes (𝟙 H.val) z)) ∧
      ∃ (T : ClosedSubgroup O.val) (U : ClosedSubgroup H.val) (fT : U.group ⟶ T.group),
        IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧
        IsSplitTorus U.group ∧ IsGeometricallyMaximal U ∧ IsTorusRestriction f fT ∧
        IsPullback fT.hom.hom U.inclusion.hom.hom T.inclusion.hom.hom f.hom.hom ∧
        ∃ (t : ∀ R : TestAlgebra k, SchemePoints T.group R ≃* (Fin n → Rˣ))
          (u : ∀ R : TestAlgebra k, SchemePoints U.group R ≃* liftTorus (R := R) n),
          (∀ R (a : SchemePoints T.group R) x,
            oddMatrixAction (o R (a ≫ T.inclusion.hom.hom)).val x = diagonalOddVector (t R a) x) ∧
          (∀ R (a : SchemePoints U.group R), (u R a).val.1 = t R (a ≫ fT.hom.hom)) ∧
          ∃ (comm : IsCommMonObj T.group.X),
            letI := comm
            ∃ (D : Datum T) (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
              (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ)),
              IsTypeBDatum n T D X Y ∧
              (corootLatticeOf D).map Y.toLinearMap = evenSum (Fin n) ∧
              Function.Injective (fun c : Cocharacter U.group => c ≫ fT) ∧
              Set.range (fun c : Cocharacter U.group => Y (Additive.ofMul (c ≫ fT))) = evenSum (Fin n)


section Approximation

open Opposite
open AutomorphismSequence (AdjointQuotient IsSeparableForm SplitSequence relativePoints)
open RelativeFormComparison (fieldTest)
open Pinning (AttachedDatum PinnedGroup SplitBorelPair)
open RootGroups (AdditiveLine)
open CharacterDescent (Cocharacter)
open Arithmetic.OddSpinInnerDescent (SpinAdjointAction typeBCartan SpansRationally)
open OppositeRadicals (IsNoncentral)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open IsotropicSpinGeneration (IsRegular IsIsotropic)
open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (StrongApproximation)
open IntegralModels (MatrixRealization)

open AbstractPairing (Root)

/-- Coordinates for the full simply connected type-B datum. Its cocharacter
lattice is the even-sum lattice. The character lattice is paired perfectly
with this lattice, and the indicated roots act by integer dot products. -/
structure SimplyConnectedTypeBMarking {k : Type u} [Field k] {G : AffineAlgebraicGroup k}
    {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] (n : ℕ) (D : Datum T) where
  cocharacters : Additive (Cocharacter T.group) ≃ₗ[ℤ] evenSum (Fin n)
  roots : Root T ≃ ↥(Arithmetic.OddSpinAwayFromTwo.corootPairs n)
  pairing_eq : ∀ (a : Root T) (c : Additive (Cocharacter T.group)),
    D.rootDatum.toLinearMap (D.rootDatum.root a) c =
      ∑ i, (roots a).val.1 i * (cocharacters c).val i
  coroot_eq : ∀ a, (cocharacters (D.rootDatum.coroot a)).val = (roots a).val.2

/-- The marked adjoint type-B datum determines the full lattices and paired
roots of a simply connected central cover. -/
def TypeBMarkingFromAdjoint : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (E : AttachedDatum P) (n : ℕ),
    0 < n → IsSemisimple P.G → GeometricallySimplyConnected P.G →
    ∀ (O : AffineAlgebraicGroup k), GeometricRadicals.IsReductive O →
      ∀ (T : ClosedSubgroup O.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
        ∀ (f : P.G.val ⟶ O.val), IsCentralIsogeny f →
          ∀ (q : P.T.group ⟶ T.group), IsTorusRestriction f q →
            ∀ [IsCommMonObj T.group.X] (D : Datum T)
              (X : Additive (Character T.group) ≃ₗ[ℤ] (Fin n → ℤ))
              (Y : Additive (Cocharacter T.group) ≃ₗ[ℤ] (Fin n → ℤ)),
              IsTypeBDatum n T D X Y →
              letI := E.comm
              Nonempty (SimplyConnectedTypeBMarking n E.datum)

/-- An odd quadratic model of the given group, including all test-algebra
points, the isotropic-vector implication, and strong approximation. -/
def OddSpinDescription {k : Type u} [Field k] (rank : ℕ) (G : AffineAlgebraicGroup k) : Prop :=
  ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module k W) (_ : Module.Finite k W)
    (q : QuadraticForm k W) (g : ∀ R : TestAlgebra k, SchemePoints G.val R →* (ScalarClifford q R)ˣ),
    Module.finrank k W = 2 * rank + 1 ∧ IsRegular q ∧ IsSpinPointRepresentation q G.val g ∧
    (∀ c : Cocharacter G.val, IsNoncentral c → IsIsotropic q) ∧
    ∀ (F : GlobalFieldData.{u, v} k), IsAbsolutelyAlmostSimple G →
      (∃ c : Cocharacter G.val, IsNoncentral c) →
      ∀ (i : MatrixRealization G) (S : Finset F.Place), S.Nonempty → StrongApproximation F i S

/-- The inner-descent and approximation step for a pinned type-B model with
its quadratic adjoint action. The resulting spin representation belongs to
the original group, so approximation uses its prescribed matrix realization. -/
def TypeBDescentApproximation : Prop :=
  ∀ {k S V I : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    [AddCommGroup V] [Module k V] [Module.Finite k V] [LinearOrder I]
    {L : AdditiveLine k} {P : PinnedGroup L} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {J : AdjointQuotient P.pair.G}
    (E : SplitSequence P D l J)
    (n : ℕ) (simple : Fin (n + 1) ≃ D.toBased.base.support)
    (q₀ : QuadraticForm k V) (b₀ : Module.Basis I k V)
    (g₀ : ∀ R : TestAlgebra k, SchemePoints P.pair.G.val R →* (ScalarClifford q₀ R)ˣ)
    (_ : SpinAdjointAction q₀ b₀ P.pair.G J.quotient E.inner g₀)
    (G : AffineAlgebraicGroup k)
    (_ : relativePoints P.pair.G.val (fieldTest k S) ≅ relativePoints G.val (fieldTest k S)),
    (∀ i j, D.toBased.datum.pairing (simple i).val (simple j).val = typeBCartan n i j) →
    SpansRationally (Set.range fun i => D.toBased.datum.coroot (simple i).val) →
    IsRegular q₀ → Module.finrank k V = 2 * (n + 1) + 1 →
    IsSpinPointRepresentation q₀ P.pair.G.val g₀ →
    OddSpinDescription.{u,v} (n + 1) G

/-- Every separable form of the split simply connected type-B group has an
intrinsic regular odd spin model. The type is specified on the actual
split root datum, in the paired root and coroot coordinates. -/
def TypeBFormDescent : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P)
    (n : ℕ) (G : AffineAlgebraicGroup k),
    (letI := D.comm; Nonempty (SimplyConnectedTypeBMarking (n + 1) D.datum)) →
    IsSeparableForm P.G G → OddSpinDescription.{u,v} (n + 1) G

/-- A simply connected absolutely almost simple group whose actual geometric
Cartan datum has type B has a regular odd quadratic spin model over its ground
field. -/
def TypeBApplicability : Prop :=
  ∀ {k : Type u} [Field k] (rank : ℕ) (hRank : 2 ≤ rank)
    (G : AffineAlgebraicGroup k), IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G →
    ∀ (P : SplitBorelPair (AlgebraicClosure k)), P.G = GeometricRadicals.GeometricGroup G →
    ∀ D : AttachedDatum P,
      (letI := D.comm
       AbsoluteDynkinTypes.HasDynkinType (RootData.integralCartan D.datum.rootDatum D.base)
         (.B rank hRank)) →
      OddSpinDescription.{u,v} rank G

end Approximation


end

end LinearAlgebraicGroups.Specs.Arithmetic.OddSpinModels
