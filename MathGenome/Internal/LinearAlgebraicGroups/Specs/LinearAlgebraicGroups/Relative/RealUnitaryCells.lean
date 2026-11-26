import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SpecialLinearDatum
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeBruhat
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RelativeChambers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
import Mathlib.Algebra.QuadraticAlgebra.BaseChange
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

open CategoryTheory AlgebraicGeometry
open scoped Matrix TensorProduct CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Specs.RealUnitaryCells

noncomputable section

abbrev Complexification (R : Type*) [CommRing R] := QuadraticAlgebra R (-1) 0

abbrev SL (R : Type*) [CommRing R] := Matrix.SpecialLinearGroup (Fin 3) R

/-- The Hermitian form in the ordered isotropic basis of D10. -/
def J (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 0]

/-- The longest permutation with the middle entry corrected to determinant one. -/
def longestMatrix (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 1; 0, -1, 0; 1, 0, 0]

/-- A determinant-one representative of the adjacent transposition (12). -/
def adjacentMatrix (R : Type*) [CommRing R] : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 1]

def IsUnitary {R : Type*} [CommRing R] [StarRing R] (g : SL R) : Prop :=
  g.valᴴ * J R * g.val = J R

/-- The first basis line is preserved. In the determinant-one group the
restriction to that line is then invertible, even over general rings. -/
def PreservesLine {R : Type*} [CommRing R] (g : SL R) : Prop :=
  g.val 1 0 = 0 ∧ g.val 2 0 = 0

def InDoubleCoset {R : Type*} [CommRing R] (P : SL R → Prop) (w g : SL R) : Prop :=
  ∃ p q : SL R, P p ∧ P q ∧ g = p * w * q

/-- The all-algebra comparison of C tensor R with the real and imaginary
coordinates, with conjugation acting on the C factor. -/
def ComplexTensorModel : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℝ R],
    ∃ e : R ⊗[ℝ] ℂ ≃ₐ[R] Complexification R,
      ∀ (r : R) (z : ℂ), e (r ⊗ₜ z) =
        ⟨r * algebraMap ℝ R z.re, r * algebraMap ℝ R z.im⟩

/-- On all complex test algebras the two coordinates are evaluations at
the two square roots of minus one. Conjugation interchanges the factors. -/
def ComplexSplitting : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℂ R],
    ∃ e : Complexification R ≃ₐ[R] R × R,
      (∀ z, e z = (z.re + z.im * algebraMap ℂ R Complex.I,
        z.re - z.im * algebraMap ℂ R Complex.I)) ∧
      ∀ z, e (star z) = (e z).swap

/-- Over each complex test algebra the group in the Hermitian equations
is parameterized by the first matrix. The line stabilizer corresponds to
the upper triangular subgroup, through that same comparison. -/
def ComplexGroupComparison : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra ℂ R],
    ∃ e : {g : SL (Complexification R) // IsUnitary g} ≃ SL R,
      (∀ g i j, (e g).val i j =
        (g.val.val i j).re + (g.val.val i j).im * algebraMap ℂ R Complex.I) ∧
      (∀ g h m, m.val = g.val * h.val → e m = e g * e h) ∧
      ∀ g, PreservesLine g.val ↔ (e g).val.IsUpperTriangular

/-- The three-by-three Hermitian form has two positive directions and
one negative direction, by an explicit diagonalizing basis. -/
def Signature : Prop :=
  ∃ B : Matrix (Fin 3) (Fin 3) ℂ, IsUnit B.det ∧
    Bᴴ * J ℂ * B = Matrix.diagonal ![1, 1, -1]

/-- Over the real ground field the two disjoint double cosets are distinguished
by the bottom entry of the first column. -/
def RealDoubleCosets : Prop :=
  ∃ w : SL ℂ, w.val = longestMatrix ℂ ∧ IsUnitary w ∧
    ∀ g : SL ℂ, IsUnitary g →
      let P := fun x : SL ℂ ↦ IsUnitary x ∧ PreservesLine x
      (InDoubleCoset P 1 g ↔ g.val 2 0 = 0) ∧
      (InDoubleCoset P w g ↔ g.val 2 0 ≠ 0)

/-- The (12) cell supplies a point outside the identity and longest cells. -/
def MissingComplexCell : Prop :=
  ∃ w s : SL ℂ, w.val = longestMatrix ℂ ∧ s.val = adjacentMatrix ℂ ∧
    ¬ InDoubleCoset (fun x : SL ℂ ↦ x.val.IsUpperTriangular) 1 s ∧
    ¬ InDoubleCoset (fun x : SL ℂ ↦ x.val.IsUpperTriangular) w s

/-- Extension of coefficients in the real and imaginary coordinates. -/
def complexMap {R A : Type*} [CommRing R] [CommRing A] (f : R →+* A) :
    Complexification R →+* Complexification A where
  toFun x := ⟨f x.re, f x.im⟩
  map_one' := by
    apply QuadraticAlgebra.ext
    · exact map_one f
    · exact map_zero f
  map_zero' := by apply QuadraticAlgebra.ext <;> simp
  map_mul' _ _ := by
    apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  map_add' _ _ := by apply QuadraticAlgebra.ext <;> simp

/-- Coordinates for the unitary group and its line stabilizer. -/
abbrev CoordinateIndex := Bool × Fin 3 × Fin 3

abbrev MatrixPolynomial := MvPolynomial CoordinateIndex ℝ

def genericUnitaryMatrix : Matrix (Fin 3) (Fin 3) (Complexification MatrixPolynomial) :=
  fun i j => ⟨MvPolynomial.X (false, i, j), MvPolynomial.X (true, i, j)⟩

def coefficientSet
    (u : Set (Complexification MatrixPolynomial)) : Set MatrixPolynomial :=
  (QuadraticAlgebra.re '' u) ∪ (QuadraticAlgebra.im '' u)

def unitaryIdeal : Ideal MatrixPolynomial :=
  Ideal.span (coefficientSet ({genericUnitaryMatrix.det - 1} ∪
    Set.range (fun p : Fin 3 × Fin 3 =>
      (genericUnitaryMatrixᴴ * J (Complexification MatrixPolynomial) * genericUnitaryMatrix -
        J (Complexification MatrixPolynomial)) p.1 p.2)))

def lineIdeal : Ideal MatrixPolynomial :=
  Ideal.span (coefficientSet {genericUnitaryMatrix 1 0, genericUnitaryMatrix 2 0})

abbrev Coordinates (line : Bool) :=
  MatrixPolynomial ⧸ (unitaryIdeal ⊔ if line then lineIdeal else ⊥)

instance coordinatesFiniteType (line : Bool) : Algebra.FiniteType ℝ (Coordinates line) :=
  inferInstanceAs (Algebra.FiniteType ℝ (MatrixPolynomial ⧸ _))

def MatrixCondition (line : Bool) {R : Type*} [CommRing R]
    (g : SL (Complexification R)) : Prop :=
  IsUnitary g ∧ (line = true → PreservesLine g)

/-- Both functors are represented by the explicit real coordinate rings.
Compatibility with multiplication and change of test algebra is part
of the comparison. -/
def RealGroupModels : Prop :=
  ∀ line : Bool, ∃ (h : StandardGroups.HopfOperations ℝ (Coordinates line)),
    letI := h.hopf
    let G := StandardGroups.spectrum ℝ (Coordinates line)
    ∃ E : ∀ R : TestAlgebra ℝ,
      Points G.val.X R ≃ {g : SL (Complexification R) // MatrixCondition line g},
    (∀ (R A : TestAlgebra ℝ) (f : R ⟶ A) (g : Points G.val.X R),
      (E A (mapPoints f g)).val =
        Matrix.SpecialLinearGroup.map (complexMap f.hom.toRingHom) (E R g).val) ∧
    (∀ (R : TestAlgebra ℝ) (g h : Points G.val.X R),
      (E R (g * h)).val = (E R g).val * (E R h).val)

open SpecialLinearDatum
open GeneralLinearStructure (SpecialMatrixPoints)
open Unipotent (Index)

open CharacterDescent (Character)
open CharacterPairing (pairing)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open GeometricRadicals (IsReductive IsSplitTorus)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open Relative.RelativeChambers (relativeRoots)
open SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (unitPoint)

abbrev MultiplicativeLine (k : Type) [Field k] := specGroup (groupAlgebra k IntegerCharacters)

/-- The real equations and their canonical first-factor complex identification,
with the upper triangular Borel for the actual matrix pinning. -/
structure UnitaryComparison where
  realGroup : AffineAlgebraicGroup ℝ
  line : ClosedSubgroup realGroup.val
  points : ∀ R : TestAlgebra ℝ,
    Points realGroup.val.X R ≃ {g : SL (Complexification R) // MatrixCondition false g}
  pointsNatural : ∀ (R A : TestAlgebra ℝ) (f : R ⟶ A) (g : Points realGroup.val.X R),
    (points A (mapPoints f g)).val =
      Matrix.SpecialLinearGroup.map (complexMap f.hom.toRingHom) (points R g).val
  pointsMul : ∀ (R : TestAlgebra ℝ) (g h : Points realGroup.val.X R),
    (points R (g * h)).val = (points R g).val * (points R h).val
  complexGroup : AffineAlgebraicGroup ℂ
  matrixPoints : SpecialMatrixPoints complexGroup 3
  complexIso : (groupBaseChange ℝ ℂ).obj realGroup.val ≅ complexGroup.val
  complexCoordinateModel :
    ∃ H : StandardGroups.HopfOperations ℂ (StandardGroups.SLCoordinates ℂ (Index.{0} 3)),
      letI := H.hopf
      Nonempty (complexGroup.val ≅
        (StandardGroups.spectrum ℂ (StandardGroups.SLCoordinates ℂ (Index.{0} 3))).val)
  linePoints : ∀ (R : TestAlgebra ℝ) (g : Points realGroup.val.X R),
    (∃ p : Points line.group.X R, p ≫ line.inclusion.hom.hom = g) ↔ PreservesLine (points R g).val
  complexPoints : ∀ (R : TestAlgebra ℂ)
    (g : Points ((groupBaseChange ℝ ℂ).obj realGroup.val).X R) (i j : Fin 3),
    (matrixPoints.hom.app R (g ≫ complexIso.hom.hom.hom)).val ⟨i⟩ ⟨j⟩ =
      let z := ((points _ (baseChangePoint ℝ ℂ realGroup.val.X R g)).val.val) i j
      z.re + z.im * algebraMap ℂ R Complex.I
  diagonal : DiagonalTorus matrixPoints
  lattice : LatticeIdentification diagonal
  roots : RootIdentification diagonal lattice
  borel : UpperTriangularBorel diagonal lattice roots
  datum : Pinning.AttachedDatum borel.pair
  basedDatum : IsMatrixBasedDatum borel datum
  pinning : HasTransvectionPinning borel
  borelIso : (groupBaseChange ℝ ℂ).obj line.group ≅ borel.limits.parabolic.group
  borelInclusion : borelIso.hom ≫ borel.limits.parabolic.inclusion =
    (groupBaseChange ℝ ℂ).map line.inclusion ≫ complexIso.hom

def UnitarySchemeComparison : Prop := Nonempty UnitaryComparison

/-- The rank-one split subgroup is marked by the diagonal parameter. The
character exponent is the pairing against this cocharacter. -/
structure SplitTorusComparison (C : UnitaryComparison) where
  torus : ClosedSubgroup C.realGroup.val
  parameter : MultiplicativeLine ℝ ≅ torus.group
  matrix : ∀ (R : TestAlgebra ℝ) (t : Rˣ),
    (C.points R ((unitPoint R t ≫ parameter.hom.hom.hom) ≫ torus.inclusion.hom.hom)).val.val =
      Matrix.diagonal (fun i => algebraMap R (Complexification R) (![↑t, 1, ↑t⁻¹] i))
  isSplit : IsSplitTorus torus.group
  contained : IsSubgroupOf torus C.line
  reductive : IsReductive C.realGroup
  minimal : IsMinimalParabolic C.realGroup C.line
  complexParameter : MultiplicativeLine ℂ ≅ (groupBaseChange ℝ ℂ).obj torus.group
  complexParameterValue : ∀ (R : TestAlgebra ℂ) (t : Rˣ),
    baseChangePoint ℝ ℂ torus.group.X R (unitPoint R t ≫ complexParameter.hom.hom.hom) =
      unitPoint ((restrictTestAlgebra ℝ ℂ).obj R) t ≫ parameter.hom.hom.hom
  complexInclusion : (groupBaseChange ℝ ℂ).obj torus.group ⟶ C.diagonal.subgroup.group
  complexFactor : complexInclusion ≫ C.diagonal.subgroup.inclusion =
    (groupBaseChange ℝ ℂ).map torus.inclusion ≫ C.complexIso.hom
  absoluteRestriction : ∀ p : RootIndices 3,
    pairing C.diagonal.subgroup.group (C.roots.indices p).val
      (complexParameter.hom ≫ complexInclusion) =
      (![1, 0, -1] : Fin 3 → ℤ) p.val.1 - (![1, 0, -1] : Fin 3 → ℤ) p.val.2
  characterExponents : Function.Bijective
    (fun a : Character torus.group => pairing torus.group a parameter.hom)
  relativeRootExponents :
    Set.range (fun a : relativeRoots torus => pairing torus.group a.val parameter.hom) =
      ({1, -1, 2, -2} : Set ℤ)

/-- The simple roots of the marked Borel restrict to exponent one. Their
sum, written as a product of characters, restricts to exponent two. -/
def SimpleRootRestrictions {C : UnitaryComparison} (S : SplitTorusComparison C) : Prop :=
  letI := C.datum.comm
  let root01 := C.roots.indices ⟨(0, 1), by decide⟩
  let root12 := C.roots.indices ⟨(1, 2), by decide⟩
  let root02 := C.roots.indices ⟨(0, 2), by decide⟩
  let c := S.complexParameter.hom ≫ S.complexInclusion
  (∀ r, r ∈ C.datum.base.support ↔ r = root01 ∨ r = root12) ∧
    root01.val * root12.val = root02.val ∧
    pairing C.diagonal.subgroup.group root01.val c = 1 ∧
    pairing C.diagonal.subgroup.group root12.val c = 1 ∧
    pairing C.diagonal.subgroup.group root02.val c = 2

/-- The marked comparison and the restrictions giving BC₁. -/
def UnitaryRootSystem : Prop :=
  ∃ (C : UnitaryComparison) (S : SplitTorusComparison C), SimpleRootRestrictions S

def MaximalUnitarySplitTorus : Prop :=
  ∃ (C : UnitaryComparison) (S : SplitTorusComparison C), IsMaximalSplitTorus S.torus

open Relative.RelativeBruhat (DoubleOrbit)
open Relative.RelativeWeylScheme (QuotientData rationalProjection)
open SimpleParabolicProduct (doubleCoset)
open AbstractPairing (Datum)
open DatumAndWeyl (Identification)
open BruhatOrbitParametrization (IsRepresentative)
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

/-- The tensor unit and the test scheme for the ground field have the same
underlying spectrum with its identity structure morphism. -/
def rationalTestIso (k : Type) [Field k] :
    𝟙_ (SchemeOver k) ≅ (testSpec k).obj (.op (CommAlgCat.of k k)) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change (𝟙 (Spec (CommRingCat.of k))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _
    rw [Category.id_comp]
    exact Spec.map_id _)

/-- The index of a monomial representative sends each column to the row of
its nonzero entry. -/
def HasPermutationSupport {R : Type*} [CommRing R] (σ : Equiv.Perm (Fin 3)) (g : Matrix (Fin 3) (Fin 3) R) : Prop :=
  ∀ i j, g i j ≠ 0 ↔ i = σ j

abbrev longestPermutation : Equiv.Perm (Fin 3) := Equiv.swap 0 2

abbrev adjacentPermutation : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The actual relative normalizer quotient, its two marked rational
representatives, and the fppf images of their double-orbit maps. -/
structure UnitaryRelativeOrbits {C : UnitaryComparison} (S : SplitTorusComparison C) where
  quotient : QuotientData S.torus
  longestLift : 𝟙_ (SchemeOver ℝ) ⟶ quotient.normalizer.group.X
  longestLabel : quotient.splitImage.labels
  longestProjects : rationalProjection quotient longestLift =
    quotient.splitImage.constantGroup.sectionPoint longestLabel
  longestLabel_ne_one : longestLabel ≠ 1
  twoLabels : ∀ w : quotient.splitImage.labels, w = 1 ∨ w = longestLabel
  longestMatrix_eq :
    (C.points (CommAlgCat.of ℝ ℝ) ((rationalTestIso ℝ).inv ≫
      longestLift ≫ quotient.normalizer.inclusion.hom.hom)).val.val =
        longestMatrix (Complexification ℝ)
  inversion :
    conjugateFamily S.torus.inclusion (longestLift ≫ quotient.normalizer.inclusion.hom.hom) =
      (fst S.torus.group.X (𝟙_ (SchemeOver ℝ)) ≫ S.torus.inclusion.hom.hom)⁻¹
  identityOrbit : DoubleOrbit C.line 1
  longestOrbit : DoubleOrbit C.line (longestLift ≫ quotient.normalizer.inclusion.hom.hom)
  rationalCover : doubleCoset C.line (𝟙_ (SchemeOver ℝ)) 1 ∪
    doubleCoset C.line (𝟙_ (SchemeOver ℝ))
      (longestLift ≫ quotient.normalizer.inclusion.hom.hom) = Set.univ
  rationalDisjoint : Disjoint (doubleCoset C.line (𝟙_ (SchemeOver ℝ)) 1)
    (doubleCoset C.line (𝟙_ (SchemeOver ℝ))
      (longestLift ≫ quotient.normalizer.inclusion.hom.hom))

abbrev UnitaryRelativeOrbits.longestPoint {C : UnitaryComparison} {S : SplitTorusComparison C}
    (O : UnitaryRelativeOrbits S) : 𝟙_ (SchemeOver ℝ) ⟶ C.realGroup.val.X :=
  O.longestLift ≫ O.quotient.normalizer.inclusion.hom.hom

/-- The six complex cells, labeled by their permutation action on the
coordinate lines of the actual diagonal torus. -/
structure UnitaryAbsoluteOrbits (C : UnitaryComparison) where
  comm : IsCommMonObj C.diagonal.subgroup.group.X
  datum : letI := comm; Datum C.diagonal.subgroup
  normalizer : letI := comm; Identification datum
  index : Equiv.Perm (Fin 3) ≃ datum.rootDatum.weylGroup
  cardinality : Nat.card datum.rootDatum.weylGroup = 6
  longestReversesOrder : ∀ i j : Fin 3, i < j ↔ longestPermutation j < longestPermutation i
  lift : Equiv.Perm (Fin 3) → (𝟙_ (SchemeOver ℂ) ⟶ normalizer.normalizer.group.X)
  representative : ∀ σ : Equiv.Perm (Fin 3), letI := comm;
    IsRepresentative normalizer (index σ) (lift σ)
  support : ∀ σ : Equiv.Perm (Fin 3), HasPermutationSupport σ
    ((C.matrixPoints.hom.app (CommAlgCat.of ℂ ℂ) ((rationalTestIso ℂ).inv ≫
      lift σ ≫ normalizer.normalizer.inclusion.hom.hom)).val.submatrix ULift.up ULift.up)
  identity_eq : lift 1 ≫ normalizer.normalizer.inclusion.hom.hom = 1
  longestMatrix_eq : ∀ i j : Fin 3,
    (C.matrixPoints.hom.app (CommAlgCat.of ℂ ℂ) ((rationalTestIso ℂ).inv ≫
      lift longestPermutation ≫ normalizer.normalizer.inclusion.hom.hom)).val ⟨i⟩ ⟨j⟩ =
      longestMatrix ℂ i j
  adjacentMatrix_eq : ∀ i j : Fin 3,
    (C.matrixPoints.hom.app (CommAlgCat.of ℂ ℂ) ((rationalTestIso ℂ).inv ≫
      lift adjacentPermutation ≫ normalizer.normalizer.inclusion.hom.hom)).val ⟨i⟩ ⟨j⟩ =
      adjacentMatrix ℂ i j
  orbits : ∀ σ : Equiv.Perm (Fin 3), DoubleOrbit C.borel.limits.parabolic
    (lift σ ≫ normalizer.normalizer.inclusion.hom.hom)
  partition : (⋃ σ, Set.range (orbits σ).inclusion.left) = Set.univ
  disjoint : Pairwise (fun σ τ =>
    Disjoint (Set.range (orbits σ).inclusion.left) (Set.range (orbits τ).inclusion.left))

abbrev UnitaryAbsoluteOrbits.point {C : UnitaryComparison} (O : UnitaryAbsoluteOrbits C)
    (σ : Equiv.Perm (Fin 3)) : 𝟙_ (SchemeOver ℂ) ⟶ C.complexGroup.val.X :=
  letI := O.comm
  O.lift σ ≫ O.normalizer.normalizer.inclusion.hom.hom

/-- The two relative fppf orbit schemes, after scalar extension, are the
specified absolute cells as immersed subschemes of the same group. -/
def OrbitBaseChangeComparison {C : UnitaryComparison}
    {n : 𝟙_ (SchemeOver ℝ) ⟶ C.realGroup.val.X} {m : 𝟙_ (SchemeOver ℂ) ⟶ C.complexGroup.val.X}
    (A : DoubleOrbit C.line n) (B : DoubleOrbit C.borel.limits.parabolic m) : Prop :=
  ∃ e : (baseChange ℝ ℂ).obj A.scheme ≅ B.scheme,
    e.hom ≫ B.inclusion = (baseChange ℝ ℂ).map A.inclusion ≫ C.complexIso.hom.hom.hom

def UnitaryCells : Prop :=
  ∃ (C : UnitaryComparison) (S : SplitTorusComparison C),
    IsMaximalSplitTorus S.torus ∧
    ∃ (R : UnitaryRelativeOrbits S) (A : UnitaryAbsoluteOrbits C),
      OrbitBaseChangeComparison R.identityOrbit (A.orbits 1) ∧
      OrbitBaseChangeComparison R.longestOrbit (A.orbits longestPermutation) ∧
      let x := (A.point adjacentPermutation).left (IsLocalRing.closedPoint ℂ)
      x ∈ Set.range (A.orbits adjacentPermutation).inclusion.left ∧
      x ∉ Set.range ((baseChange ℝ ℂ).map R.identityOrbit.inclusion ≫
          C.complexIso.hom.hom.hom).left ∪
        Set.range ((baseChange ℝ ℂ).map R.longestOrbit.inclusion ≫
          C.complexIso.hom.hom.hom).left

end

end LinearAlgebraicGroups.Specs.RealUnitaryCells
