import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.TorusAdaptedTriangularModel
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.UnitriangularSupportSubgroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import Mathlib.Algebra.Polynomial.Laurent

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.TorusLimitFactorization

open Unipotent StandardGroups SmoothDiagonalKernel SplitSolvableRadical
open TorusAdaptedTriangularModel (characterValue DiagonalWeights)
open UnitriangularSupportSubgroups (HasSupport)
open DiagonalizableGroups (IntegerCharacters groupAlgebra)

noncomputable section

/-- Every transitive mask on strict upper entries cuts out a subgroup. -/
def TransitiveSupportSubgroup : Prop :=
  ∀ {R : Type u} [CommRing R] (n : ℕ) (q : Index.{u} n → Index.{u} n → Prop),
    (∀ i j l, q i j → q j l → q i l) →
    ∃ S : Subgroup (upperUnitriangular (Index.{u} n) R),
      ∀ g, g ∈ S ↔ HasSupport q (g.val.val - 1)

/-- The signs of the cocharacter weights prescribe the three off-diagonal supports. -/
def AmbientFactorization : Prop :=
  ∀ {R : Type u} [CommRing R] (n : ℕ) (w : Index.{u} n → ℤ)
    (g : upperUnitriangular (Index.{u} n) R),
    ∃! p : upperUnitriangular (Index.{u} n) R ×
        upperUnitriangular (Index.{u} n) R × upperUnitriangular (Index.{u} n) R,
      HasSupport (fun i j ↦ w i < w j) (p.1.val.val - 1) ∧
      HasSupport (fun i j ↦ w j < w i) (p.2.1.val.val - 1) ∧
      HasSupport (fun i j ↦ w i = w j) (p.2.2.val.val - 1) ∧
      p.1 * p.2.1 * p.2.2 = g

/-- Evaluating the conjugation orbit at the universal Laurent parameter.
The diagonal cocharacter acts on position `(i,j)` through the difference of its weights. -/
def laurentConjugate {J R : Type*} [CommRing R] (w : J → ℤ) (a : Matrix J J R) :
    Matrix J J (LaurentPolynomial R) :=
  fun i j ↦ LaurentPolynomial.C (a i j) * LaurentPolynomial.T (w i - w j)

/-- The two Laurent diagonal matrices are given by the cocharacter and its inverse. -/
def LaurentConjugationFormula : Prop :=
  ∀ {R : Type u} [CommRing R] (n : ℕ) (w : Index.{u} n → ℤ)
    (a : Matrix (Index.{u} n) (Index.{u} n) R),
    Matrix.diagonal (fun i ↦ LaurentPolynomial.T (w i)) * a.map LaurentPolynomial.C *
      Matrix.diagonal (fun i ↦ LaurentPolynomial.T (-w i)) = laurentConjugate w a

/-- Invariance under the universal cocharacter is exactly the zero-weight support. -/
def LaurentFixedCriterion : Prop :=
  ∀ {R : Type u} [CommRing R] (n : ℕ) (w : Index.{u} n → ℤ)
    (g : upperUnitriangular (Index.{u} n) R),
    laurentConjugate w g.val.val = g.val.val.map LaurentPolynomial.C ↔
      HasSupport (fun i j ↦ w i = w j) (g.val.val - 1)

/-- Existence of an extension to the polynomial chart with identity value at zero.
Using the opposite cocharacter gives the chart at infinity. -/
def HasIdentityLimit {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]
    (w : J → ℤ) (a : Matrix.GeneralLinearGroup J R) : Prop :=
  ∃ b : Matrix.GeneralLinearGroup J (Polynomial R),
    b.val.map Polynomial.toLaurent = laurentConjugate w a.val ∧
    b.val.map (Polynomial.evalRingHom 0) = 1

/-- The entry criterion for the ambient limit at zero. -/
def IdentityLimitCriterion : Prop :=
  ∀ {R : Type u} [CommRing R] (n : ℕ) (w : Index.{u} n → ℤ)
    (g : upperUnitriangular (Index.{u} n) R),
    HasIdentityLimit w g.val ↔ HasSupport (fun i j ↦ w j < w i) (g.val.val - 1)

/-- Functions on the two polynomial charts of the projective line that agree on
the Laurent chart have constant common value. -/
def PolynomialChartIntersection : Prop :=
  ∀ {R : Type u} [CommRing R] (f g : Polynomial R),
    f.toLaurent = LaurentPolynomial.invert g.toLaurent →
    f.toLaurent = LaurentPolynomial.C (f.coeff 0) ∧ f.coeff 0 = g.coeff 0

/-- The polynomial chart argument for the column spanning the stabilizing line.
The two matrix families meet the identity at their respective endpoints. -/
def StabilizingLineCharts : Prop :=
  ∀ {R J : Type u} [CommRing R] [Fintype J] [DecidableEq J]
    (i : J) (A B : Matrix J J (Polynomial R)) (Z : Matrix J J R) (c : Rˣ),
    A.map (Polynomial.evalRingHom 0) = 1 →
    B.map (Polynomial.evalRingHom 0) = 1 →
    (∀ j, (∑ l, A j l * Polynomial.C (Z l i)).toLaurent =
      LaurentPolynomial.invert ((Polynomial.C (c : R) * B j i).toLaurent)) →
    (∀ j, Z j i = (c : R) * (1 : Matrix J J R) j i) ∧
    (∀ j, (A j i).eval 1 = (1 : Matrix J J R) j i) ∧
    (∀ j, (B j i).eval 1 = (1 : Matrix J J R) j i)

variable {k : Type u} [Field k]

/-- A cocharacter is specified in split coordinates by its integral exponents. -/
def cocharacterWeight {r : ℕ} (l m : Index.{u} r → ℤ) : ℤ :=
  ∑ i, m i * l i

/-- In split coordinates the cocharacter sends a unit to its specified powers. -/
def cocharacterCoordinates {r : ℕ} (l : Index.{u} r → ℤ) :
    multiplicativePoints k ⟶ multiplicativePowerPoints k (Index.{u} r) where
  app R := GrpCat.ofHom (MonoidHom.pi fun i ↦ zpowGroupHom (l i))
  naturality R S f := by
    apply GrpCat.ext
    intro a
    funext i
    change (Units.map f.hom.toMonoidHom a) ^ l i = Units.map f.hom.toMonoidHom (a ^ l i)
    exact (map_zpow (Units.map f.hom.toMonoidHom) a (l i)).symm

/-- The cocharacter is transported along the chosen split-torus isomorphism. -/
def cocharacterPoints {r : ℕ} {T : GroupScheme k}
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Index.{u} r))
    (l : Index.{u} r → ℤ) : multiplicativePoints k ⟶ (groupPointsFunctor k).obj T :=
  cocharacterCoordinates l ≫ t.inv

/-- The point of the multiplicative group that sends its coordinate generator to a unit. -/
def multiplicativeParameter (R : TestAlgebra k) (a : Rˣ) :
    Points (specGroup (groupAlgebra k IntegerCharacters)).X R :=
  let powers : IntegerCharacters.{u} →* Rˣ :=
    (zpowersHom Rˣ a).comp MulEquiv.ulift.toMonoidHom
  let f := MonoidAlgebra.lift k R IntegerCharacters ((Units.coeHom (M := R)).comp powers)
  (testSpec k).map (CommAlgCat.ofHom f).op

/-- Realization of the cocharacter as a homomorphism of group schemes. -/
def RealizesCocharacter {r : ℕ} {T : GroupScheme k}
    (t : (groupPointsFunctor k).obj T ≅ multiplicativePowerPoints k (Index.{u} r))
    (l : Index.{u} r → ℤ) : Prop :=
  ∃ lambda : CharacterDescent.Cocharacter T, ∀ (R : TestAlgebra k) (a : Rˣ),
    multiplicativeParameter R a ≫ lambda.hom.hom = (cocharacterPoints t l).app R a

/-- The orbit of a family extends to the identity on the polynomial chart.
At infinity, the coordinate of the polynomial chart is the inverse parameter. -/
def HasGroupIdentityLimit {G : GroupScheme k} (U T : ClosedSubgroup G) {r : ℕ}
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} r))
    (l : Index.{u} r → ℤ) (atInfinity : Bool) {R : TestAlgebra k}
    (x : Points U.group.X R) : Prop :=
  let RP := CommAlgCat.of k (Polynomial R)
  let RL := CommAlgCat.of k (LaurentPolynomial R)
  let zero : RP ⟶ R := CommAlgCat.ofHom ((Polynomial.aeval (0 : R) :
    Polynomial R →ₐ[R] R).restrictScalars k)
  let punctured : RP ⟶ RL := CommAlgCat.ofHom (Polynomial.toLaurentAlg.restrictScalars k)
  let constant : R ⟶ RL := CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (LaurentPolynomial R))
  let tau : RLˣ := (LaurentPolynomial.isUnit_T (R := R) 1).unit
  let a : Points T.group.X RL := (cocharacterPoints t l).app RL
    (if atInfinity then tau⁻¹ else tau)
  let b : Points G.X RL := a ≫ T.inclusion.hom.hom
  ∃ y : Points U.group.X RP,
    mapPoints zero y = 1 ∧
    mapPoints punctured y ≫ U.inclusion.hom.hom =
      b * (mapPoints constant x ≫ U.inclusion.hom.hom) * b⁻¹

/-- A single cocharacter separates all distinct weights in a finite family. -/
def SeparatingCocharacter : Prop :=
  ∀ (n r : ℕ) (m : Index.{u} n → Index.{u} r → ℤ),
    ∃ l : Index.{u} r → ℤ,
      ∀ i j, cocharacterWeight l (m i) = cocharacterWeight l (m j) ↔ m i = m j

/-- Pulling the character back along the cocharacter gives the prescribed power. -/
def CharacterOnCocharacter : Prop :=
  ∀ {k : Type u} [Field k] {R : TestAlgebra k} (r : ℕ)
    (l m : Index.{u} r → ℤ) (a : Rˣ),
    characterValue m ((cocharacterCoordinates l).app R a) = a ^ cocharacterWeight l m

/-- Commutation with the embedded torus after every change of test algebra. -/
def CentralizesTorus {G U : GroupScheme k} (uι : U ⟶ G)
    (T : ClosedSubgroup G) {R : TestAlgebra k} (x : Points U.X R) : Prop :=
  ∀ (S : TestAlgebra k) (f : R ⟶ S) (a : Points T.group.X S),
    Commute (((groupPointsFunctor k).map uι).app S (mapPoints f x))
      (((groupPointsFunctor k).map T.inclusion).app S a)

/-- A separating cocharacter identifies the centralizer of the whole torus
with the zero-weight support of the unitriangular matrices. -/
def TorusCentralizerCriterion : Prop :=
  ∀ {k : Type u} [Field k] {G H : AffineAlgebraicGroup k} {n r : ℕ}
    (j : G.val ⟶ H.val) (U T : ClosedSubgroup G.val)
    (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} r))
    (m : Index.{u} n → Index.{u} r → ℤ) (l : Index.{u} r → ℤ),
    IsClosedImmersion j.hom.hom.left →
    DiagonalWeights (T.inclusion ≫ j) e t m →
    (∀ i j', cocharacterWeight l (m i) = cocharacterWeight l (m j') ↔ m i = m j') →
    ∀ (R : TestAlgebra k) (x : Points U.group.X R),
    let w := fun i ↦ cocharacterWeight l (m i)
    let a := (matrixPoint (U.inclusion ≫ j) e R x).val
    IsUpperUnitriangular a →
    (HasSupport (fun i j' ↦ w i = w j') (a - 1) ↔ CentralizesTorus U.inclusion T x)

/-- A closed subscheme of an affine scheme detects membership after any injective
change of test algebra. -/
def ClosedPointsAlongInjection : Prop :=
  ∀ {k : Type u} [Field k] {X Y : SchemeOver k} (j : X ⟶ Y),
    IsAffine Y.left → IsClosedImmersion j.left →
    ∀ {R S : TestAlgebra k} (f : R ⟶ S), Function.Injective f.hom →
      ∀ x : Points Y R, (∃ y : Points X S, y ≫ j = mapPoints f x) →
        ∃ y : Points X R, y ≫ j = x

/-- Multiplication of points of the negative and positive limit subgroups. -/
def pairProduct {U : GroupScheme k} (N P : ClosedSubgroup U) :
    N.group.X ⊗ P.group.X ⟶ U.X :=
  (fst N.group.X P.group.X ≫ N.inclusion.hom.hom) *
    (snd N.group.X P.group.X ≫ P.inclusion.hom.hom)

/-- Multiplication from the three closed subgroups, in the indicated order. -/
def tripleProduct {U : GroupScheme k} (N P Z : ClosedSubgroup U) :
    (N.group.X ⊗ P.group.X) ⊗ Z.group.X ⟶ U.X :=
  (fst (N.group.X ⊗ P.group.X) Z.group.X ≫ pairProduct N P) *
    (snd (N.group.X ⊗ P.group.X) Z.group.X ≫ Z.inclusion.hom.hom)

/-- The first two factors represent the quotient for right multiplication by the third. -/
def RepresentsSplitQuotient {U : GroupScheme k} (N P Z : ClosedSubgroup U) : Prop :=
  ∃ q : U.X ⟶ N.group.X ⊗ P.group.X,
    (∃ E : rightQuotientSheaf Z ≅ schemeFppfSheaf (N.group.X ⊗ P.group.X),
      rightQuotientProjection Z ≫ E.hom = (fppfOver k).uliftYoneda.map q) ∧
    pairProduct N P ≫ q = 𝟙 _

/-- A multiplication isomorphism with a last subgroup gives a section of its
homogeneous quotient. -/
def SplitQuotient : Prop :=
  ∀ {k : Type u} [Field k] {U : GroupScheme k} (N P Z : ClosedSubgroup U),
    IsIso (tripleProduct N P Z) → RepresentsSplitQuotient N P Z

/-- An injective unitriangular realization whose ambient factors stay in its image
induces the multiplication isomorphism when the signed supports are represented
by the indicated closed subgroups. -/
def MultiplicationFromPointFactors : Prop :=
  ∀ {k : Type u} [Field k] (U : AffineAlgebraicGroup k)
    (N P Z : ClosedSubgroup U.val) (n : ℕ) (w : Index.{u} n → ℤ)
    (E : ∀ R : TestAlgebra k, Points U.val.X R →* upperUnitriangular (Index.{u} n) R),
    (∀ R, Function.Injective (E R)) →
    (∀ R (x : Points U.val.X R),
      (HasSupport (fun i j ↦ w i < w j) ((E R x).val.val - 1) ↔
        ∃ y : Points N.group.X R, y ≫ N.inclusion.hom.hom = x) ∧
      (HasSupport (fun i j ↦ w j < w i) ((E R x).val.val - 1) ↔
        ∃ y : Points P.group.X R, y ≫ P.inclusion.hom.hom = x) ∧
      (HasSupport (fun i j ↦ w i = w j) ((E R x).val.val - 1) ↔
        ∃ y : Points Z.group.X R, y ≫ Z.inclusion.hom.hom = x)) →
    (∀ R (x : Points U.val.X R) (a b c : upperUnitriangular (Index.{u} n) R),
      HasSupport (fun i j ↦ w i < w j) (a.val.val - 1) →
      HasSupport (fun i j ↦ w j < w i) (b.val.val - 1) →
      HasSupport (fun i j ↦ w i = w j) (c.val.val - 1) →
      a * b * c = E R x →
      a ∈ (E R).range ∧ b ∈ (E R).range ∧ c ∈ (E R).range) →
    IsIso (tripleProduct N P Z)

/-- Factorization for a split solvable group with a torus complement to its radical.
The support signs are relative to the weights of the chosen cocharacter. -/
def Factorization : Prop :=
  ∀ {k : Type u} [Field k] (G D : AffineAlgebraicGroup k)
    (p : G.val ⟶ D.val) (U T : ClosedSubgroup G.val),
    SchemeDerivedGroup.IsSplitSolvable G.val →
    IsSplitTorus D → IsSchemeKernel p U →
    Smooth U.group.X.hom → GeometricallyConnected U.group.X.hom →
    IsNormalSubgroup U.inclusion →
    IsSplitTorus (closedSubgroupAlgebraicGroup T) →
    IsIso (T.inclusion ≫ p) →
    IsUnipotent (closedSubgroupAlgebraicGroup U) →
    (∀ V : ClosedSubgroup G.val, IsUnipotent (closedSubgroupAlgebraicGroup V) →
      SchemeDerivedGroup.IsSubgroupOf V U) →
    ∃ (n r : ℕ) (H : AffineAlgebraicGroup k) (j : G.val ⟶ H.val)
      (e : (groupPointsFunctor k).obj H.val ≅ generalLinearPoints k (Index.{u} n))
      (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} r))
      (m : Index.{u} n → Index.{u} r → ℤ) (l : Index.{u} r → ℤ)
      (N P Z : ClosedSubgroup U.group),
      IsClosedImmersion j.hom.hom.left ∧ IsUpperTriangular j e ∧
      DiagonalWeights (T.inclusion ≫ j) e t m ∧
      (∀ i j', cocharacterWeight l (m i) = cocharacterWeight l (m j') ↔ m i = m j') ∧
      RealizesCocharacter t l ∧
      (let w := fun i ↦ cocharacterWeight l (m i)
       ∀ (R : TestAlgebra k) (x : Points U.group.X R),
        let a := (matrixPoint (U.inclusion ≫ j) e R x).val - 1
        IsUpperUnitriangular (matrixPoint (U.inclusion ≫ j) e R x).val ∧
        (HasGroupIdentityLimit U T t l true x ↔
          ∃ y : Points N.group.X R, y ≫ N.inclusion.hom.hom = x) ∧
        (HasGroupIdentityLimit U T t l false x ↔
          ∃ y : Points P.group.X R, y ≫ P.inclusion.hom.hom = x) ∧
        (HasSupport (fun i j' ↦ w i = w j') a ↔ Centralizes T.inclusion (x ≫ U.inclusion.hom.hom)) ∧
        (Centralizes T.inclusion (x ≫ U.inclusion.hom.hom) ↔
          ∃ y : Points Z.group.X R, y ≫ Z.inclusion.hom.hom = x)) ∧
      IsIso (tripleProduct N P Z) ∧ RepresentsSplitQuotient N P Z

end
end LinearAlgebraicGroups.Specs.TorusLimitFactorization
