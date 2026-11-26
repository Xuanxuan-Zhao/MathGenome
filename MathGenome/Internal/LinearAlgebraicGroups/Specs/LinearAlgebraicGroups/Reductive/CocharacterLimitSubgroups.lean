import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.AdjointRepresentation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.Stabilizers
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import Mathlib.Algebra.Polynomial.Laurent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj LaurentPolynomial

universe u

namespace LinearAlgebraicGroups.CocharacterDynamics

open LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.CharacterDescent (Cocharacter)
open Specs.DiagonalizableGroups (groupAlgebra groupAlgebraMap IntegerCharacters)

noncomputable section

variable {k : Type u} [Field k] {G H : GroupScheme k}

/-- The subgroup cut out by a closed immersion in an affine algebraic group is
itself an affine algebraic group. -/
def affineAlgebraicSubgroup {G : GroupScheme k}
    (S : ClosedSubgroup G) (ha : IsAffine G.X.left) (hf : LocallyOfFiniteType G.X.hom)
    (hq : QuasiCompact G.X.hom) :
    AffineAlgebraicGroup k := by
  letI := ha
  letI := hf
  letI := S.isClosedImmersion
  refine ⟨S.group, isAffine_of_isAffineHom S.inclusion.hom.hom.left, ?_, ?_⟩
  · rw [← Over.w S.inclusion.hom.hom]
    infer_instance
  · let := hq
    rw [← Over.w S.inclusion.hom.hom]
    infer_instance

/-- Evaluation of the coordinate characters of the multiplicative group at a unit. -/
def unitCoordinates (R : TestAlgebra k) (t : Rˣ) :
    MonoidAlgebra k IntegerCharacters →ₐ[k] R :=
  MonoidAlgebra.lift k R IntegerCharacters <|
    (Units.coeHom R).comp ((zpowersHom Rˣ t).comp MulEquiv.ulift.toMonoidHom)

/-- The point of the multiplicative group associated to a unit of a test algebra. -/
def unitPoint (R : TestAlgebra k) (t : Rˣ) :
    GroupPoints (specGroup (groupAlgebra k IntegerCharacters)) R :=
  (testSpec k).map (CommAlgCat.ofHom (unitCoordinates R t)).op

/-- The inverse cocharacter, obtained by precomposition with inversion of the
multiplicative group. -/
def oppositeCocharacter (cochar : Cocharacter G) : Cocharacter G :=
  specGroupMap (groupAlgebraMap k
    (invMonoidHom (α := IntegerCharacters.{u}))) ≫ cochar

/-- The image of a unit under the given cocharacter. -/
def cocharacterPoint (cochar : Cocharacter G) (R : TestAlgebra k) (t : Rˣ) : GroupPoints G R :=
  ((groupPointsFunctor k).map cochar).app R (unitPoint R t)

abbrev polynomialAlgebra (R : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (Polynomial R)

abbrev laurentAlgebra (R : TestAlgebra k) : TestAlgebra k :=
  CommAlgCat.of k (LaurentPolynomial R)

def polynomialToLaurent (R : TestAlgebra k) : polynomialAlgebra R ⟶ laurentAlgebra R :=
  CommAlgCat.ofHom (Polynomial.toLaurentAlg.restrictScalars k)

def polynomialEvaluate (R : TestAlgebra k) (c : R) : polynomialAlgebra R ⟶ R :=
  CommAlgCat.ofHom (Polynomial.aevalTower (AlgHom.id k R) c)

def laurentConstants (R : TestAlgebra k) : R ⟶ laurentAlgebra R :=
  CommAlgCat.ofHom (IsScalarTower.toAlgHom k R (LaurentPolynomial R))

/-- The Laurent variable as a unit, with inverse the monomial of degree −1. -/
def laurentParameter (R : TestAlgebra k) : (laurentAlgebra R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num [LaurentPolynomial.T_zero]
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num [LaurentPolynomial.T_zero]

/-- The conjugation family over the punctured affine line over the test algebra. -/
def orbit (cochar : Cocharacter G) {R : TestAlgebra k} (g : GroupPoints G R) :
    GroupPoints G (laurentAlgebra R) :=
  let t := cocharacterPoint cochar (laurentAlgebra R) (laurentParameter R)
  t * (show GroupPoints G (laurentAlgebra R) from mapPoints (laurentConstants R) g) * t⁻¹

/-- A polynomial extension of the punctured-line family with prescribed value at zero. -/
def HasLimit (cochar : Cocharacter G) {R : TestAlgebra k} (g z : GroupPoints G R) : Prop :=
  ∃ f : GroupPoints G (polynomialAlgebra R),
    mapPoints (polynomialToLaurent R) f = orbit cochar g ∧
    mapPoints (polynomialEvaluate R 0) f = z

def HasExtension (cochar : Cocharacter G) {R : TestAlgebra k} (g : GroupPoints G R) : Prop :=
  ∃ z, HasLimit cochar g z

/-- A subgroup represents a functor on all commutative test algebras. -/
def RepresentsOnAlgebras (S : ClosedSubgroup G)
    (P : ∀ R : TestAlgebra k, GroupPoints G R → Prop) : Prop :=
  ∀ R g, P R g ↔ ∃ s : GroupPoints S.group R,
    ((groupPointsFunctor k).map S.inclusion).app R s = g

/-- Multiplication of the two displayed subgroup factors. -/
def multiplyFactors {L : GroupScheme k} (f : H ⟶ G) (g : L ⟶ G) : H.X ⊗ L.X ⟶ G.X :=
  (fst _ _ ≫ f.hom.hom) * (snd _ _ ≫ g.hom.hom)

/-- The closed subgroups and the split kernel sequence defined by the limit. -/
structure LimitDecomposition (cochar : Cocharacter G) where
  parabolic : ClosedSubgroup G
  contracting : ClosedSubgroup G
  centralizer : ClosedSubgroup G
  parabolic_points : RepresentsOnAlgebras parabolic (fun _ g ↦ HasExtension cochar g)
  contracting_points : RepresentsOnAlgebras contracting (fun _ g ↦ HasLimit cochar g 1)
  centralizer_points : RepresentsSubgroup centralizer (fun _ g ↦ Centralizes cochar g)
  contractingToParabolic : contracting.group ⟶ parabolic.group
  contracting_in_G : contractingToParabolic ≫ parabolic.inclusion = contracting.inclusion
  sectionMap : centralizer.group ⟶ parabolic.group
  section_in_G : sectionMap ≫ parabolic.inclusion = centralizer.inclusion
  limit : parabolic.group ⟶ centralizer.group
  limit_points : ∀ (R : TestAlgebra k) (p : GroupPoints parabolic.group R),
    HasLimit cochar
      (((groupPointsFunctor k).map parabolic.inclusion).app R p)
      (((groupPointsFunctor k).map (limit ≫ centralizer.inclusion)).app R p)
  section_limit : sectionMap ≫ limit = 𝟙 _
  isKernel : IsPullback contractingToParabolic.hom.hom
    (toUnit _) limit.hom.hom η[centralizer.group.X]
  product_iso : IsIso (multiplyFactors sectionMap contractingToParabolic)

/-- The actual multiplication map from the three subgroups in the big cell. -/
def bigCellMap {cochar : Cocharacter G} (D : LimitDecomposition cochar)
    (Dneg : LimitDecomposition (oppositeCocharacter cochar)) :
    Dneg.contracting.group.X ⊗ (D.centralizer.group.X ⊗ D.contracting.group.X) ⟶ G.X :=
  (fst _ _ ≫ Dneg.contracting.inclusion.hom.hom) *
    (snd _ _ ≫ multiplyFactors D.centralizer.inclusion D.contracting.inclusion)

end

end LinearAlgebraicGroups.CocharacterDynamics

namespace LinearAlgebraicGroups.Specs.CocharacterDynamics

open LinearAlgebraicGroups.CocharacterDynamics
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Cocharacter)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)

def LimitIsUnique : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} [IsAffine G.X.left]
    (cochar : Cocharacter G) {R : TestAlgebra k} {g z z' : GroupPoints G R}, HasLimit cochar g z → HasLimit cochar g z' → z = z'

def ParabolicSubgroupExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (cochar : Cocharacter G.val),
    ∃ P : ClosedSubgroup G.val, RepresentsOnAlgebras P (fun _ g ↦ HasExtension cochar g)

def CocharacterCentralizerExists : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (cochar : Cocharacter G.val),
    ∃ C : ClosedSubgroup G.val, RepresentsSubgroup C (fun _ g ↦ Centralizes cochar g)

def ExistsLimitDecomposition : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (cochar : Cocharacter G.val),
    Nonempty (LimitDecomposition cochar)

/-- The intersection with the opposite contracting subgroup is the identity scheme. -/
def OppositeLimitIntersection : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (cochar : Cocharacter G.val)
    (D : LimitDecomposition cochar) (E : LimitDecomposition (oppositeCocharacter cochar)),
    IsPullback (η[E.contracting.group.X]) (η[D.parabolic.group.X])
      E.contracting.inclusion.hom.hom D.parabolic.inclusion.hom.hom

/-- Scalar extension identifies the subgroup functors for the scalar-extended
cocharacter. Its source is identified with the new multiplicative group by the
isomorphism sending every unit point to the same unit under restriction of scalars. -/
def LimitSubgroupsBaseChange : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    (G : AffineAlgebraicGroup k) (cochar : Cocharacter G.val) (D : LimitDecomposition cochar),
    ∃ e : specGroup (groupAlgebra K IntegerCharacters) ≅
        (groupBaseChange k K).obj (specGroup (groupAlgebra k IntegerCharacters)),
      (∀ (R : TestAlgebra K) (s : Rˣ),
        baseChangePoint k K (specGroup (groupAlgebra k IntegerCharacters)).X R
          (unitPoint R s ≫ e.hom.hom.hom) = unitPoint ((restrictTestAlgebra k K).obj R) s) ∧
      let cocharK : Cocharacter ((groupBaseChange k K).obj G.val) :=
        e.hom ≫ (groupBaseChange k K).map cochar
      ∃ hp hu hz,
        RepresentsOnAlgebras (scalarExtendedSubgroup K D.parabolic hp)
          (fun _ g ↦ HasExtension cocharK g) ∧
        RepresentsOnAlgebras (scalarExtendedSubgroup K D.contracting hu)
          (fun _ g ↦ HasLimit cocharK g 1) ∧
        RepresentsSubgroup (scalarExtendedSubgroup K D.centralizer hz)
          (fun _ g ↦ Centralizes cocharK g) ∧
        ∀ (R : TestAlgebra K) (p : GroupPoints ((groupBaseChange k K).obj D.parabolic.group) R),
          HasLimit cocharK
            (((groupPointsFunctor K).map ((groupBaseChange k K).map D.parabolic.inclusion)).app R p)
            (((groupPointsFunctor K).map
              ((groupBaseChange k K).map (D.limit ≫ D.centralizer.inclusion))).app R p)

end LinearAlgebraicGroups.Specs.CocharacterDynamics
