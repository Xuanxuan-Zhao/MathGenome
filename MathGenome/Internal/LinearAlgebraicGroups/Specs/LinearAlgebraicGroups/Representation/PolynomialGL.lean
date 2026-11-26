import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.GeneralLinearStructure
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.PrimitiveLine
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Order.Hom.PowersetCard

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.PolynomialGL

noncomputable section

open StandardGroups
open Unipotent (Index)
open GeneralLinearStructure (MatrixPoints)
open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CocharacterDynamics (cocharacterPoint)

variable {k m I : Type u} [Field k] [Fintype m] [DecidableEq m]
  [Fintype I] [DecidableEq I]

/-- Rational representations of the represented matrix group in a finite basis. -/
abbrev MatrixRepresentation (k m I : Type u) [Field k] [Fintype m] [DecidableEq m]
    [Fintype I] [DecidableEq I] :=
  generalLinearPoints k m ⟶ generalLinearPoints k I

/-- The group homomorphism at a test algebra, expressed in matrix coordinates. -/
def representationAt (ρ : MatrixRepresentation k m I) (R : TestAlgebra k) :
    Matrix.GeneralLinearGroup m R →* Matrix.GeneralLinearGroup I R :=
  (ρ.app R).hom

/-- Evaluation of a universal matrix coefficient on an arbitrary matrix. -/
def evaluateMatrix {R : Type u} [CommRing R] [Algebra k R]
    (M : Matrix m m R) : MvPolynomial (m × m) k →ₐ[k] R :=
  MvPolynomial.aeval (fun ij => M ij.1 ij.2)

/-- Evaluation of a coefficient matrix on the whole affine matrix space. -/
def evaluateCoefficients {R : Type u} [CommRing R] [Algebra k R]
    (P : Matrix I I (MvPolynomial (m × m) k)) (M : Matrix m m R) : Matrix I I R :=
  (evaluateMatrix M).mapMatrix P

/-- The coefficient identity holds over every commutative test algebra. -/
def EvaluatesTo (ρ : MatrixRepresentation k m I)
    (P : Matrix I I (MvPolynomial (m × m) k)) : Prop :=
  ∀ (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup m R),
    (representationAt ρ R g).val = evaluateCoefficients P g.val

def IsPolynomial (ρ : MatrixRepresentation k m I) : Prop :=
  ∃ P, EvaluatesTo ρ P

/-- The underlying morphism of affine schemes is specified by its polynomials. -/
def IsMatrixMonoidExtension (ρ : MatrixRepresentation k m I)
    (P : Matrix I I (MvPolynomial (m × m) k)) : Prop :=
  EvaluatesTo ρ P ∧
    ∀ R : TestAlgebra k,
      evaluateCoefficients P (1 : Matrix m m R) = 1 ∧
      ∀ X Y : Matrix m m R,
        evaluateCoefficients P (X * Y) = evaluateCoefficients P X * evaluateCoefficients P Y

/-- Twisting by the determinant character to an integral power. -/
def determinantTwist (ρ : MatrixRepresentation k m I) (a : ℤ) :
    MatrixRepresentation k m I where
  app R := GrpCat.ofHom
    (show Matrix.GeneralLinearGroup m R →* Matrix.GeneralLinearGroup I R from
      { toFun := fun g =>
          Matrix.GeneralLinearGroup.scalar I (Matrix.GeneralLinearGroup.det g ^ a) *
            representationAt ρ R g
        map_one' := by
          change _ * representationAt ρ R (1 : Matrix.GeneralLinearGroup m R) = 1
          simp [map_one]
        map_mul' := by
          intro g h
          change _ * representationAt ρ R (g * h) = _
          rw [show representationAt ρ R (g * h) =
            representationAt ρ R g *
              representationAt ρ R h from (representationAt ρ R).map_mul g h]
          simp only [map_mul, mul_zpow]
          exact (show Commute _ _ from
            Matrix.GeneralLinearGroup.scalar_commute _ _).mul_mul_mul_comm _ _ })
  naturality R S f := GrpCat.ext fun g => by
    change Matrix.GeneralLinearGroup m R at g
    symm
    change Matrix.GeneralLinearGroup.map f.hom.toRingHom
        (Matrix.GeneralLinearGroup.scalar I (Matrix.GeneralLinearGroup.det g ^ a) *
          representationAt ρ R g) =
      Matrix.GeneralLinearGroup.scalar I
        (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map f.hom.toRingHom g) ^ a) *
          representationAt ρ S ((generalLinearPoints k m).map f g)
    rw [map_mul, Matrix.GeneralLinearGroup.map_scalar, map_zpow,
      Matrix.GeneralLinearGroup.map_det]
    congr 1
    exact (ConcreteCategory.congr_hom (ρ.naturality f) g).symm

/-- A diagonal point of the standard torus in GL. -/
def diagonalPoint {R : Type u} [CommRing R] (t : m → Rˣ) :
    Matrix.GeneralLinearGroup m R :=
  Units.map (Matrix.diagonalRingHom m R).toMonoidHom (MulEquiv.piUnits.symm t)

/-- Evaluation of the character with the given exponent vector. -/
def weightValue {R : Type u} [CommRing R] (lam : m → ℤ) (t : m → Rˣ) : Rˣ :=
  ∏ i, t i ^ lam i

/-- A vector of a specified diagonal-torus weight. -/
def HasWeight (ρ : MatrixRepresentation k m I) (lam : m → ℤ) (v : I → k) : Prop :=
  ∀ (R : TestAlgebra k) (t : m → Rˣ),
    (representationAt ρ R (diagonalPoint t)).val.mulVec
      (RootWeightAction.extendVector R v) = (weightValue lam t : R) •
      RootWeightAction.extendVector R v

/-- The upper triangular Borel radical is the group of upper unitriangular matrices. -/
def IsPrimitive {n : ℕ} (ρ : MatrixRepresentation k (Index.{u} n) I)
    (lam : Index.{u} n → ℤ) (v : I → k) : Prop :=
  v ≠ 0 ∧ HasWeight ρ lam v ∧
    ∀ (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup (Index.{u} n) R),
      g.val.IsUpperTriangular → (∀ i, g.val i i = 1) →
      (representationAt ρ R g).val.mulVec
        (RootWeightAction.extendVector R v) = RootWeightAction.extendVector R v

/-- The standard two-coordinate diagonal of the determinant-one block. -/
def corootPoint {R : Type u} [CommRing R] (i j : m) (t : Rˣ) : m → Rˣ :=
  fun l => if l = i then t else if l = j then t⁻¹ else 1

/-- The diagonal in a determinant-one block and its evaluation on torus characters. -/
def CorootEvaluation : Prop :=
  ∀ (m R : Type u) [Fintype m] [DecidableEq m] [CommRing R]
    (i j : m) (_hij : i ≠ j) (z : Rˣ),
    (diagonalPoint (corootPoint i j z)).det = 1 ∧
    ∀ lam : m → ℤ, weightValue lam (corootPoint i j z) = z ^ (lam i - lam j)


/-- The determinant-one diagonal is the normalized rank-one transvection word. -/
def MatrixCorootWord : Prop :=
  ∀ (m R : Type u) [Fintype m] [DecidableEq m] [CommRing R]
    (i j : m) (hij : i ≠ j) (z : Rˣ),
    let w (a : Rˣ) :=
      Matrix.GeneralLinearGroup.transvection i j hij a.val *
        Matrix.GeneralLinearGroup.transvection j i hij.symm (-(a⁻¹).val) *
        Matrix.GeneralLinearGroup.transvection i j hij a.val
    w z * (w 1)⁻¹ = diagonalPoint (corootPoint i j z)

/-- Dominance for the adjacent two-coordinate coroots is the weakly decreasing order. -/
def AdjacentDominance : Prop :=
  ∀ (n : ℕ) (lam : Index.{u} (n + 1) → ℤ),
    (∀ i : Fin n, 0 ≤ lam ⟨i.castSucc⟩ - lam ⟨i.succ⟩) ↔ Antitone lam

/-- Multiplication by the polynomial coefficients is inherited by a submodule or quotient
in any finite basis. The constant matrices represent the inclusion or quotient and a
vector-space splitting of that map. -/
def PolynomialSubquotients : Prop :=
  ∀ (k m I J : Type u) [Field k] [Fintype m] [DecidableEq m]
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (ρ : MatrixRepresentation k m I) (σ : MatrixRepresentation k m J)
    (p : Matrix J I k) (s : Matrix I J k), p * s = 1 →
    ((∀ (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup m R),
        (representationAt ρ R g).val * s.map (algebraMap k R) =
          s.map (algebraMap k R) * (representationAt σ R g).val) ∨
      (∀ (R : TestAlgebra k) (g : Matrix.GeneralLinearGroup m R),
        p.map (algebraMap k R) * (representationAt ρ R g).val =
          (representationAt σ R g).val * p.map (algebraMap k R))) →
    IsPolynomial ρ → IsPolynomial σ

/-- Matrix coordinates compatible with the inclusion of the diagonal torus. -/
abbrev DiagonalCoordinates {n : ℕ} {G : AffineAlgebraicGroup k}
    (e : MatrixPoints G n) (T : ClosedSubgroup G.val)
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)) : Prop :=
  ∀ (R : TestAlgebra k) (x : GroupPoints T.group R),
    e.hom.app R (x ≫ T.inclusion.hom.hom) = diagonalPoint (t.hom.app R x)

/-- The Borel represented by the upper triangular invertible matrices. -/
abbrev UpperTriangularCoordinates {n : ℕ} {G : AffineAlgebraicGroup k}
    (e : MatrixPoints G n) (B : ClosedSubgroup G.val) : Prop :=
  ∀ (R : TestAlgebra k) (g : Points G.val.X R),
    g ∈ SubgroupSections B ((testSpec k).obj (Opposite.op R)) ↔
      (e.hom.app R g).val.IsUpperTriangular

/-- The evaluation of a character in the coordinate lattice over every test algebra. -/
abbrev CharacterEvaluation {n : ℕ} {G : AffineAlgebraicGroup k} {T : ClosedSubgroup G.val}
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n))
    (c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)) : Prop :=
  ∀ (lam : Index.{u} n → ℤ) (R : TestAlgebra k) (x : GroupPoints T.group R),
    CharacterPairing.characterValue (Additive.toMul (c lam)) R x =
      (weightValue lam (t.hom.app R x)).val

/-- The exponent of the ratio of two diagonal coordinates. -/
def rootExponent {n : ℕ} (i j : Index.{u} n) : Index.{u} n → ℤ :=
  Pi.single i 1 - Pi.single j 1

/-- All characters of the diagonal torus are uniquely given by exponent vectors. -/
def CharacterCoordinates : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (G : AffineAlgebraicGroup k) (T : ClosedSubgroup G.val)
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)),
    ∃ c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group), CharacterEvaluation t c

/-- The simple coroots of the standard Borel are the cocharacters of the
adjacent determinant-one blocks. -/
def StandardSimpleCoroots : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (G : AffineAlgebraicGroup k)
    (e : MatrixPoints G n) (T B : ClosedSubgroup G.val)
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)),
    DiagonalCoordinates e T t → UpperTriangularCoordinates e B →
    ∀ (c : (Index.{u} n → ℤ) ≃+ Additive (Character T.group)), CharacterEvaluation t c →
    ∀ [IsCommMonObj T.group.X] (D : AbstractPairing.Datum T),
      (∀ a : RootWeightAction.SimpleRoot T B,
        ∃ i j : Index.{u} n, i.down.val + 1 = j.down.val ∧
          a.val.val = Additive.toMul (c (rootExponent i j)) ∧
          (∀ lam, D.rootDatum.toLinearMap (c lam) (D.rootDatum.coroot a.val) = lam i - lam j) ∧
          ∀ (R : TestAlgebra k) (z : Rˣ),
            e.hom.app R
              (cocharacterPoint (Additive.toMul (D.rootDatum.coroot a.val)) R z ≫
                T.inclusion.hom.hom) = diagonalPoint (corootPoint i j z)) ∧
      ∀ i j : Index.{u} n, i.down.val + 1 = j.down.val →
        ∃ a : RootWeightAction.SimpleRoot T B, a.val.val = Additive.toMul (c (rootExponent i j))

def Dominance : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (_ : 0 < n) (G : AffineAlgebraicGroup k)
    (e : MatrixPoints G n) (T B : ClosedSubgroup G.val)
    (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} n)),
    DiagonalCoordinates e T t → UpperTriangularCoordinates e B →
    ∀ [IsCommMonObj T.group.X] (D : AbstractPairing.Datum T)
      (χ : Character T.group) (lam : Index.{u} n → ℤ),
      (∀ (R : TestAlgebra k) (x : GroupPoints T.group R),
        CharacterPairing.characterValue χ R x = (weightValue lam (t.hom.app R x) : R)) →
      (RootWeightAction.IsDominant D B χ ↔ Antitone lam)

def CommonDenominator : Prop :=
  ∀ (k m I : Type u) [Field k] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
    (ρ : MatrixRepresentation k m I),
    ∃ a : ℕ, IsPolynomial (determinantTwist ρ (a : ℤ))

def MonoidExtension : Prop :=
  ∀ (k m I : Type u) [Field k] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
    (ρ : MatrixRepresentation k m I),
    IsPolynomial ρ ↔ ∃! P, IsMatrixMonoidExtension ρ P

def ShiftWeights : Prop :=
  ∀ (k m I : Type u) [Field k] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
    (ρ : MatrixRepresentation k m I) (a : ℤ) (lam : m → ℤ) (v : I → k),
    HasWeight (determinantTwist ρ a) (fun i => lam i + a) v ↔ HasWeight ρ lam v

def NonnegativeWeights : Prop :=
  ∀ (k m I : Type u) [Field k] [Fintype m] [DecidableEq m] [Fintype I] [DecidableEq I]
    (ρ : MatrixRepresentation k m I), IsPolynomial ρ →
    ∀ (lam : m → ℤ) (v : I → k), v ≠ 0 → HasWeight ρ lam v → ∀ i, 0 ≤ lam i

/-- The compound matrix in the increasing-wedge basis. -/
def minorMatrix {m R : Type u} [LinearOrder m] [CommRing R] (q : ℕ)
    (X : Matrix m m R) : Matrix (Set.powersetCard m q) (Set.powersetCard m q) R :=
  fun s t => (X.submatrix (Set.powersetCard.ofFinEmbEquiv.symm s)
    (Set.powersetCard.ofFinEmbEquiv.symm t)).det

/-- The exterior power has polynomial coefficients given by its minors. -/
def ExteriorCoefficients : Prop :=
  ∀ (k m : Type u) [Field k] [Fintype m] [LinearOrder m] [DecidableEq m] (q : ℕ),
    ∃ ρ : MatrixRepresentation k m (Set.powersetCard m q),
      EvaluatesTo ρ (minorMatrix q (genericMatrix k m))

/-- The first (q) matrix indices, in increasing order. -/
def initialEmbedding {q n : ℕ} (h : q ≤ n) : Fin q ↪o Index.{u} n where
  toFun i := ⟨Fin.castLE h i⟩
  inj' := by
    intro i j e
    have hval := congrArg (fun x : Index.{u} n => x.down.val) e
    exact Fin.ext hval
  map_rel_iff' := Iff.rfl

/-- The wedge of the first (q) basis vectors is primitive. -/
def ExteriorPrimitive : Prop :=
  ∀ (k : Type u) [Field k] (n q : ℕ) (h : q ≤ n),
    ∃ ρ : MatrixRepresentation k (Index.{u} n) (Set.powersetCard (Index.{u} n) q),
      EvaluatesTo ρ (minorMatrix q (genericMatrix k (Index.{u} n))) ∧
      IsPrimitive ρ (fun i => if i.down.val < q then 1 else 0)
        (Pi.single (Set.powersetCard.ofFinEmbEquiv (initialEmbedding h)) 1)

/-- Every dominant weight with nonnegative last coordinate has a polynomial primitive model. -/
def PolynomialPrimitiveExistence : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (lam : Index.{u} (n + 1) → ℤ),
    Antitone lam → 0 ≤ lam ⟨Fin.last n⟩ →
    ∃ (J : Type u) (hJ : Fintype J) (dJ : DecidableEq J),
      letI := hJ
      letI := dJ
      ∃ (σ : MatrixRepresentation k (Index.{u} (n + 1)) J) (w : J → k),
        IsPolynomial σ ∧ IsPrimitive σ lam w

/-- Polynomiality implies the last-coordinate bound on a primitive weight. -/
def SimpleCriterionNecessary : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (n : ℕ)
    (ρ : MatrixRepresentation k (Index.{u} (n + 1)) I)
    (lam : Index.{u} (n + 1) → ℤ) (v : I → k),
    IsPolynomial ρ → IsPrimitive ρ lam v → 0 ≤ lam ⟨Fin.last n⟩

/-- The polynomial criterion for scheme-theoretic highest weights of the
standard Borel pair. -/
def SimpleHighestWeightCriterion : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (G : AffineAlgebraicGroup k) (e : MatrixPoints G (n + 1)),
    ∃ (T B : ClosedSubgroup G.val)
      (t : (groupPointsFunctor k).obj T.group ≅ multiplicativePowerPoints k (Index.{u} (n + 1)))
      (c : (Index.{u} (n + 1) → ℤ) ≃+ Additive (Character T.group))
      (U : ClosedSubgroup B.group),
      DiagonalCoordinates e T t ∧ UpperTriangularCoordinates e B ∧ CharacterEvaluation t c ∧
      IsSplitTorus T.group ∧ IsGeometricallyMaximal T ∧ IsKBorel B ∧ IsSubgroupOf T B ∧
      IsUnipotentRadical (closedSubgroupAlgebraicGroup B) U ∧
      ∀ (I : Type u) [Fintype I] [DecidableEq I]
        (ρ : MatrixRepresentation k (Index.{u} (n + 1)) I),
        PrimitiveLine.IsSimple (G := G) (e.hom ≫ ρ) →
        ∀ (lam : Index.{u} (n + 1) → ℤ) (v : I → k),
          RootWeightAction.IsPrimitive (e.hom ≫ ρ) T B U (Additive.toMul (c lam)) v →
          (IsPolynomial ρ ↔ 0 ≤ lam ⟨Fin.last n⟩)

/-- The highest-weight criterion for every presentation of the rational simple module. -/
def SimpleCriterion : Prop :=
  ∀ (k I : Type u) [Field k] [Fintype I] [DecidableEq I] (n : ℕ)
    (G : AffineAlgebraicGroup k) (e : MatrixPoints G (n + 1))
    (ρ : MatrixRepresentation k (Index.{u} (n + 1)) I),
    PrimitiveLine.IsSimple (G := G) (e.hom ≫ ρ) →
    ∀ (lam : Index.{u} (n + 1) → ℤ) (v : I → k),
      IsPrimitive ρ lam v → (IsPolynomial ρ ↔ 0 ≤ lam ⟨Fin.last n⟩)

end

end LinearAlgebraicGroups.Specs.PolynomialGL
