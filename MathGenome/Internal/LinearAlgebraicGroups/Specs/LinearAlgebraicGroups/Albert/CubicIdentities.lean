import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.HermitianCoordinates
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff

/-! The cubic norm and adjoint of a weighted Hermitian octonion algebra, in
the coordinates of NA13-C04.01. All polar forms are full polar forms. -/

namespace LinearAlgebraicGroups.Albert.CubicSpecification

open HermitianSpecification
open Composition.AdjointSpecification (trace conjugate NormLaws)
open Composition.Specification (OctonionNormConditions normBaseChange)
open scoped BigOperators TensorProduct

set_option linter.checkUnivs false

universe u v w z

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]

def blockWeight (γ : Fin 3 → Rˣ) (i : Fin 3) : R :=
  (γ (cyclicNext i) : R) * (γ (cyclicPrev i) : R)

def weightProduct (γ : Fin 3 → Rˣ) : R := (γ 0 : R) * (γ 1 : R) * (γ 2 : R)

def cubicUnit : Coordinates R A := (fun _ => 1, 0)

def cubicNorm (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (x : Coordinates R A) : R :=
  x.1 0 * x.1 1 * x.1 2 - (∑ i, blockWeight γ i * x.1 i * n (x.2 i)) +
    weightProduct γ * trace n ((x.2 0 * x.2 1) * x.2 2)

def cubicAdjoint (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (x : Coordinates R A) :
    Coordinates R A :=
  (fun i => x.1 (cyclicNext i) * x.1 (cyclicPrev i) - blockWeight γ i * n (x.2 i),
   fun i => -(x.1 i) • x.2 i +
     (γ i : R) • conjugate n (x.2 (cyclicNext i) * x.2 (cyclicPrev i)))

def tracePairing (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) :
    LinearMap.BilinForm R (Coordinates R A) where
  toFun x :=
    { toFun := fun y => ∑ i, (x.1 i * y.1 i + blockWeight γ i * n.polarBilin (x.2 i) (y.2 i))
      map_add' := by
        intro y z
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add, mul_add]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ac_rfl
      map_smul' := by
        intro r y
        simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, map_smul,
          smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, LinearMap.map_add₂, add_mul, mul_add, ← Finset.sum_add_distrib,
      LinearMap.add_apply]
    apply Finset.sum_congr rfl
    intro i _
    ac_rfl
  map_smul' := by
    intro r x
    apply LinearMap.ext
    intro y
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Prod.smul_fst, Prod.smul_snd,
      Pi.smul_apply, LinearMap.map_smul₂, LinearMap.smul_apply, smul_eq_mul,
      RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def linearTrace (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) :
    Coordinates R A →ₗ[R] R := (tracePairing n γ).flip cubicUnit

def quadraticTrace (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (x : Coordinates R A) : R :=
  linearTrace n γ (cubicAdjoint n γ x)

def adjointCross (n : QuadraticForm R A) (γ : Fin 3 → Rˣ) (x y : Coordinates R A) :
    Coordinates R A :=
  cubicAdjoint n γ (x + y) - cubicAdjoint n γ x - cubicAdjoint n γ y

/-- The scalar coordinate axes and single octonion blocks. -/
def diagonalCoordinates (a : Fin 3 → R) : Coordinates R A := (a, 0)

def singleBlockCoordinates (i : Fin 3) (c : A) : Coordinates R A := (0, Pi.single i c)

def cubicUnitType := ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A], Coordinates R A
def blockWeightType := ∀ {R : Type u} [CommRing R], (Fin 3 → Rˣ) → Fin 3 → R
def weightProductType := ∀ {R : Type u} [CommRing R], (Fin 3 → Rˣ) → R
def cubicNormType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Coordinates R A → R
def cubicAdjointType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Coordinates R A → Coordinates R A
def tracePairingType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → LinearMap.BilinForm R (Coordinates R A)
def linearTraceType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Coordinates R A →ₗ[R] R
def quadraticTraceType := cubicNormType
def adjointCrossType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Coordinates R A → Coordinates R A → Coordinates R A
def diagonalCoordinatesType :=
  ∀ {R : Type u} {A : Type v}, [NonAssocRing A] → (Fin 3 → R) → Coordinates R A
def singleBlockCoordinatesType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A], Fin 3 → A → Coordinates R A

variable (n : QuadraticForm R A) (γ : Fin 3 → Rˣ)

def unitIdentities : Prop :=
  cubicNorm n γ (cubicUnit (R := R) (A := A)) = 1 ∧
    cubicAdjoint n γ cubicUnit = cubicUnit ∧
    ∀ x, adjointCross n γ cubicUnit x = linearTrace n γ x • cubicUnit - x

def traceFormulas : Prop :=
  ∀ x : Coordinates R A, linearTrace n γ x = ∑ i, x.1 i

def quadraticTracePolar : Prop :=
  ∀ x y, quadraticTrace n γ (x + y) - quadraticTrace n γ x - quadraticTrace n γ y =
    linearTrace n γ x * linearTrace n γ y - tracePairing n γ x y

def diagonalFormulas : Prop :=
  ∀ a : Fin 3 → R,
    cubicNorm n γ (diagonalCoordinates a) = a 0 * a 1 * a 2 ∧
    cubicAdjoint n γ (diagonalCoordinates a) =
      diagonalCoordinates (fun i => a (cyclicNext i) * a (cyclicPrev i))

def singleBlockFormulas : Prop :=
  ∀ i c, cubicNorm n γ (singleBlockCoordinates i c) = 0 ∧
    cubicAdjoint n γ (singleBlockCoordinates i c) =
      diagonalCoordinates (Pi.single i (-(blockWeight γ i * n c))) ∧
    cubicAdjoint n γ (cubicAdjoint n γ (singleBlockCoordinates i c)) = 0

def tracePerfect : Prop :=
  n.polarBilin.IsPerfPair → (tracePairing n γ).IsPerfPair

def adjointLine : Prop :=
  ∀ (x y : Coordinates R A) (s : R),
    cubicAdjoint n γ (x + s • y) =
      cubicAdjoint n γ x + s • adjointCross n γ x y + (s * s) • cubicAdjoint n γ y

def coordinateMatrixFormulas : Prop :=
  assemble n γ (cubicUnit (R := R) (A := A)) = 1 ∧
    (∀ a : Fin 3 → R, assemble n γ (diagonalCoordinates a) = Matrix.diagonal (fun i => a i • (1 : A))) ∧
    ∀ i c, assemble n γ (singleBlockCoordinates i c) = block n γ i c

def adjointQuadratic : Prop :=
  ∃ q : QuadraticMap R (Coordinates R A) (Coordinates R A),
    (∀ x, q x = cubicAdjoint n γ x) ∧
    ∀ x y, q.polarBilin x y = adjointCross n γ x y

variable [IsScalarTower R A A] [SMulCommClass R A A]

def adjointIdentity : Prop :=
  OctonionNormConditions n →
  ∀ x, cubicAdjoint n γ (cubicAdjoint n γ x) = cubicNorm n γ x • x

def normLine : Prop :=
  NormLaws n → ∀ (x y : Coordinates R A) (s : R),
    cubicNorm n γ (x + s • y) = cubicNorm n γ x +
      s * tracePairing n γ (cubicAdjoint n γ x) y +
      s ^ 2 * tracePairing n γ (cubicAdjoint n γ y) x + s ^ 3 * cubicNorm n γ y

def normHomogeneous : Prop :=
  ∀ (r : R) (x : Coordinates R A), cubicNorm n γ (r • x) = r ^ 3 * cubicNorm n γ x

section Extension

variable (B : Type w) [CommRing B] [Algebra R B]

/-- The image of a vector on extension of scalars. -/
noncomputable def extendCoordinates (x : Coordinates R A) : Coordinates B (B ⊗[R] A) :=
  coordinatesBaseChange B (1 ⊗ₜ[R] x)

def extendCoordinatesType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (B : Type w) [CommRing B] [Algebra R B], Coordinates R A → Coordinates B (B ⊗[R] A)

def cubicBaseChange : Prop :=
  ∀ h : OctonionNormConditions n,
    letI := h.projective
    let q := normBaseChange B n
    let δ := baseChangedWeights B γ
    let e := extendCoordinates (R := R) (A := A) B
    e cubicUnit = cubicUnit ∧
      (∀ x, cubicNorm q δ (e x) = algebraMap R B (cubicNorm n γ x)) ∧
      (∀ x, cubicAdjoint q δ (e x) = e (cubicAdjoint n γ x)) ∧
      (∀ x y, tracePairing q δ (e x) (e y) = algebraMap R B (tracePairing n γ x y))

variable {D : Type z} [CommRing D] [Algebra R D]

/-- The coordinate map between two scalar extensions along an algebra map. -/
def mapExtendedCoordinates (f : B →ₐ[R] D) (x : Coordinates B (B ⊗[R] A)) :
    Coordinates D (D ⊗[R] A) :=
  (fun i => f (x.1 i), fun i => f.toLinearMap.rTensor A (x.2 i))

def mapExtendedCoordinatesType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (B : Type w) [CommRing B] [Algebra R B] {D : Type z} [CommRing D] [Algebra R D],
    (B →ₐ[R] D) → Coordinates B (B ⊗[R] A) → Coordinates D (D ⊗[R] A)

def coordinatesExtensionNaturality : Prop :=
  ∀ (f : B →ₐ[R] D) (x : B ⊗[R] Coordinates R A),
    mapExtendedCoordinates B f (coordinatesBaseChange B x) =
      coordinatesBaseChange D (f.toLinearMap.rTensor (Coordinates R A) x)

/-- Naturality on arbitrary points of scalar extensions, expressed using
the tensor-coordinate equivalence. -/
def cubicExtensionNaturality : Prop :=
  ∀ h : OctonionNormConditions n,
    letI := h.projective
    let qB := normBaseChange B n
    let qD := normBaseChange D n
    let γB := baseChangedWeights B γ
    let γD := baseChangedWeights D γ
    ∀ (f : B →ₐ[R] D) (x y : Coordinates B (B ⊗[R] A)),
      let e := mapExtendedCoordinates B (A := A) f
      cubicNorm qD γD (e x) = f (cubicNorm qB γB x) ∧
        cubicAdjoint qD γD (e x) = e (cubicAdjoint qB γB x) ∧
        tracePairing qD γD (e x) (e y) = f (tracePairing qB γB x y)

end Extension

variable [Module.Projective R A]

/-- The actual norm polynomial on the line (x+Xy), computed on the scalar
extension to the polynomial ring. -/
noncomputable def cubicLinePolynomial (x y : Coordinates R A) : Polynomial R :=
  cubicNorm (normBaseChange (Polynomial R) n) (baseChangedWeights (Polynomial R) γ)
    (extendCoordinates (Polynomial R) x + (Polynomial.X : Polynomial R) • extendCoordinates (Polynomial R) y)

def linePolynomialType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (_ : QuadraticForm R A) (_ : Fin 3 → Rˣ)
    [IsScalarTower R A A] [SMulCommClass R A A] [Module.Projective R A], Coordinates R A → Coordinates R A → Polynomial R

/-- The coefficient of (X) in (N(x+Xy)). -/
noncomputable def normDerivative (x y : Coordinates R A) : R :=
  (cubicLinePolynomial n γ x y).coeff 1

/-- The mixed coefficient of (X Y) in (N(1+Xx+Yy)).
Take the coefficient of (Y) over the coefficient ring (R[X]), then
take its coefficient of (X) over (R). -/
noncomputable def normMixedCoefficient (x y : Coordinates R A) : R :=
  let q := normBaseChange (Polynomial R) n
  let δ := baseChangedWeights (Polynomial R) γ
  let x' := extendCoordinates (Polynomial R) x
  let y' := extendCoordinates (Polynomial R) y
  (normDerivative q δ (cubicUnit + (Polynomial.X : Polynomial R) • x') y').coeff 1

def coefficientType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (_ : QuadraticForm R A) (_ : Fin 3 → Rˣ)
    [IsScalarTower R A A] [SMulCommClass R A A] [Module.Projective R A], Coordinates R A → Coordinates R A → R

omit [Module.Projective R A] in
def normDerivativeFormula : Prop :=
  ∀ h : OctonionNormConditions n, letI := h.projective
    ∀ x y, normDerivative n γ x y = tracePairing n γ (cubicAdjoint n γ x) y

omit [Module.Projective R A] in
def traceCoefficientFormula : Prop :=
  ∀ h : OctonionNormConditions n, letI := h.projective
    (∀ x, normDerivative n γ cubicUnit x = linearTrace n γ x) ∧
    (∀ x y, tracePairing n γ x y =
      normDerivative n γ cubicUnit x * normDerivative n γ cubicUnit y -
        normMixedCoefficient n γ x y)

omit [Module.Projective R A] in
def scalarExtensionIdentities (B : Type w) [CommRing B] [Algebra R B] : Prop :=
  ∀ h : OctonionNormConditions n,
    letI := h.projective
    let q := normBaseChange B n
    let δ := baseChangedWeights B γ
    unitIdentities q δ ∧ (tracePairing q δ).IsPerfPair ∧
      (∀ x, cubicAdjoint q δ (cubicAdjoint q δ x) = cubicNorm q δ x • x) ∧
      (∀ x y, normDerivative q δ x y = tracePairing q δ (cubicAdjoint q δ x) y) ∧
      (∀ x y, tracePairing q δ x y =
        normDerivative q δ cubicUnit x * normDerivative q δ cubicUnit y -
          normMixedCoefficient q δ x y)

def scalarExtensionIdentitiesType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A]
    (B : Type w) [CommRing B] [Algebra R B], scalarExtensionIdentities n γ B

def normHomogeneousType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A],
    normHomogeneous n γ

def traceFormulasType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ), traceFormulas n γ

def tracePerfectType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ), tracePerfect n γ

def unitIdentitiesType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ), unitIdentities n γ

def quadraticTracePolarType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ), quadraticTracePolar n γ

def diagonalFormulasType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ), diagonalFormulas n γ

def singleBlockFormulasType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ), singleBlockFormulas n γ

def adjointLineType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A], adjointLine n γ

def normLineType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A], normLine n γ

def adjointIdentityType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A], adjointIdentity n γ

def normDerivativeFormulaType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A], normDerivativeFormula n γ

def traceCoefficientFormulaType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A], traceCoefficientFormula n γ

def cubicBaseChangeType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A]
    (B : Type w) [CommRing B] [Algebra R B],
    cubicBaseChange n γ B

def coordinatesExtensionNaturalityType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    (B : Type w) [CommRing B] [Algebra R B] {D : Type z} [CommRing D] [Algebra R D],
    coordinatesExtensionNaturality (R := R) (A := A) B (D := D)

def cubicExtensionNaturalityType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A]
    (B : Type w) [CommRing B] [Algebra R B]
    {D : Type z} [CommRing D] [Algebra R D],
    cubicExtensionNaturality n γ B (D := D)

def coordinateMatrixFormulasType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ), coordinateMatrixFormulas n γ

def adjointQuadraticType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) [IsScalarTower R A A] [SMulCommClass R A A],
    adjointQuadratic n γ

end LinearAlgebraicGroups.Albert.CubicSpecification
