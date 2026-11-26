import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.Algebras
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.AlternativeIdentities
import Mathlib.Algebra.Algebra.Bilinear

/-! Trace, conjugation and division for regular composition norms. -/

namespace LinearAlgebraicGroups.Composition.AdjointSpecification

open scoped TensorProduct
open Specification

set_option linter.checkUnivs false

universe u v w

section Definitions

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]

def traceType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → A →ₗ[R] R

/-- Scalar trace from the full polar form. -/
def trace (n : QuadraticForm R A) : A →ₗ[R] R := n.polarBilin.flip 1

def conjugateType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → A →ₗ[R] A

/-- Standard conjugation, defined without division by two. -/
def conjugate (n : QuadraticForm R A) : A →ₗ[R] A :=
  (trace n).smulRight 1 - LinearMap.id

/-- The inverse candidate for an element whose norm is the specified unit. -/
def inverseByNorm (n : QuadraticForm R A) (x : A) (a : Rˣ) : A :=
  ((a⁻¹ : Rˣ) : R) • conjugate n x

def inverseByNormType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → A → Rˣ → A

end Definitions

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]

/-- The norm laws shared by the field and ring cases of the adjoint argument. -/
structure NormLaws (n : QuadraticForm R A) : Prop where
  map_one : n 1 = 1
  map_mul : ∀ x y, n (x * y) = n x * n y
  nondegenerate : n.polarBilin.Nondegenerate

def normLawsType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → Prop

def normLaws := @NormLaws

def octonionNormLaws : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    OctonionNormConditions n → NormLaws n

def fieldNormLaws : Prop :=
  ∀ {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {q : QuadraticForm k C},
    FieldNormConditions q → NormLaws q

def traceOne : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A},
    NormLaws n → trace n 1 = 2

def traceScalar : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A},
    NormLaws n → ∀ r : R, trace n (r • (1 : A)) = 2 * r

def normScalar : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A},
    NormLaws n → ∀ r : R, n (r • (1 : A)) = r ^ 2

def traceConjugate : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A},
    NormLaws n → ∀ x, trace n (conjugate n x) = trace n x

def conjugateInvolutive : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A},
    NormLaws n → Function.Involutive (conjugate n)

def normConjugate : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A},
    NormLaws n → ∀ x, n (conjugate n x) = n x

def conjugateOne : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    {n : QuadraticForm R A},
    NormLaws n → conjugate n 1 = 1

def conjugateMul : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y, conjugate n (x * y) = conjugate n y * conjugate n x

def quadraticEquation : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x, x * x - trace n x • x + n x • (1 : A) = 0

def leftAdjoint : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x,
      LinearMap.IsAdjointPair n.polarBilin n.polarBilin
        (LinearMap.mul R A x) (LinearMap.mul R A (conjugate n x))

def rightAdjoint : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x,
      LinearMap.IsAdjointPair n.polarBilin n.polarBilin
        ((LinearMap.mul R A).flip x) ((LinearMap.mul R A).flip (conjugate n x))

def conjugateLeftProducts : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y,
      (conjugate n x * (x * y) = n x • y) ∧ (x * (conjugate n x * y) = n x • y)

def conjugateRightProducts : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y,
      ((y * x) * conjugate n x = n x • y) ∧ ((y * conjugate n x) * x = n x • y)

def mulConjugate : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x,
      x * conjugate n x = n x • (1 : A) ∧ conjugate n x * x = n x • (1 : A)

def polarMulConjugate : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y,
      x * conjugate n y + y * conjugate n x = n.polarBilin x y • (1 : A)

def traceMulFormula : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y,
      trace n (x * y) = trace n x * trace n y - n.polarBilin x y

def traceMulComm : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y, trace n (x * y) = trace n (y * x)

def traceMulConjugate : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y, trace n (x * conjugate n y) = n.polarBilin x y

def traceMulAsPolar : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y, trace n (x * y) = n.polarBilin x (conjugate n y)

def traceMulAssoc : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y z, trace n ((x * y) * z) = trace n (x * (y * z))

def traceMulCyclic : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x y z, trace n ((x * y) * z) = trace n ((y * z) * x)

def alternative : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → Specs.LinearAlgebraicGroups.Composition.AlternativeIdentities.isAlternative A

def inverse : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x (a : Rˣ), (a : R) = n x →
      x * inverseByNorm n x a = 1 ∧ inverseByNorm n x a * x = 1

def inverseOperators : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x (a : Rˣ), (a : R) = n x →
      let L := LinearMap.mul R A
      let P := (LinearMap.mul R A).flip
      let y := inverseByNorm n x a
      (L x).comp (L y) = LinearMap.id ∧ (L y).comp (L x) = LinearMap.id ∧
        (P x).comp (P y) = LinearMap.id ∧ (P y).comp (P x) = LinearMap.id

def inverseIffNormUnit : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A},
    NormLaws n → ∀ x,
      (∃ y, x * y = 1 ∧ y * x = 1) ↔ IsUnit (n x)

def fieldInverse : Prop :=
  ∀ {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {q : QuadraticForm k C},
    FieldNormConditions q → ∀ x, q x ≠ 0 →
    let y := (q x)⁻¹ • conjugate q x
    x * y = 1 ∧ y * x = 1 ∧
    Function.LeftInverse (fun z => y * z) (fun z => x * z) ∧
    Function.RightInverse (fun z => y * z) (fun z => x * z) ∧
    Function.LeftInverse (fun z => z * y) (fun z => z * x) ∧
    Function.RightInverse (fun z => z * y) (fun z => z * x)

def zeroNormNoInverse : Prop :=
  ∀ {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {q : QuadraticForm k C},
    FieldNormConditions q → ∀ x, q x = 0 → ∀ y, x * y ≠ 1 ∧ y * x ≠ 1

def divisionIffAnisotropic : Prop :=
  ∀ {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {q : QuadraticForm k C},
    FieldNormConditions q →
      ((∀ x : C, x ≠ 0 → Function.Bijective (fun y => x * y) ∧ Function.Bijective (fun y => y * x))
        ↔ ¬ isotropic q)

def fieldNormUnique : Prop :=
  ∀ {k : Type u} {C : Type v} [Field k] [NonAssocRing C] [Module k C]
    [IsScalarTower k C C] [SMulCommClass k C C] {q q' : QuadraticForm k C},
    FieldNormConditions q → FieldNormConditions q' → q = q' ∧ trace q = trace q'

def octonionNormUnique : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n n' : QuadraticForm R A},
    OctonionNormConditions n → OctonionNormConditions n' → n = n' ∧ trace n = trace n'

def octonionAutomorphismInvariance : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : OctonionNormConditions n) (S : Type w) [CommRing S] [Algebra R S],
    letI := h.projective
    let q := normBaseChange S n
    ∀ (f : (S ⊗[R] A) ≃ₗ[S] (S ⊗[R] A)),
      f 1 = 1 → (∀ x y, f (x * y) = f x * f y) →
        q.comp f.toLinearMap = q ∧ (trace q).comp f.toLinearMap = trace q ∧
          (conjugate q).comp f.toLinearMap = f.toLinearMap.comp (conjugate q)

/-- The diagonal, mixed, and linear coefficients in any coordinates on a test ring. -/
def octonionAutomorphismCoefficients : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] {n : QuadraticForm R A}
    (h : OctonionNormConditions n) (S : Type w) [CommRing S] [Algebra R S],
    letI := h.projective
    let q := normBaseChange S n
    ∀ (f : (S ⊗[R] A) ≃ₗ[S] (S ⊗[R] A)),
      f 1 = 1 → (∀ x y, f (x * y) = f x * f y) →
      ∀ x y, q (f x) = q x ∧ q.polarBilin (f x) (f y) = q.polarBilin x y ∧
        trace q (f x) = trace q x

def traceBaseChangeOnTensors : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [Module.Projective R A]
    (S : Type w) [CommRing S] [Algebra R S] (n : QuadraticForm R A) (s : S) (x : A),
    trace (normBaseChange S n) (s ⊗ₜ[R] x) = s * algebraMap R S (trace n x)

def conjugateBaseChange : Prop :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] [Module.Projective R A]
    (S : Type w) [CommRing S] [Algebra R S] (n : QuadraticForm R A),
    conjugate (normBaseChange S n) = (conjugate n).baseChange S

end LinearAlgebraicGroups.Composition.AdjointSpecification
