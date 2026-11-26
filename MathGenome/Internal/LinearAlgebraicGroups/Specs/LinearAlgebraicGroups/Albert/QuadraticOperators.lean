import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.CubicIdentities
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan

/-! The quadratic operator identities and matrix comparison in NA13-C04.02. -/

namespace LinearAlgebraicGroups.Albert.QuadraticOperatorSpecification

open HermitianSpecification CubicSpecification
open Composition.Specification (OctonionNormConditions normBaseChange)
open scoped TensorProduct

universe u v w z

set_option linter.checkUnivs false

variable {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
variable (n : QuadraticForm R A) (γ : Fin 3 → Rˣ)

def applyOperator (x y : Coordinates R A) : Coordinates R A :=
  tracePairing n γ x y • x - adjointCross n γ (cubicAdjoint n γ x) y

def applyOperatorType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A],
    QuadraticForm R A → (Fin 3 → Rˣ) → Coordinates R A → Coordinates R A → Coordinates R A

def triple (x y z : Coordinates R A) : Coordinates R A :=
  applyOperator n γ (x + z) y - applyOperator n γ x y - applyOperator n γ z y

def operatorIdentities : Prop :=
  let U := applyOperator n γ
  let P := adjointCross n γ
  let adj := cubicAdjoint n γ
  let N := cubicNorm n γ
  let T := tracePairing n γ
  let t := linearTrace n γ
  let S := quadraticTrace n γ
  (∀ y, U cubicUnit y = y) ∧
  (∀ x y z, triple n γ x y z = T x y • z + T z y • x - P (P x z) y) ∧
  (∀ x y z, T (U x y) z = T y (U x z)) ∧
  (∀ x y, adj (U x y) = U (adj x) (adj y)) ∧
  (∀ x, U x (adj x) = N x • x) ∧
  (∀ x y, U x (U (adj x) y) = N x ^ 2 • y ∧ U (adj x) (U x y) = N x ^ 2 • y) ∧
  (∀ x y z, U (U x y) z = U x (U y (U x z))) ∧
  (∀ x y z, U x (triple n γ y x z) = triple n γ (U x y) z x) ∧
  (∀ x, U x cubicUnit = adj x + t x • x - S x • cubicUnit) ∧
  (∀ x y, t (U x y) = T y (U x cubicUnit))

variable [IsScalarTower R A A] [SMulCommClass R A A]

def identitiesType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ),
    OctonionNormConditions n → operatorIdentities n γ

def matrixSquareType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ),
    OctonionNormConditions n → ∀ x : Coordinates R A,
      assemble n γ (applyOperator n γ x cubicUnit) = assemble n γ x * assemble n γ x

def inverseType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ),
    OctonionNormConditions n → ∀ (x : Coordinates R A) (d : Rˣ), (d : R) = cubicNorm n γ x →
      ∃ V : (Module.End R (Coordinates R A))ˣ,
        (∀ y, (↑V : Module.End R (Coordinates R A)) y = applyOperator n γ x y) ∧
        (↑V⁻¹ : Module.End R (Coordinates R A)) x = (↑d⁻¹ : R) • cubicAdjoint n γ x

def scalarExtensionType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) (B : Type w) [CommRing B] [Algebra R B]
    (h : OctonionNormConditions n),
    letI := h.projective
    let q := normBaseChange B n
    let δ := baseChangedWeights B γ
    let M := Coordinates B (B ⊗[R] A)
    operatorIdentities q δ ∧
    (∀ x : M, assemble q δ (applyOperator q δ x cubicUnit) = assemble q δ x * assemble q δ x) ∧
    ∃ U : QuadraticMap B M (Module.End B M), ∀ x y : M, U x y = applyOperator q δ x y

def naturalityType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) (h : OctonionNormConditions n)
    (B : Type w) [CommRing B] [Algebra R B] (D : Type z) [CommRing D] [Algebra R D],
    letI := h.projective
    ∀ (f : B →ₐ[R] D) (x y : Coordinates B (B ⊗[R] A)),
      let F := mapExtendedCoordinates B f
      F (applyOperator (normBaseChange B n) (baseChangedWeights B γ) x y) =
        applyOperator (normBaseChange D n) (baseChangedWeights D γ) (F x) (F y)

def jordanStructureType :=
  ∀ {R : Type u} {A : Type v} [CommRing R] [NonAssocRing A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A]
    {n : QuadraticForm R A} (γ : Fin 3 → Rˣ) (h : OctonionNormConditions n),
    letI := h.projective
    ∃ J : Specs.LinearAlgebraicGroups.Albert.QuadraticJordan R (Coordinates R A),
      J.unit = cubicUnit ∧
      (∀ x y : Coordinates R A, J.groundOp x y = applyOperator n γ x y) ∧
      (∀ (B : Type u) [CommRing B] [Algebra R B] (x y : B ⊗[R] Coordinates R A),
        coordinatesBaseChange B (J.op B x y) =
          applyOperator (normBaseChange B n) (baseChangedWeights B γ)
            (coordinatesBaseChange B x) (coordinatesBaseChange B y)) ∧
      (∀ (d : Rˣ), (d : R) = 2 → ∀ x y : Coordinates R A,
        assemble n γ (J.groundProduct d x y) =
          (↑d⁻¹ : R) • (assemble n γ x * assemble n γ y + assemble n γ y * assemble n γ x))

end LinearAlgebraicGroups.Albert.QuadraticOperatorSpecification
