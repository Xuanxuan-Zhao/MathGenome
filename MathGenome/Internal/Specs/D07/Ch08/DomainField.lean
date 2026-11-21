import MathGenome.Internal.Specs.D07.Ch08.RingDefinition
import MathGenome.Internal.Specs.D07.Ch08.Units
import MathGenome.Internal.Specs.D07.Ch08.DomainFieldQuaternionDivisionExample
import Mathlib.Algebra.Field.Basic

/-!
Independent specifications for K07.08.domain_field, paper.tex:1228–1247.
The characterizations retain the supplied ring operations. Division rings
need not be commutative, whereas fields and integral domains are commutative
and nontrivial. In particular, `IsDomain` is used only over `CommRing` here.
The quaternion assertions use the exact coordinates, conjugate, denominator,
and matrix presentation of the prerequisite specification.
-/

universe u

namespace Specs.D07.Ch08.DomainField

def DivisionRingCharacterization : Prop :=
  ∀ (R : Type u) (s : Ring R),
    ((0 : R) ≠ 1 ∧ ∀ a : R, a ≠ 0 → IsUnit a) ↔
      ∃ d : DivisionRing R, d.toRing = s

def FieldCharacterization : Prop :=
  ∀ (R : Type u) (s : Ring R),
    ((0 : R) ≠ 1 ∧ (∀ a : R, a ≠ 0 → IsUnit a) ∧
      ∀ a b : R, a * b = b * a) ↔
      ∃ f : Field R, f.toRing = s

/-- Adding commutativity to a division ring gives precisely a field,
retaining its ring and inverse operations. -/
def CommutativeDivisionRingCharacterization : Prop :=
  ∀ (R : Type u) (d : DivisionRing R),
    (∀ a b : R, a * b = b * a) ↔
      ∃ f : Field R, f.toDivisionRing = d

def IntegralDomainCharacterization : Prop :=
  ∀ (R : Type u) [CommRing R],
    IsDomain R ↔ ((0 : R) ≠ 1 ∧
      ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0)

/-- The inverse argument does not require commutativity. -/
def DivisionRingLeftZeroProduct : Prop :=
  ∀ (R : Type u) [DivisionRing R] (a b : R), a ≠ 0 → a * b = 0 → b = 0

def FieldIsDomain : Prop := ∀ (R : Type u) [Field R], IsDomain R

open DomainFieldQuaternionDivisionExample in
def QuaternionDivisionRing : Prop :=
  (0 : H) ≠ 1 ∧ (∀ q : H, q ≠ 0 → IsUnit q) ∧
    ¬ (∀ p q : H, p * q = q * p)

open DomainFieldQuaternionDivisionExample in
def QuaternionRelations : Prop :=
  iH * jH = kH ∧ jH * iH = -kH ∧ iH * jH = -(jH * iH)

open DomainFieldQuaternionDivisionExample in
def QuaternionConjugateAndInverse : Prop :=
  (∀ q : H, q * conjugate q = (denominator q : H) ∧
    conjugate q * q = (denominator q : H)) ∧
  (∀ q : H, q ≠ 0 → 0 < denominator q) ∧
  (∀ q : H, q ≠ 0 → q⁻¹ = inverseCandidate q ∧
    q * inverseCandidate q = 1 ∧ inverseCandidate q * q = 1)

open DomainFieldQuaternionDivisionExample in
/-- The displayed real linear matrix space, with inherited operations,
is a real subalgebra isomorphic to the canonical real quaternions. -/
def QuaternionMatrixConstruction : Prop :=
  CoordinateExpansion ∧ MatrixRealization ∧ MatrixAlgebraEquivalence ∧ MatrixClosure ∧ RingLaws

end Specs.D07.Ch08.DomainField
