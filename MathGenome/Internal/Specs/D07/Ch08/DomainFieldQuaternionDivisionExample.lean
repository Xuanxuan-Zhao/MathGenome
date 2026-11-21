import MathGenome.Internal.Specs.D07.Ch08.MatrixRing
import Mathlib.Algebra.Quaternion
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
Independent specification for the quaternion example in K07.08.domain_field,
paper.tex:1233–1246. The coordinates are real, and the matrix entries have
exactly the signs in the source. The matrix subalgebra and its equivalence
are conclusions, rather than assumed structures on the displayed set.
The norm denominator is the sum of four squares, not the analytic norm.
-/

noncomputable section

namespace Specs.D07.Ch08.DomainFieldQuaternionDivisionExample

abbrev H := Quaternion ℝ
abbrev M := Matrix (Fin 2) (Fin 2) ℂ

def coordinates (a b c d : ℝ) : M :=
  !![(a : ℂ) + (b : ℂ) * Complex.I, (c : ℂ) + (d : ℂ) * Complex.I;
     -(c : ℂ) + (d : ℂ) * Complex.I, (a : ℂ) - (b : ℂ) * Complex.I]

def matrixMap (q : H) : M := coordinates q.re q.imI q.imJ q.imK

def matrixCarrier : Set M := {A | ∃ a b c d : ℝ, coordinates a b c d = A}

def iH : H := ⟨0, 1, 0, 0⟩
def jH : H := ⟨0, 0, 1, 0⟩
def kH : H := ⟨0, 0, 0, 1⟩

def denominator (q : H) : ℝ := q.re ^ 2 + q.imI ^ 2 + q.imJ ^ 2 + q.imK ^ 2

def conjugate (q : H) : H := ⟨q.re, -q.imI, -q.imJ, -q.imK⟩

/-- Division by the real denominator means real scalar multiplication. -/
def inverseCandidate (q : H) : H := (denominator q)⁻¹ • conjugate q

def CoordinateExpansion : Prop :=
  ∀ a b c d : ℝ, (⟨a, b, c, d⟩ : H) = (a : H) + b • iH + c • jH + d • kH

/-- The explicit faithful real algebra representation, including its value. -/
def MatrixRealization : Prop :=
  ∃ f : H →ₐ[ℝ] M, (∀ q, f q = matrixMap q) ∧ Function.Injective f

/-- The displayed matrices, with inherited operations, are isomorphic to ℍ. -/
def MatrixAlgebraEquivalence : Prop :=
  ∃ S : Subalgebra ℝ M, (∀ A, A ∈ S ↔ A ∈ matrixCarrier) ∧
    ∃ e : H ≃ₐ[ℝ] S, ∀ q, (e q : M) = matrixMap q

def MatrixClosure : Prop :=
  (0 : M) ∈ matrixCarrier ∧ (1 : M) ∈ matrixCarrier ∧
    (∀ A B : M, A ∈ matrixCarrier → B ∈ matrixCarrier →
      A + B ∈ matrixCarrier ∧ A * B ∈ matrixCarrier) ∧
    (∀ A : M, A ∈ matrixCarrier → -A ∈ matrixCarrier) ∧
    (∀ (r : ℝ) (A : M), A ∈ matrixCarrier → r • A ∈ matrixCarrier)

def RingLaws : Prop :=
  ∀ p q r : H,
    (p * q) * r = p * (q * r) ∧ 1 * p = p ∧ p * 1 = p ∧
    p * (q + r) = p * q + p * r ∧ (p + q) * r = p * r + q * r

def UnitRelations : Prop :=
  iH * iH = -1 ∧ jH * jH = -1 ∧ kH * kH = -1 ∧
    iH * jH = kH ∧ jH * iH = -kH ∧ iH * jH = -(jH * iH)

def ConjugateProducts : Prop :=
  ∀ q : H, q * conjugate q = (denominator q : H) ∧
    conjugate q * q = (denominator q : H)

def PositiveDenominator : Prop := ∀ q : H, q ≠ 0 → 0 < denominator q

def InverseFormula : Prop :=
  ∀ q : H, q ≠ 0 → q⁻¹ = inverseCandidate q ∧
    q * inverseCandidate q = 1 ∧ inverseCandidate q * q = 1

def DivisionRingExample : Prop :=
  (0 : H) ≠ 1 ∧ (∀ q : H, q ≠ 0 → IsUnit q) ∧
    ¬ (∀ p q : H, p * q = q * p)

end Specs.D07.Ch08.DomainFieldQuaternionDivisionExample
