import MathGenome.Internal.Specs.D07.Ch23.FrobeniusComplexSubfieldCentralizer
import MathGenome.Internal.Specs.D07.Ch23.QuaternionAlgebra

/-! Statements for the anticommuting part of paper.tex:7503–7535.
The complex image need not be central in D. Only the real scalar map is
central. No finite dimension is assumed. -/
noncomputable section
universe u
namespace Specs.D07.Ch23.FrobeniusAnticommutingDecomposition

variable {D : Type u} [DivisionRing D] [Algebra ℝ D]

/-- Conjugation by the embedded imaginary unit, as in the source. -/
def conjugation (φ : ℂ →ₐ[ℝ] D) (y : D) : D :=
  φ Complex.I * y * (φ Complex.I)⁻¹

def positive (φ : ℂ →ₐ[ℝ] D) : Submodule ℝ D := φ.range.toSubmodule

/-- The anticommuting real subspace. -/
def negative (φ : ℂ →ₐ[ℝ] D) : Submodule ℝ D where
  carrier := {y | φ Complex.I * y = -(y * φ Complex.I)}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    simp only [mul_add, add_mul, ha, hb, neg_add]
  smul_mem' := by
    intro r y hy
    simp only [Set.mem_ofPred_eq] at *
    simp only [mul_smul_comm, smul_mul_assoc, hy, smul_neg]

def positivePart (φ : ℂ →ₐ[ℝ] D) (y : D) : D :=
  (1 / 2 : ℝ) • (y + conjugation φ y)

def negativePart (φ : ℂ →ₐ[ℝ] D) (y : D) : D :=
  (1 / 2 : ℝ) • (y - conjugation φ y)

def CentralizerCondition (φ : ℂ →ₐ[ℝ] D) : Prop :=
  ∀ y : D, y * φ Complex.I = φ Complex.I * y ↔ y ∈ Set.range φ

/-- Real linearity and involutivity of T, internal direct sum, and the
source's explicit projections. -/
def Decomposition (φ : ℂ →ₐ[ℝ] D) : Prop :=
  (∃ T : D →ₗ[ℝ] D, (∀ y, T y = conjugation φ y) ∧ Function.Involutive T) ∧
  IsCompl (positive φ) (negative φ) ∧
  ∀ y : D, positivePart φ y ∈ positive φ ∧ negativePart φ y ∈ negative φ ∧
    positivePart φ y + negativePart φ y = y

def ConjugateAction (φ : ℂ →ₐ[ℝ] D) : Prop :=
  ∀ j ∈ negative φ, ∀ z : ℂ, j * φ z = φ (star z) * j

def NegativeLine (φ : ℂ →ₐ[ℝ] D) : Prop :=
  ∀ j ∈ negative φ, j ≠ 0 →
    ∀ y : D, y ∈ negative φ ↔ ∃ z : ℂ, y = φ z * j

def NegativeSquare (φ : ℂ →ₐ[ℝ] D) : Prop :=
  ∀ j ∈ negative φ, j ≠ 0 →
    ∃ r : ℝ, r < 0 ∧ r ≠ 0 ∧ j ^ 2 = algebraMap ℝ D r

/-- Normalize any chosen nonzero anticommuting element by a positive real
scalar, preserving its entire complex line. -/
def Normalization (φ : ℂ →ₐ[ℝ] D) : Prop :=
  ∀ j ∈ negative φ, j ≠ 0 →
    ∃ (s : ℝ) (j₀ : D), 0 < s ∧ j₀ = s • j ∧
      j₀ ∈ negative φ ∧ j₀ ≠ 0 ∧ j₀ ^ 2 = -1 ∧
      (∀ y : D, (∃ z : ℂ, y = φ z * j₀) ↔ ∃ z : ℂ, y = φ z * j)

/-- A normalized anticommuting generator gives exactly the pair-coordinate
algebra equivalence asserted in the source. -/
def QuaternionEquivalence (φ : ℂ →ₐ[ℝ] D) : Prop :=
  ∀ j ∈ negative φ, j ^ 2 = -1 →
    ∃ e : Quaternion ℝ ≃ₐ[ℝ] D,
      ∀ z w : ℂ, e (QuaternionAlgebra.toH (z, w)) = φ z + φ w * j

/-- The source's uniqueness of the complex-pair expression. -/
def UniqueCoordinates (φ : ℂ →ₐ[ℝ] D) : Prop :=
  ∀ j ∈ negative φ, j ^ 2 = -1 →
    ∀ y : D, ∃! u : ℂ × ℂ, φ u.1 + φ u.2 * j = y

/-- The zero anticommuting space gives the complex case. -/
def ComplexCase (φ : ℂ →ₐ[ℝ] D) : Prop :=
  negative φ = ⊥ → ∃ e : ℂ ≃ₐ[ℝ] D, ∀ z, e z = φ z

/-- Nonzero anticommuting space supplies a normalized generator and the
explicit real-algebra equivalence, without any finiteness premise. -/
def QuaternionCase (φ : ℂ →ₐ[ℝ] D) : Prop :=
  negative φ ≠ ⊥ → ∃ j ∈ negative φ, j ^ 2 = -1 ∧
    ∃ e : Quaternion ℝ ≃ₐ[ℝ] D,
      ∀ z w : ℂ, e (QuaternionAlgebra.toH (z, w)) = φ z + φ w * j

def AnticommutingResults (φ : ℂ →ₐ[ℝ] D) : Prop :=
  Decomposition φ ∧ ConjugateAction φ ∧ NegativeLine φ ∧
  NegativeSquare φ ∧ Normalization φ ∧ QuaternionEquivalence φ ∧ UniqueCoordinates φ ∧
  ComplexCase φ ∧ QuaternionCase φ

/-- The later stages of the proof only need the centralizer identification. -/
def CentralizerAnticommutingResults : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    ∀ φ : ℂ →ₐ[ℝ] D, CentralizerCondition φ → AnticommutingResults φ

/-- In the algebraic setting the required centralizer hypothesis follows
from the earlier part of Frobenius's proof. -/
def AlgebraicAnticommutingResults : Prop :=
  ∀ (D : Type u) [DivisionRing D] [Algebra ℝ D],
    (∀ x : D, IsAlgebraic ℝ x) →
    ∀ φ : ℂ →ₐ[ℝ] D, AnticommutingResults φ

end Specs.D07.Ch23.FrobeniusAnticommutingDecomposition
