import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.Symmetry
import Mathlib.Data.Nat.Choose.Multinomial

/-! Independent specification of the factorial bridge, in all finite dimensions
and at every natural-number order. The finite antidiagonal is precisely |α| = j. -/
noncomputable section
open scoped BigOperators
namespace Specs.D04.C03.FactorialBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
namespace Model

def multiIndices (n j : ℕ) : Finset (MultiIndex n) :=
  Finset.piAntidiag Finset.univ j

/-- Basis coefficient of a tensor, using the shared canonical coordinate word.
The off-degree value is zero and is never used in the bridge sum. -/
def tensorMultiIndex {n j : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : Differential (E n) Y j) (α : MultiIndex n) : Y :=
  if h : (multiIndexWord α).length = j then
    T (fun r => standardBasis n ((multiIndexWord α).get (Fin.cast h.symm r)))
  else 0

def multiIndexTaylorPolynomial {n : ℕ} {Y : Type} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (k : ℕ) (f : E n → Y) (a h : E n) : Y :=
  ∑ j ∈ Finset.range (k+1), ∑ α ∈ multiIndices n j,
    (multiIndexMonomial α h / (multiIndexFactorial α : ℝ)) • multiIndexPartial α f a
end Model
open Model

def multiIndicesType := (n j : ℕ) → Finset (MultiIndex n)
def multiIndicesValue : multiIndicesType := Model.multiIndices

def tensorMultiIndexType := {n j : ℕ} → {Y : Type} → [NormedAddCommGroup Y] →
  [NormedSpace ℝ Y] → Differential (E n) Y j → MultiIndex n → Y
def tensorMultiIndexValue : tensorMultiIndexType := @Model.tensorMultiIndex

def multiIndexTaylorPolynomialType := {n : ℕ} → {Y : Type} → [NormedAddCommGroup Y] →
  [NormedSpace ℝ Y] → ℕ → (E n → Y) → E n → E n → Y
def multiIndexTaylorPolynomialValue : multiIndexTaylorPolynomialType := @Model.multiIndexTaylorPolynomial

def symmetric_factorial_bridgeType : Prop :=
  ∀ {n j : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : Differential (E n) Y j),
    (∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → E n), T (v ∘ σ) = T v) →
    ∀ h : E n, ((j.factorial : ℝ)⁻¹) • differentialDiagonal T h =
      ∑ α ∈ multiIndices n j,
        (multiIndexMonomial α h / (multiIndexFactorial α : ℝ)) • tensorMultiIndex T α

def factorial_bridgeType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (j : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n),
    TimesDifferentiableAt j U f a → ∀ h : E n,
      ((j.factorial : ℝ)⁻¹) • differentialDiagonal (higherDifferential j f a) h =
        ∑ α ∈ multiIndices n j,
          (multiIndexMonomial α h / (multiIndexFactorial α : ℝ)) • multiIndexPartial α f a

def taylorPolynomial_eq_multiIndexType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (k : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n),
    TimesDifferentiableAt k U f a →
      taylorPolynomial k f a = multiIndexTaylorPolynomial k f a

def mem_multiIndices_iffType : Prop :=
  ∀ {n j : ℕ} (α : MultiIndex n),
    α ∈ multiIndices n j ↔ multiIndexDegree α = j

def coordinate_tuple_multiplicityType : Prop :=
  ∀ {n j : ℕ} (α : MultiIndex n), multiIndexDegree α = j →
    (Finset.univ.filter (fun w : Fin j → Fin n =>
      ∀ i, (List.ofFn w).count i = α i)).card = j.factorial / multiIndexFactorial α

def factorial_bridge_scalarType : Prop :=
  ∀ {n : ℕ} (j : ℕ) (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt j U f a → ∀ h : E n,
      differentialDiagonal (higherDifferential j f a) h / (j.factorial : ℝ) =
        ∑ α ∈ multiIndices n j,
          (multiIndexPartial α f a / (multiIndexFactorial α : ℝ)) * multiIndexMonomial α h

def multiIndices_zeroType : Prop :=
  ∀ n : ℕ, multiIndices n 0 = {0}

def multiIndices_dimension_zero_succType : Prop :=
  ∀ j : ℕ, multiIndices 0 (j+1) = ∅

end Specs.D04.C03.FactorialBridge
