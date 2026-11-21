import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TorusFourierBasis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.DiagonalLpSpectrum
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Logic.Equiv.Nat

/-! The bounded, compact spectral model in `fa2:p3:periodic-convolution`.
The separate operator-ideal criteria are allocated to PeriodicConvolutionIdeals.
All positive periods use normalized Haar measure, including the angular circle.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology

namespace ExpandedFA.Models.PeriodicConvolutionSpec

abbrev Circle (T : ℝ) := AddCircle T
abbrev Haar (T : ℝ) [Fact (0 < T)] := AddCircle.haarAddCircle (T := T)
abbrev Kernel (T : ℝ) [Fact (0 < T)] := Lp ℂ 1 (Haar T)
abbrev Space (T : ℝ) [Fact (0 < T)] := Lp ℂ 2 (Haar T)

/-- Enumeration only changes the indexing of the Fourier basis. -/
def frequency : ℕ ≃ ℤ := Equiv.intEquivNat.symm

def enumeratedBasis (T : ℝ) [Fact (0 < T)] : HilbertBasis ℕ ℂ (Space T) :=
  HilbertBasis.mk (orthonormal_fourier.comp frequency frequency.injective) (by
    have hr : Set.range (fourierLp (T := T) 2 ∘ frequency) =
        Set.range (fourierLp (T := T) 2) := frequency.surjective.range_comp _
    rw [hr, span_fourierLp_closure_eq_top (by simp)])

lemma coefficient_bound {T : ℝ} [Fact (0 < T)] (k : Kernel T) (n : ℤ) :
    ‖fourierCoeff k n‖ ≤ ‖k‖ := by
  rw [L1.norm_eq_integral_norm]
  apply norm_integral_le_of_norm_le (memLp_one_iff_integrable.mp (Lp.memLp k)).norm
  apply ae_of_all
  intro x
  simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul, le_refl]

def coefficients {T : ℝ} [Fact (0 < T)] (k : Kernel T) :
    DiagonalLpSpectrumSpec.Sequence ∞ :=
  ⟨fun j => fourierCoeff k (frequency j), memℓp_infty ⟨‖k‖, by
    rintro _ ⟨j, rfl⟩
    exact coefficient_bound k _⟩⟩

/-- Canonical bounded Fourier multiplier. The integral identification is an
independent theorem below, not an assumption in this definition. -/
def operatorValue {T : ℝ} [Fact (0 < T)] (k : Kernel T) : Space T →L[ℂ] Space T :=
  (enumeratedBasis T).repr.symm.toLinearIsometry.toContinuousLinearMap ∘L
    DiagonalLpSpectrumSpec.diagonalValue 2 (coefficients k) ∘L
      (enumeratedBasis T).repr.toLinearIsometry.toContinuousLinearMap

def OperatorType := ∀ {T : ℝ} [Fact (0 < T)], Kernel T → (Space T →L[ℂ] Space T)

def IntegralIdentification : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T) (f : Space T),
    (∀ᵐ x ∂Haar T, Integrable (fun t => k t * f (x - t)) (Haar T)) ∧
    (operatorValue k f : Circle T → ℂ) =ᵐ[Haar T]
      fun x => ∫ t, k t * f (x - t) ∂Haar T

def NormBound : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T), ‖operatorValue k‖ ≤ ‖k‖

def FourierDiagonal : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T) (n : ℤ),
    operatorValue k (fourierLp 2 n) = fourierCoeff k n • fourierLp 2 n

def CoefficientAction : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T) (f : Space T) (n : ℤ),
    fourierCoeff (operatorValue k f) n = fourierCoeff k n * fourierCoeff f n

def Compactness : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T), IsCompactOperator (operatorValue k)

def Normality : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T), IsStarNormal (operatorValue k)

def SpectrumLaw : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T),
    spectrum ℂ (operatorValue k) = closure (Set.range (fourierCoeff k))

def SelfAdjointCriterion : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T),
    IsSelfAdjoint (operatorValue k) ↔ ∀ n, (fourierCoeff k n).im = 0

def PositivityCriterion : Prop :=
  ∀ (T : ℝ) [Fact (0 < T)] (k : Kernel T),
    (operatorValue k).IsPositive ↔
      ∀ n, (fourierCoeff k n).im = 0 ∧ 0 ≤ (fourierCoeff k n).re

end ExpandedFA.Models.PeriodicConvolutionSpec
