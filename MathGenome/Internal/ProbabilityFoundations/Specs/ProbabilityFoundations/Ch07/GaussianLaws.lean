import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
Independent specifications for the existence, transform, uniqueness, and actual
moments of the Gaussian law in paper.tex, Theorem 7.7 (2604–2609, 2619–2626).
`Matrix.PosSemidef` includes symmetry over ℝ and allows singular matrices.
All dimensions, including zero, are included. Coordinate marginals identify
the construction with `gaussianReal`, whose second parameter is the variance.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace NNReal

namespace Specs.ProbabilityFoundations.Ch07.GaussianLaws

open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.TransformObjects

def gaussianLawType :=
  {d : ℕ} → Euclidean d → Matrix (Fin d) (Fin d) ℝ → Measure (Euclidean d)

noncomputable def gaussianLawValue : gaussianLawType :=
  fun {_d} m S => multivariateGaussian m S

def gaussianLawProbability : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    IsProbabilityMeasure (gaussianLawValue m S)

def gaussianLawGaussian : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    IsGaussian (gaussianLawValue m S)

/-- The plus-sign characteristic function, with no 2π in the exponent. -/
def gaussianLawCharacteristicFunction : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    S.PosSemidef → ∀ t : Euclidean d,
    characteristicFunctionValue (gaussianLawValue m S) t =
      Complex.exp (Complex.I * (inner ℝ t m : ℂ) - ((t ⬝ᵥ S *ᵥ t : ℝ) : ℂ) / 2)

/-- Uniqueness among all Borel probability laws, with no moment assumption. -/
def gaussianLawUnique : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    S.PosSemidef → ∀ μ : Measure (Euclidean d), IsProbabilityMeasure μ →
    (∀ t : Euclidean d, characteristicFunctionValue μ t =
      Complex.exp (Complex.I * (inner ℝ t m : ℂ) - ((t ⬝ᵥ S *ᵥ t : ℝ) : ℂ) / 2)) →
    μ = gaussianLawValue m S

def gaussianLawIntegrable : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    Integrable (fun x => x) (gaussianLawValue m S)

def gaussianLawMean : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    (∫ x, x ∂gaussianLawValue m S) = m

/-- Covariance means the integral of the product of centered coordinates. -/
def gaussianLawCovariance : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    S.PosSemidef → ∀ i j : Fin d,
    covariance (fun x => x i) (fun x => x j) (gaussianLawValue m S) = S i j

def gaussianLawMemLpTwo : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    MemLp (fun x => x) 2 (gaussianLawValue m S)

def gaussianLawSecondMoment : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    Integrable (fun x => ‖x‖ ^ 2) (gaussianLawValue m S)

def gaussianLawZeroCovariance : Prop :=
  ∀ {d : ℕ} (m : Euclidean d), gaussianLawValue m 0 = Measure.dirac m

/-- Each coordinate has the existing real normal law with its actual variance. -/
def gaussianLawCoordinate : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
    S.PosSemidef → ∀ i : Fin d,
    (gaussianLawValue m S).map (fun x => x i) = gaussianReal (m i) (S i i).toNNReal

/-- Explicit identification of ℝ¹ with ℝ, including variance zero. -/
def gaussianLawUnivariate : Prop :=
  ∀ (m : ℝ) (v : ℝ≥0),
    (gaussianLawValue (WithLp.toLp 2 (fun _ : Fin 1 => m))
      (Matrix.diagonal (fun _ : Fin 1 => (v : ℝ)))).map (fun x => x 0) = gaussianReal m v

end Specs.ProbabilityFoundations.Ch07.GaussianLaws
