import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations
import Mathlib.Analysis.Distribution.Support
import Mathlib.Data.Finsupp.Basic

/-! Independent statements for the two parametrix clauses of
`fa2:p4:elliptic-parametrix`, paper.tex:18050–18055. Local elliptic regularity
is allocated separately to `ops_elliptic_regular`.

The operator is a finite sum of ordinary coordinate derivatives. The principal
symbol below omits the common nonzero factor i^m; hence its nonvanishing is
exactly ellipticity for the Fourier convention exp(-2πi x·ξ). Both scalar
fields, all dimensions, and order zero are included. -/

noncomputable section
open MeasureTheory Set
open scoped SchwartzMap ContDiff FourierTransform

namespace ExpandedFA.Sobolev.Elliptic
open ExpandedFA.Fourier ExpandedFA.Distributions

abbrev Coefficients (𝕜 : Type) [RCLike 𝕜] (d : ℕ) := (Fin d → ℕ) →₀ 𝕜

def degree {d : ℕ} (α : Fin d → ℕ) : ℕ := ∑ i, α i

/-- Exact order, rather than an a priori inverse-symbol bound. In dimension
zero this forces order zero and a nonzero scalar coefficient. -/
def HasOrder {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (c : Coefficients 𝕜 d) (m : ℕ) : Prop :=
  (∀ α ∈ c.support, degree α ≤ m) ∧ ∃ α ∈ c.support, degree α = m

def principalSymbol {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (m : ℕ) (ξ : Euclidean d) : 𝕜 :=
  ∑ α ∈ c.support.filter (fun α => degree α = m), c α * ∏ i, (ξ i : 𝕜) ^ α i

/-- The usual principal-symbol hypothesis on real nonzero covectors. -/
def IsElliptic {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (m : ℕ) : Prop :=
  HasOrder c m ∧ ∀ ξ : Euclidean d, ξ ≠ 0 → principalSymbol c m ξ ≠ 0

/-- Negative transpose differentiation on the original scalar-linear dual. -/
def wordPartial {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    List (Fin d) → Tempered 𝕜 d → Tempered 𝕜 d
  | [], T => T
  | i :: w, T => wordPartial w
      (-T.comp (LineDeriv.lineDerivOpCLM 𝕜 (Schwartz 𝕜 d) (basisVector i)))

/-- The differential operator itself, not an abstract map with an assumed
Fourier-symbol or solvability certificate. -/
def applyOperator {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : Coefficients 𝕜 d) (T : Tempered 𝕜 d) : Tempered 𝕜 d :=
  ∑ α ∈ c.support, c α • wordPartial (multiIndexWord α) T

/-- The ordinary bilinear integral embedding of a Schwartz function. -/
def regularSchwartz {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : Schwartz 𝕜 d) : Tempered 𝕜 d :=
  (SchwartzMap.integralCLM 𝕜 (volume : Measure (Euclidean d))).comp
    (SchwartzMap.pairing (ContinuousLinearMap.mul 𝕜 𝕜) f)

/-- Smoothness on U means equality with a smooth function on every compactly
supported smooth test in U, with actual Lebesgue-integrable pairings. The
unrestricted values of f outside U have no role. -/
def SmoothOn {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (T : Tempered 𝕜 d) (U : Set (Euclidean d)) : Prop :=
  ∃ f : Euclidean d → 𝕜, ContDiffOn ℝ ∞ f U ∧
    ∀ φ : Schwartz 𝕜 d, HasCompactSupport φ → tsupport φ ⊆ U →
      Integrable (fun x => f x * φ x) ∧ T φ = ∫ x, f x * φ x

/-- The precise Fourier symbol of the ordinary derivative operator. -/
def fourierSymbol {d : ℕ} (c : Coefficients ℂ d) (ξ : Euclidean d) : ℂ :=
  ∑ α ∈ c.support, c α * ∏ i, ((2 * Real.pi * Complex.I) * (ξ i : ℂ)) ^ α i

end ExpandedFA.Sobolev.Elliptic

namespace Specs.ExpandedFA.Sobolev.EllipticParametrix
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Fourier.Examples
open _root_.ExpandedFA.Sobolev.Elliptic

/-- Global tempered parametrix, with a Schwartz remainder and smoothness on
the entire punctured space. No estimate on an inverse symbol is assumed. -/
def globalParametrixType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (c : Coefficients 𝕜 d), IsElliptic c m →
  ∃ (Q : Tempered 𝕜 d) (r : Schwartz 𝕜 d),
    SmoothOn Q ({0}ᶜ : Set (Euclidean d)) ∧
    applyOperator c Q = delta 𝕜 d + regularSchwartz r

/-- Every prescribed positive-radius open ball contains the distributional
support of a parametrix. Its remainder is smooth (indeed it can be chosen
Schwartz, since the localized remainder has compact support). The support is
the native distributional support of the original functional on smooth tests,
not the support of a selected function representative. -/
def compactParametrixType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (c : Coefficients 𝕜 d), IsElliptic c m → ∀ R : ℝ, 0 < R →
  ∃ (Q : Tempered 𝕜 d) (r : Schwartz 𝕜 d),
    _root_.Distribution.dsupport (fun φ : Schwartz 𝕜 d => Q φ) ⊆ Metric.ball 0 R ∧
    SmoothOn Q ({0}ᶜ : Set (Euclidean d)) ∧
    applyOperator c Q = delta 𝕜 d + regularSchwartz r

/-- A supplementary operator identity, needed by the Fourier construction. -/
def fourierOperatorType : Prop := ∀ (d : ℕ) (c : Coefficients ℂ d) (T : Tempered ℂ d),
  temperedFourier (applyOperator c T) =
    TemperedDistribution.smulLeftCLM ℂ (fourierSymbol c) (temperedFourier T)

/-- Completed boundary cases, with one Q working for every positive ball. -/
def boundaryParametrixType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d m : ℕ)
    (c : Coefficients 𝕜 d), HasOrder c m → d = 0 ∨ m = 0 →
  ∃ (Q : Tempered 𝕜 d) (r : Schwartz 𝕜 d),
    (∀ R : ℝ, 0 < R →
      _root_.Distribution.dsupport (fun φ : Schwartz 𝕜 d => Q φ) ⊆ Metric.ball 0 R) ∧
    SmoothOn Q ({0}ᶜ : Set (Euclidean d)) ∧
    applyOperator c Q = delta 𝕜 d + regularSchwartz r

/-- An assembly lemma with explicit intermediate data; this does not replace
or assume the required elliptic-symbol existence theorem. -/
def inverseSymbolEquationType : Prop := ∀ (d : ℕ) (c : Coefficients ℂ d)
    (q : Euclidean d → ℂ), q.HasTemperateGrowth → ∀ χ : Schwartz ℂ d,
  (∀ ξ, fourierSymbol c ξ * q ξ = 1 - χ ξ) →
  applyOperator c
      (𝓕⁻ (TemperedDistribution.smulLeftCLM ℂ q (oneDistribution ℂ d)) :
        TemperedDistribution (Euclidean d) ℂ) =
    delta ℂ d + regularSchwartz (-(𝓕⁻ χ) : Schwartz ℂ d)

end Specs.ExpandedFA.Sobolev.EllipticParametrix
