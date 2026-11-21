import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierInversion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual

open MeasureTheory TopologicalSpace
open scoped SchwartzMap Topology

noncomputable section
namespace ExpandedFA.Fourier.Examples
open ExpandedFA.Distributions

/-- Coordinate-space test functions, transported to the Euclidean realization of ℝᵈ. -/
def testSchwartz (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) : Schwartz 𝕜 d :=
  SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 (EuclideanSpace.equiv (Fin d) ℝ)
    (φ.hasCompactSupport.toSchwartzMap φ.contDiff)

/-- The regular distribution of the constant function one. -/
def oneDistribution (𝕜 : Type) [RCLike 𝕜] (d : ℕ) : Tempered 𝕜 d :=
  SchwartzMap.integralCLM 𝕜 volume

/-- Delta is scalar-linear evaluation, without conjugation. -/
def delta (𝕜 : Type) [RCLike 𝕜] (d : ℕ) : Tempered 𝕜 d :=
  (BoundedContinuousFunction.evalCLM 𝕜 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM 𝕜 (Euclidean d) 𝕜)

/-- Coordinate words represent every multi-index; the empty word is degree zero. -/
def wordMonomial {d : ℕ} : List (Fin d) → Euclidean d → ℂ
  | [], _ => 1
  | i :: w, x => (x i : ℂ) * wordMonomial w x

def monomialDistribution {d : ℕ} : List (Fin d) → Tempered ℂ d
  | [] => oneDistribution ℂ d
  | i :: w => temperedCoordinateMultiply i (monomialDistribution w)

def deltaDerivative {d : ℕ} : List (Fin d) → Tempered ℂ d
  | [] => delta ℂ d
  | i :: w => temperedPartial i (deltaDerivative w)

end ExpandedFA.Fourier.Examples

namespace Specs.ExpandedFA.Fourier.TemperedExamples
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Fourier.Examples
open _root_.ExpandedFA.Distributions

/-- No finite-order certificate is assumed: compactness of the actual distribution
support is the sole extra hypothesis. Equality is on the original LF tests. -/
def compactSupportType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d))),
  IsCompact (distributionSupport u) →
    ∃ U : Tempered 𝕜 d, ∀ φ, U (testSchwartz 𝕜 φ) = u φ

/-- The integral-growth hypothesis, not a pointwise polynomial bound. Products
are integrable and the continuous functional has exactly their ordinary integral. -/
def integralGrowthType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (f : Euclidean d → 𝕜), LocallyIntegrable f volume →
    ∀ N : ℕ, Integrable (fun x => (1 + ‖x‖)⁻¹ ^ N * ‖f x‖) →
    ∃ U : Tempered 𝕜 d, ∀ φ : Schwartz 𝕜 d,
      Integrable (fun x => f x * φ x) ∧ U φ = ∫ x, f x * φ x

def basicFourierType : Prop := ∀ d : ℕ,
  temperedFourier (oneDistribution ℂ d) = delta ℂ d ∧
  temperedFourier (delta ℂ d) = oneDistribution ℂ d

/-- The constructed monomial really has the regular integral pairing. -/
def monomialPairingType : Prop := ∀ (d : ℕ) (w : List (Fin d)) (φ : Schwartz ℂ d),
  Integrable (fun x => wordMonomial w x * φ x) ∧
    monomialDistribution w φ = ∫ x, wordMonomial w x * φ x

/-- Exact constants for both directions, for every monomial and hence every
polynomial. The finite sum includes the zero polynomial and dimension zero. -/
def polynomialFourierType : Prop := ∀ (d : ℕ) (s : Finset (List (Fin d)))
    (c : List (Fin d) → ℂ),
  temperedFourier (∑ w ∈ s, c w • monomialDistribution w) =
    ∑ w ∈ s, (c w * (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ w.length) •
      deltaDerivative w ∧
  temperedFourier (∑ w ∈ s, c w • deltaDerivative w) =
    ∑ w ∈ s, (c w * (2 * (Real.pi : ℂ) * Complex.I) ^ w.length) •
      monomialDistribution w

/-- The explicit counterexample on ℝ, expressed in the original coordinate LF
space. The Schwartz images of actual compact tests tend to zero, while their
pairings tend to +∞, ruling out any continuous tempered extension. -/
def nonTemperedType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∃ u : ScalarDistribution 𝕜 (⊤ : Opens (Domain 1)),
    (∀ φ, u φ = ∫ x : Domain 1, (Real.exp ((x 0)^2) : 𝕜) * φ x) ∧
    (∃ ψ : ℕ → Tests 𝕜 (⊤ : Opens (Domain 1)),
      Filter.Tendsto (fun n => testSchwartz 𝕜 (ψ n)) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun n => RCLike.re (u (ψ n))) Filter.atTop Filter.atTop) ∧
    ¬ ∃ U : Tempered 𝕜 1, ∀ φ, U (testSchwartz 𝕜 φ) = u φ

end Specs.ExpandedFA.Fourier.TemperedExamples
