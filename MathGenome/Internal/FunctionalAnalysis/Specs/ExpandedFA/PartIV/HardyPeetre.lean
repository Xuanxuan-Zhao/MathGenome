import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLowpass

/-! Independent statements for paper.tex, `fa2:p4:hardy-peetre`.
The lowpass and inverse are actual kernels. The L¹ condition and conclusions
use nonnegative extended integrals so infinite suprema are never discarded.
The real representative of the radial maximal function is used only under
its explicit integrability assumption, which entails a.e. finiteness. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ExpandedFA.PartIV.HardyPeetreSpec
open ExpandedFA.Fourier HardyMaximalSpec HardyLowpassSpec
open ExpandedFA.SingularIntegrals.MaximalWeakBoundSpec

/-- The first, linear bound justifies the subsequent nonlinear bootstrap. -/
def LinearBound : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (Φ : Euclidean d → 𝕜), IsFixedKernel Φ →
    ∀ (η : Schwartz 𝕜 d) (Ψ : Euclidean d → 𝕜) (D : ℝ),
      Integrable Ψ → 0 ≤ D →
      (∀ z, ‖Ψ z‖ ≤ D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 2)) →
      (∀ z, η z = convolve Ψ Φ z) →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜), Integrable f →
      (∫⁻ x, radial Φ f x) < ∞ → ∀ x,
      peetre η f x ≤ ENNReal.ofReal C *
        MaximalValue volume (fun z => (radial Φ f z).toReal) x

/-- In particular the actual Peetre supremum is finite before any division. -/
def FiniteAlmostEverywhere : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (Φ : Euclidean d → 𝕜), IsFixedKernel Φ →
    ∀ (η : Schwartz 𝕜 d) (Ψ : Euclidean d → 𝕜) (D : ℝ),
      Integrable Ψ → 0 ≤ D →
      (∀ z, ‖Ψ z‖ ≤ D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 2)) →
      (∀ z, η z = convolve Ψ Φ z) →
    ∀ (f : Euclidean d → 𝕜), Integrable f →
      (∫⁻ x, radial Φ f x) < ∞ →
      ∀ᵐ x ∂volume, peetre η f x < ∞

/-- For the same chosen lowpass, A=d+1 and r=1-1/(4(d+1)).
Constants precede f and x; no bootstrap bound is assumed. -/
def NonlinearBound : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (N : ℕ), AdmissibleOrder d N →
    ∀ (Φ : Euclidean d → 𝕜), IsFixedKernel Φ →
    ∀ (η : Schwartz 𝕜 d) (R : ℝ) (Ψ : Euclidean d → 𝕜) (D : ℝ),
      IsLowpass η R → Integrable Ψ → 0 ≤ D →
      (∀ z, ‖Ψ z‖ ≤ D * (1 + ‖z‖) ^ (-(d : ℝ) - 1 / 2)) →
      (∀ z, η z = convolve Ψ Φ z) →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜), Integrable f →
      (∫⁻ x, radial Φ f x) < ∞ →
      ∀ᵐ x ∂volume, peetre η f x ≤ ENNReal.ofReal C *
        (MaximalValue volume
          (fun z => (radial Φ f z).toReal ^ averagingExponent d) x) ^
            (1 / averagingExponent d)

/-- The grand maximal bound for every admissible test order. -/
def GrandL1Bound : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}, 0 < d →
    ∀ (N : ℕ), AdmissibleOrder d N →
    ∀ (Φ : Euclidean d → 𝕜), IsFixedKernel Φ →
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Euclidean d → 𝕜), Integrable f →
      (∫⁻ x, radial Φ f x) < ∞ →
      (∫⁻ x, grand N f x) ≤ ENNReal.ofReal C * ∫⁻ x, radial Φ f x

end ExpandedFA.PartIV.HardyPeetreSpec
