import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.EllipticParametrix
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus

/-! Local elliptic regularity, the last clause of `fa2:p4:elliptic-parametrix`.
The domain and distribution are the original open-set LF test space and its
continuous scalar-linear dual. No temperedness, finite order, boundedness of
the open set, or boundary regularity is assumed.

The integral is written in the Euclidean realization of R^d. `testSchwartzOn`
merely extends a compact test to the whole space and changes from coordinate
space to Euclidean space by the canonical volume-preserving equivalence.
Smoothness is equality with one smooth function on the entire open set, not
just a statement about selected representatives or almost-everywhere values. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped SchwartzMap ContDiff
namespace ExpandedFA.Sobolev.Elliptic
open ExpandedFA.Fourier ExpandedFA.Distributions

def testSchwartzOn {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (φ : Tests 𝕜 Ω) : Schwartz 𝕜 d :=
  Examples.testSchwartz 𝕜 (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 ⊤)

/-- Ordinary derivatives, defined by negative transposition on the local dual. -/
def localWordPartial {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)} :
    List (Fin d) → ScalarDistribution 𝕜 Ω → ScalarDistribution 𝕜 Ω
  | [], u => u
  | i :: w, u => localWordPartial w
      (-u.comp (TestFunction.lineDerivCLM 𝕜 (coordinateVector i)))

/-- The same finite constant-coefficient differential operator on local distributions. -/
def localOperator {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (c : Coefficients 𝕜 d) (u : ScalarDistribution 𝕜 Ω) : ScalarDistribution 𝕜 Ω :=
  ∑ α ∈ c.support, c α • localWordPartial (multiIndexWord α) u

/-- An actual smooth integral representative on V. Values outside V are immaterial. -/
def DistributionSmoothOn {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : ScalarDistribution 𝕜 Ω) (V : Set (Domain d)) : Prop :=
  ∃ f : Euclidean d → 𝕜,
    ContDiffOn ℝ ∞ f ((EuclideanSpace.equiv (Fin d) ℝ) ⁻¹' V) ∧
    ∀ φ : Tests 𝕜 Ω, tsupport φ ⊆ V →
      Integrable (fun x => f x * testSchwartzOn φ x) ∧
      u φ = ∫ x, f x * testSchwartzOn φ x

/-- The standard coordinate-space formulation of smoothness, using ordinary
Lebesgue pairings with the original LF tests. -/
def CoordinateSmoothOn {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    (u : ScalarDistribution 𝕜 Ω) (V : Set (Domain d)) : Prop :=
  ∃ f : Domain d → 𝕜, ContDiffOn ℝ ∞ f V ∧
    ∀ φ : Tests 𝕜 Ω, tsupport φ ⊆ V →
      Integrable (fun x => f x * φ x) ∧ u φ = ∫ x, f x * φ x

end ExpandedFA.Sobolev.Elliptic
namespace Specs.ExpandedFA.Sobolev.LocalEllipticRegularity
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.Sobolev.Elliptic

def regularityType (𝕜 : Type) [RCLike 𝕜] : Prop := ∀ (d m : ℕ)
    (c : Coefficients 𝕜 d), IsElliptic c m → ∀ (Ω : Opens (Domain d))
    (u : ScalarDistribution 𝕜 Ω),
  DistributionSmoothOn (localOperator c u) Ω → DistributionSmoothOn u Ω

/-- The source theorem in the original coordinate-space distribution model. -/
def nativeRegularityType (𝕜 : Type) [RCLike 𝕜] : Prop := ∀ (d m : ℕ)
    (c : Coefficients 𝕜 d), IsElliptic c m → ∀ (Ω : Opens (Domain d))
    (u : ScalarDistribution 𝕜 Ω),
  CoordinateSmoothOn (localOperator c u) Ω → CoordinateSmoothOn u Ω

/-- Complex scalar-linear local elliptic regularity. -/
def complexRegularityType : Prop := nativeRegularityType ℂ

/-- Real scalar-linear local elliptic regularity. -/
def realRegularityType : Prop := nativeRegularityType ℝ

end Specs.ExpandedFA.Sobolev.LocalEllipticRegularity
