import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent specification of the Lp clause of `fa2:p3:heat-poisson`,
paper.tex:15865–15902. Coordinates carry product Lebesgue measure. Their
Banach norm is immaterial: the Gaussian uses the Euclidean squared length
`∑ i, (x i)^2`, not the supremum norm on the coordinate type.
Both scalar fields, all natural dimensions and p = 1 are retained. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace ExpandedFA.Models.HeatLp

abbrev Space (d : ℕ) := Fin d → ℝ
abbrev Test (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :=
  Distributions.Tests 𝕜 (⊤ : TopologicalSpace.Opens (Space d))
abbrev ScalarLp (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (p : ℝ≥0∞) :=
  Lp 𝕜 p (volume : Measure (Space d))

/-- The formula is used at positive times only. Time zero is the identity,
not the integral against the value obtained by substituting zero here. -/
def gaussian {d : ℕ} (t : ℝ) (x : Space d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
    Real.exp (-(∑ i, (x i) ^ 2) / (4 * t))

/-- The scalar-linear pairing has no complex conjugation. -/
def heatConvolution {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (t : ℝ) (f : Space d → 𝕜) (x : Space d) : 𝕜 :=
  ∫ y, gaussian t y • f (x - y)

/-- The ordinary Laplacian of a compactly supported smooth test. -/
def testLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ} : Test 𝕜 d →L[𝕜] Test 𝕜 d :=
  ∑ i : Fin d, Distributions.testPartialCLM [i, i]

/-- Coordinate formula on ordinary functions, used to interface with analytic
proofs stated without bundled test functions. -/
def rawLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Space d → 𝕜) (x : Space d) : 𝕜 :=
  ∑ i : Fin d, fderiv ℝ (fun y =>
    fderiv ℝ φ y (Distributions.coordinateVector i)) x (Distributions.coordinateVector i)

/-- Δf = g in distributions. Both functions are actual Lp classes; their
products with these tests are integrable by local integrability and compact
support, including at p = 1. The sign of a second derivative is positive. -/
def WeakLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞}
    (f g : ScalarLp 𝕜 d p) : Prop :=
  ∀ φ : Test 𝕜 d,
    (∫ x, f x * testLaplacian φ x) = ∫ x, g x * φ x

/-- The same distributional equation using unbundled smooth tests. -/
def RawWeakLaplacian {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞}
    (f g : ScalarLp 𝕜 d p) : Prop :=
  ∀ φ : Space d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x, f x * rawLaplacian φ x) = ∫ x, g x * φ x

/-- Positive-time identification fixes the kernel action on the a.e. quotient. -/
def IsHeatSemigroup {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p)) : Prop :=
  ∀ (t : ℝ≥0), 0 < t → ∀ f : ScalarLp 𝕜 d p,
    T.operators t f =ᵐ[volume] heatConvolution (t : ℝ) f

namespace Spec

/-- Full original obligation. The equivalence identifies the entire graph,
so it proves both the maximal domain and the value of the generator. -/
def HeatLpResult : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∃ T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p),
    IsHeatSemigroup T ∧
    (∀ t : ℝ≥0, ‖T.operators t‖ ≤ 1) ∧
    ∀ f g : ScalarLp 𝕜 d p,
      Semigroups.C0SemigroupSpec.hasGeneratorLimitValue T f g ↔ WeakLaplacian f g

def GaussianProperties : Prop := ∀ (d : ℕ) (t : ℝ), 0 < t →
  Integrable (gaussian (d := d) t) volume ∧
  (∫ x : Space d, gaussian t x) = 1 ∧ ∀ x : Space d, 0 ≤ gaussian t x

def HeatConvolutionBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞), 1 ≤ p → ∀ (t : ℝ), 0 < t →
    ∀ f : Space d → 𝕜, MemLp f p volume →
  (∀ᵐ x ∂(volume : Measure (Space d)), Integrable (fun y : Space d => gaussian t y • f (x - y))) ∧
  MemLp (heatConvolution t f) p volume ∧
  eLpNorm (heatConvolution t f) p volume ≤ eLpNorm f p volume

/-- Analytic construction subproblem; no generator assertion is assumed. -/
def HeatSemigroupExistence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∃ T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p),
    IsHeatSemigroup T ∧ ∀ t : ℝ≥0, ‖T.operators t‖ ≤ 1

/-- Forward graph inclusion, required for the actual kernel semigroup. -/
def GeneratorDistributionInclusion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ T : Semigroups.C0Semigroup 𝕜 (ScalarLp 𝕜 d p), IsHeatSemigroup T →
  ∀ f g : ScalarLp 𝕜 d p,
    Semigroups.C0SemigroupSpec.hasGeneratorLimitValue T f g → WeakLaplacian f g

/-- Only λ = 1 is needed for maximality; this is the homogeneous elliptic
uniqueness lemma, not the full domain equality in disguise. -/
def EllipticUniqueness : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
  ∀ f : ScalarLp 𝕜 d p, WeakLaplacian f f → f = 0

def TestLaplacianFormula : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (φ : Test 𝕜 d) (x : Space d), testLaplacian φ x = rawLaplacian φ x

def RawWeakLaplacianBridge : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) (f g : ScalarLp 𝕜 d p), WeakLaplacian f g ↔ RawWeakLaplacian f g

/-- Algebraic maximality from a genuine two-sided resolvent and uniqueness
in a larger linear graph. -/
def ResolventGraphCriterion : Prop :=
  ∀ {𝕜 X : Type} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (A : Unbounded.Operator 𝕜 X X) (G : Submodule 𝕜 (X × X)) (ζ : 𝕜),
    Unbounded.ResolventInverse A ζ → A.graph ≤ G →
    (∀ x : X, (x, ζ • x) ∈ G → x = 0) → A.graph = G

/-- A proved assembly target is useful independently of the three
analytic statements. These are explicit obligations, never extra hypotheses
of the original HeatLpResult. -/
def Assembly : Prop := HeatSemigroupExistence → GeneratorDistributionInclusion →
  EllipticUniqueness → HeatLpResult

end Spec
end ExpandedFA.Models.HeatLp
