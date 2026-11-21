import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakEntireLiouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
Independent statements for `fa2:p1:frechet-holomorphy`, paper.tex:2183–2220.
The target has its original Hausdorff locally convex topology, with translation
completeness and metrizability supplied by the shared `FrechetSpace` definition.
In particular, no norm on the target is assumed.

Complex differentiability into a TVS is convergence of complex difference
quotients in its given topology. Taylor convergence is uniform on smaller
closed disks in every continuous seminorm; thus it covers every choice of
defining seminorms. The coefficients are identified by all scalar Taylor
coefficients. Contour integration uses the Pettis characterization: each
scalar test is circle-integrable and its integral is the test of a single
vector in the original target. The conclusion specifies that vector, so
existence in the target is a conclusion, not a hypothesis.
-/

open Set Filter
open scoped Topology

namespace ExpandedFA.P1.FrechetHolomorphySpec

universe u

section Definitions
variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

def WeakHolomorphicOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ ℓ : E →L[ℂ] ℂ, DifferentiableOn ℂ (fun z => ℓ (f z)) Ω

def HolomorphicOn (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ z ∈ Ω, ∃ v : E,
    Tendsto (fun w : ℂ => (w - z)⁻¹ • (f w - f z)) (𝓝[≠] z) (𝓝 v)

def HasPettisCircleIntegral (g : ℂ → E) (c : ℂ) (r : ℝ) (v : E) : Prop :=
  ∀ ℓ : E →L[ℂ] ℂ,
    CircleIntegrable (fun ζ => ℓ (g ζ)) c r ∧
      circleIntegral (fun ζ => ℓ (g ζ)) c r = ℓ v

def CauchyFormulas (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → Metric.closedBall c r ⊆ Ω →
    ∀ z ∈ Metric.ball c r,
      HasPettisCircleIntegral (fun ζ => (ζ - z)⁻¹ • f ζ) c r
        ((2 * Real.pi * Complex.I : ℂ) • f z)

def TaylorExpansionOnDisk (f : ℂ → E) (c : ℂ) (r : ℝ) (a : ℕ → E) : Prop :=
  (∀ (ℓ : E →L[ℂ] ℂ) (n : ℕ),
    ℓ (a n) = (n.factorial : ℂ)⁻¹ * iteratedDeriv n (fun z => ℓ (f z)) c) ∧
  (∀ (p : Seminorm ℂ E), Continuous p → ∀ ρ : ℝ, 0 ≤ ρ → ρ < r →
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ Metric.closedBall c ρ,
      p (f z - ∑ k ∈ Finset.range n, (z - c) ^ k • a k) < ε) ∧
  (∀ z ∈ Metric.ball c r,
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, (z - c) ^ k • a k)
      atTop (𝓝 (f z))) ∧
  (∀ n : ℕ,
    HasPettisCircleIntegral (fun ζ => ((ζ - c) ^ (n + 1))⁻¹ • f ζ) c r
      ((2 * Real.pi * Complex.I : ℂ) • a n))

def LocalTaylorSeries (f : ℂ → E) (Ω : Set ℂ) : Prop :=
  ∀ c ∈ Ω, ∃ r : ℝ, 0 < r ∧ Metric.closedBall c r ⊆ Ω ∧
    ∃ a : ℕ → E, TaylorExpansionOnDisk f c r a

end Definitions

/-- The continuity clause, also valid without completeness or metrizability. -/
def WeakHolomorphyContinuity : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [TopologicalSpace E] [T2Space E],
    LCS ℂ E → ∀ (Ω : Set ℂ), IsOpen Ω → ∀ f : ℂ → E,
      WeakHolomorphicOn f Ω → ContinuousOn f Ω

def WeakHolomorphyDifferentiability : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [TopologicalSpace E],
    FrechetSpace ℂ E → ∀ (Ω : Set ℂ), IsOpen Ω → ∀ f : ℂ → E,
      WeakHolomorphicOn f Ω → HolomorphicOn f Ω

/-- The Cauchy formula as a vector-valued Pettis integral. -/
def WeakCauchyFormulas : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (Ω : Set ℂ) (f : ℂ → E),
      WeakHolomorphicOn f Ω → CauchyFormulas f Ω

/-- The complete Fréchet-space assertion, including the scalar-linear dual. -/
def WeakHolomorphy : Prop :=
  ∀ (E : Type u) [AddCommGroup E] [Module ℂ E] [Module ℝ E]
    [IsScalarTower ℝ ℂ E] [TopologicalSpace E],
    FrechetSpace ℂ E → ∀ (Ω : Set ℂ), IsOpen Ω → ∀ f : ℂ → E,
      WeakHolomorphicOn f Ω →
        ContinuousOn f Ω ∧ HolomorphicOn f Ω ∧
          LocalTaylorSeries f Ω ∧ CauchyFormulas f Ω

/-- The final TVS clause has no local convexity or completeness hypothesis. -/
def WeakEntireConstant : Prop := WeakEntireLiouvilleSpec.WeakEntireConstant.{u}

end ExpandedFA.P1.FrechetHolomorphySpec
