import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.Truncation
import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.WeakDirichlet

/-! Weak divergence-form comparison, paper.tex, Theorem E04.
All functions and coefficients are real. Bulk assertions require only a
bounded open set; boundary regularity occurs solely in the trace corollary. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Matrix.Norms.Elementwise ENNReal
namespace P201Specs.WeakComparison

/-- The variational expression for −div(A∇u) + cu on actual H¹ classes. -/
def energy {n : ℕ} (Ω : Domain n) (A : Dirichlet.MatrixField n)
    (c : Space n → ℝ) (u v : H ℝ Ω 1) : ℝ :=
  ellipticEnergyForm Ω A u v +
    ∫ x, c x * hUnderlying Ω 1 u x * hUnderlying Ω 1 v x ∂domainMeasure Ω

/-- The manuscript's smooth-test integral: ∫ A∇u·∇φ + cuφ. -/
def testEnergy {n : ℕ} (Ω : Domain n) (A : Dirichlet.MatrixField n)
    (c : Space n → ℝ) (u : H ℝ Ω 1) (φ : Test ℝ Ω) : ℝ :=
  ∫ x, (∑ i, ∑ j, A x i j * hFirstDerivative u j x * gradient φ x i) +
    c x * hUnderlying Ω 1 u x * φ x ∂domainMeasure Ω

/-- A load is evaluated only on compact smooth tests. No continuity of the
load is needed for comparison with a supersolution for the same load. -/
def Subsolution {n : ℕ} (Ω : Domain n) (A : Dirichlet.MatrixField n)
    (c : Space n → ℝ) (f : Test ℝ Ω → ℝ) (u : H ℝ Ω 1) : Prop :=
  ∀ φ : Test ℝ Ω, (∀ x, 0 ≤ φ x) → testEnergy Ω A c u φ ≤ f φ

def Supersolution {n : ℕ} (Ω : Domain n) (A : Dirichlet.MatrixField n)
    (c : Space n → ℝ) (f : Test ℝ Ω → ℝ) (u : H ℝ Ω 1) : Prop :=
  ∀ φ : Test ℝ Ω, (∀ x, 0 ≤ φ x) → f φ ≤ testEnergy Ω A c u φ

/-- Legitimate extension from nonnegative smooth tests to the entire
nonnegative H¹₀ cone, in the full H¹ topology. -/
def TestExtensionStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (A : Dirichlet.MatrixField n),
    MemLp A ∞ (domainMeasure Ω) → ∀ c : Space n → ℝ,
    MemLp c ∞ (domainMeasure Ω) → ∀ u : H ℝ Ω 1,
    Subsolution Ω A c (fun _ => 0) u →
    ∀ w : H10 ℝ Ω, (∀ᵐ x ∂domainMeasure Ω, 0 ≤ hZeroUnderlying Ω w x) →
      energy Ω A c u w.val ≤ 0

def MaximumStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ Ω : Domain n,
    Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ A : Dirichlet.MatrixField n, MemLp A ∞ (domainMeasure Ω) →
    ∀ lam : ℝ, 0 < lam → Dirichlet.Elliptic Ω A lam →
    ∀ c : Space n → ℝ, MemLp c ∞ (domainMeasure Ω) →
    (∀ᵐ x ∂domainMeasure Ω, 0 ≤ c x) →
    ∀ u : H ℝ Ω 1, Truncation.positivePart Ω u ∈ hZeroSubmodule ℝ Ω →
    Subsolution Ω A c (fun _ => 0) u →
    ∀ᵐ x ∂domainMeasure Ω, hUnderlying Ω 1 u x ≤ 0

def ComparisonStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ Ω : Domain n,
    Bornology.IsBounded (Ω : Set (Space n)) →
    ∀ A : Dirichlet.MatrixField n, MemLp A ∞ (domainMeasure Ω) →
    ∀ lam : ℝ, 0 < lam → Dirichlet.Elliptic Ω A lam →
    ∀ c : Space n → ℝ, MemLp c ∞ (domainMeasure Ω) →
    (∀ᵐ x ∂domainMeasure Ω, 0 ≤ c x) →
    ∀ (f : Test ℝ Ω → ℝ) (u v : H ℝ Ω 1),
    Truncation.positivePart Ω (u - v) ∈ hZeroSubmodule ℝ Ω →
    Subsolution Ω A c f u → Supersolution Ω A c f v →
    ∀ᵐ x ∂domainMeasure Ω, hUnderlying Ω 1 u x ≤ hUnderlying Ω 1 v x

/-- The trace is the physical surface-measure trace, and any trace agreeing
with smooth restrictions can be used. Dimension one is included. -/
def OrderedTraceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth T →
    ∀ A : Dirichlet.MatrixField (m + 1), MemLp A ∞ (domainMeasure Ω) →
    ∀ lam : ℝ, 0 < lam → Dirichlet.Elliptic Ω A lam →
    ∀ c : Space (m + 1) → ℝ, MemLp c ∞ (domainMeasure Ω) →
    (∀ᵐ x ∂domainMeasure Ω, 0 ≤ c x) →
    ∀ (f : Test ℝ Ω → ℝ) (u v : H ℝ Ω 1),
    (∀ᵐ x ∂boundaryMeasure Ω,
      Trace.inclusion Ω hΩ (T u) x ≤ Trace.inclusion Ω hΩ (T v) x) →
    Subsolution Ω A c f u → Supersolution Ω A c f v →
    ∀ᵐ x ∂domainMeasure Ω, hUnderlying Ω 1 u x ≤ hUnderlying Ω 1 v x

end P201Specs.WeakComparison
