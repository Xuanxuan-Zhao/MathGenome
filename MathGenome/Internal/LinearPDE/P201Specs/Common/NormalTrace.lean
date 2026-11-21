import MathGenome.Internal.LinearPDE.P201Specs.Common.ExactTrace
import MathGenome.Internal.LinearPDE.P201Specs.Common.SmoothFlux

/-! The C02 normal trace is a continuous dual functional on the physical trace
space. Divergence and Laplacian hypotheses below are actual distributional
equalities. No normal-trace or Green identity is assumed in these definitions. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff InnerProductSpace
namespace P201Specs.NormalTrace

abbrev VectorL2 {n : ℕ} (Ω : Domain n) :=
  MeasureTheory.Lp (Space n) 2 (domainMeasure Ω)

/-- Positive distributional divergence, with the manuscript's sign. -/
def HasDivergence {n : ℕ} (Ω : Domain n) (F : VectorL2 Ω) (d : Lp ℝ Ω 2) : Prop :=
  negativeDivergenceDistribution Ω F = -regularDistribution Ω d

/-- The distributional Laplacian of the actual zero-order Sobolev class. -/
def HasLaplacian {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) (d : Lp ℝ Ω 2) : Prop :=
  distributionLaplacian (regularDistribution Ω (hUnderlying Ω 1 u)) =
    regularDistribution Ω d

/-- A bounded trace and section, retaining the physical boundary values and
actual H¹₀ kernel. Existence is supplied by the upstream exact trace theorem. -/
structure TraceData {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω) where
  trace : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ
  lift : Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1
  smooth : Trace.AgreesWithSmooth trace
  right_inverse : ∀ g, trace (lift g) = g
  kernel : trace.ker = hZeroSubmodule ℝ Ω

/-- Green's first identity, for every H¹ test, defines the weak normal trace. -/
def Pairing {m : ℕ} {Ω : Domain (m + 1)} {hΩ : IsBoundedLipschitzOpen Ω}
    (D : TraceData Ω hΩ) (F : VectorL2 Ω) (d : Lp ℝ Ω 2)
    (τ : HminusHalf Ω hΩ) : Prop :=
  ∀ v : H ℝ Ω 1, τ (D.trace v) =
    ∫ x in Ω, inner ℝ (F x) (hGradient v x) + d x * hUnderlying Ω 1 v x

/-- The domain constant is uniform over all fields and their L² divergences. -/
def ForEveryTraceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (D : TraceData Ω hΩ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : VectorL2 Ω) (d : Lp ℝ Ω 2), HasDivergence Ω F d →
        ∃ τ : HminusHalf Ω hΩ,
          Pairing D F d τ ∧ ‖τ‖ ≤ C * (‖F‖ + ‖d‖) ∧
            ∀ σ : HminusHalf Ω hΩ, Pairing D F d σ → σ = τ

/-- Existence of the trace map and the normal trace, on every domain in scope. -/
def ExistenceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    ∃ D : TraceData Ω hΩ, ∃ C : ℝ, 0 < C ∧
      ∀ (F : VectorL2 Ω) (d : Lp ℝ Ω 2), HasDivergence Ω F d →
        ∃ τ : HminusHalf Ω hΩ,
          Pairing D F d τ ∧ ‖τ‖ ≤ C * (‖F‖ + ‖d‖) ∧
            ∀ σ : HminusHalf Ω hΩ, Pairing D F d σ → σ = τ

/-- The distributional Laplacian hypothesis really supplies the divergence of
the weak gradient; this bridge is needed to apply the normal trace to H¹ data. -/
def GradientDivergenceStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) (d : Lp ℝ Ω 2),
    HasLaplacian Ω u d → HasDivergence Ω (hGradient u) d

/-- Smooth physical fields have actual L² realizations, and their normal trace
is the geometric outward flux on every boundary datum, not just smooth tests.
The dimension m=0 includes the endpoint counting measure. -/
def SmoothAgreementStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    ∃ ν : Space (m + 1) → Space (m + 1),
      SmoothFlux.IsGeometricNormalField Ω ν ∧
      ∀ (D : TraceData Ω hΩ) (U : Set (Space (m + 1)))
        (F₀ : Space (m + 1) → Space (m + 1)),
        IsOpen U → closure (Ω : Set (Space (m + 1))) ⊆ U → ContDiffOn ℝ 1 F₀ U →
        ∃ (F : VectorL2 Ω) (d : Lp ℝ Ω 2),
          (F : Space (m + 1) → Space (m + 1)) =ᵐ[domainMeasure Ω] F₀ ∧
          (d : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] divergence F₀ ∧
          HasDivergence Ω F d ∧
          ∀ τ : HminusHalf Ω hΩ, Pairing D F d τ →
            ∀ g : Hhalf Ω hΩ,
              Integrable (fun x => Trace.inclusion Ω hΩ g x * inner ℝ (F₀ x) (ν x))
                (boundaryMeasure Ω) ∧
              τ g = ∫ x, Trace.inclusion Ω hΩ g x * inner ℝ (F₀ x) (ν x)
                ∂boundaryMeasure Ω

/-- Both weak normal traces exist, and the second Green identity holds for
arbitrary H¹ functions with L² distributional Laplacians. -/
def GreenStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (D : TraceData Ω hΩ) (u v : H ℝ Ω 1) (du dv : Lp ℝ Ω 2),
    HasLaplacian Ω u du → HasLaplacian Ω v dv →
      ∃ τu τv : HminusHalf Ω hΩ,
        Pairing D (hGradient u) du τu ∧ Pairing D (hGradient v) dv τv ∧
        (∫ x in Ω, hUnderlying Ω 1 u x * dv x - hUnderlying Ω 1 v x * du x) =
          τv (D.trace u) - τu (D.trace v)

/-- Explicitly retain the one-dimensional boundary convention. The signed
interval identity is the endpoint outward-flux formula in real coordinates. -/
def EndpointStatement : Prop :=
  (∀ (Ω : Domain 1) (hΩ : IsBoundedLipschitzOpen Ω),
    boundaryMeasure Ω = Measure.count.restrict (frontier (Ω : Set (Space 1))) ∧
      ∀ g : Hhalf Ω hΩ, ‖g‖ = ‖Trace.inclusion Ω hΩ g‖) ∧
  SmoothFlux.IntervalFluxStatement

end P201Specs.NormalTrace
