import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.Truncation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.Holder

/-! Independent statement of paper.tex, `pde:heat-positive-chain`.
The H¹ trajectory need not belong to H¹₀. Its continuous L² representative
and its H⁻¹ distributional derivative are separate, compatible data. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Topology
namespace P201Specs.OrderedTraceChain

abbrev timeMeasure (T : ℝ) : Measure ℝ := volume.restrict (Ioo 0 T)

/-- The canonical positive part on the actual spatial L² quotient. -/
abbrev positiveL2 {n : ℕ} (Ω : Domain n) : Lp ℝ Ω 2 → Lp ℝ Ω 2 :=
  MeasureTheory.Lp.posPart

/-- A total auxiliary extension into H¹₀, obtained by orthogonal projection
in the full H¹ norm. The theorem asserts that, under the trace sign, this
projection equals the spatial positive part a.e.; no such equality is assumed. -/
def zeroPositive {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) : H10 ℝ Ω :=
  (hZeroSubmodule ℝ Ω).orthogonalProjectionOnto (Truncation.positivePart Ω u)

/-- Distributional differentiation through the L² pivot, with scalar compact
smooth time tests and every fixed H¹₀ spatial test. -/
def HasBulkTimeDerivative {n : ℕ} (Ω : Domain n) (T : ℝ)
    (U : ℝ → Lp ℝ Ω 2) (du : ℝ → Hminus1 ℝ Ω) : Prop :=
  ∀ v : H10 ℝ Ω,
    ∀ φ : TestFunction (⟨Ioo 0 T, isOpen_Ioo⟩ : Opens ℝ) ℝ ⊤,
      (∫ t in Ioo 0 T, deriv φ t * inner ℝ (U t) (hZeroUnderlying Ω v)) =
        -(∫ t in Ioo 0 T, φ t * du t v)

/-- Nonpositive physical Sobolev trace, a.e. in time and boundary measure. -/
def NonpositiveTrace {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ) (w : ℝ → H ℝ Ω 1) (T : ℝ) : Prop :=
  ∀ᵐ t ∂timeMeasure T, ∀ᵐ x ∂boundaryMeasure Ω,
    Trace.inclusion Ω hΩ (tr (w t)) x ≤ 0

/-- Spatial and time-space membership with the exact continuous representative,
and genuine integrability of the H⁻¹,H¹₀ dual pairing. -/
def MembershipStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth tr →
    ∀ (T : ℝ) (w : ℝ → H ℝ Ω 1) (du : ℝ → Hminus1 ℝ Ω)
      (U : ℝ → Lp ℝ Ω 2),
      MemLp w 2 (timeMeasure T) → MemLp du 2 (timeMeasure T) →
      ContinuousOn U (Icc 0 T) →
      (∀ᵐ t ∂timeMeasure T, U t = hUnderlying Ω 1 (w t)) →
      NonpositiveTrace Ω hΩ tr w T →
        MemLp (fun t => zeroPositive Ω (w t)) 2 (timeMeasure T) ∧
        (∀ᵐ t ∂timeMeasure T,
          (zeroPositive Ω (w t)).val = Truncation.positivePart Ω (w t)) ∧
        ContinuousOn (fun t => positiveL2 Ω (U t)) (Icc 0 T) ∧
        (∀ᵐ t ∂timeMeasure T,
          hZeroUnderlying Ω (zeroPositive Ω (w t)) = positiveL2 Ω (U t)) ∧
        Integrable (fun t => du t (zeroPositive Ω (w t))) (timeMeasure T)

def PositiveL2ContractionStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n), LipschitzWith 1 (positiveL2 Ω)

def TimeContinuityStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (T : ℝ) (w : ℕ → ℝ → H ℝ Ω 1) (v : ℝ → H ℝ Ω 1),
    (∀ k, MemLp (w k) 2 (timeMeasure T)) → MemLp v 2 (timeMeasure T) →
    Filter.Tendsto (fun k => eLpNorm (w k - v) 2 (timeMeasure T)) Filter.atTop (𝓝 0) →
    Filter.Tendsto (fun k => eLpNorm
      (fun t => Truncation.positivePart Ω (w k t) - Truncation.positivePart Ω (v t))
      2 (timeMeasure T)) Filter.atTop (𝓝 0)

/-- Local graph regularization with a nonnegative time kernel. This is a
construction obligation, not part of the original hypotheses. The derivative
of each approximant is the actual L² pivot of its H¹-valued derivative. -/
def LocalRegularizationStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth tr →
    ∀ (T : ℝ), 0 < T →
    ∀ (w : ℝ → H ℝ Ω 1) (du : ℝ → Hminus1 ℝ Ω) (U : ℝ → Lp ℝ Ω 2),
      MemLp w 2 (timeMeasure T) → MemLp du 2 (timeMeasure T) →
      ContinuousOn U (Icc 0 T) →
      (∀ᵐ t ∂timeMeasure T, U t = hUnderlying Ω 1 (w t)) →
      HasBulkTimeDerivative Ω T U du → NonpositiveTrace Ω hΩ tr w T →
      ∀ a b : ℝ, 0 < a → a < b → b < T →
        ∃ F : ℕ → ℝ → H ℝ Ω 1,
          (∀ k, ContDiff ℝ 1 (F k)) ∧
          (∀ k r, r ∈ Icc a b → ∀ᵐ x ∂boundaryMeasure Ω,
            Trace.inclusion Ω hΩ (tr (F k r)) x ≤ 0) ∧
          (∀ k, MemLp (F k) 2 (volume.restrict (Ioc a b))) ∧
          (∀ k, MemLp (fun r => pivot Ω (hUnderlying Ω 1 (deriv (F k) r)))
            2 (volume.restrict (Ioc a b))) ∧
          Filter.Tendsto (fun k => eLpNorm (F k - w) 2 (volume.restrict (Ioc a b)))
            Filter.atTop (𝓝 0) ∧
          Filter.Tendsto (fun k => eLpNorm
            (fun r => pivot Ω (hUnderlying Ω 1 (deriv (F k) r)) - du r)
              2 (volume.restrict (Ioc a b))) Filter.atTop (𝓝 0) ∧
          ∀ r ∈ Icc a b, Filter.Tendsto (fun k => hUnderlying Ω 1 (F k r))
            Filter.atTop (𝓝 (U r))

/-- The full ordered-trace time chain rule, including both endpoints, all
positive dimensions, and the precise continuous L² representative. -/
def FullStatement : Prop :=
  MembershipStatement ∧
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth tr →
    ∀ (T : ℝ), 0 < T →
    ∀ (w : ℝ → H ℝ Ω 1) (du : ℝ → Hminus1 ℝ Ω) (U : ℝ → Lp ℝ Ω 2),
      MemLp w 2 (timeMeasure T) → MemLp du 2 (timeMeasure T) →
      ContinuousOn U (Icc 0 T) →
      (∀ᵐ t ∂timeMeasure T, U t = hUnderlying Ω 1 (w t)) →
      HasBulkTimeDerivative Ω T U du → NonpositiveTrace Ω hΩ tr w T →
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        (1 / 2 : ℝ) * ‖positiveL2 Ω (U t)‖ ^ 2 -
          (1 / 2 : ℝ) * ‖positiveL2 Ω (U s)‖ ^ 2 =
            ∫ r in Ioc s t, du r (zeroPositive Ω (w r))

/-- Separates the remaining regularization construction from the final
membership, classical-chain, strong-limit and endpoint arguments. -/
def AssemblyStatement : Prop := LocalRegularizationStatement → FullStatement

end P201Specs.OrderedTraceChain
