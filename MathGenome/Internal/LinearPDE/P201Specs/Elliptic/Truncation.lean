import MathGenome.Internal.LinearPDE.P201Specs.Common.ExactTrace
import MathGenome.Internal.FourierSobolev.P102.U4.Truncations

/-! Positive parts and nonnegative test approximation in the concrete, full-norm
real H¹ spaces. These specifications impose no boundary regularity on bulk
truncation or H¹₀ density. The trace clauses use the physical trace of C02. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology
namespace P201Specs.Truncation

/-- The canonical positive-part Sobolev class supplied by the proved weak
truncation theorem, transferred without changing derivative coordinates. -/
def positivePart {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) : H ℝ Ω 1 :=
  (hToW ℝ Ω 1).symm
    (P102.U4.lower_truncation_rule Ω 2 (hToW ℝ Ω 1 u) 0 (Or.inl le_rfl)).choose

/-- Canonical inclusion of a compact smooth test in full-norm H¹. -/
def testToH {n : ℕ} (Ω : Domain n) (φ : Test ℝ Ω) : H ℝ Ω 1 :=
  (hToW ℝ Ω 1).symm (P102.U4.zeroExtension_smoothInclusion Ω 1 2 φ).choose

abbrev PositivePartType := {n : ℕ} → (Ω : Domain n) → H ℝ Ω 1 → H ℝ Ω 1
abbrev TestToHType := {n : ℕ} → (Ω : Domain n) → Test ℝ Ω → H ℝ Ω 1

/-- Membership and the precise strict-positive gradient formula, on every
open set and without a finite-volume assumption. -/
def PositivePartStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1),
    ((hUnderlying Ω 1 (positivePart Ω u) : Space n → ℝ) =ᵐ[domainMeasure Ω]
      fun x => max (hUnderlying Ω 1 u x) 0) ∧
    ∀ᵐ x ∂domainMeasure Ω,
      hGradient (positivePart Ω u) x =
        if 0 < hUnderlying Ω 1 u x then hGradient u x else 0

/-- The gradient of the original function vanishes on its zero level set. -/
def ZeroLevelStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1),
    ∀ᵐ x ∂domainMeasure Ω, hUnderlying Ω 1 u x = 0 → hGradient u x = 0

/-- Continuity for the full H¹ topology, not only its zero-order L² term. -/
def ContinuityStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n), Continuous (positivePart Ω)

/-- Every C02 trace commutes with positive part, as equality of actual
surface-measure classes. Its existence and kernel are established upstream. -/
def TraceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth T →
    ∀ u : H ℝ Ω 1,
      (Trace.inclusion Ω hΩ (T (positivePart Ω u)) : Space (m + 1) → ℝ)
        =ᵐ[boundaryMeasure Ω]
      fun x => max (Trace.inclusion Ω hΩ (T u) x) 0

/-- Ordered traces make the positive part of the difference an actual
member of the closure H¹₀. No boundary order is imposed on bulk representatives. -/
def OrderedTraceStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)
    (T : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ), Trace.AgreesWithSmooth T →
    ∀ u v : H ℝ Ω 1,
      (∀ᵐ x ∂boundaryMeasure Ω,
        Trace.inclusion Ω hΩ (T u) x ≤ Trace.inclusion Ω hΩ (T v) x) →
      positivePart Ω (u - v) ∈ hZeroSubmodule ℝ Ω

/-- Pointwise nonnegative compact smooth tests approximate every nonnegative
H¹₀ class in the full H¹ norm, on arbitrary open sets. -/
def NonnegativeDensityStatement : Prop :=
  ∀ {n : ℕ} (Ω : Domain n) (u : H10 ℝ Ω),
    (∀ᵐ x ∂domainMeasure Ω, 0 ≤ hZeroUnderlying Ω u x) →
    ∃ φ : ℕ → Test ℝ Ω,
      (∀ k x, 0 ≤ φ k x) ∧
      Tendsto (fun k => testToH Ω (φ k)) atTop (𝓝 u.val)

def FullStatement : Prop :=
  PositivePartStatement ∧ ZeroLevelStatement ∧ ContinuityStatement ∧
    TraceStatement ∧ OrderedTraceStatement ∧ NonnegativeDensityStatement

end P201Specs.Truncation
