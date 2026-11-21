import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
Independent statements for the Euclidean assertion of
`fa2:p5:weakly-singular-kernel`, paper.tex:21765–21788.

The measure on G is the pullback of ambient Lebesgue measure by the subtype
inclusion (equivalently, restricted Lebesgue measure transported to G).
There is no positive-dimension, nonempty-interior or positive-mass hypothesis.
The diagonal values are unrestricted; in positive dimension they are null in
each section, and in dimension zero the full operator is finite dimensional.
The added constant M allows every bounded remainder that is continuous off
the diagonal, by the triangle inequality. No regularity of the boundary of G
is assumed. The surface assertion is allocated to a separate goal.
-/

open MeasureTheory
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartV.WeaklySingularEuclidean

abbrev Euclidean (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Lebesgue measure on a compact subset, including a singleton in dimension 0. -/
noncomputable def domainMeasure {d : ℕ} (G : Set (Euclidean d)) : Measure G :=
  volume.comap (Subtype.val : G → Euclidean d)

/-- Off-diagonal continuity and the power bound, allowing a bounded remainder. -/
def Admissible {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (G : Set (Euclidean d)) (k : G × G → 𝕜) (α : ℝ) (C M : ℝ≥0) : Prop :=
  ContinuousOn k {z | z.1 ≠ z.2} ∧
  ∀ x y : G, x ≠ y → ‖k (x,y)‖ ≤ C * dist x y ^ (α - d) + M

/-- Both compact operators use the source's actual integral formula.
For continuous inputs absolute existence holds at every point; for Lp inputs
it holds a.e. This includes p=1 and p=∞, for both scalar fields. -/
def CompactIntegralMaps {X 𝕜 : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (k : X × X → 𝕜) : Prop :=
  (∃ T : C(X, 𝕜) →L[𝕜] C(X, 𝕜), IsCompactOperator T ∧
    ∀ f x, Integrable (fun y => k (x,y) * f y) μ ∧
      T f x = ∫ y, k (x,y) * f y ∂μ) ∧
  (∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ, IsCompactOperator T ∧
      ∀ f : Lp 𝕜 p μ,
        (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) μ) ∧
        (T f : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * f y ∂μ)

/-- A measurable representative will be obtained by setting diagonal values
 to zero. This does not alter any section integral in positive dimension. -/
noncomputable def zeroDiagonal {X 𝕜 : Type*} [Zero 𝕜]
    (k : X × X → 𝕜) (z : X × X) : 𝕜 := by
  classical
  exact if z.1 = z.2 then 0 else k z

/-- A continuous scalar cutoff: zero at distances ≤ δ, one at distances ≥ 2δ. -/
noncomputable def cutoffProfile (δ t : ℝ) : ℝ := max 0 (min 1 (t / δ - 1))

noncomputable def cutoffKernel {X 𝕜 : Type*} [PseudoMetricSpace X] [RCLike 𝕜]
    (δ : ℝ) (k : X × X → 𝕜) (z : X × X) : 𝕜 :=
  cutoffProfile δ (dist z.1 z.2) • k z

/-- Approximation by continuous kernels in uniform row and column L¹ norms.
The row bounds are pointwise, as required for the operator on C(X). -/
def UniformKernelApproximation {X 𝕜 : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [RCLike 𝕜] (μ : Measure X) (k : X × X → 𝕜) : Prop :=
  (∃ A : ℝ≥0, (∀ x, ∫⁻ y, ‖k (x,y)‖ₑ ∂μ ≤ A) ∧
    (∀ y, ∫⁻ x, ‖k (x,y)‖ₑ ∂μ ≤ A)) ∧
  ∃ (h : ℕ → C(X × X, 𝕜)) (e : ℕ → ℝ≥0),
    Filter.Tendsto e Filter.atTop (𝓝 0) ∧
    ∀ n, (∀ x, ∫⁻ y, ‖k (x,y) - h n (x,y)‖ₑ ∂μ ≤ e n) ∧
      (∀ y, ∫⁻ x, ‖k (x,y) - h n (x,y)‖ₑ ∂μ ≤ e n)

namespace Spec

/-- Analytic approximation underlying the positive-dimensional assertion. -/
def UniformCutoffApproximation : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type*) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (G : Set (Euclidean d)) (hG : IsCompact G) (k : G × G → 𝕜)
    (α : ℝ) (C M : ℝ≥0), 0 < α → Admissible G k α C M →
      Measurable (zeroDiagonal k) ∧
      UniformKernelApproximation (domainMeasure G) (zeroDiagonal k)

/-- Full original Euclidean conclusion, including an off-diagonal-continuous
bounded remainder. This is an unassumed proposition, not a certificate. -/
def EuclideanCompactness : Prop :=
  ∀ (d : ℕ) (𝕜 : Type*) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (G : Set (Euclidean d)) (hG : IsCompact G) (k : G × G → 𝕜)
    (α : ℝ) (C M : ℝ≥0), 0 < α → Admissible G k α C M →
    letI : CompactSpace G := isCompact_iff_compactSpace.mp hG
    CompactIntegralMaps (domainMeasure G) k

/-- In dimension zero no condition at all on the kernel is necessary. -/
def ZeroDimensionalCompactness : Prop :=
  ∀ (𝕜 : Type*) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (G : Set (Euclidean 0)) (hG : IsCompact G) (k : G × G → 𝕜),
    letI : CompactSpace G := isCompact_iff_compactSpace.mp hG
    CompactIntegralMaps (domainMeasure G) k

def DiagonalRemoval : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d) (𝕜 : Type*) [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (G : Set (Euclidean d)) (_hG : IsCompact G) (k : G × G → 𝕜),
    ContinuousOn k {z | z.1 ≠ z.2} →
      Measurable (zeroDiagonal k) ∧
      (∀ x : G, (fun y => k (x,y)) =ᵐ[domainMeasure G]
        fun y => zeroDiagonal k (x,y)) ∧
      (∀ y : G, (fun x => k (x,y)) =ᵐ[domainMeasure G]
        fun x => zeroDiagonal k (x,y))

def RadialMajorantLocalIntegrability : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (α : ℝ), 0 < α → ∀ (C M : ℝ),
    LocallyIntegrable (fun x : Euclidean d => C * ‖x‖ ^ (α - d) + M) volume

def CutoffContinuity : Prop :=
  ∀ {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    (k : X × X → 𝕜), ContinuousOn k {z | z.1 ≠ z.2} →
    ∀ δ : ℝ, 0 < δ → Continuous (cutoffKernel δ k)

end Spec
end ExpandedFA.PartV.WeaklySingularEuclidean
