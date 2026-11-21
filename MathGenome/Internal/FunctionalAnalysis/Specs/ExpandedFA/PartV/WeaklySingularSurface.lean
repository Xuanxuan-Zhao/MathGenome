import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeaklySingularEuclidean
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Hausdorff

/-! The surface part of `fa2:p5:weakly-singular-kernel`, paper.tex:21777–21808.

A local graph is expressed by a C¹ parametrization with a continuous linear
coordinate projection as its left inverse. Requiring the surface to be locally
contained in such graphs also allows graph pieces with boundary. In particular
it includes the usual embedded C¹ surfaces, without any choice of global chart.
The measure is normalized Hausdorff measure on the original surface, not a
measure supplied together with an assumed growth or integral certificate.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartV.WeaklySingularSurface
open WeaklySingularEuclidean (Euclidean CompactIntegralMaps UniformKernelApproximation)

/-- A C¹ graph chart, with its origin at the point under consideration. The
linear coordinate map need not be orthogonal or have norm one. -/
structure C1GraphPatch (n d : ℕ) (x : Euclidean d) where
  source : Set (Euclidean n)
  open_source : IsOpen source
  zero_mem : (0 : Euclidean n) ∈ source
  param : Euclidean n → Euclidean d
  coord : Euclidean d →L[ℝ] Euclidean n
  param_zero : param 0 = x
  smooth : ContDiffOn ℝ 1 param source
  coord_param : ∀ u ∈ source, coord (param u - x) = u

/-- The ordinary local graph condition, in a form also covering compact pieces
of C¹ surfaces. A neighborhood relative to S is contained in the graph. -/
def LocallyContainedInC1Graphs (n : ℕ) {d : ℕ} (S : Set (Euclidean d)) : Prop :=
  ∀ x ∈ S, ∃ g : C1GraphPatch n d x, g.param '' g.source ∈ 𝓝[S] x

/-- The conventional factor ωₙ / 2ⁿ for diameter-defined Hausdorff measure.
In dimension zero this is one and surface measure is counting measure. -/
noncomputable def surfaceNormalization (n : ℕ) : ℝ≥0 :=
  (volume (Metric.ball (0 : Euclidean n) 1)).toNNReal / 2 ^ n

/-- Surface area on S, transported to its subtype. In positive dimension this
is the usual normalized n-dimensional Hausdorff measure (Euclidean surface
area); in dimension zero it is counting measure. -/
noncomputable def surfaceMeasure (n : ℕ) {d : ℕ} (S : Set (Euclidean d)) : Measure S :=
  surfaceNormalization n •
    (Measure.hausdorffMeasure (n : ℝ)).comap (Subtype.val : S → Euclidean d)

/-- The full kernel hypothesis; M permits a bounded remainder continuous off
the diagonal. Diagonal values are arbitrary. -/
def Admissible (n : ℕ) {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (S : Set (Euclidean d)) (k : S × S → 𝕜) (α : ℝ) (C M : ℝ≥0) : Prop :=
  ContinuousOn k {z | z.1 ≠ z.2} ∧
    ∀ x y : S, x ≠ y → ‖k (x,y)‖ ≤ C * dist x y ^ (α - n) + M

/-- Uniform integrability of the power majorant on shrinking diagonal strips.
This is an analytic intermediate property, not part of the surface definition.
The zero value on the diagonal avoids imposing a convention for 0^negative. -/
noncomputable def radialBound {X : Type*} [MetricSpace X]
    (n : ℕ) (α : ℝ) (C M : ℝ≥0) (x y : X) : ℝ≥0∞ := by
  classical
  exact if x = y then 0 else ENNReal.ofReal (C * dist x y ^ (α - n) + M)

def UniformRadialSmallness {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : Measure X) (n : ℕ) (α : ℝ) (C M : ℝ≥0) : Prop :=
  ∃ b : ℝ → ℝ≥0,
    Tendsto b (𝓝[>] 0) (𝓝 0) ∧
    ∀ r : ℝ, 0 < r → ∀ x : X,
      ∫⁻ y in Metric.ball x r,
        radialBound n α C M x y ∂μ ≤ b r

namespace Spec

/-- The complete source conclusion, with actual surface area and kernel
integrals, on C(S) and every Lp including both endpoints and both fields. -/
def SurfaceCompactness : Prop :=
  ∀ (n d : ℕ) (𝕜 : Type*) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (S : Set (Euclidean d)) (hS : IsCompact S),
    LocallyContainedInC1Graphs n S → ∀ (k : S × S → 𝕜)
    (α : ℝ) (C M : ℝ≥0), 0 < α → Admissible n S k α C M →
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    CompactIntegralMaps (surfaceMeasure n S) k

/-- Surface area is finite, derived from compactness and the C¹ graphs. -/
def SurfaceMeasureFinite : Prop :=
  ∀ (n d : ℕ) (S : Set (Euclidean d)), IsCompact S →
    LocallyContainedInC1Graphs n S → IsFiniteMeasure (surfaceMeasure n S)

/-- The geometric estimate required by the singular-kernel argument. -/
def SurfaceBallGrowth : Prop :=
  ∀ (n d : ℕ), 0 < n → ∀ (S : Set (Euclidean d)), IsCompact S →
    LocallyContainedInC1Graphs n S →
    ∃ A : ℝ≥0, ∀ (x : S) (r : ℝ), 0 < r →
      surfaceMeasure n S (Metric.ball x r) ≤ ENNReal.ofReal (A * r ^ n)

/-- Zero-dimensional surfaces are finite, without an a priori finiteness
assumption or a positive-dimension restriction on the main theorem. -/
def ZeroDimensionalFiniteness : Prop :=
  ∀ (d : ℕ) (S : Set (Euclidean d)), IsCompact S →
    LocallyContainedInC1Graphs 0 S → S.Finite

def ZeroDimensionalCompactness : Prop :=
  ∀ (d : ℕ) (𝕜 : Type*) [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (S : Set (Euclidean d)) (hS : IsCompact S),
    LocallyContainedInC1Graphs 0 S → ∀ k : S × S → 𝕜,
    letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    CompactIntegralMaps (surfaceMeasure 0 S) k

/-- Analytic reduction on general compact metric spaces: no geometry is
assumed in the compactness argument itself. -/
def CompactnessFromRadialSmallness : Prop :=
  ∀ {X 𝕜 : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (k : X × X → 𝕜) (n : ℕ) (α : ℝ) (C M : ℝ≥0),
    ContinuousOn k {z | z.1 ≠ z.2} →
    (∀ x y, x ≠ y → ‖k (x,y)‖ ≤ C * dist x y ^ (α - n) + M) →
    UniformRadialSmallness μ n α C M → CompactIntegralMaps μ k

/-- The analytic implication is stated independently, so radial smallness is
established from the geometric growth estimate. -/
def RadialSmallnessFromGrowth : Prop :=
  ∀ {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] [NullSingletonClass μ]
    (n : ℕ), 0 < n → ∀ (A : ℝ≥0),
    (∀ (x : X) (r : ℝ), 0 < r → μ (Metric.ball x r) ≤ ENNReal.ofReal (A * r ^ n)) →
    ∀ (α : ℝ) (C M : ℝ≥0), 0 < α → UniformRadialSmallness μ n α C M

end Spec
end ExpandedFA.PartV.WeaklySingularSurface
