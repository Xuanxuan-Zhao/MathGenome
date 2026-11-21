import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.FourierHilbertScale
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent specification of the smooth-curve clauses of
`fa2:p4:periodic-sobolev`, paper.tex:18015–18051.

The final targets construct complete Sobolev Hilbert spaces of actual intrinsic
scalar distributions at every real order, with exact finite-chart norms,
atlas equivalences and smooth reparametrization isomorphisms over both scalar
fields. Their exact-image conditions identify the original chartwise Sobolev
membership. Supporting targets provide the local estimates and density geometry.
Scalar pullback uses the inverse absolute Jacobian on test densities, with
no orientation choice or complex conjugation. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace ExpandedFA.Sobolev.Curve

/-- For a coordinate map e from x to y, the test density used to pull a scalar
distribution back from y to x. Values outside e.target are immaterial. -/
def inverseDensity {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (φ : ℝ → 𝕜) : ℝ → 𝕜 :=
  fun y => |deriv e.symm y| • φ (e.symm y)

/-- Scalar coordinate pullback with a cutoff, extended by zero off the chart
source. This is a function on the whole line, as required by the local Hs norm. -/
def localizedPullback {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a f : ℝ → 𝕜) : ℝ → 𝕜 :=
  e.source.indicator (fun x => a x * f (e x))

/-- The compactly localized test density transposed by scalar pullback. -/
def localizedDensity {𝕜 : Type*} [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ) (a φ : ℝ → 𝕜) : ℝ → 𝕜 :=
  e.target.indicator (inverseDensity e (a * φ))

end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
open _root_.ExpandedFA.Sobolev.FourierScale
open _root_.ExpandedFA.Fourier

/-- The scalar-density change of variables, including orientation-reversing
maps and empty sources. Differentiability only of the inverse is needed for
this integral identity. Integrals use the native total Bochner convention. -/
def densityPairingType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ),
    (∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) →
    ∀ f φ : ℝ → 𝕜,
      (∫ x in e.source, f (e x) * φ x) =
        ∫ y in e.target, f y * inverseDensity e φ y

/-- Integrability is preserved by the same scalar-density formula. This
separate assertion prevents using the total integral to infer integrability. -/
def densityIntegrabilityType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ),
    (∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) →
    ∀ f φ : ℝ → 𝕜,
      IntegrableOn (fun x => f (e x) * φ x) e.source ↔
        IntegrableOn (fun y => f y * inverseDensity e φ y) e.target

/-- The exact local L² energy transformation is valid even if either side
is infinite. The inverse Jacobian is essential for scalar pullback. -/
def localizedEnergyType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ),
    (∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) → ∀ a f : ℝ → 𝕜,
    (∫⁻ x, ‖localizedPullback e a f x‖ₑ ^ 2) =
      ∫⁻ y in e.target, ENNReal.ofReal |deriv e.symm y| *
        ‖a (e.symm y)‖ₑ ^ 2 * ‖f y‖ₑ ^ 2

/-- A compactly localized scalar coordinate change acts boundedly on the
actual whole-line L² classes. The constant is derived from compactness;
no global derivative or Jacobian bound is imposed on the chart map. This
is the order-zero analytic step, not the all-order curve theorem. -/
def localizedL2Type : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ), ContDiffOn ℝ 1 e.symm e.target →
    ∀ a : ℝ → 𝕜, Continuous a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∃ C : ℝ, 1 ≤ C ∧
      ∃! A : Lp 𝕜 2 (volume : Measure ℝ) →L[𝕜] Lp 𝕜 2 (volume : Measure ℝ),
        ‖A‖ ≤ C ∧ ∀ f : Lp 𝕜 2 (volume : Measure ℝ),
          A f =ᵐ[volume] localizedPullback e a f

/-- Bounded test operators transfer to negative orders by the *linear* dual
pairing, with a uniform bound and uniqueness. The bounded operator A is input
to this helper; the actual coordinate operators are proved bounded separately below.
This helper alone is not an assumption of atlas independence. -/
def negativeTransposeType : Prop := ∀ (d e : ℕ) (s t : ℝ)
    (A : Hs d s →L[ℂ] Hs e t),
    ∃! B : Hs e (-t) →L[ℂ] Hs d (-s),
      (∀ u v, dualPairing (s := s) u (B v) = dualPairing (s := t) (A u) v) ∧ ‖B‖ ≤ ‖A‖

/-- The real form uses the actual Hermitian Fourier subspaces and real
distribution pairing from the accepted Euclidean scale. -/
def realNegativeTransposeType : Prop := ∀ (d e : ℕ) (s t : ℝ)
    (A : RealHs d s →L[ℝ] RealHs e t),
    ∃! B : RealHs e (-t) →L[ℝ] RealHs d (-s),
      (∀ u v, realDualPairing (s := s) u (B v) = realDualPairing (s := t) (A u) v) ∧ ‖B‖ ≤ ‖A‖

/-- When the positive-order operator is an isomorphism its transpose is an
isomorphism as well, with the same bilinear pairing law. -/
def negativeEquivalenceType : Prop := ∀ (d e : ℕ) (s t : ℝ)
    (A : Hs d s ≃L[ℂ] Hs e t),
    ∃ B : Hs e (-t) ≃L[ℂ] Hs d (-s),
      (∀ u v, dualPairing (s := s) u (B v) = dualPairing (s := t) (A u) v) ∧
      ‖B.toContinuousLinearMap‖ ≤ ‖A.toContinuousLinearMap‖ ∧
      ‖B.symm.toContinuousLinearMap‖ ≤ ‖A.symm.toContinuousLinearMap‖

def realNegativeEquivalenceType : Prop := ∀ (d e : ℕ) (s t : ℝ)
    (A : RealHs d s ≃L[ℝ] RealHs e t),
    ∃ B : RealHs e (-t) ≃L[ℝ] RealHs d (-s),
      (∀ u v, realDualPairing (s := s) u (B v) = realDualPairing (s := t) (A u) v) ∧
      ‖B.toContinuousLinearMap‖ ≤ ‖A.toContinuousLinearMap‖ ∧
      ‖B.symm.toContinuousLinearMap‖ ≤ ‖A.symm.toContinuousLinearMap‖

/-- The abstract transpose has the required action on actual distributions,
whenever A sends a represented test φ to a represented test ψ. Thus the
Jacobian-weighted positive test operator, once constructed, determines the
negative-order scalar pullback rather than a different abstract isomorphism. -/
def transposeRealizationType : Prop := ∀ (d e : ℕ) (s t : ℝ)
    (A : Hs d s →L[ℂ] Hs e t) (B : Hs e (-t) →L[ℂ] Hs d (-s)),
    (∀ u v, dualPairing (s := s) u (B v) = dualPairing (s := t) (A u) v) →
    ∀ (φ : Schwartz ℂ d) (ψ : Schwartz ℂ e) (u : Hs d s) (v : Hs e (-t)),
      realization (s := s) u = schwartzRegularDistribution φ →
      realization (s := t) (A u) = schwartzRegularDistribution ψ →
      realization (s := -s) (B v) φ = realization (s := -t) v ψ

def realTransposeRealizationType : Prop := ∀ (d e : ℕ) (s t : ℝ)
    (A : RealHs d s →L[ℝ] RealHs e t)
    (B : RealHs e (-t) →L[ℝ] RealHs d (-s)),
    (∀ u v, realDualPairing (s := s) u (B v) =
      realDualPairing (s := t) (A u) v) →
    ∀ (φ : Schwartz ℝ d) (ψ : Schwartz ℝ e) (u : RealHs d s) (v : RealHs e (-t)),
      realRealization (s := s) u = realSchwartzRegularDistribution φ →
      realRealization (s := t) (A u) = realSchwartzRegularDistribution ψ →
      realRealization (s := -s) (B v) φ = realRealization (s := -t) v ψ

/-- The finite estimate used after writing one atlas localization as a sum of
localized chart transitions from another atlas. Empty index sets are allowed.
The actual chart transitions and their local boundedness are proved separately.
Global distribution synthesis remains a separate step. -/
def finiteLocalizationBoundType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E] (m n : ℕ)
    (a : Fin m → E) (b : Fin n → E) (T : Fin m → Fin n → E →L[𝕜] E),
    (∀ i, a i = ∑ j, T i j (b j)) →
    (∑ i, ‖a i‖) ≤ (∑ i, ∑ j, ‖T i j‖) * ∑ j, ‖b j‖

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales

noncomputable section
open Set ChartedSpace IsManifold Filter
open scoped Topology Manifold ContDiff
universe u
namespace ExpandedFA.Sobolev.Curve
variable (M : Type u) [TopologicalSpace M] [ChartedSpace ℝ M]
/-- A finite smooth chart partition on a boundaryless smooth curve.
No connectedness, orientability or nonemptiness is imposed. -/
structure FiniteChartPartition where
  n : ℕ
  chart : Fin n → OpenPartialHomeomorph M ℝ
  chart_smooth : ∀ i, chart i ∈ maximalAtlas (𝓘(ℝ)) ∞ M
  cutoff : Fin n → C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯
  nonneg : ∀ i x, 0 ≤ cutoff i x
  sum_one : ∀ x, ∑ i, cutoff i x = 1
  subordinate : ∀ i, tsupport (cutoff i) ⊆ (chart i).source


namespace FiniteChartPartition
variable {M}
/-- The genuine coordinate transition from A coordinates to B coordinates. -/
def transition (A B : FiniteChartPartition M) (i : Fin A.n) (j : Fin B.n) :
    OpenPartialHomeomorph ℝ ℝ := (A.chart i).symm.trans (B.chart j)


end FiniteChartPartition
end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve

def finiteChartPartitionType : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M],
    Nonempty (FiniteChartPartition M)

def chartTransitionSmoothType : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] (A B : FiniteChartPartition M)
    (i : Fin A.n) (j : Fin B.n),
    ContDiffOn ℝ ∞ (A.transition B i j) (A.transition B i j).source ∧
    ContDiffOn ℝ ∞ (A.transition B i j).symm (A.transition B i j).target

def overlapCutoffType : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (A B : FiniteChartPartition M) (i : Fin A.n) (j : Fin B.n),
    ∃ f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯,
      (∀ᶠ x in 𝓝ˢ (tsupport (A.cutoff i) ∩ tsupport (B.cutoff j)), f x = 1) ∧
      tsupport f ⊆ (A.chart i).source ∩ (B.chart j).source ∧
      (∀ x, f x ∈ Icc 0 1) ∧ HasCompactSupport f

def chartTestType : Prop :=
  ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (𝕜 : Type*) [RCLike 𝕜] (e : OpenPartialHomeomorph M ℝ),
    e ∈ maximalAtlas (𝓘(ℝ)) ∞ M →
    ∀ f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯, tsupport f ⊆ e.source →
    ∃! φ : TestFunction (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens ℝ) 𝕜 ⊤,
      ∀ y ∈ e.target, φ y = f (e.symm y)

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales

namespace ExpandedFA.Sobolev.Curve
def differenceKernel {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (f : ℝ → E) (x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖f x - f y‖ ^ 2 / |x - y| ^ p)

def differenceEnergy {E : Type*} [NormedAddCommGroup E]
    (p : ℝ) (f : ℝ → E) (s : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ x in s, ∫⁻ y in s, differenceKernel p f x y

end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve _root_.ExpandedFA.Fourier

/-- Exact whole-line scalar-density pairing for a compactly localized coordinate
operation. This is valid for the total Bochner integral, with a separate
integrability theorem retained above. -/
def localizedPairingType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ),
    (∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) → ∀ a f φ : ℝ → 𝕜,
    (∫ x, localizedPullback e a f x * φ x) = ∫ y, f y * localizedDensity e a φ y

/-- Both localized scalar composition and its exact density transpose act
continuously on the actual whole-line Schwartz tests. No global bounds on the
coordinate map outside the compact localization are assumed. -/
def localizedSchwartzType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ),
    ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
    ∀ a : ℝ → 𝕜, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∃ P Q : SchwartzMap ℝ 𝕜 →L[𝕜] SchwartzMap ℝ 𝕜,
      (∀ φ x, P φ x = localizedPullback e a φ x) ∧
      (∀ φ x, Q φ x = localizedDensity e a φ x)

/-- A quantitative coordinate estimate for restricted fractional difference
energies. The stated Lipschitz and Jacobian bounds are hypotheses of this local
analytic helper; the required compact chart estimates and the Fourier/difference-norm
equivalence are derived separately below. -/
def fractionalCoordinateType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ), 0 ≤ p → ∀ (f : ℝ → 𝕜) (e : OpenPartialHomeomorph ℝ ℝ),
    (∀ y ∈ e.target, DifferentiableAt ℝ e.symm y) →
    ∀ L J : ℝ, 0 < L → 0 ≤ J →
    (∀ x ∈ e.source, ∀ y ∈ e.source, |e x - e y| ≤ L * |x-y|) →
    (∀ y ∈ e.target, |deriv e.symm y| ≤ J) →
    differenceEnergy p (f ∘ e) e.source ≤
      ENNReal.ofReal (J ^ 2 * L ^ p) * differenceEnergy p f e.target

/-- Plancherel and Tonelli give the weighted difference-energy identity even
when its value is infinite. In the fractional case w(h)=|h|^(-d-2σ); the scaling
constant and Bessel norm comparison are proved separately below. -/
def weightedDifferenceFourierType : Prop := ∀ (d : ℕ) (f : Euclidean d → ℂ),
    Integrable f → MemLp f 2 → ∀ w : Euclidean d → ENNReal, Measurable w →
    (∫⁻ h, w h * ∫⁻ x, ‖f (x + h) - f x‖ₑ ^ 2) =
      ∫⁻ ξ, (∫⁻ h, w h * ‖(Real.fourierChar (inner ℝ h ξ) : ℂ) - 1‖ₑ ^ 2) *
        ‖integralFourier f ξ‖ₑ ^ 2

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales

namespace ExpandedFA.Sobolev.Curve
/-- The one-dimensional difference-norm constant uses the manuscript's 2π
Fourier normalization. -/
def fractionalKernel (σ t : ℝ) : ℝ :=
  ‖(Real.fourierChar t : ℂ) - 1‖ ^ 2 * |t| ^ (-1 - 2 * σ)
end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve

/-- Compact localization gives an actual continuous scalar distribution,
uniquely fixed by the inverse-absolute-Jacobian density formula. -/
def localizedDistributionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ),
    ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
    ∀ a : ℝ → 𝕜, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∀ T : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜,
    ∃! S : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜,
      ∀ φ ψ : SchwartzMap ℝ 𝕜,
        (∀ x, ψ x = localizedDensity e a φ x) → S φ = T ψ

/-- The constructed distributional pullback agrees with scalar composition
and multiplication whenever the input is represented by a function. -/
def localizedDistributionRegularType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (e : OpenPartialHomeomorph ℝ ℝ),
    ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
    ∀ a : ℝ → 𝕜, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∀ T S : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜,
    (∀ φ ψ : SchwartzMap ℝ 𝕜,
      (∀ x, ψ x = localizedDensity e a φ x) → S φ = T ψ) →
    ∀ f : ℝ → 𝕜, (∀ ψ : SchwartzMap ℝ 𝕜, T ψ = ∫ x, f x * ψ x) →
    ∀ φ : SchwartzMap ℝ 𝕜, S φ = ∫ x, localizedPullback e a f x * φ x

/-- The zero-extension constant depends on the fixed compact subset and open
chart domain, and is uniform over the localized functions. -/
def fractionalExtensionType : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ), 1 < p → ∀ K : Set ℝ, IsCompact K →
    ∀ U : Set ℝ, IsOpen U → K ⊆ U →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ g : ℝ → 𝕜, Continuous g → tsupport g ⊆ K →
      differenceEnergy p g univ ≤ differenceEnergy p g U +
        C * ∫⁻ x in U, ENNReal.ofReal (‖g x‖ ^ 2)

/-- Finiteness and strict positivity of the constant in the fractional
Plancherel identity. Neither a normalization constant nor its integrability is
assumed. -/
def fractionalConstantType : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 →
    Integrable (fractionalKernel σ) ∧ 0 < ∫ t, fractionalKernel σ t

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales

namespace ExpandedFA.Sobolev.Curve
universe v
variable {M : Type v} [TopologicalSpace M] [ChartedSpace ℝ M]
/-- Scalar localization in a finite smooth chart partition, extended by zero
on the whole coordinate line. -/
def chartLocalFunction {𝕜 : Type*} [RCLike 𝕜]
    (A : FiniteChartPartition M) (f : M → 𝕜) (i : Fin A.n) : ℝ → 𝕜 :=
  (A.chart i).target.indicator
    (fun y => (A.cutoff i ((A.chart i).symm y)) • f ((A.chart i).symm y))
end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
universe v

/-- Smooth scalar localizations really are compact smooth functions on the
whole line, with full support inside the chart target. -/
def smoothCompactLocalizationType : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (𝕜 : Type*) [RCLike 𝕜] (A : FiniteChartPartition M)
    (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯) (i : Fin A.n),
    ContDiff ℝ ∞ (chartLocalFunction A f i) ∧
      HasCompactSupport (chartLocalFunction A f i) ∧
      tsupport (chartLocalFunction A f i) ⊆ (A.chart i).target

/-- The actual coordinate-transition coefficients are derived from the two
partitions and compact overlap cutoffs. No analytic boundedness premise occurs
in this geometric decomposition. -/
def finiteCoordinateDecompositionType : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (𝕜 : Type*) [RCLike 𝕜] (A B : FiniteChartPartition M),
    ∃ a : Fin A.n → Fin B.n → ℝ → 𝕜,
      (∀ i j, ContDiff ℝ ∞ (a i j) ∧ HasCompactSupport (a i j) ∧
        tsupport (a i j) ⊆ (A.transition B i j).source) ∧
      ∀ (f : M → 𝕜) (i : Fin A.n), chartLocalFunction A f i = fun y =>
        ∑ j, localizedPullback (A.transition B i j) (a i j)
          (chartLocalFunction B f j) y

/-- Coordinate localization recovers the original scalar function pointwise,
including on an empty curve. -/
def chartReconstructionType : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] (𝕜 : Type*) [RCLike 𝕜]
    (A : FiniteChartPartition M) (f : M → 𝕜) (x : M),
    (∑ i, (A.chart i).source.indicator
      (fun z => chartLocalFunction A f i ((A.chart i) z)) x) = f x

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales

open scoped FourierTransform
namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve

/-- The source's fractional Plancherel identity, with the exact 2π-normalized
positive finite constant, for continuous L¹∩L² functions on the coordinate line.
The ENNReal statement includes infinite difference energies. -/
def fractionalPlancherelType : Prop := ∀ σ : ℝ, 0 < σ → σ < 1 →
    ∀ f : ℝ → ℂ, Continuous f → Integrable f → MemLp f 2 →
    differenceEnergy (1 + 2 * σ) f univ =
      ENNReal.ofReal (∫ t, fractionalKernel σ t) *
        ∫⁻ ξ, ENNReal.ofReal (|ξ| ^ (2 * σ)) * ‖𝓕 f ξ‖ₑ ^ 2

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
/-- The Bessel frequency weight and 1+|ξ|^(2σ) are comparable with explicit
finite constants. This connects the fractional Plancherel energy to the
manuscript's precise frequency normalization. -/
def fractionalWeightComparisonType : Prop := ∀ σ ξ : ℝ, 0 ≤ σ →
    1 + |ξ| ^ (2 * σ) ≤ 2 * (1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ σ ∧
    (1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ σ ≤
      (1 + 4 * Real.pi ^ 2) ^ σ * (1 + |ξ| ^ (2 * σ))
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier

/-- The canonical orthonormal identification of the coordinate line with R^1. -/
def realLineIsometry : ℝ ≃ₗᵢ[ℝ] Euclidean 1 :=
  (OrthonormalBasis.singleton (Fin 1) ℝ).repr

/-- Sum of the extended L² sizes of the scalar chart localizations.
Finiteness includes the required almost-everywhere measurability. -/
def chartL2Size {M : Type*} [TopologicalSpace M] [ChartedSpace ℝ M]
    {𝕜 : Type*} [RCLike 𝕜] (A : FiniteChartPartition M) (f : M → 𝕜) : ℝ≥0∞ :=
  ∑ i, eLpNorm (chartLocalFunction A f i) 2 volume

end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
universe v w

/-- Order-zero atlas comparison on the actual scalar functions, including
infinite extended norms. This supporting result does not assert the missing
all-order distribution theorem. -/
def atlasL2Type : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (𝕜 : Type*) [RCLike 𝕜] (A B : FiniteChartPartition M),
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ f : M → 𝕜,
        chartL2Size A f ≤ ENNReal.ofReal C * chartL2Size B f ∧
        chartL2Size B f ≤ ENNReal.ofReal C * chartL2Size A f) ∧
      ∀ f : M → 𝕜,
        (∀ i, MemLp (chartLocalFunction A f i) 2 volume) ↔
          ∀ j, MemLp (chartLocalFunction B f j) 2 volume

/-- The actual smooth reparametrization preserves order-zero membership and
has two-sided uniform L² bounds for any chosen chart partitions. -/
def reparametrizationL2Type : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (N : Type w) [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold (𝓘(ℝ)) ∞ N] [T2Space N] [CompactSpace N]
    (𝕜 : Type*) [RCLike 𝕜] (A : FiniteChartPartition M) (B : FiniteChartPartition N)
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N),
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ f : N → 𝕜,
        chartL2Size A (f ∘ e) ≤ ENNReal.ofReal C * chartL2Size B f ∧
        chartL2Size B f ≤ ENNReal.ofReal C * chartL2Size A (f ∘ e)) ∧
      ∀ f : N → 𝕜,
        (∀ i, MemLp (chartLocalFunction A (f ∘ e) i) 2 volume) ↔
          ∀ j, MemLp (chartLocalFunction B f j) 2 volume
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier

/-- Canonical transport of a whole-line Schwartz test to Euclidean R^1. -/
def lineSchwartzToEuclidean (f : SchwartzMap ℝ ℂ) : Schwartz ℂ 1 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    realLineIsometry.symm.toContinuousLinearEquiv f

/-- The ordinary derivative, as an actual Schwartz function on the line. -/
def lineSchwartzDeriv (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap ℝ ℂ) (1 : ℝ) f

end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve _root_.ExpandedFA.Sobolev.FourierScale
open _root_.ExpandedFA.Fourier

/-- Full fractional energy bound for compact scalar chart changes. No
Lipschitz or Jacobian certificate is assumed: the constant is derived from
the smooth chart and compact cutoff before the input function is chosen. -/
def localizedFractionalEnergyType : Prop := ∀ (𝕜 : Type*) [RCLike 𝕜]
    (σ : ℝ), 0 < σ → σ < 1 → ∀ (e : OpenPartialHomeomorph ℝ ℝ),
    ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
    ∀ a : ℝ → 𝕜, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : ℝ → 𝕜, Continuous f →
      differenceEnergy (1 + 2 * σ) (localizedPullback e a f) univ +
          (∫⁻ x, ENNReal.ofReal (‖localizedPullback e a f x‖ ^ 2)) ≤
        C * (differenceEnergy (1 + 2 * σ) f univ + ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2))

/-- The line Fourier norm is the norm of an actual represented Hs element. -/
def lineSchwartzHsType : Prop := ∀ (s : ℝ) (f : SchwartzMap ℝ ℂ),
    ∃ u : Hs 1 s,
      realization (s := s) u = schwartzRegularDistribution (lineSchwartzToEuclidean f) ∧
      ENNReal.ofReal (‖u‖ ^ 2) =
        ∫⁻ ξ : ℝ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * |ξ| ^ 2) ^ s) *
          ‖𝓕 (⇑f) ξ‖ₑ ^ 2

/-- Fractional difference energy controls and is controlled by the actual
Hs norm, with the finite strictly positive normalization proved above. -/
def fractionalHsComparisonType : Prop := ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∀ (f : SchwartzMap ℝ ℂ) (u : Hs 1 σ),
      realization (s := σ) u = schwartzRegularDistribution (lineSchwartzToEuclidean f) →
      let E := (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) +
        (ENNReal.ofReal (∫ t, fractionalKernel σ t))⁻¹ *
          differenceEnergy (1 + 2 * σ) f univ
      E ≤ 2 * ENNReal.ofReal (‖u‖ ^ 2) ∧
        ENNReal.ofReal (‖u‖ ^ 2) ≤ ENNReal.ofReal ((1 + 4 * Real.pi ^ 2) ^ σ) * E

/-- The exact one-dimensional derivative norm recurrence, fixing its actual
Schwartz derivative and represented distributions at every real order. -/
def successorHsType : Prop := ∀ (s : ℝ) (f : SchwartzMap ℝ ℂ)
    (u : Hs 1 (s + 1)) (v w : Hs 1 s),
    realization (s := s + 1) u = schwartzRegularDistribution (lineSchwartzToEuclidean f) →
    realization (s := s) v = schwartzRegularDistribution (lineSchwartzToEuclidean f) →
    realization (s := s) w =
      schwartzRegularDistribution (lineSchwartzToEuclidean (lineSchwartzDeriv f)) →
    ‖u‖ ^ 2 = ‖v‖ ^ 2 + ‖w‖ ^ 2

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace ExpandedFA.Sobolev.Curve
universe uc
variable {M : Type uc} [TopologicalSpace M] [ChartedSpace ℝ M]
  [IsManifold (𝓘(ℝ)) ∞ M]

/-- Every smooth coordinate chart, without a finiteness or connectedness restriction. -/
structure SmoothChart (M : Type uc) [TopologicalSpace M] [ChartedSpace ℝ M] where
  val : OpenPartialHomeomorph M ℝ
  property : val ∈ maximalAtlas (𝓘(ℝ)) ∞ M

namespace SmoothChart

def transition (e f : SmoothChart M) : OpenPartialHomeomorph ℝ ℝ :=
  e.val.symm.trans f.val

/-- The coordinate Jacobian measured in the preferred chart at the point.
This is a gauge for comparing actual density sections, not a choice of orientation. -/
def densityJacobian (e : SmoothChart M) (x : M) : ℝ :=
  |deriv ((⟨chartAt ℝ x, chart_mem_maximalAtlas x⟩ : SmoothChart M).transition e)
    ((chartAt ℝ x) x)|

end SmoothChart

/-- A chart coefficient is turned into a pointwise density, using the preferred
chart at each point only to compare coefficients of the same geometric section. -/
def chartDensityFunction {𝕜 : Type*} [RCLike 𝕜] (e : SmoothChart M)
    (φ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤) : M → 𝕜 :=
  e.val.source.indicator (fun x => e.densityJacobian x • φ (e.val x))

def chartDensityLM (𝕜 : Type*) [RCLike 𝕜] (e : SmoothChart M) :
    TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤ →ₗ[𝕜] (M → 𝕜) where
  toFun := chartDensityFunction e
  map_add' φ ψ := by
    ext x
    by_cases hx : x ∈ e.val.source <;> simp [chartDensityFunction, hx, smul_add]
  map_smul' c φ := by
    ext x
    by_cases hx : x ∈ e.val.source <;>
      simp [chartDensityFunction, hx]

/-- Compactly supported smooth test densities, presented by their coordinate
coefficients. The chart injections generate the space, so linearity imposes all
relations between presentations of the same pointwise density. -/
def TestDensities (𝕜 : Type*) [RCLike 𝕜] (M : Type uc)
    [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M] : Submodule 𝕜 (M → 𝕜) :=
  Submodule.span 𝕜 (⋃ e : SmoothChart M, Set.range (chartDensityLM 𝕜 e))

def chartTestDensity (𝕜 : Type*) [RCLike 𝕜] (e : SmoothChart M) :
    TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤ →ₗ[𝕜] TestDensities 𝕜 M :=
  (chartDensityLM 𝕜 e).codRestrict _ (fun φ =>
    Submodule.subset_span (mem_iUnion.mpr ⟨e, mem_range_self φ⟩))

/-- Scalar-linear functionals on compact test densities with the local LF
continuity required of a distribution. -/
def scalarCurveDistributionSubmodule (𝕜 : Type*) [RCLike 𝕜] (M : Type uc)
    [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M] :
    Submodule 𝕜 (TestDensities 𝕜 M →ₗ[𝕜] 𝕜) where
  carrier := {T | ∀ e : SmoothChart M, Continuous (T.comp (chartTestDensity 𝕜 e))}
  zero_mem' := fun _ => continuous_const
  add_mem' := fun hT hS e => (hT e).add (hS e)
  smul_mem' := fun c _ hT e => (hT e).const_smul c

/-- Intrinsic scalar distributions, paired with compactly supported smooth
test densities. The scalar field can be real or complex. -/
def ScalarCurveDistribution (𝕜 : Type*) [RCLike 𝕜] (M : Type uc)
    [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M] : Type _ :=
  ↥(scalarCurveDistributionSubmodule 𝕜 M)

namespace ScalarCurveDistribution
variable {𝕜 : Type*} [RCLike 𝕜]

instance : AddCommGroup (ScalarCurveDistribution 𝕜 M) :=
  inferInstanceAs (AddCommGroup ↥(scalarCurveDistributionSubmodule 𝕜 M))

instance : Module 𝕜 (ScalarCurveDistribution 𝕜 M) :=
  inferInstanceAs (Module 𝕜 ↥(scalarCurveDistributionSubmodule 𝕜 M))

def toLinearMap (T : ScalarCurveDistribution 𝕜 M) : TestDensities 𝕜 M →ₗ[𝕜] 𝕜 := T.val

lemma continuous_chart (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M) :
    Continuous (T.toLinearMap.comp (chartTestDensity 𝕜 e)) := T.property e

def inChart (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M) :
    TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤ →L[𝕜] 𝕜 :=
  ⟨T.toLinearMap.comp (chartTestDensity 𝕜 e), T.continuous_chart e⟩

end ScalarCurveDistribution
end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve _root_.ExpandedFA.Sobolev.FourierScale
open _root_.ExpandedFA.Fourier

/-- Every compactly localized smooth coordinate change acts boundedly on the
actual complex Hs distributions at every real order. Its action on represented
functions and on arbitrary distributions is fixed by scalar composition and
the inverse absolute Jacobian, respectively. -/
def coordinateHsType : Prop := ∀ (s : ℝ) (e : OpenPartialHomeomorph ℝ ℝ),
    ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
    ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∃ (P Q : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ)
      (A : Hs 1 s →L[ℂ] Hs 1 s) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ (f : SchwartzMap ℝ ℂ) (u : Hs 1 s),
        realization (s := s) u = schwartzRegularDistribution (lineSchwartzToEuclidean f) →
        realization (s := s) (A u) =
          schwartzRegularDistribution (lineSchwartzToEuclidean (P f))) ∧
      (∀ (u : Hs 1 s) (φ : SchwartzMap ℝ ℂ),
        realization (s := s) (A u) (lineSchwartzToEuclidean φ) =
          realization (s := s) u (lineSchwartzToEuclidean (Q φ)))
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
universe ud

def curveDistributionChartType : Prop :=
  ∀ (M : Type ud) [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
    (𝕜 : Type) [RCLike 𝕜] (T : ScalarCurveDistribution 𝕜 M) (e f : SmoothChart M)
    (φ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤),
    tsupport φ ⊆ (e.transition f).source →
    ∃ ψ : TestFunction ⟨f.val.target, f.val.open_target⟩ 𝕜 ⊤,
      (∀ y, ψ y = (e.transition f).target.indicator (inverseDensity (e.transition f) φ) y) ∧
      T.inChart e φ = T.inChart f ψ

def curveDistributionLocalizationType : Prop :=
  ∀ (M : Type ud) [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
    (𝕜 : Type) [RCLike 𝕜] (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M)
    (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤),
    ∃! S : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜,
      ∀ (φ : SchwartzMap ℝ 𝕜) (ψ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤),
        (∀ x, ψ x = a x * φ x) → S φ = T.inChart e ψ

def curveDistributionRegularType : Prop :=
  ∀ (M : Type ud) [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
    (𝕜 : Type) [RCLike 𝕜] (T : ScalarCurveDistribution 𝕜 M) (e : SmoothChart M)
    (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
    (S : SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜),
    (∀ (φ : SchwartzMap ℝ 𝕜) (ψ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤),
      (∀ x, ψ x = a x * φ x) → S φ = T.inChart e ψ) →
    ∀ f : ℝ → 𝕜, (∀ ψ, T.inChart e ψ = ∫ x, f x * ψ x) →
    ∀ φ : SchwartzMap ℝ 𝕜, S φ = ∫ x, (a x * f x) * φ x

def curveDistributionFaithfulnessType : Prop :=
  ∀ (M : Type ud) [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
    (𝕜 : Type) [RCLike 𝕜] (T S : ScalarCurveDistribution 𝕜 M),
    (∀ (e : SmoothChart M) (a : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
      (φ : SchwartzMap ℝ 𝕜) (ψ : TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤),
      (∀ x, ψ x = a x * φ x) → T.inChart e ψ = S.inChart e ψ) → T = S

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


namespace ExpandedFA.Sobolev.Curve
open ExpandedFA.Fourier
/-- Canonical transport of a real Schwartz test to Euclidean R^1. -/
def lineRealSchwartzToEuclidean (f : SchwartzMap ℝ ℝ) : Schwartz ℝ 1 :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    realLineIsometry.symm.toContinuousLinearEquiv f
end ExpandedFA.Sobolev.Curve

namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve _root_.ExpandedFA.Sobolev.FourierScale
open _root_.ExpandedFA.Fourier
/-- The real form uses the canonical Hermitian Fourier subspace, and the actual
real distribution pairing. No separate abstract real Hilbert model is substituted. -/
def realCoordinateHsType : Prop := ∀ (s : ℝ) (e : OpenPartialHomeomorph ℝ ℝ),
    ContDiffOn ℝ ∞ e e.source → ContDiffOn ℝ ∞ e.symm e.target →
    ∀ a : ℝ → ℝ, ContDiff ℝ ∞ a → HasCompactSupport a → tsupport a ⊆ e.source →
    ∃ (P Q : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ)
      (A : RealHs 1 s →L[ℝ] RealHs 1 s) (C : ℝ), 0 ≤ C ∧ ‖A‖ ≤ C ∧
      (∀ f x, P f x = localizedPullback e a f x) ∧
      (∀ φ y, Q φ y = localizedDensity e a φ y) ∧
      (∀ (f : SchwartzMap ℝ ℝ) (u : RealHs 1 s),
        realRealization (s := s) u =
          realSchwartzRegularDistribution (lineRealSchwartzToEuclidean f) →
        realRealization (s := s) (A u) =
          realSchwartzRegularDistribution (lineRealSchwartzToEuclidean (P f))) ∧
      (∀ (u : RealHs 1 s) (φ : SchwartzMap ℝ ℝ),
        realRealization (s := s) (A u) (lineRealSchwartzToEuclidean φ) =
          realRealization (s := s) u (lineRealSchwartzToEuclidean (Q φ)))
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
universe ue
/-- Algebraic chart restriction after a smooth scalar cutoff: the actual
compact test coefficient is constructed. Continuity of this extraction on
local LF chart injections is a separate remaining geometric obligation. -/
def densityCoefficientExtractionType : Prop :=
  ∀ (M : Type ue) [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
    (𝕜 : Type) [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯), tsupport ρ ⊆ e.val.source →
    ∃ R : TestDensities 𝕜 M →ₗ[𝕜] TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤,
      ∀ density, chartDensityFunction e (R density) = fun x => ρ x • density.val x
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


noncomputable section
open Set ChartedSpace IsManifold Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
universe ufgeom

/-- Exact extraction of a chart-supported scalar multiple of an intrinsic test
density, with the Schwartz-valued extraction continuous on every native chart LF space. -/
def densityCoefficientSchwartzContinuityType : Prop :=
  ∀ (M : Type ufgeom) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] (𝕜 : Type) [RCLike 𝕜] (e : SmoothChart M)
    (ρ : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯), tsupport ρ ⊆ e.val.source →
    ∃ (R : TestDensities 𝕜 M →ₗ[𝕜]
        TestFunction ⟨e.val.target, e.val.open_target⟩ 𝕜 ⊤)
      (E : TestDensities 𝕜 M →ₗ[𝕜] SchwartzMap ℝ 𝕜),
      (∀ d, chartDensityFunction e (R d) = fun x => ρ x • d.val x) ∧
      (∀ d y, E d y = R d y) ∧
      ∀ f : SmoothChart M, Continuous (E.comp (chartTestDensity 𝕜 f))

/-- Every finite smooth chart partition decomposes actual compact test densities
into their exact cutoff coefficients, whose chart injections sum to the density. -/
def finiteDensityReconstructionType : Prop :=
  ∀ (M : Type ufgeom) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] (𝕜 : Type) [RCLike 𝕜] (A : FiniteChartPartition M),
    ∃ R : ∀ i : Fin A.n, TestDensities 𝕜 M →ₗ[𝕜]
        TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤,
      (∀ i d, chartDensityFunction ⟨A.chart i, A.chart_smooth i⟩ (R i d) =
        fun x => A.cutoff i x • d.val x) ∧
      ∀ d, (∑ i, chartTestDensity 𝕜 ⟨A.chart i, A.chart_smooth i⟩ (R i d)) = d

/-- Finite compact chart localization and synthesis are actual scalar-linear
maps on intrinsic scalar distributions. The coefficient extractions have their
exact density meaning and native LF continuity; synthesis is a left inverse of
localization on every distribution, including negative-order distributions. -/
def finiteDistributionSynthesisType : Prop :=
  ∀ (M : Type ufgeom) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (𝕜 : Type) [RCLike 𝕜] (A : FiniteChartPartition M),
    ∃ (ρ : Fin A.n → C^∞⟮𝓘(ℝ), M; 𝓘(ℝ), ℝ⟯)
      (R : ∀ i : Fin A.n, TestDensities 𝕜 M →ₗ[𝕜]
        TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤)
      (E : Fin A.n → TestDensities 𝕜 M →ₗ[𝕜] SchwartzMap ℝ 𝕜)
      (L : ScalarCurveDistribution 𝕜 M →ₗ[𝕜]
        (Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)))
      (G : (Fin A.n → (SchwartzMap ℝ 𝕜 →L[𝕜] 𝕜)) →ₗ[𝕜]
        ScalarCurveDistribution 𝕜 M),
      (∀ i, tsupport (ρ i) ⊆ (A.chart i).source ∧
        ∀ x ∈ tsupport (A.cutoff i), ρ i x = 1) ∧
      (∀ i d, chartDensityFunction ⟨A.chart i, A.chart_smooth i⟩ (R i d) =
        fun x => ρ i x • d.val x) ∧
      (∀ i d y, E i d y = R i d y) ∧
      (∀ i (f : SmoothChart M), Continuous ((E i).comp (chartTestDensity 𝕜 f))) ∧
      (∀ (T : ScalarCurveDistribution 𝕜 M) (i : Fin A.n) (φ : SchwartzMap ℝ 𝕜)
        (ψ : TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤),
        (∀ y, ψ y = chartLocalFunction A (fun _ => (1 : 𝕜)) i y * φ y) →
        L T i φ = T.inChart ⟨A.chart i, A.chart_smooth i⟩ ψ) ∧
      (∀ v d, (G v).toLinearMap d = ∑ i, v i (E i d)) ∧
      ∀ T, G (L T) = T

/-- The finitely many compact chart localizations of any finite smooth partition
jointly determine an intrinsic scalar distribution. Localization is characterized
by testing on the precise scalar cutoff times a whole-line Schwartz test. -/
def finiteDistributionFaithfulnessType : Prop :=
  ∀ (M : Type ufgeom) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (𝕜 : Type) [RCLike 𝕜] (A : FiniteChartPartition M)
    (T S : ScalarCurveDistribution 𝕜 M),
    (∀ (i : Fin A.n) (φ : SchwartzMap ℝ 𝕜)
      (ψ : TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤),
      (∀ y, ψ y = chartLocalFunction A (fun _ => (1 : 𝕜)) i y * φ y) →
      T.inChart ⟨A.chart i, A.chart_smooth i⟩ ψ =
        S.inChart ⟨A.chart i, A.chart_smooth i⟩ ψ) → T = S

end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales

noncomputable section
open Set ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
universe ur vr
/-- Scalar reparametrization of intrinsic distributions is the transpose of
actual test-density transport by the inverse absolute coordinate Jacobian. -/
def curveDistributionReparametrizationType : Prop :=
  ∀ (M : Type ur) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M]
    (N : Type vr) [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold (𝓘(ℝ)) ∞ N] (𝕜 : Type) [RCLike 𝕜]
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N),
    ∃ (D : TestDensities 𝕜 M ≃ₗ[𝕜] TestDensities 𝕜 N)
      (P : ScalarCurveDistribution 𝕜 N ≃ₗ[𝕜] ScalarCurveDistribution 𝕜 M),
      (∀ (ρ : TestDensities 𝕜 M) (y : N), (D ρ).val y =
        |deriv (fun z : ℝ => (chartAt ℝ (e.symm y))
          (e.symm ((chartAt ℝ y).symm z))) ((chartAt ℝ y) y)| • ρ.val (e.symm y)) ∧
      (∀ (T : ScalarCurveDistribution 𝕜 N) (ρ : TestDensities 𝕜 M),
        (P T).toLinearMap ρ = T.toLinearMap (D ρ))
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


noncomputable section
open Set ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve _root_.ExpandedFA.Sobolev.FourierScale
universe ug vg

/-- A Hilbert presentation has exactly the prescribed chartwise Sobolev
membership and chart square-sum norm on actual intrinsic scalar distributions. -/
def CurveScalePresentation {𝕜 : Type} [RCLike 𝕜]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (R : H → SchwartzMap ℝ 𝕜 → 𝕜)
    {M : Type ug} [TopologicalSpace M] [ChartedSpace ℝ M] [IsManifold (𝓘(ℝ)) ∞ M]
    (A : FiniteChartPartition M) (S : Submodule 𝕜 (PiLp 2 (fun _ : Fin A.n => H)))
    (U : S →ₗ[𝕜] ScalarCurveDistribution 𝕜 M) : Prop :=
  IsClosed (S : Set (PiLp 2 (fun _ : Fin A.n => H))) ∧ CompleteSpace S ∧
    Function.Injective U ∧
    (∀ (u : S) (i : Fin A.n) (φ : SchwartzMap ℝ 𝕜)
      (ψ : TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤),
      (∀ y, ψ y = chartLocalFunction A (fun _ => (1 : 𝕜)) i y * φ y) →
      R (u.val i) φ = (U u).inChart ⟨A.chart i, A.chart_smooth i⟩ ψ) ∧
    (∀ T : ScalarCurveDistribution 𝕜 M, (∃ u : S, U u = T) ↔
      ∀ i : Fin A.n, ∃ v : H, ∀ (φ : SchwartzMap ℝ 𝕜)
        (ψ : TestFunction ⟨(A.chart i).target, (A.chart i).open_target⟩ 𝕜 ⊤),
        (∀ y, ψ y = chartLocalFunction A (fun _ => (1 : 𝕜)) i y * φ y) →
        R v φ = T.inChart ⟨A.chart i, A.chart_smooth i⟩ ψ) ∧
    ∀ u : S, ‖u‖ ^ 2 = ∑ i, ‖u.val i‖ ^ 2

/-- Complete global construction and atlas-independent norms, with each atlas
identification preserving the actual scalar distribution. -/
def CurveHilbertAtlasResult {𝕜 : Type} [RCLike 𝕜]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (R : H → SchwartzMap ℝ 𝕜 → 𝕜) : Prop :=
  ∀ (M : Type ug) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M],
    ∃ (S : ∀ A : FiniteChartPartition M, Submodule 𝕜 (PiLp 2 (fun _ : Fin A.n => H)))
      (U : ∀ A : FiniteChartPartition M, S A →ₗ[𝕜] ScalarCurveDistribution 𝕜 M),
      (∀ A, CurveScalePresentation R A (S A) (U A)) ∧
      ∀ A B : FiniteChartPartition M, ∃ (E : S A ≃L[𝕜] S B) (C : ℝ),
        1 ≤ C ∧ ‖E.toContinuousLinearMap‖ ≤ C ∧ ‖E.symm.toContinuousLinearMap‖ ≤ C ∧
        ∀ u : S A, U B (E u) = U A u

/-- Every smooth reparametrization induces an actual Sobolev isomorphism for
arbitrary finite atlases; its distribution action is the transpose of the
inverse absolute Jacobian on density tests. -/
def CurveHilbertReparametrizationResult {𝕜 : Type} [RCLike 𝕜]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (R : H → SchwartzMap ℝ 𝕜 → 𝕜) : Prop :=
  ∀ (M : Type ug) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (N : Type vg) [TopologicalSpace N] [ChartedSpace ℝ N]
    [IsManifold (𝓘(ℝ)) ∞ N] [T2Space N] [CompactSpace N]
    (A : FiniteChartPartition M) (B : FiniteChartPartition N)
    (e : M ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ N),
    ∃ (SM : Submodule 𝕜 (PiLp 2 (fun _ : Fin A.n => H)))
      (SN : Submodule 𝕜 (PiLp 2 (fun _ : Fin B.n => H)))
      (UM : SM →ₗ[𝕜] ScalarCurveDistribution 𝕜 M)
      (UN : SN →ₗ[𝕜] ScalarCurveDistribution 𝕜 N)
      (D : TestDensities 𝕜 M ≃ₗ[𝕜] TestDensities 𝕜 N)
      (P : ScalarCurveDistribution 𝕜 N ≃ₗ[𝕜] ScalarCurveDistribution 𝕜 M)
      (F : SN ≃L[𝕜] SM),
      CurveScalePresentation R A SM UM ∧ CurveScalePresentation R B SN UN ∧
      (∀ (ρ : TestDensities 𝕜 M) (y : N), (D ρ).val y =
        |deriv (fun z : ℝ => (chartAt ℝ (e.symm y))
          (e.symm ((chartAt ℝ y).symm z))) ((chartAt ℝ y) y)| • ρ.val (e.symm y)) ∧
      (∀ (T : ScalarCurveDistribution 𝕜 N) (ρ : TestDensities 𝕜 M),
        (P T).toLinearMap ρ = T.toLinearMap (D ρ)) ∧
      ∀ u : SN, UM (F u) = P (UN u)

def curveHilbertAtlasType : Prop := ∀ s : ℝ,
  CurveHilbertAtlasResult.{ug} (fun (u : Hs 1 s) φ =>
    realization (s := s) u (lineSchwartzToEuclidean φ))

def realCurveHilbertAtlasType : Prop := ∀ s : ℝ,
  CurveHilbertAtlasResult.{ug} (fun (u : RealHs 1 s) φ =>
    realRealization (s := s) u (lineRealSchwartzToEuclidean φ))

def curveHilbertReparametrizationType : Prop := ∀ s : ℝ,
  CurveHilbertReparametrizationResult.{ug, vg} (fun (u : Hs 1 s) φ =>
    realization (s := s) u (lineSchwartzToEuclidean φ))

def realCurveHilbertReparametrizationType : Prop := ∀ s : ℝ,
  CurveHilbertReparametrizationResult.{ug, vg} (fun (u : RealHs 1 s) φ =>
    realRealization (s := s) u (lineRealSchwartzToEuclidean φ))
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales


noncomputable section
open Set MeasureTheory ChartedSpace IsManifold
open scoped Topology Manifold ContDiff
namespace Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
open _root_.ExpandedFA.Sobolev.Curve
universe ur
/-- Smooth scalar functions define intrinsic distributions with their ordinary
scalar representative in every chart, uniquely and independently of the atlas. -/
def smoothCurveRegularDistributionType : Prop :=
  ∀ (M : Type ur) [TopologicalSpace M] [ChartedSpace ℝ M]
    [IsManifold (𝓘(ℝ)) ∞ M] [T2Space M] [CompactSpace M]
    (𝕜 : Type) [RCLike 𝕜] (f : C^∞⟮𝓘(ℝ), M; 𝓘(ℝ, 𝕜), 𝕜⟯),
    ∃! T : ScalarCurveDistribution 𝕜 M,
      ∀ (c : SmoothChart M) (φ : TestFunction ⟨c.val.target, c.val.open_target⟩ 𝕜 ⊤),
        T.inChart c φ = ∫ y, f (c.val.symm y) * φ y
end Specs.ExpandedFA.Sobolev.SmoothCurveHilbertScales
