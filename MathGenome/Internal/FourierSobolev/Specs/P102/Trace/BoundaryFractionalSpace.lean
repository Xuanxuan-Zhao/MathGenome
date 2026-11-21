import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Localization

/-!
Boundary spaces in paper.tex:2564–2593. Write d=m+1; the boundary dimension is m,
so the singular exponent is m+sp, not the ambient dimension m+1+sp.
The analytic conclusions below require m≥1, 0<s<1, and 1≤p<⊤.
Definitions use extended norms, retaining infinity until finiteness is proved.
No trace, lifting, or assumed analytic estimate occurs in the geometric data.
-/
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal ContDiff

namespace P102.Trace.BoundaryFractional
open P102.U4.GraphPieces P102.Sobolev.Geometry

/-- Euclidean-normalized Hausdorff measure restricted to the boundary.
Lp and a.e. statements allow completed-measure representatives. -/
def surfaceMeasure {m : ℕ} (Ω : Set (Ambient m)) : Measure (Ambient m) :=
  (μHE[m] : Measure (Ambient m)).restrict (frontier Ω)

/-- The intrinsic iterated integral with explicit zero diagonal. -/
def energy {m : ℕ} {𝕜 : Type*} [RCLike 𝕜] (Ω : Set (Ambient m))
    (s : ℝ) (p : ℝ≥0∞) (g : Ambient m → 𝕜) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, if x = y then 0 else
    ‖g x - g y‖ₑ ^ p.toReal /
      ENNReal.ofReal ‖x - y‖ ^ ((m : ℝ) + s * p.toReal)
    ∂surfaceMeasure Ω ∂surfaceMeasure Ω

def seminorm {m : ℕ} {𝕜 : Type*} [RCLike 𝕜] (Ω : Set (Ambient m))
    (s : ℝ) (p : ℝ≥0∞) (g : Ambient m → 𝕜) : ℝ≥0∞ :=
  energy Ω s p g ^ (1 / p.toReal)

/-- The sum norm specified in the source, extended to arbitrary representatives. -/
def intrinsicNorm {m : ℕ} {𝕜 : Type*} [RCLike 𝕜] (Ω : Set (Ambient m))
    (s : ℝ) (p : ℝ≥0∞) (g : Ambient m → 𝕜) : ℝ≥0∞ :=
  eLpNorm g p (surfaceMeasure Ω) + seminorm Ω s p g

/-- The intrinsic space as a set of actual Lp classes, with finite seminorm. -/
def space {m : ℕ} (𝕜 : Type*) [RCLike 𝕜] (Ω : Set (Ambient m))
    (s : ℝ) (p : ℝ≥0∞) : Set (Lp 𝕜 p (surfaceMeasure Ω)) :=
  {g | seminorm Ω s p (g : Ambient m → 𝕜) < ⊤}

/-- The real-valued sum norm on members of the intrinsic space. -/
def spaceNorm {m : ℕ} {𝕜 : Type*} [RCLike 𝕜] {Ω : Set (Ambient m)}
    {s : ℝ} {p : ℝ≥0∞} (g : space 𝕜 Ω s p) : ℝ :=
  ‖g.val‖ + (seminorm Ω s p (g.val : Ambient m → 𝕜)).toReal

/-- A finite smooth boundary partition subordinate to strictly smaller graph
cylinders. These are geometric conditions only. They cover arbitrary admissible
choices, so the comparison theorem implies independence of charts and partition. -/
structure Atlas {m : ℕ} (Ω : Set (Ambient m)) where
  count : ℕ
  chart : Fin count → BoundaryChart Ω
  radius : Fin count → ℝ
  height : Fin count → ℝ
  smaller : ∀ i, 0 < radius i ∧ radius i < (chart i).radius ∧
    0 < height i ∧ height i < (chart i).height
  cover : frontier Ω ⊆ ⋃ i, chartImage (chart i).frame (chart i).graphFunction
    (chart i).center (radius i) (height i)
  cutoff : Fin count → Ambient m → ℝ
  smooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (cutoff i)
  compact : ∀ i, HasCompactSupport (cutoff i)
  nonneg : ∀ i x, 0 ≤ cutoff i x
  sum_eq_one : ∀ x ∈ frontier Ω, ∑ i, cutoff i x = 1
  support_subset : ∀ i, tsupport (cutoff i) ⊆
    chartImage (chart i).frame (chart i).graphFunction (chart i).center
      (radius i) (height i)

/-- The physical graph parameterization in the chart's rigid frame. -/
def graphMap {m : ℕ} {Ω : Set (Ambient m)} (C : BoundaryChart Ω)
    (x : P102.U4.Space m) : Ambient m := C.frame (graph C.graphFunction x)

/-- Localize on the physical boundary, pull back to the full tangential base,
and set the result to zero everywhere else in R^m. -/
def localizedPullback {m : ℕ} {𝕜 : Type*} [RCLike 𝕜] {Ω : Set (Ambient m)}
    (A : Atlas Ω) (i : Fin A.count) (g : Ambient m → 𝕜)
    (x : P102.U4.Space m) : 𝕜 := by
  classical
  exact if x ∈ ball (A.chart i).center (A.chart i).radius then
    A.cutoff i (graphMap (A.chart i) x) • g (graphMap (A.chart i) x) else 0

/-- Finite sum of whole-space Gagliardo sum norms of the zero extensions. -/
def chartNorm {m : ℕ} {𝕜 : Type*} [RCLike 𝕜] {Ω : Set (Ambient m)}
    (A : Atlas Ω) (s : ℝ) (p : ℝ≥0∞) (g : Ambient m → 𝕜) : ℝ≥0∞ :=
  ∑ i, (eLpNorm (localizedPullback A i g) p volume +
    P102.Fractional.seminorm Set.univ s p (localizedPullback A i g))

/-- Chart membership is tested on the same underlying Lp(σ) classes. -/
def chartSpace {m : ℕ} (𝕜 : Type*) [RCLike 𝕜] {Ω : Set (Ambient m)}
    (A : Atlas Ω) (s : ℝ) (p : ℝ≥0∞) : Set (Lp 𝕜 p (surfaceMeasure Ω)) :=
  {g | chartNorm A s p (g : Ambient m → 𝕜) < ⊤}

namespace Expected
universe u

def surfaceMeasureType := {m : ℕ} → Set (Ambient m) → Measure (Ambient m)
def surfaceMeasureValue : surfaceMeasureType := @surfaceMeasure

def energyType := {m : ℕ} → {𝕜 : Type u} → [RCLike 𝕜] →
  Set (Ambient m) → ℝ → ℝ≥0∞ → (Ambient m → 𝕜) → ℝ≥0∞
def energyValue : energyType := @energy

def seminormType := energyType.{u}
def seminormValue : seminormType := @seminorm

def intrinsicNormType := energyType.{u}
def intrinsicNormValue : intrinsicNormType := @intrinsicNorm

def spaceType := {m : ℕ} → (𝕜 : Type u) → [RCLike 𝕜] →
  (Ω : Set (Ambient m)) → ℝ → (p : ℝ≥0∞) → Set (Lp 𝕜 p (surfaceMeasure Ω))
def spaceValue : spaceType := @space

def spaceNormType := {m : ℕ} → {𝕜 : Type u} → [RCLike 𝕜] →
  {Ω : Set (Ambient m)} → {s : ℝ} → {p : ℝ≥0∞} → space 𝕜 Ω s p → ℝ
def spaceNormValue : spaceNormType := @spaceNorm

def localizedPullbackType := {m : ℕ} → {𝕜 : Type u} → [RCLike 𝕜] →
  {Ω : Set (Ambient m)} → (A : Atlas Ω) → Fin A.count →
    (Ambient m → 𝕜) → P102.U4.Space m → 𝕜
def localizedPullbackValue : localizedPullbackType := @localizedPullback

def chartNormType := {m : ℕ} → {𝕜 : Type u} → [RCLike 𝕜] →
  {Ω : Set (Ambient m)} → Atlas Ω → ℝ → ℝ≥0∞ → (Ambient m → 𝕜) → ℝ≥0∞
def chartNormValue : chartNormType := @chartNorm

def chartSpaceType := {m : ℕ} → (𝕜 : Type u) → [RCLike 𝕜] →
  {Ω : Set (Ambient m)} → Atlas Ω → ℝ → (p : ℝ≥0∞) →
    Set (Lp 𝕜 p (surfaceMeasure Ω))
def chartSpaceValue : chartSpaceType := @chartSpace

/-- Existence includes the empty Lipschitz open set. No connectedness is required. -/
def AtlasExistence : Prop :=
  ∀ (m : ℕ) (Ω : Set (Ambient m)), IsLipschitzOpen Ω → Nonempty (Atlas Ω)

def IntrinsicRepresentativeIndependence : Prop :=
  ∀ {m : ℕ} {𝕜 : Type u} [RCLike 𝕜] {Ω : Set (Ambient m)} {s : ℝ} {p : ℝ≥0∞}
    {g h : Ambient m → 𝕜}, g =ᵐ[surfaceMeasure Ω] h →
    energy Ω s p g = energy Ω s p h ∧
    seminorm Ω s p g = seminorm Ω s p h ∧
    intrinsicNorm Ω s p g = intrinsicNorm Ω s p h

/-- In particular the real norm formula belongs to the chosen Lp class. -/
def NormFormula : Prop :=
  ∀ {m : ℕ} {𝕜 : Type u} [RCLike 𝕜] {Ω : Set (Ambient m)} {s : ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (g : space 𝕜 Ω s p),
    ENNReal.ofReal (spaceNorm g) = intrinsicNorm Ω s p (g.val : Ambient m → 𝕜)

/-- Completed/a.e. representatives pull back to the same whole-space classes. -/
def ChartRepresentativeIndependence : Prop :=
  ∀ {m : ℕ} {𝕜 : Type u} [RCLike 𝕜] {Ω : Set (Ambient m)} (A : Atlas Ω)
    {g h : Ambient m → 𝕜}, g =ᵐ[surfaceMeasure Ω] h →
    (∀ i, localizedPullback A i g =ᵐ[volume] localizedPullback A i h) ∧
    ∀ s p, chartNorm A s p g = chartNorm A s p h

/-- Finite total surface measure, including empty boundaries. -/
def FiniteSurfaceMeasure : Prop :=
  ∀ (m : ℕ) (Ω : Set (Ambient m)), IsLipschitzOpen Ω → surfaceMeasure Ω Set.univ < ⊤

/-- Both directions, with finite positive constants independent of g and of its
representative. The chart norm uses whole-space zero extensions, not base norms. -/
def NormComparison : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (Ω : Set (Ambient m)), IsLipschitzOpen Ω →
    ∀ (A : Atlas Ω) (s : ℝ), 0 < s → s < 1 →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∃ C D : ℝ≥0, 0 < C ∧ 0 < D ∧
      ∀ {𝕜 : Type u} [RCLike 𝕜] (g : Ambient m → 𝕜), MemLp g p (surfaceMeasure Ω) →
        chartNorm A s p g ≤ (C : ℝ≥0∞) * intrinsicNorm Ω s p g ∧
        intrinsicNorm Ω s p g ≤ (D : ℝ≥0∞) * chartNorm A s p g

/-- Equality of sets in the same Lp space, not merely an abstract isomorphism. -/
def CommonUnderlyingClasses : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (Ω : Set (Ambient m)), IsLipschitzOpen Ω →
    ∀ (A : Atlas Ω) (s : ℝ), 0 < s → s < 1 →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ (𝕜 : Type u) [RCLike 𝕜], space 𝕜 Ω s p = chartSpace 𝕜 A s p

/-- Quantitative independence of every admissible finite chart/partition choice. -/
def AtlasIndependence : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (Ω : Set (Ambient m)), IsLipschitzOpen Ω →
    ∀ (A B : Atlas Ω) (s : ℝ), 0 < s → s < 1 →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∃ C D : ℝ≥0, 0 < C ∧ 0 < D ∧
      ∀ {𝕜 : Type u} [RCLike 𝕜] (g : Ambient m → 𝕜), MemLp g p (surfaceMeasure Ω) →
        chartNorm A s p g ≤ (C : ℝ≥0∞) * chartNorm B s p g ∧
        chartNorm B s p g ≤ (D : ℝ≥0∞) * chartNorm A s p g

end Expected
end P102.Trace.BoundaryFractional
