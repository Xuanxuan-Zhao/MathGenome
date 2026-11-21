import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.CircularExhaustion
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.FiniteCircularArcs
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.ClassicalRegularDomains
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent geometric obligation for paper.tex:2669–2677.
No harmonic functions, Green identities, or rounding certificates are hypotheses.
The theorem `circular_corner_rounding_type` below is the full global obligation;
`rounding_arc_type` is only its explicit local construction. -/
noncomputable section
open Set Metric MeasureTheory
open scoped Topology ContDiff

namespace D12Complex.CircularCornerRounding

/-- Angular interpolation, including its stationary endpoint values. -/
def smoothStep (t : ℝ) : ℝ := 3 * t ^ 2 - 2 * t ^ 3

/-- The radial factor used in the source's construction. -/
def radialProfile (t : ℝ) : ℝ := 1 - Real.sin (Real.pi * t) / 2

/-- The literal rounding arc in sector coordinates. Positive boundary orientation
uses this curve in reverse order. -/
def roundingArc (ε θ t : ℝ) : ℂ :=
  (ε * radialProfile t : ℝ) * Complex.exp ((θ * smoothStep t : ℝ) * Complex.I)

/-- Velocity in increasing parameter order. -/
def roundingVelocity (ε θ t : ℝ) : ℂ :=
  ((-(ε * Real.pi / 2) * Real.cos (Real.pi * t) : ℝ) +
    (ε * radialProfile t * (θ * (6 * t * (1 - t))) : ℝ) * Complex.I) *
    Complex.exp ((θ * smoothStep t : ℝ) * Complex.I)

/-- Straight bottom ray, with exactly the rounding curve's endpoint speed. -/
def bottomRay (ε t : ℝ) : ℂ := ((ε - (ε * Real.pi / 2) * t : ℝ) : ℂ)

/-- Straight upper ray, with exactly the rounding curve's endpoint speed. -/
def topRay (ε θ t : ℝ) : ℂ :=
  ((ε + (ε * Real.pi / 2) * (t - 1) : ℝ) : ℂ) *
    Complex.exp ((θ : ℂ) * Complex.I)

/-- A literal curve through both new joins. Increasing parameter runs from the
bottom ray to the top ray. No arclength reparametrization is assumed. -/
def joinedRounding (ε θ : ℝ) : ℝ → ℂ :=
  (Iic (0 : ℝ)).piecewise (bottomRay ε)
    ((Iic (1 : ℝ)).piecewise (roundingArc ε θ) (topRay ε θ))

/-- Traversal from the incoming upper ray to the outgoing bottom ray. The
set-side verification for a rounded domain belongs to the global obligation. -/
def positiveJoinedRounding (ε θ t : ℝ) : ℂ := joinedRounding ε θ (1 - t)

/-- Normal coordinates with the normal frozen at one parameter. Only C1
regularity of the joined curve is needed. -/
def normalChartMap (ε θ a : ℝ) (z : ℂ) : ℂ :=
  positiveJoinedRounding ε θ z.re + z.im • (Complex.I * deriv (positiveJoinedRounding ε θ) a)

/-- The closed tip swept out by radial segments from zero to the rounding arc.
This is an explicit subset of the plane, including its two short ray segments. -/
def sectorTip (ε θ : ℝ) : Set ℂ :=
  (fun p : ℝ × ℝ => p.2 • roundingArc ε θ p.1) ''
    ((Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1))

/-- The actual sector after removal of its closed rounding tip. -/
def roundedSector (ε θ : ℝ) : Set ℂ := CircularExhaustion.sector θ \ sectorTip ε θ

/-- The two short original boundary pieces at the model vertex. -/
def shortRays (ε θ : ℝ) : Set ℂ :=
  (fun r : ℝ => (r : ℂ)) '' Icc 0 ε ∪
    (fun r : ℝ => (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) '' Icc 0 ε

/-- Actual Euclidean coordinates, with their Euclidean rather than product norm. -/
def realPlane := Complex.orthonormalBasisOneI.repr

/-- A regular local parametrization of a boundary. The side and outward
orientation are specified by a genuine defining function, below. -/
def HasRegularBoundaryParametrizations (V : Set ℂ) : Prop :=
  ∀ p ∈ frontier V, ∃ (δ : ℝ) (W : Set ℂ) (γ : ℝ → ℂ),
    0 < δ ∧ IsOpen W ∧ p ∈ W ∧ γ 0 = p ∧
    ContDiffOn ℝ 1 γ (Ioo (-δ) δ) ∧
    (∀ t ∈ Ioo (-δ) δ, deriv γ t ≠ 0) ∧
    InjOn γ (Ioo (-δ) δ) ∧ γ '' Ioo (-δ) δ = frontier V ∩ W

/-- Actual local C1 defining functions on the complex plane, including the
negative side and nonzero real differential on the zero level. -/
def HasC1DefiningFunctions (V : Set ℂ) : Prop :=
  ∀ p ∈ frontier V, ∃ (W : Set ℂ) (ρ : ℂ → ℝ),
    IsOpen W ∧ p ∈ W ∧ ContDiffOn ℝ 1 ρ W ∧
    (∀ z ∈ W, z ∈ V ↔ ρ z < 0) ∧
    (∀ z ∈ W, z ∈ frontier V ↔ ρ z = 0) ∧
    ∀ z ∈ W, ρ z = 0 → fderiv ℝ ρ z ≠ 0

/-- A finite circle-arc boundary, with genuinely disjoint arc interiors. Full-circle
pieces and artificial endpoints at smooth boundary points are allowed.
Sector charts state the actual side of the open set. -/
def RoundingGeometry (U : Set ℂ) (J : Finset ℂ) : Prop :=
  IsOpen U ∧ Bornology.IsBounded U ∧
  (↑J : Set ℂ) ⊆ frontier U ∧
  (∃ (n : ℕ) (c : Fin n → ℂ) (R a b : Fin n → ℝ),
    (∀ i, 0 < R i ∧ a i < b i ∧ b i - a i ≤ 2 * Real.pi) ∧
    frontier U = ⋃ i, CircularExhaustion.arcParam (c i) (R i) '' Icc (a i) (b i) ∧
    (∀ i j, i ≠ j → Disjoint
      (CircularExhaustion.arcParam (c i) (R i) '' Ioo (a i) (b i))
      (CircularExhaustion.arcParam (c j) (R j) '' Ioo (a j) (b j)))) ∧
  (∀ p ∈ frontier U, p ∉ J → CircularExhaustion.SectorChart U p Real.pi) ∧
  ∀ p ∈ J, ∃ θ : ℝ, 0 < θ ∧ θ < 2 * Real.pi ∧
    CircularExhaustion.SectorChart U p θ

/-- The neighborhoods in which boundaries are changed. -/
def joinNeighborhoods (J : Finset ℂ) (r : ℝ) : Set ℂ :=
  ⋃ p ∈ J, ball p r

/-- Full conclusion for one scale. The neighborhood equality preserves both
boundary and set side, hence also boundary orientation on retained pieces.
Hausdorff one-measure is the actual arclength of the changed boundary portions.
The D04 predicate includes C1 defining functions with nonzero real differential. -/
def IsRoundingAt (U V : Set ℂ) (J : Finset ℂ) (C ε : ℝ) : Prop :=
  IsOpen V ∧ V ⊆ U ∧
  Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain
    (realPlane '' V) ∧
  HasRegularBoundaryParametrizations V ∧
  (∀ p ∈ J, ∀ q ∈ J, p ≠ q → Disjoint (ball p (C * ε)) (ball q (C * ε))) ∧
  U \ V ⊆ joinNeighborhoods J (C * ε) ∧
  (∀ z ∉ joinNeighborhoods J (C * ε), ∃ W : Set ℂ,
    IsOpen W ∧ z ∈ W ∧ U ∩ W = V ∩ W) ∧
  frontier U \ frontier V ⊆ joinNeighborhoods J (C * ε) ∧
  frontier V \ frontier U ⊆ joinNeighborhoods J (C * ε) ∧
  Measure.hausdorffMeasure 1 (frontier U \ frontier V) ≤ ENNReal.ofReal (C * ε) ∧
  Measure.hausdorffMeasure 1 (frontier V \ frontier U) ≤ ENNReal.ofReal (C * ε) ∧
  volume (U \ V) ≤ ENNReal.ofReal (C * ε ^ 2)

end D12Complex.CircularCornerRounding

namespace Specs.D12Complex.Ch14.CircularCornerRounding
open _root_.D12Complex.CircularCornerRounding

/-- The full unchanged global task, with constants uniform for the fixed input.
In particular the input can be a fixed cut domain once its geometry is proved. -/
def circular_corner_rounding_type : Prop :=
  ∀ (U : Set ℂ) (J : Finset ℂ), RoundingGeometry U J →
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ V : Set ℂ, IsRoundingAt U V J C ε

/-- Local construction, a proper part of the full task. This includes actual
velocities, regularity, injectivity, endpoint tangents, and a uniform length
bound; it does not claim a global domain has been constructed. -/
def rounding_arc_type : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → θ < 2 * Real.pi →
    ContDiff ℝ ∞ (roundingArc ε θ) ∧
    roundingArc ε θ 0 = (ε : ℂ) ∧
    roundingArc ε θ 1 = (ε : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      ε / 2 ≤ ‖roundingArc ε θ t‖ ∧ ‖roundingArc ε θ t‖ ≤ ε) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1,
      roundingArc ε θ t ∈ _root_.D12Complex.CircularExhaustion.sector θ) ∧
    InjOn (roundingArc ε θ) (Icc (0 : ℝ) 1) ∧
    (∀ t : ℝ, HasDerivAt (roundingArc ε θ) (roundingVelocity ε θ t) t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, deriv (roundingArc ε θ) t ≠ 0) ∧
    deriv (roundingArc ε θ) 0 = (-(ε * Real.pi / 2) : ℝ) ∧
    deriv (roundingArc ε θ) 1 = (ε * Real.pi / 2 : ℝ) *
      Complex.exp ((θ : ℂ) * Complex.I) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      ‖deriv (roundingArc ε θ) t‖ ≤ (Real.pi / 2 + 6 * θ) * ε) ∧
    (∫ t in (0 : ℝ)..1, ‖deriv (roundingArc ε θ) t‖) ≤
      (Real.pi / 2 + 6 * θ) * ε

/-- Genuine C1 parametrizations across the new joins, with matched endpoint
velocities and the source's positive traversal order. -/
def joined_rounding_type : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → θ < 2 * Real.pi →
    ContDiff ℝ 1 (positiveJoinedRounding ε θ) ∧
    Function.Injective (positiveJoinedRounding ε θ) ∧
    (∀ t : ℝ, deriv (positiveJoinedRounding ε θ) t ≠ 0) ∧
    (∀ t ≤ 0, positiveJoinedRounding ε θ t = topRay ε θ (1 - t)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1,
      positiveJoinedRounding ε θ t = roundingArc ε θ (1 - t)) ∧
    (∀ t ≥ 1, positiveJoinedRounding ε θ t = bottomRay ε (1 - t)) ∧
    deriv (positiveJoinedRounding ε θ) 0 =
      (-(ε * Real.pi / 2) : ℝ) * Complex.exp ((θ : ℂ) * Complex.I) ∧
    deriv (positiveJoinedRounding ε θ) 1 = (ε * Real.pi / 2 : ℝ)

/-- Support and area control for the actual model tip, and arclength control for
the actual added arc. Pullback and assembly into the global domain remain
separate obligations. -/
def sector_tip_type : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → θ < 2 * Real.pi →
    IsCompact (sectorTip ε θ) ∧ sectorTip ε θ ⊆ closedBall (0 : ℂ) ε ∧
    0 ∈ sectorTip ε θ ∧ roundingArc ε θ '' Icc (0 : ℝ) 1 ⊆ sectorTip ε θ ∧
    _root_.D12Complex.CircularExhaustion.sector θ ∩ ball (0 : ℂ) (ε / 2) ⊆ sectorTip ε θ ∧
    volume (sectorTip ε θ) ≤ ENNReal.ofReal (Real.pi * ε ^ 2) ∧
    Measure.hausdorffMeasure 1 (roundingArc ε θ '' Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal ((Real.pi / 2 + 6 * θ) * ε) ∧
    ∀ U : Set ℂ, IsOpen U → IsOpen (U \ sectorTip ε θ) ∧
      U \ (U \ sectorTip ε θ) ⊆ closedBall (0 : ℂ) ε ∧
      volume (U \ (U \ sectorTip ε θ)) ≤ ENNReal.ofReal (Real.pi * ε ^ 2)

/-- Uniform support, length and area bounds after an actual C1 chart map. The
radius and Lipschitz constant are obtained from C1 regularity, not assumed as a
rounding certificate. This is still a local estimate, not the global theorem. -/
def chart_estimates_type : Prop :=
  ∀ g : ℂ → ℂ, ContDiffAt ℝ 1 g 0 →
    ∃ R L : ℝ, 0 < R ∧ 0 < L ∧
      ∀ ε θ : ℝ, 0 < ε → ε ≤ R → 0 < θ → θ < 2 * Real.pi →
        IsCompact (g '' sectorTip ε θ) ∧
        g '' sectorTip ε θ ⊆ closedBall (g 0) (L * ε) ∧
        volume (g '' sectorTip ε θ) ≤ ENNReal.ofReal (Real.pi * (L * ε) ^ 2) ∧
        Measure.hausdorffMeasure 1 (g '' (roundingArc ε θ '' Icc (0 : ℝ) 1)) ≤
          ENNReal.ofReal (L * (Real.pi / 2 + 6 * θ) * ε)

/-- Exact geometry and quantitative estimates for the actual model rounded
sector. This proper part includes the complete frontier and local regular
parametrizations; it does not assert the global finite-chart construction. -/
def model_sector_geometry_type : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → θ < 2 * Real.pi →
    IsOpen (roundedSector ε θ) ∧
    frontier (roundedSector ε θ) = Set.range (positiveJoinedRounding ε θ) ∧
    HasRegularBoundaryParametrizations (roundedSector ε θ) ∧
    (0 : ℂ) ∉ closure (roundedSector ε θ) ∧
    (∀ z : ℂ, z ∈ roundedSector ε θ ↔ ∃ r t : ℝ, t ∈ Ioo (0 : ℝ) 1 ∧
      ε * radialProfile t < r ∧
      z = (r : ℂ) * Complex.exp ((θ * smoothStep t : ℝ) * Complex.I)) ∧
    frontier (_root_.D12Complex.CircularExhaustion.sector θ) \ frontier (roundedSector ε θ) ⊆
      shortRays ε θ ∧
    frontier (roundedSector ε θ) \ frontier (_root_.D12Complex.CircularExhaustion.sector θ) ⊆
      roundingArc ε θ '' Icc (0 : ℝ) 1 ∧
    Measure.hausdorffMeasure 1
      (frontier (_root_.D12Complex.CircularExhaustion.sector θ) \ frontier (roundedSector ε θ)) ≤
        ENNReal.ofReal (2 * ε) ∧
    Measure.hausdorffMeasure 1
      (frontier (roundedSector ε θ) \ frontier (_root_.D12Complex.CircularExhaustion.sector θ)) ≤
        ENNReal.ofReal ((Real.pi / 2 + 6 * θ) * ε)

/-- Actual inverse-function charts and actual regular C1 zero-level descriptions
at every model boundary point. The D04 negative-side condition is deliberately
not claimed by this proper part and remains part of the full task above. -/
def model_normal_charts_type : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → θ < 2 * Real.pi → ∀ a : ℝ,
    (∃ e : OpenPartialHomeomorph ℂ ℂ,
      (e : ℂ → ℂ) = normalChartMap ε θ a ∧ (a : ℂ) ∈ e.source ∧
      positiveJoinedRounding ε θ a ∈ e.target ∧
      e.symm (positiveJoinedRounding ε θ a) = (a : ℂ) ∧
      ContDiffAt ℝ 1 e.symm (positiveJoinedRounding ε θ a)) ∧
    ∃ (W : Set ℂ) (ψ : ℂ → ℂ), IsOpen W ∧ positiveJoinedRounding ε θ a ∈ W ∧
      ContDiffOn ℝ 1 ψ W ∧
      (∀ z ∈ W, fderiv ℝ (fun w => (ψ w).im) z ≠ 0) ∧
      ψ (positiveJoinedRounding ε θ a) = (a : ℂ) ∧
      ∀ z ∈ W, z ∈ frontier (roundedSector ε θ) ↔ (ψ z).im = 0

/-- Full model side verification, including both new joins. -/
def model_defining_functions_type : Prop :=
  ∀ ε θ : ℝ, 0 < ε → 0 < θ → θ < 2 * Real.pi →
    HasC1DefiningFunctions (roundedSector ε θ)

/-- The literal real isometry transports genuine defining functions to the
exact prior D04 predicate; boundedness and openness are explicit premises. -/
def classical_domain_bridge_type : Prop :=
  ∀ V : Set ℂ, Bornology.IsBounded V → IsOpen V → HasC1DefiningFunctions V →
    Specs.D04.C12.ClassicalRegularDomains.Model.IsClassicalRegularDomain (realPlane '' V)

end Specs.D12Complex.Ch14.CircularCornerRounding
