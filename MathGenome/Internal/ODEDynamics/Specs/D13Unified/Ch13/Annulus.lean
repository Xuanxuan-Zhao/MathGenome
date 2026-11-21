import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Invariant
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Orbits
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! Independent statements for paper.tex, Example d13:13:annulus.
The oriented real plane is represented by ℂ; the Cartesian formula and the
coordinate derivative equivalence below check this representation explicitly.
The radius uses the Euclidean norm. Angular coordinates are local lifts, not
an assertion that the principal argument is continuous around the circle. -/
noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch13.Annulus

/-- The original polynomial field, in the real plane ℂ. -/
def vectorField (z : ℂ) : ℂ := ((1 - ‖z‖ ^ 2 : ℝ) : ℂ) * z + Complex.I * z

lemma continuous_vectorField : Continuous vectorField := by
  unfold vectorField
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub
    (continuous_norm.pow 2))).mul continuous_id).add (continuous_const.mul continuous_id)

/-- Actual state domain: all of the plane. -/
def oscillator : D13Unified.AutonomousODE ℂ where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun z => vectorField z.val
  continuous_field := continuous_vectorField.comp continuous_subtype_val

def annulus : Set ℂ := {z | (1 / 2 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 2}
def unitCircle : Set ℂ := {z | ‖z‖ = 1}
def polar (r θ : ℝ) : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
def circleCurve (t : ℝ) : ℂ := polar 1 t
end D13Unified.Ch13.Annulus

namespace Specs.D13Unified.Ch13.Annulus
open _root_.D13Unified _root_.D13Unified.Ch13.Annulus
open _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters

def CartesianField : Prop := ∀ z : ℂ,
  (vectorField z).re = (1-z.re^2-z.im^2)*z.re-z.im ∧
  (vectorField z).im = z.re+(1-z.re^2-z.im^2)*z.im

def CartesianDerivative : Prop := ∀ (z : ℝ → ℂ) (t : ℝ),
  HasDerivAt z (vectorField (z t)) t ↔
    HasDerivAt (fun u => (z u).re) ((1-(z t).re^2-(z t).im^2)*(z t).re-(z t).im) t ∧
    HasDerivAt (fun u => (z u).im) ((z t).re+(1-(z t).re^2-(z t).im^2)*(z t).im) t

/-- Converse bridge: the two actual polar differential equations yield the
Cartesian equation, with no branch assumption on the lifted angle. -/
def PolarToCartesian : Prop := ∀ (r θ : ℝ → ℝ) (t : ℝ),
  0 < r t → HasDerivAt r (r t * (1-r t^2)) t → HasDerivAt θ 1 t →
    HasDerivAt (fun u => polar (r u) (θ u)) (vectorField (polar (r t) (θ t))) t

/-- Every solution near each of its nonzero points admits actual differentiable
polar coordinates. J retains a neighborhood of the chosen time in the original
solution interval; its radius is the Euclidean radius of that solution. -/
def LocalPolar : Prop := ∀ (I : OpenTimeInterval) (z : ℝ → ℂ),
  classicalAutonomousSolutionOnValue oscillator I z →
  ∀ s ∈ I.carrier, z s ≠ 0 → ∃ (J : OpenTimeInterval) (r θ : ℝ → ℝ),
    s ∈ J.carrier ∧ J.carrier ⊆ I.carrier ∧
    ∀ t ∈ J.carrier, 0 < r t ∧ r t = ‖z t‖ ∧ z t = polar (r t) (θ t) ∧
      HasDerivAt r (r t * (1-r t^2)) t ∧ HasDerivAt θ 1 t

def PositiveInvariance : Prop := Ch11.Invariant.positiveInvariantValue oscillator annulus

def NoEquilibrium : Prop := ∀ z ∈ annulus, vectorField z ≠ 0

/-- The displayed periodic orbit is contained in the trapping annulus. -/
def CircleInAnnulus : Prop := unitCircle ⊆ annulus

/-- The circle is the image of a complete nonconstant canonical solution with
least positive period 2π. -/
def PeriodicCircle : Prop :=
  ((flowInterval oscillator (1:ℂ)).carrier = univ ∧
    ∀ t : ℝ, flow oscillator t 1 = circleCurve t) ∧
  (∀ t : ℝ, HasDerivAt circleCurve (vectorField (circleCurve t)) t) ∧
  Set.range circleCurve = unitCircle ∧ (∃ t u : ℝ, circleCurve t ≠ circleCurve u) ∧
  0 < 2 * Real.pi ∧ Function.Periodic circleCurve (2 * Real.pi) ∧
  ∀ T : ℝ, 0 < T → Function.Periodic circleCurve T → 2 * Real.pi ≤ T

/-- The canonical maximal solution has every forward time in its actual
lifespan, stays nonzero there, and approaches the circle in actual distance. -/
def ForwardAttraction : Prop := ∀ z : ℂ, z ≠ 0 →
  Ici (0 : ℝ) ⊆ (flowInterval oscillator z).carrier ∧
  (∀ t : ℝ, 0 ≤ t → flow oscillator t z ≠ 0) ∧
  Tendsto (fun t => Metric.infDist (flow oscillator t z) unitCircle) atTop (𝓝 0)
end Specs.D13Unified.Ch13.Annulus
