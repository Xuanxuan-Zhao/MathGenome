import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.StateDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! Independent statements for the construction and regularity clauses of
paper.tex, Theorem d13:16:triangular-center. The slow flow is the upstream
canonical maximal flow. Endomorphisms use the operator norm of the fixed
normed realization; their exponential is the normed-algebra exponential.
All finite dimensions, including zero, and any fixed norms are allowed.
The constants C and D are arbitrary finite bounds for g and Dg, respectively.
No graph, completeness, flow derivative, or integral convergence is assumed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff NNReal

namespace D13Unified.Ch16.TriangularGraphRegularity

variable (E H : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

structure Data where
  slow : AutonomousODE E
  full_domain : slow.domain = univ
  slow_c1 : ContDiffOn ℝ 1
    (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue slow) slow.domain
  L : ℝ≥0
  slow_lipschitz : LipschitzWith L
    (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue slow)
  slow_zero : Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue slow 0 = 0
  slow_derivative_zero : fderiv ℝ
    (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue slow) 0 = 0
  g : E → H
  g_c1 : ContDiff ℝ 1 g
  C : ℝ≥0
  D : ℝ≥0
  g_bound : ∀ x, ‖g x‖ ≤ C
  dg_bound : ∀ x, ‖fderiv ℝ g x‖ ≤ D
  g_zero : g 0 = 0
  dg_zero : fderiv ℝ g 0 = 0
  B : H →L[ℝ] H
  M : ℝ
  β : ℝ
  gap : (L : ℝ) < β
  decay : ∀ s : ℝ, 0 ≤ s →
    ‖NormedSpace.exp ((-s) • B)‖ ≤ M * Real.exp (-β * s)

variable {E H}

def slowFlow (d : Data E H) (t : ℝ) (x : E) : E :=
  Ch06.StateDerivative.flow d.slow t x

def kernel (d : Data E H) (s : ℝ) : H →L[ℝ] H :=
  NormedSpace.exp ((-s) • d.B)

def integrand (d : Data E H) (x : E) (s : ℝ) : H :=
  kernel d s (d.g (slowFlow d (-s) x))

def graph (d : Data E H) (x : E) : H :=
  ∫ s in Ici (0 : ℝ), integrand d x s

def derivativeIntegrand (d : Data E H) (x : E) (s : ℝ) : E →L[ℝ] H :=
  (kernel d s).comp ((fderiv ℝ d.g (slowFlow d (-s) x)).comp
    (fderiv ℝ (slowFlow d (-s)) x))

def graphDerivative (d : Data E H) (x : E) : E →L[ℝ] H :=
  ∫ s in Ici (0 : ℝ), derivativeIntegrand d x s

def derivativeBound (d : Data E H) (s : ℝ) : ℝ :=
  d.M * (d.D : ℝ) * Real.exp (-(d.β - d.L) * s)

end D13Unified.Ch16.TriangularGraphRegularity

namespace Specs.D13Unified.Ch16.TriangularGraphRegularity
open _root_.D13Unified _root_.D13Unified.Ch16.TriangularGraphRegularity
universe u v

/-- Completeness concerns the actual maximal interval, not its totalization. -/
def Completeness : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H),
    (∀ x, (Ch06.StateDerivative.flowInterval d.slow x).carrier = univ) ∧
    (∀ x, slowFlow d 0 x = x) ∧
    (∀ x t, HasDerivAt (fun r => slowFlow d r x)
      (Ch01.AutonomousParameters.autonomousEvalValue d.slow (slowFlow d t x)) t) ∧
    ContDiff ℝ 1 (fun q : ℝ × E => slowFlow d q.1 q.2) ∧
    (∀ t x, ‖fderiv ℝ (slowFlow d t) x‖ ≤ Real.exp (d.L * |t|)) ∧
    (∀ t, slowFlow d t 0 = 0)

def IntegralConvergence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H),
    (∀ x, IntegrableOn (integrand d x) (Ici 0) ∧
      IntegrableOn (fun s => ‖integrand d x s‖) (Ici 0)) ∧
    TendstoUniformly (fun T : ℝ => fun x => ∫ s in (0 : ℝ)..T, integrand d x s)
      (graph d) atTop

def Regularity : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H),
    IntegrableOn (derivativeBound d) (Ici 0) ∧
    (∀ x s, 0 ≤ s → ‖derivativeIntegrand d x s‖ ≤ derivativeBound d s) ∧
    (∀ x, IntegrableOn (derivativeIntegrand d x) (Ici 0)) ∧
    (∀ x, HasFDerivAt (graph d) (graphDerivative d x) x) ∧
    Continuous (graphDerivative d) ∧ ContDiff ℝ 1 (graph d)

def AtOrigin : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H), graph d 0 = 0 ∧ fderiv ℝ (graph d) 0 = 0

end Specs.D13Unified.Ch16.TriangularGraphRegularity
