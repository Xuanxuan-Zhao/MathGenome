import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.TriangularGraphRegularity
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.InvariantGraph

/-! The full triangular theorem, with the same data and integral graph as the
regularity prerequisite. Solutions retain their actual open time intervals.
Invariance is asserted in both time directions, and tracking at every available
nonnegative time. Finite dimensions and the fixed norms are arbitrary. -/
noncomputable section
open Set
open scoped ContDiff
namespace D13Unified.Ch16.TriangularCenter
open TriangularGraphRegularity
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H]

def field (d : Data E H) (z : E × H) : E × H :=
  (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue d.slow z.1,
    -d.B z.2 + d.g z.1)

lemma field_contDiff (d : Data E H) : ContDiff ℝ 1 (field d) := by
  have hf : ContDiff ℝ 1
      (Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue d.slow) := by
    simpa [d.full_domain, contDiffOn_univ] using d.slow_c1
  exact (hf.comp contDiff_fst).prodMk
    ((d.B.contDiff.comp contDiff_snd).neg.add (d.g_c1.comp contDiff_fst))

def fullODE (d : Data E H) : ODE (E × H) :=
  InvariantGraph.odeOn univ isOpen_univ (field d) (field_contDiff d).continuous.continuousOn
end D13Unified.Ch16.TriangularCenter

namespace Specs.D13Unified.Ch16.TriangularCenter
open _root_.D13Unified _root_.D13Unified.Ch16.TriangularGraphRegularity
open _root_.D13Unified.Ch16.TriangularCenter
universe u v

def RegularityAndTangency : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H),
    ContDiff ℝ 1 (graph d) ∧ graph d 0 = 0 ∧ fderiv ℝ (graph d) 0 = 0 ∧
    ∀ x, fderiv ℝ (graph d) x
      (Ch01.AutonomousParameters.autonomousEvalValue d.slow x) =
        -d.B (graph d x) + d.g x

def LiftedSolutions : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H) (x : E),
    ContDiff ℝ 1 (fun r => (slowFlow d r x, graph d (slowFlow d r x))) ∧
    ∀ t : ℝ, HasDerivAt (fun r => (slowFlow d r x, graph d (slowFlow d r x)))
      (field d (slowFlow d t x, graph d (slowFlow d t x))) t

/-- Every initial point of every vertical fiber has a complete trajectory. -/
def CompleteSolutions : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H) (x : E) (y : H),
    let z : ℝ → E × H := fun t =>
      (slowFlow d t x, graph d (slowFlow d t x) + kernel d t (y - graph d x))
    ContDiff ℝ 1 z ∧ z 0 = (x, y) ∧
    ∀ t : ℝ, HasDerivAt z (field d (z t)) t

def Invariance : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H) (I : OpenTimeInterval) (z : ℝ → E × H) (s : ℝ),
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue (fullODE d) I z → s ∈ I.carrier →
    (z s).2 = graph d (z s).1 →
    ∀ t ∈ I.carrier, (z t).2 = graph d (z t).1

def Tracking : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (d : Data E H) (I : OpenTimeInterval) (z : ℝ → E × H),
    Specs.D13Unified.Ch01.SolutionConcepts.classicalSolutionOnValue (fullODE d) I z → 0 ∈ I.carrier →
    ∀ t ∈ I.carrier, 0 ≤ t →
      (z t).2 - graph d (z t).1 =
        kernel d t ((z 0).2 - graph d (z 0).1) ∧
      ‖(z t).2 - graph d (z t).1‖ ≤
        d.M * Real.exp (-d.β * t) * ‖(z 0).2 - graph d (z 0).1‖
end Specs.D13Unified.Ch16.TriangularCenter
