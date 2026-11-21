import MathGenome.ODEDynamics.Topics.D13Unified.Ch05
import MathGenome.ODEDynamics.Topics.D13Unified.Ch07
import MathGenome.ODEDynamics.Topics.D13Unified.Ch10
import MathGenome.ODEDynamics.Topics.D13Unified.Ch16
import MathGenome.ODEDynamics.Topics.D13Unified.Ch19

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Interval
namespace Examples.GenomeODEProbeSpecs

def zeroGronwallError : Prop :=
  ∀ (s T L : ℝ) (u : ℝ → ℝ), s ≤ T → 0 ≤ L →
    ContinuousOn u (Icc s T) → (∀ t ∈ Icc s T, 0 ≤ u t) →
    (∀ t ∈ Icc s T, u t ≤ ∫ r in s..t, L * u r) →
    ∀ t ∈ Icc s T, u t = 0

def orientationPreserved : Prop :=
  ∀ (n : ℕ) (I : D13Unified.TimeInterval)
    (A X : ℝ → Matrix (Fin n) (Fin n) ℝ),
    ContinuousOn A I.carrier →
    D13Unified.Ch07.EvolutionMatrix.IsFundamentalMatrixOn I A X →
    ∀ s ∈ I.carrier, 0 < (X s).det → ∀ t ∈ I.carrier, 0 < (X t).det

def dirichletPositiveGaps : Prop :=
  ∀ P : Specs.D13Unified.Ch10.RegularProblem.Problem,
    ∃ lam : ℕ → ℝ, StrictMono lam ∧ Tendsto lam atTop atTop ∧
      ∀ n, lam n < lam (n + 1)

def ergodicZeroMean (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∀ {X : Type} [MeasurableSpace X] (T : X → X) (μ : Measure X)
    [IsProbabilityMeasure μ],
    Specs.D13Unified.Ch19.MeasureDefinitions.PreservesMeasure T μ →
    Specs.D13Unified.Ch19.MeasureDefinitions.IsErgodic T μ →
    ∀ f : X → 𝕜, Integrable f μ → (∫ x, f x ∂μ) = 0 →
      ∀ᵐ x ∂μ, Tendsto
        (fun n => Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage T f n x)
        atTop (𝓝 0)

def realErgodicZeroMean : Prop := ergodicZeroMean ℝ
def complexErgodicZeroMean : Prop := ergodicZeroMean ℂ

def stableCycleWithLeastPeriod : Prop :=
  ∀ μ ω : ℝ, 0 < μ → 0 < ω →
    ∃ A : D13Unified.AutonomousODE ℂ, A.domain = univ ∧
      (∀ z, Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue A z =
        Specs.D13Unified.Ch16.HopfPolarExample.field μ ω z) ∧
      Specs.D13Unified.Ch16.PlanarHopf.LeastPeriodOrbit
        (Specs.D13Unified.Ch16.HopfPolarExample.field μ ω)
        (Specs.D13Unified.Ch16.HopfPolarExample.circle μ) (2 * Real.pi / ω) ∧
      Specs.D13Unified.Ch14.OrbitalDefinitions.orbitalAsymptoticallyStableValue A
        (Specs.D13Unified.Ch16.HopfPolarExample.circle μ)

end Examples.GenomeODEProbeSpecs
