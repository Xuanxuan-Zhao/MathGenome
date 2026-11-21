import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfPeriodicBranch
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.OrbitalDefinitions
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.StabilityDefinitions

/-!
Independent statement of paper.tex, Theorem d13:16:planar-hopf, lines 3699–3755.
The canonical normal form, spectral branches and first Lyapunov coefficient
are the upstream objects. The geometry retains the full fixed-neighborhood
classification and both amplitude asymptotics. The dynamical part concerns
actual physical-time solutions of the input family on a common open domain.
-/
noncomputable section
namespace Specs.D13Unified.Ch16.PlanarHopf
open Set Filter
open CubicHomologicalElimination CubicNormalForm HopfReturnExpansion HopfPeriodicBranch
open _root_.D13Unified
open Ch01.AutonomousParameters Ch12.StabilityDefinitions Ch14.OrbitalDefinitions

/-- A least period of an actual complete nonconstant solution with this trace.
Repeated periods cannot be used in the period limit. -/
def LeastPeriodOrbit (f : ℂ → ℂ) (Γ : Set ℂ) (T : ℝ) : Prop :=
  0 < T ∧ ∃ z : ℝ → ℂ, Function.Periodic z T ∧
    (∀ t : ℝ, HasDerivAt z (f (z t)) t) ∧
    (∃ s t : ℝ, z s ≠ z t) ∧ Γ = range z ∧
    ∀ S : ℝ, 0 < S → Function.Periodic z S → T ≤ S

/-- Strict return-multiplier conclusions, on a uniform smaller rectangle.
The map is the genuine return map supplied by ReturnData. -/
def MultiplierClassification : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω ε ρ δ C : ℝ) (P Q : ℝ × ℝ → ℝ),
    SourceHypotheses F ω → 0 < ε → 0 < δ → 0 < C →
    ReturnData F ω ε ρ δ C P Q →
    ∃ η > 0, ∃ d > 0, η ≤ ε ∧ d ≤ δ ∧
      ∀ μ r : ℝ, |μ| < η → r ∈ Ioo 0 d → P (r, μ) = r →
        0 < deriv (fun s => P (s, μ)) r ∧
        (firstLyapunovCoefficient F < 0 → deriv (fun s => P (s, μ)) r < 1) ∧
        (0 < firstLyapunovCoefficient F → 1 < deriv (fun s => P (s, μ)) r)

/-- The complete existence, uniqueness, amplitude and return-multiplier part.
This is a proper subset of the final theorem; it does not assert real-time
orbital stability or the period limit. -/
def Geometry : Prop := PeriodicBranch ∧ MultiplierClassification

/-- Proper subset of the full theorem: a common actual local ODE for the
input family and the two strict equilibrium conclusions. -/
def Equilibria : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε > 0, ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
    ∃ A : ℝ → AutonomousODE ℂ,
      (∀ μ : ℝ, |μ| < ε → (A μ).domain = U ∧
        (∀ z ∈ U, autonomousEvalValue (A μ) z = F (μ, z))) ∧
      ∀ μ : ℝ, |μ| < ε →
        ∃ hF : ContDiffOn ℝ 1 (autonomousEvalValue (A μ)) (A μ).domain,
        ∃ h0 : (0 : ℂ) ∈ (A μ).domain,
        ∃ heq : autonomousEvalValue (A μ) 0 = 0,
          (spectralReal F μ < 0 → locallyExponentiallyStableValue (A μ) hF h0 heq) ∧
          (0 < spectralReal F μ → unstableValue (A μ) hF h0 heq)

/-- Continuous-time conclusions for the original field, with no stability
certificate among the hypotheses. The single open U and parameter bound
are common to the orbit classification, the local ODE and period assertion.
The predicates use the canonical maximal flow and include forward existence.
There is deliberately no conclusion from spectralReal F 0 = 0 alone. -/
def Dynamics : Prop :=
  ∀ (F : ℝ × ℂ → ℂ) (ω : ℝ), SourceHypotheses F ω →
    ∃ ε > 0, ∃ U : Set ℂ, IsOpen U ∧ 0 ∈ U ∧
    ∃ A : ℝ → AutonomousODE ℂ,
      (∀ μ : ℝ, |μ| < ε → (A μ).domain = U ∧
        (∀ z ∈ U, autonomousEvalValue (A μ) z = F (μ, z))) ∧
      (∀ μ : ℝ, |μ| < ε →
        ∃ hF : ContDiffOn ℝ 1 (autonomousEvalValue (A μ)) (A μ).domain,
        ∃ h0 : (0 : ℂ) ∈ (A μ).domain,
        ∃ heq : autonomousEvalValue (A μ) 0 = 0,
          (spectralReal F μ < 0 → locallyExponentiallyStableValue (A μ) hF h0 heq) ∧
          (0 < spectralReal F μ → unstableValue (A μ) hF h0 heq) ∧
          ((∃ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ ∧ Γ ⊆ U) ↔
            spectralReal F μ * firstLyapunovCoefficient F < 0) ∧
          (∀ Γ Δ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
            IsPeriodicOrbit (fun z => F (μ,z)) Δ → Δ ⊆ U → Γ = Δ) ∧
          (∀ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
            (firstLyapunovCoefficient F < 0 → orbitalAsymptoticallyStableValue (A μ) Γ) ∧
            (0 < firstLyapunovCoefficient F → orbitalUnstableValue (A μ) Γ))) ∧
      (∀ κ > 0, ∃ ζ > 0, ∀ μ : ℝ, |μ| < min ε ζ →
        ∀ Γ : Set ℂ, IsPeriodicOrbit (fun z => F (μ,z)) Γ → Γ ⊆ U →
          ∃ T : ℝ, LeastPeriodOrbit (fun z => F (μ,z)) Γ T ∧
            |T - turnAngle / ω| < κ)

/-- Full original theorem under precisely the source hypotheses. -/
def PlanarHopf : Prop := Geometry ∧ Dynamics
end Specs.D13Unified.Ch16.PlanarHopf
